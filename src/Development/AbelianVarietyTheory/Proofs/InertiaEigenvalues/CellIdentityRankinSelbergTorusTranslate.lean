module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalLocalFactorNormSq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPairsEq
namespace GlobalTheory.WeightSumSplit

theorem sum_above {N : ℕ} (i : Fin N) (c : ℤ) :
    (∑ j : Fin N, if i < j then c else 0) = ((N : ℤ) - 1 - (i : ℕ)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi, nsmul_eq_mul]
  have hi := i.isLt
  congr 1
  omega

theorem sum_below {N : ℕ} (j : Fin N) (c : ℤ) :
    (∑ i : Fin N, if i < j then c else 0) = ((j : ℕ) : ℤ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio, nsmul_eq_mul]

theorem sum_pairs_eq (N : ℕ) (a : Fin N → ℤ) :
    (∑ i : Fin N, ∑ j : Fin N, if i < j then a i - a j else 0)
      = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  have h1 : ∀ i j : Fin N, (if i < j then a i - a j else 0) =
      (if i < j then a i else 0) - (if i < j then a j else 0) := by
    intro i j
    split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin N => if i < j then a j else 0)]
  simp_rw [sum_above, sum_below, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem wtS_eq : ∀ (N : ℕ) (a : Fin N → ℤ),
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((↑N : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * a i := by
  intro N a
  unfold GlobalTheory.CellDec.wtS
  exact sum_pairs_eq N a

end GlobalTheory.WeightSumSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalLocalFactorNormSq
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.RSCell

theorem wtS_eq_sum (N : ℕ) (a : Fin N → ℤ) :
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  first
  | exact @_root_.GlobalTheory.WeightSumSplit.wtS_eq
  | exact _root_.GlobalTheory.WeightSumSplit.wtS_eq
  | (apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSumSplit.wtS_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSumSplit.wtS_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSumSplit.wtS_eq ..)

theorem locFac_eq_wtS_sphZ : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α : Fin (n + 1) → ℂ) (x : ℝ) (ν : Fin (n + 1) → ℤ), 0 ≤ ν (Fin.last n) →
    ENNReal.ofReal ((q : ℝ) ^ GlobalTheory.CellDec.wtS (n + 1) ν) * ENNReal.ofReal ((q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) *
      ‖GlobalTheory.RSCell.sphZ q α ν‖ₑ ^ 2 = GlobalTheory.RSCell.locFac q α x ν := by
  intro q hq n α x ν hlast
  by_cases hA : Antitone ν
  · have hnn : ∀ i, 0 ≤ ν i := fun i => le_trans hlast (hA (Fin.le_last i))
    have hAn : Antitone (fun i => (ν i).toNat) := fun i j h => Int.toNat_le_toNat (hA h)
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hA, hnn⟩, GlobalTheory.RSCell.sphZ, if_pos hA, GlobalTheory.JSW.sphW, if_pos hAn]
    set s := GlobalTheory.JSW.schurAt (fun i => (ν i).toNat) α
    set w : ℤ := GlobalTheory.CellDec.wtS (n + 1) ν with hw
    have hc : (∑ i : Fin (n + 1), ((((n + 1 : ℕ)) : ℂ) - 1 - 2 * ((i : ℕ) : ℂ)) * (((ν i).toNat : ℕ) : ℂ)) = ((w : ℤ) : ℂ) := by
      rw [hw, wtS_eq_sum]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (((ν i).toNat : ℕ) : ℂ) = ((ν i : ℤ) : ℂ) by exact_mod_cast Int.toNat_of_nonneg (hnn i)]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hsum : (((∑ i, (ν i).toNat : ℕ)) : ℝ) = ∑ i, (ν i : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      exact_mod_cast Int.toNat_of_nonneg (hnn i)
    rw [hc, hsum]
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (zpow_nonneg hq'.le _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq]
    have hre : (-((w : ℂ)) / 2).re = -(w : ℝ) / 2 := by simp
    rw [hre, mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ (-(w : ℝ) / 2)), ← Real.rpow_mul hq'.le,
      ← Real.rpow_intCast]
    have h1 : (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) = 1 := by
      rw [← Real.rpow_add hq']
      norm_num
    calc (q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x)) *
          ((q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ)) * ‖s‖ ^ 2)
        = ((q : ℝ) ^ (w : ℝ) * (q : ℝ) ^ (-(w : ℝ) / 2 * ((2 : ℕ) : ℝ))) * (‖s‖ ^ 2 * (q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) := by ring
      _ = _ := by rw [h1, one_mul]
  · rw [GlobalTheory.RSCell.locFac, if_neg (fun h => hA h.1), GlobalTheory.RSCell.sphZ, if_neg hA]
    simp

end GlobalTheory.RSCell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalLocalFactorNormSqStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_local_factor_norm_sq : ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (α : Fin (n + 1) → ℂ) (x : ℝ) (ν : Fin (n + 1) → ℤ), 0 ≤ ν (Fin.last n) →
    ENNReal.ofReal ((q : ℝ) ^ GlobalTheory.CellDec.wtS (n + 1) ν) * ENNReal.ofReal ((q : ℝ) ^ (-((∑ i, (ν i : ℝ)) * x))) *
      ‖GlobalTheory.RSCell.sphZ q α ν‖ₑ ^ 2 = GlobalTheory.RSCell.locFac q α x ν := by
  first | exact @GlobalTheory.RSCell.locFac_eq_wtS_sphZ | exact GlobalTheory.RSCell.locFac_eq_wtS_sphZ | (intros; apply GlobalTheory.RSCell.locFac_eq_wtS_sphZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowDiagonalMulMemLatticeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowDiagonalMulMemLatticeIff
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.CellDec.RowPos
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_val (v : HeightOneSpectrum (𝓞 E)) (x : GA E n) (i j : Fin n) :
    (compV E n v x).val i j = pLoc E v (pFin E (x.val i j)) := rfl

theorem row_unip_mul {R : Type} [CommRing R] {m : ℕ} {U : GL (Fin (m + 1)) R}
    (hU : U ∈ GlobalTheory.SmGL.unipB R (Fin (m + 1))) (K : GL (Fin (m + 1)) R) (i : Fin (m + 1)) :
    (U * K).val (Fin.last m) i = K.val (Fin.last m) i := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hU
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · rw [h2, one_mul]
  · intro j _ hj
    rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sub_single_apply {m : ℕ} (y : Fin (m + 1) → Af E) (i : Fin (m + 1)) (v : HeightOneSpectrum (𝓞 E)) :
    (((y - Pi.single (Fin.last m) (1 : Af E)) : Fin (m + 1) → Af E) i) v = y i v - if i = Fin.last m then 1 else 0 := by
  change pLoc E v ((y - Pi.single (Fin.last m) (1 : Af E) : Fin (m + 1) → Af E) i) = pLoc E v (y i) - _
  rw [Pi.sub_apply, map_sub]
  congr 1
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]

theorem val_sub_ite_le_one {v : HeightOneSpectrum (𝓞 E)} {x : v.adicCompletion E} (hx : Valued.v x ≤ 1) (p : Prop)
    [Decidable p] : Valued.v (x - if p then 1 else 0) ≤ 1 := by
  refine (Valuation.map_sub _ _ _).trans (max_le hx ?_)
  split_ifs
  · rw [map_one]
  · rw [map_zero]; exact zero_le'

end GlobalTheory.CellDec.RowPos


open GlobalTheory.CellDec GlobalTheory.CellDec.RowPos in
theorem GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      ((fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈
        GlobalTheory.ThetaPoisson.latt (m + 1) J ↔
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J) := by
  intro E _ _ m T ϖ hϖ J hJ g hg l hl
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hgv : ∀ v i, (pFin E ((u * k).val (Fin.last m) i)) v = (compV E (m + 1) v k).val (Fin.last m) i := by
    intro v i
    change pLoc E v _ = _
    rw [← compV_val, map_mul, row_unip_mul (compV_mem_unipB v hu)]
  have htv : ∀ v i, (pFin E ((tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) v =
      ((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E) *
        (pFin E ((u * k).val (Fin.last m) i)) v := by
    intro v i
    change pLoc E v _ = _ * pLoc E v _
    rw [← compV_val, ← compV_val, map_mul (compV E (m + 1) v), compV_tl, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul]
  refine forall_congr' fun i => ?_
  rw [GroundTheory.Global.mem_idealFiniteAdeles, GroundTheory.Global.mem_idealFiniteAdeles]
  refine forall_congr' fun v => ?_
  rw [sub_single_apply, sub_single_apply]
  beta_reduce
  rw [htv]
  by_cases hv : v ∈ T
  · rw [l.2 v hv]
    simp
  · rw [hJ v hv]
    have hK := (GlobalTheory.AdelicU.mem_GLint_iff.1 (mem_US.1 hk v hv)).1 (Fin.last m) i
    have hK' : Valued.v ((compV E (m + 1) v k).val (Fin.last m) i) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hK
    have hϖ1 : Valued.v ((ϖ v : v.adicCompletion E)) ≤ 1 := by
      rw [hϖ v]; exact le_of_lt (by decide)
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (hl v)
    have hp : Valued.v (((ϖ v ^ (l.1 v (Fin.last m)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)) ≤ 1 := by
      rw [ha, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_one' hϖ1 a
    rw [hgv, neg_zero, WithZero.exp_zero]
    refine ⟨fun _ => val_sub_ite_le_one hK' _, fun _ => val_sub_ite_le_one ?_ _⟩
    rw [map_mul]
    exact mul_le_one' hp hK'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowDiagonalMulMemLatticeIffStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      ((fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈
        GlobalTheory.ThetaPoisson.latt (m + 1) J ↔
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J) := by
  first | exact @GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff | exact GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff | (intros; apply GlobalTheory.CellDec.lastRow_tl_mul_mem_latt_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleModuleDetDiagonalUniformiserMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleModuleDetDiagonalUniformiserMul
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.CellDec.DetMod

theorem prod_adl {E : Type} [Field E] [NumberField E] {ι : Type} (s : Finset ι)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : ι → HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    ∏ i ∈ s, GlobalTheory.CellDec.adl ϖ (m i) = GlobalTheory.CellDec.adl ϖ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.CellDec.adl_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, GlobalTheory.CellDec.adl_add]

theorem det_finGL' {E : Type} [Field E] [NumberField E] {a : ℕ} (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.det (finGL E a k) = finId E (GeneralLinearGroup.det k) := by
  let p : Ad E →+* InfiniteAdeleRing E := RingHom.fst (InfiniteAdeleRing E) (Af E)
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := GlobalTheory.CuspRep.det_map p (finGL E a k)
    have h0 : GeneralLinearGroup.map p (finGL E a k) = 1 :=
      map_cornerGL_of_zero (sFin E) p (fun x => rfl) k
    rw [h0, map_one, Units.val_one] at h
    change p _ = _
    rw [← h]
    change (1 : InfiniteAdeleRing E) = (1 : InfiniteAdeleRing E) - 0 + 0
    simp
  · have h := GlobalTheory.CuspRep.det_map (pFin E) (finGL E a k)
    have h0 : GeneralLinearGroup.map (pFin E) (finGL E a k) = GeneralLinearGroup.map (RingHom.id _) k :=
      map_cornerGL_of_hom (sFin E) (pFin E) (RingHom.id _) (fun x => rfl) k
    rw [h0] at h
    change pFin E _ = _
    rw [← h]
    change _ = (1 : Af E) - 1 + (GeneralLinearGroup.det k : (Af E)ˣ)
    rw [sub_self, zero_add]
    rfl

end GlobalTheory.CellDec.DetMod

theorem GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  intro E _ _ n ϖ hϖ l g
  rw [map_mul, map_mul, Positive.val_mul]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.SmGL.diagT (Af E) (Fin n)
      fun i => GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)) =
      ∏ i, GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal, Units.coe_prod]
  unfold GlobalTheory.CellDec.tl
  rw [GlobalTheory.CellDec.DetMod.det_finGL', hdet, GlobalTheory.CellDec.DetMod.prod_adl]
  rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support]
  · refine Finset.prod_congr rfl fun v _ => ?_
    congr 2
    rw [Finsupp.finsetSum_apply]
    rfl
  · intro v hv
    rw [Finsupp.notMem_support_iff] at hv
    rw [Finsupp.finsetSum_apply]
    simp [hv]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleModuleDetDiagonalUniformiserMulStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  first | exact @GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul | exact GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul | (intros; apply GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowSubSingleNotMemLatticeOfNegExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowSubSingleNotMemLatticeOfNegExponent
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.CellDec.lastRow_sub_notMem_latt : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (w : HeightOneSpectrum (𝓞 E)),
      l.1 w (Fin.last m) < 0 →
      (fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∉
        GlobalTheory.ThetaPoisson.latt (m + 1) J := by
  intro E _ _ m T ϖ hϖ J hJ g hg l w hlw hmem
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  have hwT : w ∉ T := fun h => by rw [l.2 w h] at hlw; simp at hlw
  set a := l.1 w (Fin.last m) with ha
  set K := GlobalTheory.CellDec.compV E (m+1) w k with hKdef
  have hK : K ∈ GlobalTheory.LFun.KGL w (n := (m+1)) := GlobalTheory.CellDec.mem_US.1 hk w hwT
  obtain ⟨-, hK2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have hU := (GlobalTheory.SmGL.mem_unipB _).1 (GlobalTheory.CellDec.compV_mem_unipB w hu)
  have hent : ∀ i, (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
      ((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i := by
    intro i
    have h1 : (pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k)).val (Fin.last m) i)) w =
        (GlobalTheory.CellDec.compV E (m+1) w (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * (u * k))).val (Fin.last m) i := rfl
    rw [h1, map_mul, map_mul, GlobalTheory.CellDec.compV_tl, Units.val_mul, Units.val_mul, GlobalTheory.IwaCell.val_tD,
      Matrix.diagonal_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [hU.2, one_mul]
    · intro j _ hj
      rw [hU.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

  have hb : ∀ i, Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i -
      (if i = Fin.last m then 1 else 0)) ≤ 1 := by
    intro i
    have h2 := (GroundTheory.Global.mem_idealFiniteAdeles J).1 (hmem i) w
    rw [hJ w hwT, neg_zero, WithZero.exp_zero] at h2
    convert h2 using 2
    rw [← hent i]
    by_cases hi : i = Fin.last m
    · subst hi; simp
    · simp [hi]
  have hϖv : Valued.v ((ϖ w : w.adicCompletion E)) = WithZero.exp (-1 : ℤ) := hϖ w
  have hrow : ∀ i, Valued.v (K.val (Fin.last m) i) < 1 := by
    intro i
    have hle : Valued.v (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) ≤ 1 := by
      by_cases hi : i = Fin.last m
      · have := hb i
        rw [if_pos hi] at this
        calc _ = Valued.v ((((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i - 1) + 1) := by
              rw [sub_add_cancel]
          _ ≤ max _ _ := Valuation.map_add _ _ _
          _ ≤ 1 := max_le this (by simp)
      · simpa [hi] using hb i
    have e : K.val (Fin.last m) i = ((ϖ w ^ (-a) : (w.adicCompletion E)ˣ) : w.adicCompletion E) *
        (((ϖ w ^ a : (w.adicCompletion E)ˣ) : w.adicCompletion E) * K.val (Fin.last m) i) := by
      rw [← mul_assoc, ← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_mul]
    rw [e, Valuation.map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖv, ← WithZero.exp_zsmul]
    have hlt : WithZero.exp ((-a) • (-1 : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; simp; omega
    calc _ ≤ WithZero.exp ((-a) • (-1 : ℤ)) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hlt
  have hone : ∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m) = 1 := by
    have := congrArg (fun M : Matrix (Fin (m+1)) (Fin (m+1)) (w.adicCompletion E) => M (Fin.last m) (Fin.last m))
      (Units.mul_inv K)
    simpa [Matrix.mul_apply] using this
  have hlt : Valued.v (∑ j, K.val (Fin.last m) j * (K⁻¹).val j (Fin.last m)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Valuation.map_mul]
    have hj : Valued.v ((K⁻¹).val j (Fin.last m)) ≤ 1 := hK2 j (Fin.last m)
    calc _ ≤ Valued.v (K.val (Fin.last m) j) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hrow j
  rw [hone, map_one] at hlt
  exact lt_irrefl _ hlt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowSubSingleNotMemLatticeOfNegExponentStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_sub_single_not_mem_lattice_of_neg_exponent : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ (l : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (w : HeightOneSpectrum (𝓞 E)),
      l.1 w (Fin.last m) < 0 →
      (fun i => pFin E ((GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g).val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∉
        GlobalTheory.ThetaPoisson.latt (m + 1) J := by
  first | exact @GlobalTheory.CellDec.lastRow_sub_notMem_latt | exact GlobalTheory.CellDec.lastRow_sub_notMem_latt | (intros; apply GlobalTheory.CellDec.lastRow_sub_notMem_latt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMirabolicWhittakerReductionCell
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMirabolicWhittakerReductionCell
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.WhitRed

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_eq (w : HeightOneSpectrum (𝓞 E)) (x : GA E n) :
    GlobalTheory.CellDec.compV E n w x = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem map_pLoc_prod_of_notMem (f : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (v : HeightOneSpectrum (𝓞 E)) : ∀ L : List (HeightOneSpectrum (𝓞 E)), v ∉ L →
    GeneralLinearGroup.map (pLoc E v) (L.map fun w => locGL E n w (f w)).prod = 1
  | [], _ => by simp
  | w :: L, h => by
    rw [List.mem_cons, not_or] at h
    rw [List.map_cons, List.prod_cons, map_mul, map_pLoc_prod_of_notMem f v L h.2, pLoc_locGL_of_ne h.1, one_mul]

theorem map_pLoc_prod_of_mem (f : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (v : HeightOneSpectrum (𝓞 E)) : ∀ L : List (HeightOneSpectrum (𝓞 E)), L.Nodup → v ∈ L →
    GeneralLinearGroup.map (pLoc E v) (L.map fun w => locGL E n w (f w)).prod = f v
  | [], _, h => absurd h List.not_mem_nil
  | w :: L, hL, h => by
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL, map_pLoc_prod_of_notMem f v L hL.1, mul_one]
    · rw [pLoc_locGL_of_ne hv, one_mul]
      exact map_pLoc_prod_of_mem f v L hL.2 ((List.mem_cons.1 h).resolve_left hv)

theorem row_mul_inv {R : Type} [CommRing R] {a : ℕ} (A B : GL (Fin a) R) (i : Fin a)
    (h : ∀ j, A.val i j = B.val i j) (j : Fin a) : (A * B⁻¹).val i j = (1 : Matrix (Fin a) (Fin a) R) i j := by
  have e : (A * B⁻¹).val i j = (B * B⁻¹).val i j := by
    simp only [Units.val_mul, Matrix.mul_apply, h]
  rw [e, mul_inv_cancel, Units.val_one]

variable [_root_.NumberField.IsTotallyComplex E]

theorem compV_infGL (w : HeightOneSpectrum (𝓞 E)) (y : GL (Fin n) (Cinf E)) :
    GlobalTheory.CellDec.compV E n w (infGL E n y) = 1 := by
  rw [compV_eq, pFin_infGL, map_one]

theorem comm_of_supp {x y : GA E n} (hinf : GeneralLinearGroup.map (pInf E) x = 1)
    (hw : ∀ w, GlobalTheory.CellDec.compV E n w x = 1 ∨ GlobalTheory.CellDec.compV E n w y = 1) : x * y = y * x := by
  refine ga_ext (by rw [map_mul, map_mul, hinf, one_mul, mul_one]) (GlobalTheory.CellDec.GL_ext_pLoc fun w => ?_)
  rw [map_mul, map_mul, map_mul, map_mul, ← compV_eq, ← compV_eq]
  rcases hw w with h | h <;> rw [h] <;> simp

end GlobalTheory.WhitRed


open GlobalTheory.WhitRed in
theorem GlobalTheory.WhitRed.exists_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ)
    (U : Subgroup (GL (Fin (m + 1)) (Af E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) →
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
        ‖GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
          (infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))))⁻¹)‖ =
        ‖GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l.1)‖ := by
  intro E _ _ _ m T ϖ F U J hU hK hN hκ g hg hu hy
  obtain ⟨u₁, hu₁, k, hk, he⟩ := hg
  have hrow : ∀ j, g.val (Fin.last m) j = k.val (Fin.last m) j := by
    intro j
    obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu₁
    rw [he, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
    · rw [h2, one_mul]
    · intro i _ hi
      rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last i) hi), zero_mul]
    · simp
  have hσrow : ∀ j, (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))).val (Fin.last m) j =
      pInf E (g.val (Fin.last m) j) := by
    intro j
    have := congrFun (GlobalTheory.RSTheta.single_vecMul_rowGL (ℓ := Fin.last m) (y := fun i => pInf E (g.val (Fin.last m) i)) hu) j
    rwa [Matrix.single_one_vecMul] at this
  generalize GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i)) = σ at hσrow ⊢
  obtain ⟨κ, hκU, hκoff, hκT⟩ := hκ _ hy
  obtain ⟨hf, hhf⟩ : ∃ hf : GL (Fin (m + 1)) (Af E),
      hf = (T.toList.map fun w => locGL E (m + 1) w (GlobalTheory.CellDec.compV E (m + 1) w k)).prod := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : GA E (m + 1), h = infGL E (m + 1) (GeneralLinearGroup.map (pInf E) k) * finGL E (m + 1) hf :=
    ⟨_, rfl⟩
  have hhinf : GeneralLinearGroup.map (pInf E) h = GeneralLinearGroup.map (pInf E) k := by
    rw [hh, map_mul, pInf_infGL, pInf_finGL, mul_one]
  have hhon : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w h = GlobalTheory.CellDec.compV E (m + 1) w k := by
    intro w hw
    rw [hh, map_mul, compV_infGL, one_mul, GlobalTheory.CellDec.compV_finGL, hhf,
      map_pLoc_prod_of_mem _ w _ T.nodup_toList (Finset.mem_toList.2 hw)]
  have hhoff : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w h = 1 := by
    intro w hw
    rw [hh, map_mul, compV_infGL, one_mul, GlobalTheory.CellDec.compV_finGL, hhf,
      map_pLoc_prod_of_notMem _ w _ (fun h' => hw (Finset.mem_toList.1 h'))]
  have hkT : h⁻¹ * k ∈ GlobalTheory.CellDec.US E (m + 1) T := by
    rw [GlobalTheory.CellDec.mem_US] at hk ⊢
    intro v hv
    rw [map_mul, map_inv, hhoff v hv, inv_one, one_mul]
    exact hk v hv
  have hkTinf : GeneralLinearGroup.map (pInf E) (h⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hhinf, inv_mul_cancel]
  have hkTT : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w (h⁻¹ * k) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hhon w hw, inv_mul_cancel]
  obtain ⟨p, hp⟩ : ∃ p : GA E (m + 1), p = h * (infGL E (m + 1) σ)⁻¹ * (finGL E (m + 1) κ)⁻¹ := ⟨_, rfl⟩
  have hpoff : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w p = 1 := by
    intro w hw
    rw [hp, map_mul, map_mul, map_inv, map_inv, hhoff w hw, compV_infGL, GlobalTheory.CellDec.compV_finGL, hκoff w hw]
    simp
  refine ⟨p, ⟨fun w hw => hpoff w hw, fun j => ?_⟩, fun l => ?_⟩
  · apply ad_ext
    · have e1 : pInf E (p.val (Fin.last m) j) = (GeneralLinearGroup.map (pInf E) p).val (Fin.last m) j := rfl
      have e2 : GeneralLinearGroup.map (pInf E) p = GeneralLinearGroup.map (pInf E) k * σ⁻¹ := by
        rw [hp, map_mul, map_mul, map_inv, map_inv, hhinf, pInf_infGL, pInf_finGL, inv_one, mul_one]
      have hkr : ∀ j, (GeneralLinearGroup.map (pInf E) k).val (Fin.last m) j = σ.val (Fin.last m) j := by
        intro j
        rw [hσrow, hrow]
        rfl
      rw [e1, e2, row_mul_inv _ _ _ hkr]
      by_cases hj : j = Fin.last m
      · subst hj; simp
      · rw [if_neg hj, map_zero, Matrix.one_apply_ne (Ne.symm hj)]
    · refine IsDedekindDomain.FiniteAdeleRing.ext _ fun w => ?_
      change (GlobalTheory.CellDec.compV E (m + 1) w p).val (Fin.last m) j =
        pLoc E w (pFin E (if j = Fin.last m then (1 : Ad E) else 0))
      have eR : pLoc E w (pFin E (if j = Fin.last m then (1 : Ad E) else 0)) =
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j := by
        by_cases hj : j = Fin.last m
        · subst hj; simp
        · rw [if_neg hj, map_zero, map_zero, Matrix.one_apply_ne (Ne.symm hj)]
      rw [eR]
      by_cases hw : w ∈ T
      · have e2 : GlobalTheory.CellDec.compV E (m + 1) w p =
            GlobalTheory.CellDec.compV E (m + 1) w k * (GeneralLinearGroup.map (pLoc E w) κ)⁻¹ := by
          rw [hp, map_mul, map_mul, map_inv, map_inv, hhon w hw, compV_infGL, GlobalTheory.CellDec.compV_finGL, inv_one, mul_one]
        rw [e2]
        refine row_mul_inv _ _ _ (fun j => ?_) j
        rw [hκT w hw j]
        show pLoc E w (pFin E (k.val _ _)) = _
        rw [← hrow]
      · rw [hpoff w hw]
        rfl
  · obtain ⟨t, ht⟩ : ∃ t : GA E (m + 1), t = GlobalTheory.CellDec.tl (m + 1) ϖ l.1 := ⟨_, rfl⟩
    rw [← ht]
    have htinf : GeneralLinearGroup.map (pInf E) t = 1 := by
      rw [ht, GlobalTheory.CellDec.tl]
      exact pInf_finGL _
    have htT : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w t = 1 := by
      intro w hw
      rw [ht, GlobalTheory.CellDec.compV_tl, l.2 w hw, GlobalTheory.IwaCell.tD_zero]
    have hc1 : (h⁻¹ * k) * (infGL E (m + 1) σ)⁻¹ = (infGL E (m + 1) σ)⁻¹ * (h⁻¹ * k) :=
      comm_of_supp hkTinf fun w => Or.inr (by rw [map_inv, compV_infGL, inv_one])
    have hc2 : t * p = p * t := comm_of_supp htinf fun w => by
      by_cases hw : w ∈ T
      · exact Or.inl (htT w hw)
      · exact Or.inr (hpoff w hw)
    have hp' : h * (infGL E (m + 1) σ)⁻¹ = p * finGL E (m + 1) κ := by
      rw [hp, inv_mul_cancel_right]
    have key : t * g * (infGL E (m + 1) σ)⁻¹ =
        (t * u₁ * t⁻¹) * ((p * t * finGL E (m + 1) κ) * (h⁻¹ * k)) := by
      calc t * g * (infGL E (m + 1) σ)⁻¹ = t * u₁ * (h * ((h⁻¹ * k) * (infGL E (m + 1) σ)⁻¹)) := by
            rw [he]; group
        _ = t * u₁ * ((h * (infGL E (m + 1) σ)⁻¹) * (h⁻¹ * k)) := by rw [hc1]; group
        _ = t * u₁ * t⁻¹ * ((t * p) * finGL E (m + 1) κ * (h⁻¹ * k)) := by rw [hp']; group
        _ = _ := by rw [hc2]
    have hu₁' : t * u₁ * t⁻¹ ∈ GlobalTheory.CellDec.NA E (m + 1) := by
      rw [ht]; exact GlobalTheory.CellDec.tl_conj_mem ϖ l.1 hu₁
    rw [key, hN _ hu₁', hK _ hkT hkTinf hkTT, hU κ hκU]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMirabolicWhittakerReductionCellStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mirabolic_whittaker_reduction_cell : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ)
    (U : Subgroup (GL (Fin (m + 1)) (Af E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) →
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
        ‖GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
          (infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))))⁻¹)‖ =
        ‖GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l.1)‖ := by
  first | exact @GlobalTheory.WhitRed.exists_mirabolic | exact GlobalTheory.WhitRed.exists_mirabolic | (intros; apply GlobalTheory.WhitRed.exists_mirabolic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellIdentityRankinSelbergTorusTranslate
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.CellPw

variable {E : Type} [Field E] [NumberField E]

theorem rowInf_tl [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n) (r : Fin n) :
    (fun i => pInf E ((GlobalTheory.CellDec.tl n ϖ l * g).val r i)) = fun i => pInf E (g.val r i) := by
  have h : GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl n ϖ l * g) = GeneralLinearGroup.map (pInf E) g := by
    rw [map_mul, GlobalTheory.CellDec.tl, pInf_finGL, one_mul]
  funext i
  exact congrArg (fun M : GL (Fin n) (Cinf E) => M.val r i) h

theorem bInt_of_not_mem [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∉ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h = 0 := by
  simp [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, Set.indicator_of_notMem hm]

theorem bInt_of_mem [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (h : GA E a)
    (hm : (fun i => pFin E (h.val ℓ i)) - η ∈ GlobalTheory.ThetaPoisson.latt a J) :
    GlobalTheory.RSCell.bInt ℓ F Φ J η x h =
      ENNReal.ofReal (‖GlobalTheory.JSW.whit F (h * (infGL E a (GlobalTheory.RSTheta.rowGL ℓ (fun i => pInf E (h.val ℓ i))))⁻¹)‖ ^ 2 *
        ‖Φ (fun i => pInf E (h.val ℓ i))‖ * (ideleModule E (GeneralLinearGroup.det h) : ℝ) ^ x) := by
  rw [GlobalTheory.RSCell.bInt, GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf, Set.indicator_of_mem hm,
    ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1
  simp only [Pi.one_apply, mul_one, norm_mul, Complex.norm_conj]
  ring

theorem prod_supp_add {n : ℕ} (q : HeightOneSpectrum (𝓞 E) → ℝ) (hq : ∀ v, q v ≠ 0) (f : (Fin n → ℤ) →+ ℤ)
    (a b : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    ∏ v ∈ (a + b).support, q v ^ f ((a + b) v) =
      (∏ v ∈ a.support, q v ^ f (a v)) * ∏ v ∈ b.support, q v ^ f (b v) := by
  have := Finsupp.prod_add_index' (f := a) (g := b) (h := fun v y => q v ^ f y) (fun v => by simp)
    (fun v y₁ y₂ => by simp [zpow_add₀ (hq v)])
  simpa [Finsupp.prod] using this

def wtSHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun := GlobalTheory.CellDec.wtS n
  map_zero' := by simp [GlobalTheory.CellDec.wtS]
  map_add' a b := by
    simp only [GlobalTheory.CellDec.wtS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp <;> ring

def negSumHom (n : ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun a := -∑ i, a i
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]; ring


omit [Field E] [NumberField E] in
theorem cell_identity : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ) (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T)
      (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
        ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (l.1 w))) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ (x : ℝ), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
        ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) *
          GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) := by
  intro E _ _ _ m T ϖ hϖ α F l₀ U Φ J hl₀ hU hK hN hprof hΦ hJ horb x g hg l
  have hνT : ∀ v ∈ T, (l.1 - l₀.1) v = 0 := fun v hv => by simp [l.2 v hv, l₀.2 v hv]
  let ν : GlobalTheory.CellDec.abelian₂ E (m + 1) T := ⟨l.1 - l₀.1, hνT⟩
  have hνl : l₀.1 + ν.1 = l.1 := by simp [ν]
  have hνw : ∀ w, ν.1 w (Fin.last m) = l.1 w (Fin.last m) := fun w => by simp [ν, hl₀ w]
  by_cases hneg : ∃ w, l.1 w (Fin.last m) < 0
  · obtain ⟨w, hw⟩ := hneg
    have hwT : w ∉ T := fun h => by simp [l.2 w h] at hw
    rw [bInt_of_not_mem _ _ _ _ _ _ _ (GlobalTheory.T.lastRow_sub_single_not_mem_lattice_of_neg_exponent E m T ϖ hϖ J hJ g hg l w hw)]
    have h2 : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = 0 := by
      refine Finset.prod_eq_zero (i := w) ?_ ?_
      · rw [Finsupp.mem_support_iff]
        intro h
        have := congrFun h (Fin.last m)
        simp [hl₀ w] at this
        omega
      · rw [dite_eq_right hwT]
        exact GlobalTheory.RSCell.locFac_of_neg _ _ _ (i := Fin.last m) (by simp [hl₀ w]; exact hw)
    rw [h2]
    simp
  push_neg at hneg
  have hl₀n : ∀ w, 0 ≤ l₀.1 w (Fin.last m) := fun w => (hl₀ w).ge
  have hposl := GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff E m T ϖ hϖ J hJ g hg l hneg
  have hposl₀ := GlobalTheory.T.lastRow_diagonal_mul_mem_lattice_iff E m T ϖ hϖ J hJ g hg l₀ hl₀n
  by_cases hI : (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J
  swap
  · rw [bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl.1 h)),
      bInt_of_not_mem _ _ _ _ _ _ _ (fun h => hI (hposl₀.1 h))]
    simp
  rw [bInt_of_mem _ _ _ _ _ _ _ (hposl.2 hI), bInt_of_mem _ _ _ _ _ _ _ (hposl₀.2 hI),
    rowInf_tl, rowInf_tl]
  set u : Fin (m + 1) → Cinf E := fun i => pInf E (g.val (Fin.last m) i) with hu
  by_cases hΦu : Φ u = 0
  · simp [hΦu]
  have hunit : IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) :=
    GlobalTheory.RSTheta.isUnit_of_mem_rowSet (hΦ (subset_tsupport _ hΦu))
  obtain ⟨p, hp, hpl⟩ := GlobalTheory.T.exists_mirabolic_whittaker_reduction_cell E m T ϖ F U J hU hK hN horb g hg hunit hI
  rw [hpl l, hpl l₀, GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul E (m + 1) ϖ hϖ l.1 g, GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul E (m + 1) ϖ hϖ l₀.1 g]
  have hpr := hprof p hp ν (fun w => by rw [hνw]; exact hneg w)
  rw [hνl] at hpr
  rw [hpr]

  have hq : ∀ v : HeightOneSpectrum (𝓞 E), (qV E v : ℝ) ≠ 0 := fun v => by
    rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hqpos : ∀ v : HeightOneSpectrum (𝓞 E), 0 < (qV E v : ℝ) := fun v =>
    lt_of_le_of_ne (Nat.cast_nonneg _) (hq v).symm
  have hcell : GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) = ENNReal.ofReal (∏ w ∈ ν.1.support,
      ((qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) * (qV E w : ℝ) ^ (-((∑ i, (ν.1 w i : ℝ)) * x)) *
        ‖(if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (ν.1 w))‖ ^ 2)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => by positivity)]
    refine Finset.prod_congr rfl fun w hw => ?_
    have hwT : w ∉ T := fun h => (Finsupp.mem_support_iff.1 hw) (hνT w h)
    rw [dite_eq_right hwT, dite_eq_right hwT, ← GlobalTheory.T.spherical_local_factor_norm_sq (Ideal.absNorm w.asIdeal) (Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)) m (α ⟨w, hwT⟩) x (ν.1 w) (by rw [hνw]; exact hneg w),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
    rfl
  have hd0 : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ), 0 ≤ GlobalTheory.CellDec.dinv (m + 1) k := fun k =>
    Finset.prod_nonneg fun v _ => (zpow_pos (hqpos v) _).le
  rw [hcell, ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (hd0 _), ← ENNReal.ofReal_mul (mul_nonneg (hd0 _) <| mul_nonneg (mul_nonneg (by positivity) (norm_nonneg _))
    (Real.rpow_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le)
      ((ideleModule E (GeneralLinearGroup.det g)).2.le)) _))]
  congr 1
  have hd : GlobalTheory.CellDec.dinv (m + 1) l.1 = GlobalTheory.CellDec.dinv (m + 1) l₀.1 *
      ∏ w ∈ ν.1.support, (qV E w : ℝ) ^ GlobalTheory.CellDec.wtS (m + 1) (ν.1 w) := by
    rw [← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (wtSHom (m + 1)) l₀.1 ν.1
  have hQ : ∀ k : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ),
      ∏ v ∈ k.support, ((qV E v : ℝ) ^ ∑ i, k v i)⁻¹ = ∏ v ∈ k.support, (qV E v : ℝ) ^ negSumHom (m + 1) (k v) := by
    intro k
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← _root_.zpow_neg]; rfl
  have hQl : ∏ v ∈ l.1.support, ((qV E v : ℝ) ^ ∑ i, l.1 v i)⁻¹ =
      (∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹) * ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ := by
    rw [hQ, hQ, hQ, ← hνl]
    exact prod_supp_add (fun v => (qV E v : ℝ)) hq (negSumHom (m + 1)) l₀.1 ν.1
  have hQν : (∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x =
      ∏ v ∈ ν.1.support, (qV E v : ℝ) ^ (-((∑ i, (ν.1 v i : ℝ)) * x)) := by
    have hprod : ∀ s : Finset (HeightOneSpectrum (𝓞 E)),
        (∏ v ∈ s, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x =
          ∏ v ∈ s, (((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹) ^ x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha,
          Real.mul_rpow (inv_pos.2 (zpow_pos (hqpos a) _)).le
            (Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le), ih]
    rw [hprod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_neg (hqpos v).le, ← Real.rpow_mul (hqpos v).le]
    push_cast
    ring_nf
  have hD := ((ideleModule E (GeneralLinearGroup.det g)).2 : (0 : ℝ) < _)
  have hQ₀ : 0 ≤ ∏ v ∈ l₀.1.support, ((qV E v : ℝ) ^ ∑ i, l₀.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  have hQν0 : 0 ≤ ∏ v ∈ ν.1.support, ((qV E v : ℝ) ^ ∑ i, ν.1 v i)⁻¹ :=
    Finset.prod_nonneg fun v _ => (inv_pos.2 (zpow_pos (hqpos v) _)).le
  rw [hd, hQl, Real.mul_rpow (mul_nonneg hQ₀ hQν0) hD.le, Real.mul_rpow hQ₀ hQν0, hQν, Real.mul_rpow hQ₀ hD.le,
    norm_mul, norm_prod, mul_pow, ← Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end GlobalTheory.CellPw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellIdentityRankinSelbergTorusTranslateStatement
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_identity_rankinSelberg_torus_translate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ) (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T)
      (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) T ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀.1 + l.1)) = GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) *
        ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) (l.1 w))) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ (x : ℝ), ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
      ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
        ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) *
          GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) := by
  first | exact @GlobalTheory.CellPw.cell_identity | exact GlobalTheory.CellPw.cell_identity | (intros; apply GlobalTheory.CellPw.cell_identity <;> assumption)
end
