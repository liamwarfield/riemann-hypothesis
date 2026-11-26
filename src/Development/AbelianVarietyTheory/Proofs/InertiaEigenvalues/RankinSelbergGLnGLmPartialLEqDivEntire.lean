module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatchedWhittakerVectorsShintaniRelations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmUnfoldingToMirabolicStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValLastRowEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergCellIntegralFinitePartNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeries
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.RSnmEul

open GlobalTheory.ZEul GlobalTheory.RSnmUnf

def padInt {m n : ℕ} (_h : m ≤ n) (v : Fin m → ℤ) : Fin n → ℤ :=
  fun i => if hi : (i : ℕ) < m then v ⟨i, hi⟩ else 0

theorem padInt_injective {m n : ℕ} (h : m ≤ n) : Function.Injective (padInt h) := by
  intro v w hvw
  funext j
  have := congrFun hvw ⟨j, lt_of_lt_of_le j.2 h⟩
  simpa [padInt, j.2] using this

theorem padInt_zero {m n : ℕ} (h : m ≤ n) : padInt h (0 : Fin m → ℤ) = 0 := by
  funext i; simp only [padInt, Pi.zero_apply]; split_ifs <;> rfl

theorem padInt_valid {m n : ℕ} (h : m ≤ n) {v : Fin m → ℤ} (hv : (∀ i, 0 ≤ v i) ∧ Antitone v) :
    (∀ i, 0 ≤ padInt h v i) ∧ Antitone (padInt h v) := by
  have hnn : ∀ i, 0 ≤ padInt h v i := by
    intro i; unfold padInt; split_ifs
    · exact hv.1 _
    · exact le_rfl
  refine ⟨hnn, fun a b hab => ?_⟩
  by_cases hb : (b : ℕ) < m
  · have ha : (a : ℕ) < m := lt_of_le_of_lt hab hb
    simp only [padInt, ha, hb, dite_true]
    exact hv.2 (show (⟨a, ha⟩ : Fin m) ≤ ⟨b, hb⟩ from hab)
  · have : padInt h v b = 0 := by simp [padInt, hb]
    rw [this]; exact hnn a

theorem toNat_padInt {m n : ℕ} (h : m ≤ n) (v : Fin m → ℤ) :
    (fun i => (padInt h v i).toNat) = padNat (n := n) (fun i => (v i).toNat) := by
  funext i; simp only [padInt, padNat]; split_ifs <;> simp

theorem sum_padNat {m n : ℕ} (h : m ≤ n) (l : Fin m → ℕ) : ∑ i, padNat (n := n) l i = ∑ i, l i := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro c hc
    have : ¬ (c : ℕ) < m := fun hcm => hc ⟨⟨c, hcm⟩, Fin.ext rfl⟩
    simp [padNat, this]
  · intro i; simp [padNat, i.2]

theorem norm_rsTermNM_le (q : ℕ) (hq : 0 < q) {m n : ℕ} (h : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ)
    (v : Fin m → ℤ) :
    ‖rsTermNM q α β x v‖ ≤ (sqTerm q α x (padInt h v) + sqTerm q β x v) / 2 := by
  by_cases hv : (∀ i, 0 ≤ v i) ∧ Antitone v
  · rw [rsTermNM, if_pos hv, sqTerm, if_pos (padInt_valid h hv), sqTerm, if_pos hv, toNat_padInt h v,
      sum_padNat h, norm_mul, norm_mul, Complex.norm_conj, norm_cpow_pow q hq]
    have hw : 0 ≤ (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_nonneg (sq_nonneg (‖schurAt (padNat (n := n) fun i => (v i).toNat) α‖ -
      ‖schurAt (fun i => (v i).toNat) β‖)) hw]
  · rw [rsTermNM, if_neg hv, norm_zero]
    exact div_nonneg (add_nonneg (sqTerm_nonneg _ _ _ _) (sqTerm_nonneg _ _ _ _)) zero_le_two

theorem rsTermNM_zero (q : ℕ) {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) : rsTermNM q α β x 0 = 1 := by
  have h : (fun _ : Fin m => (0 : ℕ)) = fun i => ((0 : Fin m → ℤ) i).toNat := by funext i; simp
  have hs : schurAt (padNat (n := n) fun i => ((0 : Fin m → ℤ) i).toNat) α = 1 := by
    rw [← h]
    have : (padNat (n := n) fun _ : Fin m => (0 : ℕ)) = fun _ => 0 := padNat_zero
    rw [this, schurAt, schur_zero]; simp
  have hs' : schurAt (fun i => ((0 : Fin m → ℤ) i).toNat) β = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  rw [rsTermNM, if_pos ⟨fun i => le_rfl, antitone_const⟩, hs, hs']
  simp

theorem rsTermNM_partVec (q : ℕ) {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ)
    (l : {l : Fin m → ℕ // Antitone l}) :
    rsTermNM q α β x (partVec l) =
      schurAt (padNat (n := n) l.1) α * conj (schurAt l.1 β) * ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) := by
  rw [rsTermNM, if_pos (partVec_valid l)]
  simp [partVec]

end GlobalTheory.RSnmEul

namespace GlobalTheory.RSnmEul

open GlobalTheory.ZEul GlobalTheory.RSnmUnf

theorem hasSum_rsTermNM_local (q : ℕ) {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂˣ) (β : Fin m → ℂˣ) (x : ℝ)
    (hs : Summable fun v : Fin m → ℤ => ‖rsTermNM q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v‖) :
    HasSum (fun v => rsTermNM q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v)
      (locL q (Finset.univ.val.map α) ((Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom))
        (x : ℂ)) := by
  set β' : Fin m → ℂˣ := fun j => Units.map (starRingEnd ℂ).toMonoidHom (β j) with hβ'
  have hconj : ∀ l : Fin m → ℕ, schurAt l (fun j => (β' j : ℂ)) = conj (schurAt l fun j => (β j : ℂ)) := by
    intro l
    rw [schurAt, schurAt, MvPolynomial.eval₂_comp_left, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
      (Int.castRingHom ℂ)]
    rfl
  have hpad : ∀ l : Fin m → ℕ, padTo hmn l = padNat (n := n) l := fun l => rfl
  have hm : (Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom) = Finset.univ.val.map β' :=
    Multiset.map_map _ _ _
  rw [hm]
  have hs' : Summable fun l : {l : Fin m → ℕ // Antitone l} =>
      ‖schurAt (padTo hmn l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β' j : ℂ))‖ *
        ‖(q : ℂ) ^ (-(x : ℂ))‖ ^ (∑ i, l.1 i) := by
    refine (hs.comp_injective partVec_injective).congr fun l => ?_
    simp only [Function.comp, rsTermNM_partVec, hpad, hconj, norm_mul, norm_pow, Complex.norm_conj]
  have hc := cauchy_locL hmn α β' q (x : ℂ) hs'
  rw [← (partVec_injective (n := m)).hasSum_iff]
  · convert hc using 1
    funext l
    simp only [Function.comp, rsTermNM_partVec, hpad, hconj]
  · intro v hv
    by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
    · exact absurd (mem_range_partVec hval) hv
    · rw [rsTermNM, if_neg hval]

theorem euler_rsTermNM : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  intro I q n m hmn α β x _ hq hα hβ
  set f : I → (Fin m → ℤ) → ℂ := fun i v => rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v
    with hfdef
  have hf0 : ∀ i, f i 0 = 1 := fun i => rsTermNM_zero _ _ _ _
  have hA := summable_sqTerm q (fun i j => (α i j : ℂ)) x hα
  have hB := summable_sqTerm q (fun i j => (β i j : ℂ)) x hβ
  have hinj : Function.Injective fun p : I × {v : Fin m → ℤ // v ≠ 0} =>
      ((p.1, ⟨padInt hmn p.2.1, fun h0 => p.2.2 (padInt_injective hmn (h0.trans (padInt_zero hmn).symm))⟩) :
        I × {v : Fin n → ℤ // v ≠ 0}) := by
    intro p p' hp
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hp
    exact Prod.ext hp.1 (Subtype.ext (padInt_injective hmn hp.2))
  have hA' := hA.comp_injective hinj
  have hsum : Summable fun p : I × {v : Fin m → ℤ // v ≠ 0} => ‖f p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by
        simpa only [hfdef, Function.comp_apply] using norm_rsTermNM_le (q p.1) (by have := hq p.1; omega) hmn
          (fun j => (α p.1 j : ℂ)) (fun j => (β p.1 j : ℂ)) x p.2.1) ((hA'.add hB).div_const 2)
  obtain ⟨hN, hP, -⟩ := GlobalTheory.EulerSum.euler_product_intVec m f hf0 hsum
  have hloc : ∀ i, ∑' v, f i v = locL (q i) (Finset.univ.val.map (α i))
      ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) :=
    fun i => (hasSum_rsTermNM_local (q i) hmn (α i) (β i) x (GlobalTheory.EulerSum.summable_norm_local f hsum i)).tsum_eq
  refine ⟨∑' l : I →₀ (Fin m → ℤ), l.prod f, ?_, hN.of_norm.hasSum⟩
  simpa only [hloc] using hP

end GlobalTheory.RSnmEul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeriesStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  first | (exact @GlobalTheory.RSnmEul.euler_rsTermNM) | (exact GlobalTheory.RSnmEul.euler_rsTermNM) | (intros; apply GlobalTheory.RSnmEul.euler_rsTermNM  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumPadTermNeTop
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section
namespace GlobalTheory.RSCellEul

open GlobalTheory.RSnmEul GlobalTheory.RSnmUnf

theorem term_le_locFac {m k : ℕ} (h : m + 1 ≤ k) (q : ℕ) (a : Fin k → ℂ) (x : ℝ) (v : Fin (m + 1) → ℤ) :
    (if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≤
      GlobalTheory.RSCell.locFac q a x (padInt h v) := by
  split_ifs with hv
  · have hv' := padInt_valid h hv
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hv'.2, hv'.1⟩, toNat_padInt h v, sum_padNat h]
  · exact bot_le

theorem term_zero {m k : ℕ} (q : ℕ) (a : Fin k → ℂ) (x : ℝ) :
    (if (∀ i, 0 ≤ (0 : Fin (m + 1) → ℤ) i) ∧ Antitone (0 : Fin (m + 1) → ℤ) then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => ((0 : Fin (m + 1) → ℤ) i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, ((0 : Fin (m + 1) → ℤ) i).toNat : ℕ) : ℝ) * x))) else 0) = 1 := by
  have h0 : (fun i : Fin (m + 1) => ((0 : Fin (m + 1) → ℤ) i).toNat) = 0 := funext fun _ => rfl
  rw [if_pos ⟨fun _ => le_rfl, fun _ _ _ => le_rfl⟩, h0, padNat_zero]
  rw [show (0 : Fin k → ℕ) = fun _ => 0 from rfl, GlobalTheory.RSPole.EulerPole.schurAt_const_zero]
  simp

theorem tprod_le_of_one_le {I : Type} (f g : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    ∏' i, f i ≤ ∏' i, g i := by
  have hg : ∀ i, 1 ≤ g i := fun i => (hf i).trans (hfg i)
  rw [(GlobalTheory.RSPole.EulerPole.hasProd_of_one_le f hf).tprod_eq, (GlobalTheory.RSPole.EulerPole.hasProd_of_one_le g hg).tprod_eq]
  exact iSup_mono fun s => Finset.prod_le_prod' fun i _ => hfg i

theorem tsum_padTerm_ne_top : ∀ (E : Type) [Field E] [NumberField E] (m k : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), m + 1 ≤ k →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin k → ℂ) (x : ℝ),
    GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => α w.1 i) x ≠ ⊤ →
    ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (l.1.prod fun w v => if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
            (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≠ ⊤ := by
  intro E _ _ m k S hmk α x hfin
  classical
  let g : HeightOneSpectrum (𝓞 E) → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun w v =>
    if (∀ i, 0 ≤ v i) ∧ Antitone v then
      ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
        (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0
  show ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g ≠ ⊤
  have hg0 : ∀ w, g w 0 = 1 := fun w => term_zero _ _ _
  obtain ⟨e, he⟩ := GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  let f : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun i v => g i.1 v
  have h1 : ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g = ∑' l' : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l'.prod f := by
    rw [← e.tsum_eq]; exact tsum_congr fun l => (he ℝ≥0∞ g hg0 l).symm
  rw [h1, (GlobalTheory.EulerSum.euler_product_intVec_ennreal (m + 1) f fun i => hg0 i.1).2]
  refine ne_top_of_le_ne_top hfin ?_
  rw [GlobalTheory.RSPole.eulD]
  refine tprod_le_of_one_le _ _ (fun i => ?_) (fun i => ?_)
  · exact le_of_eq_of_le (hg0 i.1).symm (ENNReal.le_tsum (f := f i) 0)
  · rw [GlobalTheory.RSCellSum.schurDir_eq_tsum_locFac]
    calc ∑' v, f i v ≤ ∑' v, GlobalTheory.RSCell.locFac (Ideal.absNorm i.1.asIdeal) (α i.1) x (padInt hmk v) :=
          ENNReal.tsum_le_tsum fun v => term_le_locFac hmk _ _ _ v
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (padInt_injective hmk) _

end GlobalTheory.RSCellEul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFourierGaussLattice
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.FourierCell

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped nonZeroDivisors SchwartzMap

variable {E : Type} [Field E] [NumberField E]

theorem finId_val (u : (Af E)ˣ) :
    ((finId E u : (Ad E)ˣ) : Ad E) = ((1, (u : Af E)) : InfiniteAdeleRing E × Af E) := by
  change (1 - sFin E 1 + sFin E (u : Af E) : Ad E) = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp
  · change (1 : Af E) - 1 + (u : Af E) = u
    simp

theorem mem_one_iff (x : Af E) :
    x ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 E)⁰ E)ˣ) ↔ ∀ v, Valued.v (pLoc E v x) ≤ 1 := by
  simp only [mem_idealFiniteAdeles, Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  rfl

theorem val_zpow_unif {w : HeightOneSpectrum (𝓞 E)} {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) (n : ℤ) :
    Valued.v (ϖ ^ n) = ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, h, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  simp

theorem ofAdd_le_one_iff (n : ℤ) :
    ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 ↔ n ≤ 0 := by
  rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]

theorem exists_fourier_gauss_lattice : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (y₀ : Fin (m + 1) → Ad E),
    (∀ w ∉ S, ∀ j, pLoc E w (pFin E (y₀ j)) ∈ w.adicCompletionIntegers E) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
      Continuous (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F) ∧
      (∀ y, 0 ≤ (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).re ∧
        (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y).im = 0) ∧
      0 < (GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y₀).re ∧
      ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
      ∀ a : HeightOneSpectrum (𝓞 E) →₀ ℤ, (∀ v ∈ S, a v = 0) →
      ∀ y : Fin (m + 1) → Ad E,
        (∀ w ∉ S, (∀ j, pLoc E w (pFin E (y j)) ∈ w.adicCompletionIntegers E) ∧
          ∃ j, Valued.v (pLoc E w (pFin E (y j))) = 1) →
        ((∀ w, 0 ≤ a w) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) =
          GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F y) ∧
        ((∃ w, a w < 0) → GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F
            (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = 0) := by
  intro E _ _ _ m S y₀ hy₀
  classical
  let φ : 𝓢(Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidean (E := Fin (m + 1) → NumberField.mixedEmbedding.mixedSpace E))
      (GroundTheory.Global.gaussianSchwartz _)
  have hφ : ∀ x, φ x = ((Real.exp (-Real.pi * ‖toEuclidean x‖ ^ 2) : ℝ) : ℂ) := fun x => by
    simp [φ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  let g : (Fin (m + 1) → Af E) → ℂ := finiteTensor fun j => cosetIndicator 1 (pFin E (y₀ j))
  have hg : g ∈ finiteSchwartzBruhatPi E :=
    finiteTensor_mem fun j => cosetIndicator_mem_finiteSchwartzBruhat _ _
  let G := schwartzBruhatTensorPi φ g
  have hG : G ∈ schwartzBruhatPi (K := E) (ι := Fin (m + 1)) := schwartzBruhatTensorPi_mem φ hg
  have hG1 := adelicFourierPi_mem_schwartzBruhatPi hG
  have hG2 := adelicFourierPi_mem_schwartzBruhatPi hG1
  have hG3 := adelicFourierPi_mem_schwartzBruhatPi hG2
  have hFG : adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) = G := by
    rw [adelicFourierPi_adelicFourierPi hG2, adelicFourierPi_adelicFourierPi hG]
    funext x
    simp
  have hGv : ∀ y, G y = φ (infPartPi y) *
      if ∀ j v, Valued.v (pLoc E v (pFin E (y j)) - pLoc E v (pFin E (y₀ j))) ≤ 1 then 1 else 0 := by
    intro y
    simp only [G, g, schwartzBruhatTensorPi, finiteTensor, cosetIndicator_apply, Finset.prod_boole,
      Finset.mem_univ, true_implies, mem_one_iff, map_sub]
    rfl
  refine ⟨adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G)), hG3, ?_, ?_, ?_, ?_⟩
  · rw [hFG]; exact continuous_of_mem_schwartzBruhatPi hG
  · intro y
    rw [hFG, hGv, hφ]
    split_ifs
    · rw [mul_one]
      exact ⟨by rw [Complex.ofReal_re]; exact (Real.exp_pos _).le, Complex.ofReal_im _⟩
    · rw [mul_zero]
      exact ⟨le_refl _, rfl⟩
  · rw [hFG, hGv, hφ, if_pos (fun j v => by simp)]
    rw [mul_one, Complex.ofReal_re]
    exact Real.exp_pos _
  · intro ϖ hϖ a ha y hy
    have hFy : ∀ z, adelicFourierPi E (adelicFourierPi E (adelicFourierPi E (adelicFourierPi E G))) z = G z :=
      fun z => by rw [hFG]
    have hinf : infPartPi (fun j => ((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j) = infPartPi y := by
      funext j
      simp only [infPartPi, finId_val]
      congr 1
      change (1 : InfiniteAdeleRing E) * (y j).1 = (y j).1
      exact one_mul _
    have hfin : ∀ j v, pLoc E v (pFin E (((finId E (GlobalTheory.CellDec.adl ϖ a) : (Ad E)ˣ) : Ad E) * y j)) =
        ((ϖ v : v.adicCompletion E) ^ a v) * pLoc E v (pFin E (y j)) := by
      intro j v
      rw [map_mul, map_mul, finId_val]
      change ((ϖ v ^ a v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * _ = _
      rw [Units.val_zpow_eq_zpow_val]
    have hint : ∀ w ∉ S, ∀ j, Valued.v (pLoc E w (pFin E (y₀ j))) ≤ 1 := fun w hw j => by
      simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using hy₀ w hw j
    constructor
    · intro hpos
      rw [hFy, hFy, hGv, hGv, hinf]
      congr 1
      refine if_congr ?_ rfl rfl
      refine forall_congr' fun j => forall_congr' fun v => ?_
      rw [hfin]
      by_cases hv : v ∈ S
      · rw [ha v hv, zpow_zero, one_mul]
      · have h1 := hint v hv j
        have h2 : Valued.v (pLoc E v (pFin E (y j))) ≤ 1 := by
          simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using (hy v hv).1 j
        have h3 : Valued.v ((ϖ v : v.adicCompletion E) ^ a v) ≤ 1 := by
          rw [val_zpow_unif (hϖ v), ofAdd_le_one_iff]
          linarith [hpos v]
        have key : ∀ t, Valued.v t ≤ 1 → Valued.v (t - pLoc E v (pFin E (y₀ j))) ≤ 1 :=
          fun t ht => (Valuation.map_sub _ _ _).trans (max_le ht h1)
        exact iff_of_true (key _ (by rw [map_mul]; exact mul_le_one' h3 h2)) (key _ h2)
    · rintro ⟨w, hw⟩
      rw [hFy, hGv, if_neg, mul_zero]
      intro hP
      have hwS : w ∉ S := fun h => by rw [ha w h] at hw; exact lt_irrefl _ hw
      obtain ⟨j, hj⟩ := (hy w hwS).2
      have h1 := hint w hwS j
      have h := hP j w
      rw [hfin] at h
      have ht : Valued.v ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j))) ≤ 1 := by
        have h4 := Valuation.map_add Valued.v
          ((ϖ w : w.adicCompletion E) ^ a w * pLoc E w (pFin E (y j)) - pLoc E w (pFin E (y₀ j)))
          (pLoc E w (pFin E (y₀ j)))
        rw [sub_add_cancel] at h4
        exact h4.trans (max_le h h1)
      rw [map_mul, hj, mul_one, val_zpow_unif (hϖ w), ofAdd_le_one_iff] at ht
      omega

end GlobalTheory.FourierCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectors
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.RSnmCells

theorem rsTermNM_zero (q : ℕ) {n m : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) :
    GlobalTheory.RSnmUnf.rsTermNM q α β x 0 = 1 := by
  have h1 : (GlobalTheory.RSnmUnf.padNat (n := n) fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0 := by
    funext i; simp [GlobalTheory.RSnmUnf.padNat]
  have h2 : (fun i : Fin m => ((0 : Fin m → ℤ) i).toNat) = fun _ => 0 := by funext i; simp
  rw [GlobalTheory.RSnmUnf.rsTermNM, if_pos ⟨fun i => le_rfl, antitone_const⟩, h1, h2]
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem unfolded_cells_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
      Continuous κ → (∀ h, 0 ≤ κ h) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) →
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) →
      (∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        ∀ x : ℝ, 1 < x →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (β w.1 i : ℂ)) x ≠ ⊤ →
          (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤) ∧ (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤) ∧
          ∫ g in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g ∂μ =
            (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) *
              ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ),
                l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ))
                  (fun i => (β w.1 i : ℂ)) x v := by
  intro E _ _ _ m r S hψ π π' hπ hπ' α β φ φ' κ hφ hφ' hU hK hU' hK' hshβ hshα hmatch hκc hκ0 hκN hκC hκU h₀
  classical
  have hϖex : ∀ w : HeightOneSpectrum (𝓞 E), ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E) := by
    intro w
    obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, IsUnifV E w ϖ := ⟨_, Formalism.L2.Host.unif_spec w⟩
    refine ⟨Units.mk0 ϖ fun h => ?_, hϖ⟩
    rw [IsUnifV, h] at hϖ
    simp at hϖ
  choose ϖ hϖ using hϖex
  have hreg : ∀ {a : ℕ} {ρ : CuspSub E a}, ρ.IsUnitary → ∀ F ∈ GlobalTheory.JSW.mspanR ρ, GlobalTheory.JSW.IsBCC F := by
    intro a ρ hρ F hF
    obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hρ F hF
    have h0 := (h []).2
    rwa [GlobalTheory.JSW.word_nil] at h0
  have hc := hreg hπ φ hφ
  have hc' := hreg hπ' φ' hφ'
  have hW : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc.cont (fun γ g => hc.left γ g) hu g
  have hW' : ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc'.cont (fun γ g => hc'.left γ g) hu g
  have hWc := GlobalTheory.JSW.WhitCont.continuous_whit E _ φ hc.cont hc.bdd
  have hWc' := GlobalTheory.JSW.WhitCont.continuous_whit E _ φ' hc'.cont hc'.bdd
  have hRI : ∀ {a : ℕ} (Φ : GA E a → ℂ), (∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧
        ∀ u ∈ U, ∀ g, Φ (g * finGL E a u) = Φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := a), ∀ g, Φ (g * finGL E a (locGL E a w k)) = Φ g) →
      ∀ k : GL (Fin a) (Af E), (∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) k ∈ KGL v (n := a)) →
      (∀ v ∈ S, Matrix.GeneralLinearGroup.map (pLoc E v) k = 1) → ∀ g, GlobalTheory.JSW.whit Φ (g * finGL E a k) = GlobalTheory.JSW.whit Φ g := by
    intro a Φ ⟨U, hUo, hUi⟩ hKi k hk1 hk2 g
    let stab : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | ∀ g, Φ (g * finGL E a k) = Φ g}
        mul_mem' := fun {a' c} ha hc g => by rw [map_mul, ← mul_assoc, hc, ha]
        one_mem' := fun g => by rw [map_one, mul_one]
        inv_mem' := fun {a'} ha g => by
          rw [← ha (g * finGL E a a'⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] }
    let V : Subgroup (GL (Fin a) (Af E)) := U ⊔ Subgroup.closure
      {k | ∃ w ∉ S, ∃ k' ∈ KGL w (n := a), locGL E a w k' = k}
    have hVle : V ≤ stab := by
      refine sup_le (fun k hk => hUi k hk) (Subgroup.closure_le _ |>.2 ?_)
      rintro _ ⟨w, hw, k, hk, rfl⟩
      exact hKi w hw k hk
    have hVo : IsOpen (V : Set (GL (Fin a) (Af E))) := Subgroup.isOpen_mono (le_sup_left : U ≤ V) hUo
    have hVK : ∀ w ∉ S, ∀ k ∈ KGL w (n := a), locGL E a w k ∈ V := fun w hw k hk =>
      (le_sup_right : Subgroup.closure _ ≤ V) (Subgroup.subset_closure ⟨w, hw, k, hk, rfl⟩)
    obtain ⟨J, -, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hVo hVK
    have hkJ : k ∈ GlobalTheory.RSLocalPart.levelAt a S J := by
      refine ⟨hk1, fun v hv i j => ?_⟩
      have e1 := congrArg (fun M : GL (Fin a) (v.adicCompletion E) => (M : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (hk2 v hv)
      have e2 : ((k.val - 1) i j) v = 0 := by
        have e1' : pLoc E v (k.val i j) = (1 : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j := by simpa using e1
        change pLoc E v (k.val i j - (1 : Matrix (Fin a) (Fin a) (Af E)) i j) = 0
        rw [map_sub, e1', Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e2, map_zero]
      exact zero_le'
    have e : (fun z => Φ (z * finGL E a k)) = Φ := funext fun z => hVle (hJV hkJ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hWK := hRI φ hU hK
  have hWK' := hRI φ' hU' hK'
  obtain ⟨h₀, hh₀, hκ₀, hW₀⟩ := h₀
  have hint : ∀ w ∉ S, ∀ j, pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) ∈ w.adicCompletionIntegers E := by
    intro w hw j
    have e1 := congrArg (fun M : GL (Fin (m + 1)) (w.adicCompletion E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j) (hh₀ w hw)
    have e2 : pLoc E w (pFin E (GlobalTheory.ZEul.lastRow h₀ j)) = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j := by
      simpa [GlobalTheory.ZEul.lastRow] using e1
    rw [e2, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨F, hFSB, hFc, hFr, hFpos, hFsc⟩ := GlobalTheory.FourierCell.exists_fourier_gauss_lattice E m S (GlobalTheory.ZEul.lastRow h₀) hint
  refine ⟨F, hFSB, ?_⟩
  intro μ _ 𝓕₀ h𝓕
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hfC, hfu, hdet, hDA, hDB⟩ := GlobalTheory.T.rankinSelberg_cell_integral_finite_part_nonneg E m r S φ φ' κ F hWc hWc' hW hW'
    hWK hWK' hmatch hκc hκ0 hκC ⟨h₀, hh₀, hκ₀, hW₀, hFpos⟩ hFc hFr μ 𝓕₀ h𝓕
  refine ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, ?_⟩
  intro x hx hdα hdβ

  have ev := GlobalTheory.CellEvalNM.uIntNM_cell_eval E m r S hψ ϖ hϖ α β φ φ' F hW hW' hWK hWK' (hshβ ϖ hϖ) (hshα ϖ hϖ)
    (fun a ha y hy => hFsc ϖ hϖ a ha y hy) x
  obtain ⟨hWbc, hFlc, hmeas, hinv, hbd⟩ := GlobalTheory.RSnmUnfProps.uIntNM_props E m r S φ φ' F hWc hWc' hW hW' hFc
  have hC0 : MeasurableSet (GlobalTheory.CellDec.C0 E (m + 1) S) := (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S).measurableSet
  set I : ℂ := ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ with hI
  have hIC : ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (f g : ℂ) * Complex.exp (x * t g) ∂μ = I := by
    rw [hI, Set.inter_comm, ← Measure.restrict_restrict hC0, ← integral_indicator hC0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg]; simp [hfC g hg]
  have hs : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ :=
    h𝓕.nullMeasurableSet.inter hC0.nullMeasurableSet

  have hlinD : ∀ (D : GA E (m + 1) → ℝ≥0∞) (c : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℝ≥0∞), Measurable D →
      (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, D (u * g) = D g) →
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        D (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) = c l * D g) →
      ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D g ∂μ ≠ ⊤ → (∑' l, c l) ≠ ⊤ → ∫⁻ g in 𝓕₀, D g ∂μ ≠ ⊤ := by
    intro D c hDm hDi hDc hD hc
    rw [GlobalTheory.CellDec.cell_lintegral μ S ϖ hϖ 𝓕₀ h𝓕 D hDm hDi]
    have : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
        c l * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, D g ∂μ := by
      intro l
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← lintegral_const_mul'' _ hDm.aemeasurable]
      exact lintegral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => hDc g hg.2 l)
    simp_rw [this, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hc hD
  have hen : ∀ {a b : ℂ}, ‖a‖ = ‖b‖ → ‖a‖ₑ = ‖b‖ₑ := fun h => by
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, h]
  have hmD : ∀ s : ℝ, Measurable fun g : GA E (m + 1) =>
      ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) g)‖ₑ ^ 2 *
        ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s) :=
    fun s => ((hWbc.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))
  have hmD' : ∀ s : ℝ, Measurable fun g : GA E (m + 1) =>
      ‖GlobalTheory.JSW.whit φ' g‖ₑ ^ 2 *
        ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow g)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s) :=
    fun s => ((hWc'.measurable.enorm.pow_const 2).mul hFlc.measurable.enorm).mul
      (ENNReal.measurable_ofReal.comp (GlobalTheory.RSnm.continuous_detAbs.measurable.pow_const s))
  have LA := hlinD _ _ (hmD _) (fun u hu g => by
      obtain ⟨h1, -, h3, h4, -⟩ := hinv u hu g
      rw [hen h1, h3, h4]) (fun g hg l => (ev g hg l).2.1) (hDA x)
    (GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + r + 1 + 1) S (by omega) (fun w i => (α w i : ℂ)) x hdα)
  have LB := hlinD _ _ (hmD' _) (fun u hu g => by
      obtain ⟨-, h2, h3, h4, -⟩ := hinv u hu g
      rw [hen h2, h3, h4]) (fun g hg l => (ev g hg l).2.2) (hDB π' hπ' hφ' hFSB x hx)
    (GlobalTheory.RSCellEul.tsum_padTerm_ne_top E m (m + 1) S le_rfl (fun w i => (β w i : ℂ)) x hdβ)
  refine ⟨LA, LB, ?_⟩

  have hDtr : ∀ (a b : ℂ) (s : ℝ) (g : GA E (m + 1)), (‖a‖ₑ ^ 2 * ‖b‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ s)).toReal =
      ‖a‖ ^ 2 * ‖b‖ * GlobalTheory.RSnm.detAbs g ^ s := by
    intro a b s g
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, toReal_enorm,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (GlobalTheory.RSnm.detAbs_pos g).le _)]
  have iA := integrable_toReal_of_lintegral_ne_top (hmD (x - ((r : ℝ) + 1))).aemeasurable LA
  have iB := integrable_toReal_of_lintegral_ne_top (hmD' x).aemeasurable LB
  have i12 : Integrable (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) (μ.restrict 𝓕₀) :=
    Integrable.mono' ((iA.add iB).div_const 2) (hmeas x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by
        simp only [Pi.add_apply, hDtr]
        exact hbd x g)
  have hl : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
      ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S,
        GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
      (l.1.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (β w i : ℂ)) x v) * I := by
    intro l
    rw [← integral_const_mul, ← hIC, ← integral_const_mul]
    refine integral_congr_ae ((ae_restrict_mem₀ hs).mono fun g hg => ?_)
    dsimp only
    rw [(ev g hg.2 l).1, hfu g hg.2, hdet, mul_assoc]
  have h := (GlobalTheory.CellDec.cell_integral μ S ϖ hϖ 𝓕₀ h𝓕 _ (hmeas x) i12 (fun u hu g => (hinv u hu g).2.2.2.2 x)).2
  simp_rw [hl] at h
  rw [← h.tsum_eq, tsum_mul_right, mul_comm]
  obtain ⟨e, he⟩ := GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  congr 1
  rw [← e.tsum_eq]
  exact tsum_congr fun l => (he ℂ (fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
    (fun i => (β w i : ℂ)) x v) (fun i => rsTermNM_zero _ _ _ _) l).symm

end GlobalTheory.RSnmCells
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectorsStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.unfolded_rankinSelberg_cellIntegral_matchedVectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) →
    ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin (m + r + 1 + 1) → ℂˣ) (β : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ)
      (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ) (κ : GA E (m + 1) → ℝ),
      φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ (g * finGL E (m + r + 1 + 1) u) = φ g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + r + 1 + 1)), ∀ g,
        φ (g * finGL E (m + r + 1 + 1) (locGL E (m + r + 1 + 1) w k)) = φ g) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ' (h * GlobalTheory.JSW.tl ϖ l) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (β w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ' h) →
      (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
        ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) →
        ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S,
          GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) (h * GlobalTheory.JSW.tl ϖ l)) =
            (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (GlobalTheory.RSnmUnf.padNat (l w))) *
              GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)) →
      (∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = (κ h : ℂ) * GlobalTheory.JSW.whit φ' h) →
      Continuous κ → (∀ h, 0 ≤ κ h) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ h, κ (u * h) = κ h) →
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, κ h ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) →
      (∃ h₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, 0 < κ h₀ ∧ GlobalTheory.JSW.whit φ' h₀ ≠ 0) →
    ∃ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
      IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
      ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
        0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
        ∀ x : ℝ, 1 < x →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
            (fun w i => (β w.1 i : ℂ)) x ≠ ⊤ →
          (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤) ∧ (∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤) ∧
          ∫ g in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x g ∂μ =
            (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) *
              ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ),
                l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ))
                  (fun i => (β w.1 i : ℂ)) x v := by
  first | (exact @GlobalTheory.RSnmCells.unfolded_cells_eq) | (exact GlobalTheory.RSnmCells.unfolded_cells_eq) | (intros; apply GlobalTheory.RSnmCells.unfolded_cells_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireGood
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.RSnmGood

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def contGood : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | Continuous F ∧ GlobalTheory.MSpanDecay.Good F}
  zero_mem' := ⟨continuous_const, (GlobalTheory.MSpanDecay.goodSub E a).zero_mem⟩
  add_mem' := fun h h' => ⟨h.1.add h'.1, (GlobalTheory.MSpanDecay.goodSub E a).add_mem h.2 h'.2⟩
  smul_mem' := fun z _ h => ⟨h.1.const_smul z, (GlobalTheory.MSpanDecay.goodSub E a).smul_mem z h.2⟩

theorem mspanR_le_contGood (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) :
    GlobalTheory.JSW.mspanR π ≤ contGood E a := by
  refine sInf_le ⟨fun φ hφ => ?_, fun F hF h => ?_, fun F hF X _ ν hν k γ hk => ?_⟩
  · exact ⟨(GlobalTheory.RSnm.mem_goodFns ha hπ (Submodule.mem_sup_left ⟨φ, hφ, rfl⟩)).1, GlobalTheory.MSpanDecay.good_of_mem hπ hφ⟩
  · exact ⟨hF.1.comp (continuous_id.mul continuous_const), GlobalTheory.RtGood.good_mul_right E a F h hF.2⟩
  · haveI := hν
    refine ⟨?_, GlobalTheory.MSpanDecay.Good.kernel hF.2 hk⟩
    exact (GlobalTheory.JSW.kerOp_integrable_continuous E a X ν k γ hk ⟨F, hF.2.1⟩ hF.1
      (GlobalTheory.RSnm.bounded_of_decays ha hF.2.decays)).2

theorem mspanR_le_goodFns (ha : 0 < a) {π : CuspSub E a} (hπ : π.IsUnitary) :
    GlobalTheory.JSW.mspanR π ≤ GlobalTheory.RSnm.goodFns a := fun F hF =>
  ⟨(mspanR_le_contGood ha hπ hF).1, (mspanR_le_contGood ha hπ hF).2.decays,
    (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ.contra (GlobalTheory.JSW.invT_mem_mspanR_contra E a π F hF)).decays⟩


open GroundTheory.Automorphic in
theorem rsIntegral_entire_good {m n : ℕ} (hm0 : 0 < m) (hmn : m < n) {φ : GA E n → ℂ} (g1 : φ ∈ GlobalTheory.RSnm.goodFns n)
    {φ' : GA E m → ℂ} (g2 : φ' ∈ GlobalTheory.RSnm.goodFns m) {F : (Fin m → Ad E) → ℂ}
    (hF : F ∈ GJMatrix.schwartzBruhatPi (K := E) (ι := Fin m)) (μ : Measure (GA E m)) [μ.IsHaarMeasure] {𝓕 : Set (GA E m)}
    (h𝓕 : IsFundamentalDomain (ratGL E m).range 𝓕 μ) :
    (∀ s : ℂ, IntegrableOn (GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s) 𝓕 μ) ∧
      ∀ s : ℂ, AnalyticAt ℂ (fun s => ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s h ∂μ) s := by
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.RSnm.bounded_of_decays (hm0.trans hmn) g1.2.1
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.RSnm.bounded_of_decays hm0 g2.2.1
  set A : GA E m → ℂ := fun h => FourierWhittaker.partialCoeff (GlobalTheory.RSnm.colSmooth m F φ) (m + 1)
    (FourierWhittaker.blockGL hmn.le h) * (starRingEnd ℂ) (φ' h)
  have hAc : Continuous A :=
    ((FourierWhittaker.continuous_partialCoeff (GlobalTheory.RSnm.continuous_colSmooth hF g1.1 hC₁) (m + 1)).comp
      (GlobalTheory.RSnm.continuous_blockGL hmn.le)).mul (Complex.continuous_conj.comp g2.1)
  have hbd : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖A h‖ ≤ C * (min (GlobalTheory.RSnm.detAbs h) (GlobalTheory.RSnm.detAbs h)⁻¹) ^ N := by
    intro N
    obtain ⟨C, hC⟩ := GlobalTheory.RSnm.colSmooth_bound hmn g1 hF N
    refine ⟨C * C₂, fun h => ?_⟩
    have hP := GlobalTheory.RSnm.partialCoeff_bound hmn (b := fun t => C * (min t t⁻¹) ^ N) hC (n - (m + 1)) (m + 1) (by omega)
      le_rfl _ (GlobalTheory.RSnm.inS_blockGL hmn h)
    simp only [GlobalTheory.RSnm.detAbs_blockGL] at hP
    rw [norm_mul, Complex.norm_conj]
    calc _ ≤ C * (min (GlobalTheory.RSnm.detAbs h) (GlobalTheory.RSnm.detAbs h)⁻¹) ^ N * C₂ :=
          mul_le_mul hP (hC₂ h) (norm_nonneg _) ((norm_nonneg _).trans hP)
      _ = _ := by ring
  obtain ⟨hI, hD⟩ := GlobalTheory.T.mellinType_integral_entire_of_rapid_decay (μ.restrict 𝓕) A GlobalTheory.RSnm.detAbs hAc.aestronglyMeasurable
    GlobalTheory.RSnm.continuous_detAbs.measurable GlobalTheory.RSnm.detAbs_pos (GlobalTheory.T.integrableOn_min_absDet_inv_fundamentalDomain E m hm0 μ 𝓕 h𝓕) hbd
  have e : ∀ s, GlobalTheory.RSnm.rsIntegrand m hmn.le F φ φ' s =
      fun h => A h * ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ (s - ((n : ℂ) - m) / 2) := fun s => rfl
  refine ⟨fun s => by rw [e]; exact hI _, fun s => ?_⟩
  simp only [e]
  exact (hD.analyticAt _).comp (analyticAt_id.sub analyticAt_const)

end GlobalTheory.RSnmGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntire
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.RSnmUnf

theorem rs_nm_partialL_eq_div : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  intro E _ _ _ n m σ σ' hm hmn hσ hσ' T hψ hT hT'
  obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = m₀ + r + 1 + 1 := ⟨n - m₀ - 2, by omega⟩
  obtain ⟨α, _ℓ, _Φ, _J, _η, π, _ω, _φ, hα, hπ, hω, hωc, _h1, _h2, _h3, _h4, _h5, _h6, _h7, hZ⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m₀ + r + 1 + 1) σ (by omega) hσ T hT
  obtain ⟨β, _ℓ', _Φ', _J', _η', π', _ω', _φ', hβ, hπ', hω', hωc', _h1', _h2', _h3', _h4', _h5', _h6', _h7', hZ'⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m₀ + 1) σ' (by omega) hσ' T hT'
  subst hπ hπ'
  have hu : π.IsUnitary := (CG.isUnitary_mk π).1 hσ
  have hu' : π'.IsUnitary := (CG.isUnitary_mk π').1 hσ'
  have hfd : ∀ a : ℕ, ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 : Set (GA E a)) (𝓕₀ : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
    intro a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
    haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
    have hsub : (GlobalTheory.CellDec.NE E a : Set (GA E a)) ⊆ ((ratGL E a).range : Set (GA E a)) := by
      rintro _ ⟨u, -, rfl⟩
      exact ⟨u, rfl⟩
    haveI : DiscreteTopology (GlobalTheory.CellDec.NE E a) :=
      DiscreteTopology.of_subset (inferInstance : DiscreteTopology ((ratGL E a).range : Set (GA E a))) hsub
    obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
    obtain ⟨𝓕₀, -, -, h𝓕₀⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GlobalTheory.CellDec.NE E a)
    exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕₀, h𝓕 _, h𝓕₀ _⟩
  obtain ⟨μ₁, hμ₁, 𝓕₁, -, h𝓕₁, -⟩ := hfd (m₀ + r + 1 + 1)
  obtain ⟨μ, hμ, 𝓕, 𝓕₀, h𝓕, h𝓕₀⟩ := hfd (m₀ + 1)
  have hfin : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ μ₁ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  have hfin' : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((β w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ' μ 𝓕 h𝓕
    exact (h x hx).2.1
  classical
  let αe : HeightOneSpectrum (𝓞 E) → Fin (m₀ + r + 1 + 1) → ℂˣ := fun w => if h : w ∉ T then α ⟨w, h⟩ else fun _ => 1
  let βe : HeightOneSpectrum (𝓞 E) → Fin (m₀ + 1) → ℂˣ := fun w => if h : w ∉ T then β ⟨w, h⟩ else fun _ => 1
  have hαe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe w.1 = α w := fun w => dif_pos w.2
  have hβe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, βe w.1 = β w := fun w => dif_pos w.2
  have hsatσ : ∀ {a : ℕ} (ρ : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk ρ).HasSat w B) →
      HasSatGL w (ρ.locRep w) (sat (CG.mk ρ) w) := fun ρ w h => by
    rw [← CG.hasSat_mk, sat, dif_pos h]
    exact h.choose_spec
  have hsat : ∀ w ∉ T, HasSatGL w (π.locRep w) (Finset.univ.val.map (αe w)) := fun w hw => by
    rw [hαe ⟨w, hw⟩, hα ⟨w, hw⟩]; exact hsatσ π w (hT w hw)
  have hsat' : ∀ w ∉ T, HasSatGL w (π'.locRep w) (Finset.univ.val.map (βe w)) := fun w hw => by
    rw [hβe ⟨w, hw⟩, hβ ⟨w, hw⟩]; exact hsatσ π' w (hT' w hw)
  obtain ⟨φ, φ', κ, hφ, hφ', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ :=
    GlobalTheory.T.exists_matchedWhittakerVectors_shintaniRelations E m₀ r T hψ π π' hu hu' αe βe hsat hsat'
  obtain ⟨F, hF, hC⟩ := GlobalTheory.T.unfolded_rankinSelberg_cellIntegral_matchedVectors E m₀ r T hψ π π' hu hu' αe βe φ φ' κ hφ hφ' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  letI : μ.IsHaarMeasure := hμ
  obtain ⟨c, hc, hU⟩ := GlobalTheory.T.rankinSelbergGLnGLm_unfolding_to_mirabolic E m₀ r μ
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hid⟩ := hC μ 𝓕₀ h𝓕₀
  obtain ⟨hdiff, hreal⟩ := GlobalTheory.exp_integral_entire_real_pos (μ.restrict 𝓕₀) f t hfm htm hf0 hfi hR
  have hlt : m₀ + 1 < m₀ + r + 1 + 1 := by omega
  have hent := GlobalTheory.RSnmGood.rsIntegral_entire_good (by omega) hlt
    (GlobalTheory.RSnmGood.mspanR_le_goodFns (by omega) hu hφ) (GlobalTheory.RSnmGood.mspanR_le_goodFns (by omega) hu' hφ') hF μ h𝓕
  refine ⟨fun s => ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m₀ + 1) hlt.le F φ φ' s h ∂μ,
    fun s => (c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (s * t g) ∂μ, fun s => (hent.2 s).differentiableAt,
    (differentiable_const _).mul hdiff, ?_, ?_⟩
  · intro x
    obtain ⟨him, hre⟩ := hreal x
    have hre' := hre hfpos
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos hc hre'
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, him, mul_zero]
  · intro x hx
    have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, 2 ≤ Ideal.absNorm w.1.asIdeal :=
      fun w => HeightOneSpectrum.one_lt_absNorm w.1
    have e1 : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m₀ + r + 1 + 1)) => ((αe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α w i : ℂˣ) : ℂ) := by funext w i; rw [hαe w]
    have e1' : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m₀ + 1)) => ((βe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((β w i : ℂˣ) : ℂ) := by funext w i; rw [hβe w]
    have hf1 := hfin x hx
    have hf1' := hfin' x hx
    rw [← e1] at hf1
    rw [← e1'] at hf1'
    obtain ⟨dd1, dd2, eq⟩ := hid x hx hf1 hf1'
    obtain ⟨-, eU⟩ := hU π π' hu hu' φ φ' hφ hφ' F hF 𝓕 𝓕₀ h𝓕 h𝓕₀ x dd1 dd2
    rw [e1] at hf1
    rw [e1'] at hf1'
    obtain ⟨P, hP, hS⟩ := GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (by omega : m₀ + 1 ≤ m₀ + r + 1 + 1) α β x hx hq hf1 hf1'
    have hsum : (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} →₀ (Fin (m₀ + 1) → ℤ),
        l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (αe w.1 i : ℂ))
          (fun i => (βe w.1 i : ℂ)) x v) = P := by
      simp only [hαe, hβe]
      exact hS.tsum_eq
    have hJ : (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp ((x : ℂ) * t g) ∂μ) ≠ 0 := by
      intro h0
      have := (hreal x).2 hfpos
      rw [h0, Complex.zero_re] at this
      exact lt_irrefl _ this
    have hval : (∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m₀ + 1) hlt.le F φ φ' (x : ℂ) h ∂μ) /
        ((c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp ((x : ℂ) * t g) ∂μ) = P := by
      rw [eU, eq, hsum]
      have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
      field_simp
    have hP' : HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal)
        (sat (CG.mk π) w.1) ((sat (CG.mk π') w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P := by
      simp only [← hα, ← hβ]
      exact hP
    simpa only [hval] using hP'

end GlobalTheory.RSnmUnf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmPartialLEqDivEntireStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  first | (exact @GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (exact GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div) | (intros; apply GlobalTheory.RSnmUnf.rs_nm_partialL_eq_div  <;> assumption)
end
