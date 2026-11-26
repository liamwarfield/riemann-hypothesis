module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizerSectionAtPrimeSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionExpandsIntegrallyGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitAwayFromLevelProdNormalisedMatrixGaussSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitAwayFromLevelProdNormalisedMatrixGaussSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.GaussUnit

theorem isIntegral_of_eq {x y : ℂ} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

theorem unitOff_of_two {N : ℕ} {u : ℂ} (h0 : u ≠ 0) {a b : ℕ} (ha : IsIntegral ℤ ((N : ℂ) ^ a * u))
    (hb : IsIntegral ℤ ((N : ℂ) ^ b * u⁻¹)) : UnitOff N u := by
  have hN : ∀ c : ℕ, IsIntegral ℤ ((N : ℂ) ^ c) := fun c => by
    have : IsIntegral ℤ ((N : ℕ) : ℂ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ)))
    exact this.pow c
  refine ⟨h0, a + b, ?_, ?_⟩
  · have := (hN b).mul ha
    refine isIntegral_of_eq (this) ?_
    ring
  · have := (hN a).mul hb
    refine isIntegral_of_eq (this) ?_
    ring

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  unitOff_of_two (a := 0) (b := 0) one_ne_zero (by simpa using isIntegral_one) (by simpa using isIntegral_one)

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, a, ha, ha'⟩ := hu
  obtain ⟨hv0, b, hb, hb'⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, a + b, ?_, ?_⟩
  · refine isIntegral_of_eq (ha.mul hb) ?_
    ring
  · refine isIntegral_of_eq (ha'.mul hb') ?_
    rw [mul_inv]
    ring

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) :=
  Finset.prod_induction f (UnitOff N) (fun _ _ => unitOff_mul) (unitOff_one N) h

theorem unitOff_normalised {N q n r : ℕ} (hq : q ≠ 0) {m : ℕ} (hd : q ∣ N ^ m) (hrn : r ≤ n) {S : ℂ}
    (h1 : ‖S‖ ^ 2 = (q : ℝ) ^ (r ^ 2)) (h2 : IsIntegral ℤ S) (h3 : IsIntegral ℤ ((q : ℂ) ^ (r ^ 2) * S⁻¹)) :
    UnitOff N (((q : ℂ) ^ (n * r))⁻¹ * S) := by
  have hI : ∀ c : ℕ, IsIntegral ℤ ((c : ℕ) : ℂ) := fun c => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (c : ℤ)))
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hS : S ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < (q : ℝ) ^ (r ^ 2) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq) _
    rw [← h1] at this
    simp at this
  obtain ⟨c, hc⟩ := hd
  have hcC : (N : ℂ) ^ m = q * c := by exact_mod_cast hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrn
  refine unitOff_of_two (a := m * ((r + d) * r)) (b := 0) (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hqC)) hS) ?_ ?_
  · refine isIntegral_of_eq (((hI c).pow ((r + d) * r)).mul h2) ?_
    rw [pow_mul, hcC, mul_pow]
    field_simp
  · refine isIntegral_of_eq (((hI q).pow (d * r)).mul h3) ?_
    rw [mul_inv, inv_inv]
    ring

theorem card_dvd_pow (k : Type) [Field k] [Fintype k] {N : ℕ} (hN : (N : k) = 0) : ∃ m, Fintype.card k ∣ N ^ m := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨m, -, hm⟩ := FiniteField.card k p
  exact ⟨m, hm ▸ pow_dvd_pow_of_dvd ((CharP.cast_eq_zero_iff k p N).mp hN) _⟩

theorem unitOff_prod_gaussSum : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → UnitOff N (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) := by
  intro D _ Q n r hrn ψP ξ hψ hξ N _ hN
  refine unitOff_prod _ _ ?_
  rintro ⟨PP, hPP⟩ -
  haveI := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have h0 : (N : kP PP) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr (hN PP hPP)
    simpa using this
  obtain ⟨m, hm⟩ := card_dvd_pow (kP PP) h0
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul (kP PP) (ψP PP) (ξ PP) r (hψ PP hPP) (hξ PP hPP) _ rfl
  rw [Nat.card_eq_fintype_card]
  exact unitOff_normalised Fintype.card_ne_zero hm hrn h1 h2 h3

end GlobalTheory.GaussUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitAwayFromLevelProdNormalisedMatrixGaussSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitAwayFromLevel_prod_normalised_matrixGaussSum : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → UnitOff N (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) := by
  first | exact @GlobalTheory.GaussUnit.unitOff_prod_gaussSum | exact GlobalTheory.GaussUnit.unitOff_prod_gaussSum | (intros; apply GlobalTheory.GaussUnit.unitOff_prod_gaussSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedPairLatticeDilationMemOfInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedPairLatticeDilationMemOfInteger
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.BaseCmp

theorem dil_mem_latP (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (ϖ : 𝓞 D.host.E) : ∀ y ∈ lattice₂ R i, dil i (ϖ : D.host.E) y ∈ lattice₂ R i := by
  intro y hy
  have hint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D := by
    have e : finPart D (incA D (ϖ : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (ϖ : D.host.E) := rfl
    rw [e]
    exact AddSubgroup.subset_closure ⟨1, fun v => by simpa using (one_mem (v.adicCompletionIntegers D.host.F)), ϖ, rfl⟩
  have h := GlobalTheory.LatticeStable.smul_mem_latO D (Vc D i) (Wc D i) _ _ _ (incA D (ϖ : D.host.E)) hint y hy
  exact h

end GlobalTheory.BaseCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedPairLatticeDilationMemOfIntegerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedPairLattice_dilation_mem_of_integer : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (ϖ : 𝓞 D.host.E), ∀ y ∈ lattice₂ R i, dil i (ϖ : D.host.E) y ∈ lattice₂ R i := by
  first | exact @GlobalTheory.BaseCmp.dil_mem_latP | exact GlobalTheory.BaseCmp.dil_mem_latP | (intros; apply GlobalTheory.BaseCmp.dil_mem_latP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueMatrixDatumFourierExpansionGaussSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueMatrixDatumFourierExpansionGaussSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ResidueFourier

section Local

variable {k : Type} [Field k] [Fintype k]

theorem sum_char_trace {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (w : Matrix (Fin n) (Fin r) k) :
    ∑ x : Matrix (Fin r) (Fin n) k, ψ (Matrix.trace (x * w)) =
      if w = 0 then ((Nat.card k : ℂ) ^ (n * r)) else 0 := by
  let L : Matrix (Fin r) (Fin n) k →+ k :=
    AddMonoidHom.mk' (fun x => Matrix.trace (x * w)) (fun a b => by rw [Matrix.add_mul, Matrix.trace_add])
  have h := AddChar.sum_eq_ite (ψ.compAddMonoidHom L)
  have h2 : ψ.compAddMonoidHom L = 0 ↔ w = 0 := by
    constructor
    · intro h0
      ext i j
      by_contra hne
      refine hψ hne ?_
      ext t
      have := DFunLike.congr_fun h0 (Matrix.single j i t)
      change ψ (Matrix.trace (Matrix.single j i t * w)) = 1 at this
      rw [Matrix.trace_single_mul, smul_eq_mul] at this
      rw [AddChar.mulShift_apply, mul_comm]
      exact this
    · rintro rfl
      ext x
      change ψ (Matrix.trace (x * (0 : Matrix (Fin n) (Fin r) k))) = 1
      simp
  refine Eq.trans h ?_
  by_cases hw : w = 0
  · rw [if_pos (h2.2 hw), if_pos hw, Nat.card_eq_fintype_card]
    have : Fintype.card (Matrix (Fin r) (Fin n) k) = Fintype.card k ^ (n * r) := by
      change Fintype.card (Fin r → Fin n → k) = _
      simp [pow_mul]
    rw [this]; push_cast; rfl
  · rw [if_neg (fun h => hw (h2.1 h)), if_neg hw]

theorem inversion {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (f : Matrix (Fin n) (Fin r) k → ℂ)
    (u : Matrix (Fin n) (Fin r) k) :
    f u = ∑ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) := by
  have hc : ((Nat.card k : ℂ) ^ (n * r)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have h1 : ∀ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) =
      ∑ v, ((Nat.card k : ℂ) ^ (n * r))⁻¹ * f v * ψ (Matrix.trace (x * (u - v))) := fun x => by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_assoc, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← Matrix.trace_add, Matrix.mul_sub, Matrix.neg_mul,
      neg_add_eq_sub]
  simp only [h1]
  rw [Finset.sum_comm, Finset.sum_eq_single u]
  · rw [← Finset.mul_sum, sum_char_trace hψ, if_pos (sub_self u)]
    field_simp
  · intro v _ hv
    rw [← Finset.mul_sum, sum_char_trace hψ, if_neg (fun h => hv (sub_eq_zero.1 h).symm), mul_zero]
  · simp

def embTop (n : ℕ) {r : ℕ} (g : Matrix (Fin r) (Fin r) k) : Matrix (Fin n) (Fin r) k :=
  fun i j => if h : i.val < r then g ⟨i.val, h⟩ j else 0

omit [Fintype k] in
theorem topL_embTop {n r : ℕ} (h : r ≤ n) (g : Matrix (Fin r) (Fin r) k) : topL r (embTop n g) = g := by
  ext i j
  have : i.val < n := lt_of_lt_of_le i.2 h
  simp [topL, embTop, this]

omit [Fintype k] in
theorem lowZero_embTop {n r : ℕ} (g : Matrix (Fin r) (Fin r) k) : LowZero r (embTop n g) := by
  intro i j hi _
  simp [embTop, not_lt.2 hi]

omit [Fintype k] in
theorem embTop_topL {n r : ℕ} {u : Matrix (Fin n) (Fin r) k} (hu : LowZero r u) : embTop n (topL r u) = u := by
  ext i j
  by_cases hi : i.val < r
  · simp [topL, embTop, hi]
  · simp [embTop, hi, hu i j (not_lt.1 hi) j.2]

omit [Fintype k] in
theorem trace_embTop {n r : ℕ} (h : r ≤ n) (x : Matrix (Fin r) (Fin n) k) (g : Matrix (Fin r) (Fin r) k) :
    Matrix.trace (x * embTop n g) = Matrix.trace (topL r x * g) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_add]
  have h2 : ∀ i : Fin r, i.val < r + t := fun i => lt_of_lt_of_le i.2 h
  simp [embTop, topL, h2]
  rfl

theorem transform {n r : ℕ} (h : r ≤ n) {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) {ξ : kˣ →* ℂˣ} (hξ : ξ ≠ 1)
    (x : Matrix (Fin r) (Fin n) k) :
    ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      (∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (g : Matrix (Fin r) (Fin r) k))) *
      (if h : IsUnit (topL r x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) := by
  obtain ⟨h0, h1⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ ξ r hψ hξ
  have step : ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      ∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (topL r x * (g : Matrix (Fin r) (Fin r) k))) := by
    symm
    apply Finset.sum_of_injOn (fun g : GL (Fin r) k => embTop n (g : Matrix (Fin r) (Fin r) k))
    · intro a _ b _ hab
      have := congrArg (topL r) hab
      simp only [topL_embTop h] at this
      exact Units.ext this
    · intro a _
      simp
    · intro u _ hu
      rw [dif_neg, zero_mul]
      rintro ⟨hl, hd⟩
      exact hu ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, by simp, embTop_topL hl⟩
    · intro g _
      have hx : IsUnit (topL r (embTop n (g : Matrix (Fin r) (Fin r) k))).det := by
        rw [topL_embTop h]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      have hdet : hx.unit = Matrix.GeneralLinearGroup.det g := Units.ext (by simp [topL_embTop h])
      rw [dif_pos ⟨lowZero_embTop _, hx⟩, trace_embTop h, hdet, zpow_neg_one, Units.val_inv_eq_inv_val]
  rw [step]
  by_cases hy : IsUnit (topL r x).det
  · have hm := (Matrix.isUnit_iff_isUnit_det _).2 hy
    have hdet : Matrix.GeneralLinearGroup.det (hm.unit : GL (Fin r) k) = hy.unit :=
      Units.ext (by simp [Matrix.GeneralLinearGroup.det])
    have key := h1 hm.unit
    rw [hdet] at key
    simp only [IsUnit.unit_spec, one_mul] at key
    rw [key, dif_pos hy, mul_comm]
  · have hz : (topL r x).det = 0 := by simpa using hy
    rw [h0 _ hz, dif_neg hy, mul_zero]

end Local

theorem dite_prod {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_fourier : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∃ c : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) → ℂ, (∀ u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) u = ∑ x, c x * ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (x PP * u PP.1))) ∧ ∀ (x : ∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) (y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP)), (∀ PP : ↥Q, y PP.1 = x PP) → c (-x) = (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) * omegaFlat Q r ξ y := by
  intro D _ Q n r hrn ψP ξ hψ hξ
  let f : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP v =>
    if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let c : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP x =>
    ((Nat.card (kP PP) : ℂ) ^ (n * r))⁻¹ * ∑ v, f PP v * ψP PP (Matrix.trace (-x * v))
  refine ⟨fun x => ∏ PP ∈ Q.attach, c PP.1 (x PP), fun u => ?_, fun x y hxy => ?_⟩
  · have h1 : omegaQ Q r ξ (-1) u = ∏ PP ∈ Q.attach, f PP.1 (u PP.1) := by
      unfold omegaQ
      convert dite_prod Q (fun PP => LowZero r (u PP) ∧ IsUnit (topL r (u PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have h2 : ∀ PP : ↥Q, f PP.1 (u PP.1) = ∑ x, c PP.1 x * ψP PP.1 (Matrix.trace (x * u PP.1)) := fun PP => by
      letI := Ideal.Quotient.field PP.1.asIdeal
      exact inversion (k := kP PP.1) (hψ PP.1 PP.2) (f PP.1) (u PP.1)
    rw [h1]
    simp only [h2, ← Finset.prod_mul_distrib, Finset.attach_eq_univ]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  · have h1 : omegaFlat Q r ξ y = ∏ PP ∈ Q.attach, if h : IsUnit (topL r (y PP.1)).det then ((ξ PP.1 h.unit : ℂˣ) : ℂ) else 0 := by
      unfold omegaFlat
      convert dite_prod Q (fun PP => IsUnit (topL r (y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [hxy PP, mul_assoc]
    simp only [c, Pi.neg_apply, neg_neg]
    congr 1
    letI := Ideal.Quotient.field PP.1.asIdeal
    convert transform (k := kP PP.1) hrn (hψ PP.1 PP.2) (hξ PP.1 PP.2) (x PP)

end GlobalTheory.ResidueFourier
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueMatrixDatumFourierExpansionGaussSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueMatrixDatum_fourierExpansion_gaussSum : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∃ c : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) → ℂ, (∀ u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) u = ∑ x, c x * ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (x PP * u PP.1))) ∧ ∀ (x : ∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) (y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP)), (∀ PP : ↥Q, y PP.1 = x PP) → c (-x) = (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) * omegaFlat Q r ξ y := by
  first | exact @GlobalTheory.ResidueFourier.omegaQ_fourier | exact GlobalTheory.ResidueFourier.omegaQ_fourier | (intros; apply GlobalTheory.ResidueFourier.omegaQ_fourier <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfDilatedReductionResidueMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfDilatedReductionResidueMatrices
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HalfLiftRed

open GlobalTheory.AdelicLatMove

theorem idem_smul_mem_latO {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (sdS : IsSelfDualC S ΛS) (frS : Formalism.L2.DIV.IsFrame βS ΛS) (frT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P) {a : 𝓞 D.host.E} (ha : a ∉ P.asIdeal)
    (haA : (a : D.host.E) ∈ D.host.AA) {x : WO S T} (hx : IsIntM (frMapO S T βS βT x)) :
    e • x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ zero_mem _)
  have ha' : (a : D.host.E) ≠ 0 := by exact_mod_cast ha0
  have hw : finPart D (e * incA D ((a : D.host.E))⁻¹) ∈ intAE D := by
    by_contra h
    exact ha ((he.2 a ha0).2 h)
  choose s hs hs' using GlobalTheory.IntHalfLat.exists_dual sdS frS
  set Y : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := HMul.hMul (x.map (toEAf D)) βS.val with hY
  have ht : ∀ j, (fun i => Y i j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛT := fun j => by
    refine (frT _).2 fun i => ?_
    have e1 : Matrix.mulVec (βT⁻¹).val (fun i => Y i j) i = frMapO S T βS βT x i j := by
      rw [frMapO, Matrix.mul_assoc]
      rfl
    rw [e1]
    exact hx i j
  have hU := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hw _
    (sum_mem fun j (_ : j ∈ Finset.univ) => rankOne_mem_latO S T ΛS ΛT (a : D.host.E) haA (s j) (hs j) _ (ht j))
  convert hU using 1
  ext i l
  have hYZ : ∑ j, Y i j * (βS⁻¹).val j l = toEAf D (x i l) := by
    rw [← Matrix.mul_apply, hY, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.map_apply]
  have hsum : (∑ j, rankOne S T (a : D.host.E) (s j) fun i => Y i j) i l =
      incA D (a : D.host.E) * x i l * finEmb D 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.sum_apply, ← finEmb_mul, mul_one, map_mul, toEAf_incA, ← hYZ, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rankOne, Matrix.of_apply, hs' j l, mul_assoc]
  have h1 : e * finEmb D 1 = e := GlobalTheory.PlaceDatum.mul_pair_one (GlobalTheory.SplitScalar.infPart_splitIdem he.1)
  have h2 : incA D ((a : D.host.E))⁻¹ * incA D (a : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha', map_one]
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, hsum]
  linear_combination (-(x i l)) * h1 - (e * x i l * finEmb D 1) * h2

end GlobalTheory.HalfLiftRed

theorem GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1), ∃ y : WO (Vc D i) (Wc D i), IsHalf eQ y ∧ dil i (ϖ : D.host.E) y ∈ lattice₂ R i ∧ ∀ PP : ↥Q, redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) y)) = x PP := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i _ Q hQ eQ he ϖ hϖ _ x
  have hSV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hFV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hBV.1
  have hFW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hBW.1
  obtain ⟨t0, hQt⟩ := hQ
  have he2 := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
  obtain ⟨⟨es, h1, h2⟩, -⟩ := he
  have hk : ∀ PP ∈ Q, toEAf D (es PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun PP hPP => (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).1
  have hdel : ∀ PP ∈ Q, ∀ PP' (hPP' : PP' ∈ Q),
      Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D (es PP'), hk PP' hPP'⟩ = if PP' = PP then 1 else 0 := by
    intro PP hPP PP' hPP'
    by_cases hq : PP' = PP
    · subst hq
      rw [if_pos rfl]
      exact (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP' hPP')).2
    · rw [if_neg hq]
      have hne : PP ≠ PP' := fun h => hq h.symm
      have horth : es PP * es PP' = 0 :=
        (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 PP hPP).1 (h1 PP' hPP').1).resolve_left fun h => by
          have h' := h1 PP' hPP'
          rw [← h] at h'
          exact hne (GlobalTheory.PlaceVec.isIdemAt_inj (h1 PP hPP) h')
      have h4 : (⟨toEAf D (es PP), hk PP hPP⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP'), hk PP' hPP'⟩ = 0 :=
        Subtype.ext (by change toEAf D (es PP) * toEAf D (es PP') = 0; rw [← RingHom.map_mul, horth, RingHom.map_zero])
      have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
      rwa [RingHom.map_mul, RingHom.map_zero, (GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)).2, one_mul] at h5
  choose a ha using fun (PP : ↥Q) (j : Fin (Wc D i).rank) (k : Fin (Vc D i).rank) =>
    Ideal.Quotient.mk_surjective (I := PP.1.asIdeal) (x PP j k)
  set Z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (EAf D) := fun j k =>
    ((⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) with hZ
  have hZe : ∀ j k, toEAf D eQ * Z j k = Z j k := fun j k => by
    simp only [hZ, MulMemClass.coe_mul]
    rw [← mul_assoc, ← RingHom.map_mul, he2]
  obtain ⟨w, hwh, -, hwZ⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) eQ he2 Z hZe
  have hint : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) := fun j k => by
    rw [hwZ]; exact Subtype.prop _
  have hϖE : (ϖ : D.host.E) ≠ 0 := by simpa using hϖ
  have hdil : dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ w) = w := by
    ext j k
    simp only [Matrix.map_apply]
    rw [← mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hϖE, RingHom.map_one, one_mul]
  refine ⟨dil i (ϖ : D.host.E)⁻¹ w, fun j k => ?_, ?_, fun PP => ?_⟩
  · simp only [Matrix.map_apply]
    rw [mul_left_comm, hwh j k]
  · rw [hdil]
    have hxe : (∑ PP ∈ Q, es PP) • w = w := by
      rw [← h2]; exact Matrix.ext fun j k => hwh j k
    rw [← hxe, Finset.sum_smul]
    refine sum_mem fun PP hPP => ?_
    have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun hm =>
      hQG.2 t0 PP (hQt hPP) (by
        push_cast
        exact Ideal.mul_mem_left _ _ hm)
    refine GlobalTheory.HalfLiftRed.idem_smul_mem_latO hSV hFV hFW (h1 PP hPP) hN ?_ hint
    rw [show (((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) : D.host.E) = ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) from
      map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _]
    exact normK_mem_AA D
  · rw [hdil]
    funext j k
    unfold redM
    rw [dite_eq_left (by rw [hwZ]; exact Subtype.prop _)]
    have hsub : (⟨frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w j k, by rw [hwZ]; exact Subtype.prop _⟩ :
        Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨toEAf D eQ, hi⟩ * ∑ PP ∈ Q.attach,
        ⟨toEAf D (es PP.1), hk PP.1 PP.2⟩ * Formalism.L2.DIV.oToS D.host.F D.host.E (a PP j k) := Subtype.ext (congrArg (fun M => M j k) hwZ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsub, RingHom.map_mul, hres PP.1 PP.2, one_mul, map_sum]
    simp_rw [RingHom.map_mul, Formalism.L2.DIV.resS_oToS]
    rw [Finset.sum_eq_single PP]
    · rw [hdel PP.1 PP.2 PP.1 PP.2, if_pos rfl, one_mul, ha]
    · intro b _ hb
      rw [hdel PP.1 PP.2 b.1 b.2, if_neg (fun h => hb (Subtype.ext h)), zero_mul]
    · intro h; exact absurd (Finset.mem_attach _ _) h

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfDilatedReductionResidueMatricesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_half_dilated_reduction_residueMatrices : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ x : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1), ∃ y : WO (Vc D i) (Wc D i), IsHalf eQ y ∧ dil i (ϖ : D.host.E) y ∈ lattice₂ R i ∧ ∀ PP : ↥Q, redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) y)) = x PP := by
  first | exact @GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq | exact GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq | (intros; apply GlobalTheory.HalfLiftRed.exists_half_dil_redM_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftDatumConjugateHalfFiniteFourierSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LiftFour

theorem dil_add {D : D7} (i : Fin D.R.m) (a : D.host.E) (x y : WO (Vc D i) (Wc D i)) :
    dil i a (x + y) = dil i a x + dil i a y := by
  exact Matrix.ext fun p q => by simp only [dil, Matrix.map_apply, Matrix.add_apply, mul_add]

theorem isHalf_add {D : D7} {m n : ℕ} {e : AE D} {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) :
    IsHalf e (x + y) := fun p q => by simp only [Matrix.add_apply, mul_add, hx p q, hy p q]

theorem isHalf_of_add {D : D7} {m n : ℕ} {e : AE D} {x y : Mx D m n} (hxy : IsHalf e (x + y)) (hy : IsHalf e y) :
    IsHalf e x := fun p q => by
  have h1 := hxy p q
  simp only [Matrix.add_apply, mul_add, hy p q] at h1
  exact add_right_cancel h1

theorem isHalf_dil {D : D7} (i : Fin D.R.m) {e : AE D} {a : D.host.E} (ha : a ≠ 0) (x : WO (Vc D i) (Wc D i)) :
    IsHalf e (dil i a x) ↔ IsHalf e x := by
  have hu : incA D a⁻¹ * incA D a = 1 := by rw [← RingHom.map_mul, inv_mul_cancel₀ ha, map_one]
  constructor
  · intro h p q
    have h1 : e * (incA D a * x p q) = incA D a * x p q := h p q
    linear_combination (incA D a⁻¹) * h1 - (e * x p q - x p q) * hu
  · intro h p q
    show e * (incA D a * x p q) = incA D a * x p q
    rw [mul_left_comm, h p q]

theorem redM_frMapO_add {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (PP : Pl D.host.E) (a b : WO S T) (ha : IsIntM (frMapO S T βS βT a)) (hb : IsIntM (frMapO S T βS βT b)) :
    redM PP (frMapO S T βS βT (a + b)) = redM PP (frMapO S T βS βT a) + redM PP (frMapO S T βS βT b) := by
  have e : frMapO S T βS βT (a + b) = frMapO S T βS βT a + frMapO S T βS βT b := by
    ext p q
    have := GlobalTheory.PlaceDatum.frMapO_add βS βT a b 1 p q
    simpa using this
  ext p q
  simp only [redM, e, Matrix.add_apply, Matrix.of_apply]
  rw [dite_eq_left (add_mem (ha p q) (hb p q)), dite_eq_left (ha p q), dite_eq_left (hb p q), ← map_add (f := _)]
  rfl

theorem datum_conj_half_fourier : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → (∀ PP ∈ Q, ξR PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∃ (Y : Finset (WO (Vc D i) (Wc D i))) (a : WO (Vc D i) (Wc D i) → ℂ) (Gc : ℂ), UnitOff N Gc ∧ (∀ y ∈ Y, IsHalf eQ y) ∧
      (∀ t, (if IsHalf (cA D eQ) t ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t)) else 0) =
        halfInd (cA D eQ) (lattice₂ R i) t * ∑ y ∈ Y, a y * R.ψ (symplO (Vc D i) (Wc D i) t y)) ∧
      ∀ t, ∑ y ∈ Y, a y * halfInd eQ (lattice₂ R i) (t + y) = Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV ξR Q hQ hξ N hN hNQ eQ heQ ϖ hϖ hϖQ
  classical
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  have hϖ' : (ϖ : D.host.E) ≠ 0 := by
    intro h; exact hϖ (by exact_mod_cast h)
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hrn : (Wc D i).rank ≤ (Vc D i).rank := by rw [rV, rW]; omega
  obtain ⟨ψP, hψP, hchar⟩ := GlobalTheory.T.exists_uniformizer_section_at_prime_set D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  obtain ⟨c, hinv, hc⟩ := GlobalTheory.T.residueMatrixDatum_fourierExpansion_gaussSum D Q (Vc D i).rank (Wc D i).rank hrn ψP ξR hψP hξ
  choose yx hyh hyl hyr using GlobalTheory.T.exists_half_dilated_reduction_residueMatrices D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  have hker := GlobalTheory.T.mem_lattice_iff_uniformiser_reduction_vanishes D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ ϖ hϖ hϖQ
  have h4a := GlobalTheory.T.mem_completedPairLattice_iff_adjointFrameMatrix_integral_conjHalf D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ
  have h4b := GlobalTheory.T.mem_completedPairLattice_iff_frameMatrix_integral_on_half D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ heQ
  have hdm := GlobalTheory.T.completedPairLattice_dilation_mem_of_integer D G Pl0 T0 A Ks R i ϖ
  have key : ∀ g : WO (Vc D i) (Wc D i) → ℂ,
      ∑ y ∈ Finset.univ.image yx, (∑ x ∈ Finset.univ.filter (fun x => yx x = y), c x) * g y = ∑ x, c x * g (yx x) := by
    intro g
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image yx) (g := yx)
      (fun x _ => Finset.mem_image_of_mem yx (Finset.mem_univ x))]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]
  refine ⟨Finset.univ.image yx, fun y => ∑ x ∈ Finset.univ.filter (fun x => yx x = y), c x, _,
    GlobalTheory.T.isUnitAwayFromLevel_prod_normalised_matrixGaussSum D Q (Vc D i).rank (Wc D i).rank hrn ψP ξR hψP hξ N hN hNQ, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    exact hyh x
  · intro t
    rw [key (fun y => R.ψ (symplO (Vc D i) (Wc D i) t y))]
    by_cases ht : IsHalf (cA D eQ) t
    · by_cases hl : t ∈ lattice₂ R i
      · have hint := (h4a t ht).2 hl
        rw [if_pos ⟨ht, hint⟩, halfInd, if_pos ⟨hl, ht⟩, one_mul, hinv]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hchar t (yx x) ht hl (hyh x) (hyl x), ← Finset.prod_attach Q]
        refine congrArg _ (Finset.prod_congr rfl fun PP _ => ?_)
        rw [hyr x PP]
      · rw [if_neg (fun h => hl ((h4a t ht).1 h.2)), halfInd, if_neg (fun h => hl h.1), zero_mul]
    · rw [if_neg (fun h => ht h.1), halfInd, if_neg (fun h => ht h.2), zero_mul]
  · intro t
    rw [key (fun y => halfInd eQ (lattice₂ R i) (t + y)), flatDat]
    by_cases ht : IsHalf eQ t
    · have hdt : IsHalf eQ (dil i (ϖ : D.host.E) t) := (isHalf_dil i hϖ' t).2 ht
      by_cases hl : dil i (ϖ : D.host.E) t ∈ lattice₂ R i
      · have hint := (h4b _ hdt).2 hl
        rw [if_pos ⟨hdt, hint⟩]
        set ρt : ∀ PP : ↥Q, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1) :=
          fun PP => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) t)) with hρt
        have hterm : ∀ x, halfInd eQ (lattice₂ R i) (t + yx x) = if x = -ρt then 1 else 0 := by
          intro x
          have hh : IsHalf eQ (t + yx x) := isHalf_add ht (hyh x)
          have hdl : dil i (ϖ : D.host.E) (t + yx x) ∈ lattice₂ R i := by
            rw [dil_add]; exact add_mem hl (hyl x)
          have hintx := (h4b _ ((isHalf_dil i hϖ' _).2 (hyh x))).2 (hyl x)
          rw [halfInd]
          by_cases hx : x = -ρt
          · have hm : t + yx x ∈ lattice₂ R i := by
              refine (hker _ hh hdl).2 fun PP hPP => ?_
              rw [dil_add, redM_frMapO_add _ _ _ _ _ hint hintx, hyr x ⟨PP, hPP⟩, hx]
              simp [hρt]
            rw [if_pos hx, if_pos ⟨hm, hh⟩]
          · rw [if_neg hx, if_neg]
            rintro ⟨hm, -⟩
            apply hx
            funext PP
            have h0 := (hker _ hh hdl).1 hm PP.1 PP.2
            rw [dil_add, redM_frMapO_add _ _ _ _ _ hint hintx, hyr x PP] at h0
            rw [Pi.neg_apply, hρt]
            exact eq_neg_of_add_eq_zero_right h0
        simp_rw [hterm, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ (-ρt) c, if_pos (Finset.mem_univ _)]
        exact hc ρt _ fun PP => rfl
      · rw [if_neg (fun h => hl ((h4b _ hdt).1 h.2))]
        rw [mul_zero]
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [halfInd, if_neg, mul_zero]
        rintro ⟨hm, -⟩
        apply hl
        have := hdm _ hm
        rw [dil_add] at this
        simpa using sub_mem this (hyl x)
    · rw [if_neg (fun h => ht ((isHalf_dil i hϖ' t).1 h.1))]
      rw [mul_zero]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [halfInd, if_neg, mul_zero]
      rintro ⟨-, hh⟩
      exact ht (isHalf_of_add hh (hyh x))

end GlobalTheory.LiftFour
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftDatumConjugateHalfFiniteFourierSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_datum_conjugate_half_finite_fourier_sum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → (∀ PP ∈ Q, ξR PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∃ (Y : Finset (WO (Vc D i) (Wc D i))) (a : WO (Vc D i) (Wc D i) → ℂ) (Gc : ℂ), UnitOff N Gc ∧ (∀ y ∈ Y, IsHalf eQ y) ∧
      (∀ t, (if IsHalf (cA D eQ) t ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t)) else 0) =
        halfInd (cA D eQ) (lattice₂ R i) t * ∑ y ∈ Y, a y * R.ψ (symplO (Vc D i) (Wc D i) t y)) ∧
      ∀ t, ∑ y ∈ Y, a y * halfInd eQ (lattice₂ R i) (t + y) = Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) t) := by
  first | exact @GlobalTheory.LiftFour.datum_conj_half_fourier | exact GlobalTheory.LiftFour.datum_conj_half_fourier | (intros; apply GlobalTheory.LiftFour.datum_conj_half_fourier <;> assumption)
end
