module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WeightCongruences.TorsionOrderLeTwoMulFinrankSq
open NumberField

private theorem le_mul_totient_sq (n : ℕ) : n ≤ (if Even n then 2 else 1) * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.totient_prime_pow hp hk]
    by_cases h2 : p = 2
    · subst h2
      have he : Even (2 ^ k) := (Nat.even_pow.2 ⟨even_two, hk.ne'⟩)
      rw [if_pos he]
      have : 2 ^ k ≤ 2 * (2 ^ (k - 1)) ^ 2 := by
        rw [← pow_mul, ← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this
    · have hodd : ¬ Even (p ^ k) := by
        rw [Nat.even_pow]; rintro ⟨he, -⟩
        exact h2 ((Nat.Prime.even_iff hp).1 he)
      rw [if_neg hodd, one_mul]
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        rcases Nat.lt_or_ge p 3 with h | h
        · interval_cases p <;> simp_all
        · exact h
      have hsq : p ≤ (p - 1) ^ 2 := by
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
        rw [show q + 3 - 1 = q + 2 by omega]
        nlinarith
      calc p ^ k ≤ p ^ (2 * (k - 1) + 1) := Nat.pow_le_pow_right hp.pos (by omega)
        _ = (p ^ (k - 1)) ^ 2 * p := by rw [pow_succ, pow_mul, ← pow_mul, mul_comm 2]; ring
        _ ≤ (p ^ (k - 1)) ^ 2 * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hsq
        _ = (p ^ (k - 1) * (p - 1)) ^ 2 := by ring
  | zero => simp
  | one => simp
  | coprime a b _ _ hab iha ihb =>
    rw [Nat.totient_mul hab]
    have hc : (if Even (a * b) then 2 else 1) = (if Even a then 2 else 1) * (if Even b then 2 else 1) := by
      by_cases ha : Even a <;> by_cases hb : Even b
      · exfalso
        have h2a : 2 ∣ a := even_iff_two_dvd.1 ha
        have h2b : 2 ∣ b := even_iff_two_dvd.1 hb
        have h := Nat.dvd_gcd h2a h2b
        rw [Nat.Coprime.gcd_eq_one hab] at h
        omega
      · simp [ha, hb, Nat.even_mul]
      · simp [ha, hb, Nat.even_mul]
      · have : ¬ Even (a * b) := by rw [Nat.even_mul]; tauto
        simp [ha, hb, this]
    rw [hc]
    calc a * b ≤ ((if Even a then 2 else 1) * a.totient ^ 2) * ((if Even b then 2 else 1) * b.totient ^ 2) :=
          Nat.mul_le_mul iha ihb
      _ = _ := by ring

private theorem le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  have h := le_mul_totient_sq n
  have hc : (if Even n then 2 else 1) ≤ 2 := by split_ifs <;> norm_num
  exact h.trans (Nat.mul_le_mul_right _ hc)

private theorem torsion_order_le_two_mul_finrank_sq (E : Type) [Field E] [NumberField E] :
    Units.torsionOrder E ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Units.torsion E)
  have hord : orderOf g = Units.torsionOrder E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    rfl
  have hpos : 0 < Units.torsionOrder E := Units.torsionOrder_pos E

  let ζ : E := algebraMap (𝓞 E) E (((g : (𝓞 E)ˣ) : 𝓞 E))
  have hprim : IsPrimitiveRoot ζ (Units.torsionOrder E) := by
    have h1 : IsPrimitiveRoot g (orderOf g) := IsPrimitiveRoot.orderOf g
    rw [hord] at h1
    have h2 := h1.map_of_injective (f := (Units.torsion E).subtype) Subtype.val_injective
    have h3 := h2.map_of_injective (f := Units.coeHom (𝓞 E)) (fun a b h => Units.ext h)
    exact h3.map_of_injective (f := algebraMap (𝓞 E) E) (FaithfulSMul.algebraMap_injective _ _)
  have : NeZero (Units.torsionOrder E) := ⟨hpos.ne'⟩
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic (Units.torsionOrder E) ℚ :=
    (hprim.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat hpos)).symm
  have hdeg : (Units.torsionOrder E).totient ≤ Module.finrank ℚ E := by
    rw [← Polynomial.natDegree_cyclotomic (Units.torsionOrder E) ℚ, ← hmin]
    exact minpoly.natDegree_le ζ
  calc Units.torsionOrder E ≤ 2 * (Units.torsionOrder E).totient ^ 2 := le_two_totient_sq _
    _ ≤ 2 * (Module.finrank ℚ E) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdeg 2)

theorem UpperTheory.torsionOrder_le_two_mul_finrank_sq :
    ∀ (E : Type) [Field E] [NumberField E], NumberField.Units.torsionOrder E ≤ 2 * Module.finrank ℚ E ^ 2 := by
  intro E _ _
  exact torsion_order_le_two_mul_finrank_sq E
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DimVRowPos
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

noncomputable section

namespace GlobalTheory.EX.WinLow

open Formalism.MainNotions.StandardLattice Finset

theorem host_cm {R : Ranks} (H : Host R) : letI := H.cmStar; Formalism.HermitianLatticesTheory.IsCMUnram H.E :=
  letI := H.cmStar
  (host_cmData R H).cmUnram

theorem finrank_E {R : Ranks} (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := H.finrank_E'

theorem fDeg_E {R : Ranks} (H : Host R) : Formalism.HermitianLatticesTheory.fDeg H.E = R.f := by
  let _ := H.cmStar
  have : IsTotallyComplex H.E := (host_cm H).1
  have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := H.E)
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank H.E
  have h3 : NumberField.InfinitePlace.nrRealPlaces H.E = 0 := by
    rw [NumberField.nrRealPlaces_eq_zero_iff]; infer_instance
  have h4 := finrank_E H
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem vInv_E {R : Ranks} (H : Host R) : Formalism.HermitianLatticesTheory.vInv H.E = H.v := by
  unfold Formalism.HermitianLatticesTheory.vInv Host.v Host.rdE
  rw [fDeg_E, finrank_E]
  push_cast
  rfl

theorem pi_le_v {R : Ranks} (H : Host R) : Real.pi ≤ H.v := by
  have hd2 : H.d ≠ 2 := fun h => H.d_notMem_small (h ▸ H.two_mem_small)
  have hd3 : 3 ≤ H.d := by have := H.d_prime.two_le; omega
  have hd : (3 : ℝ) ≤ H.d := by exact_mod_cast hd3
  have he : (2 : ℝ) ≤ R.e := by exact_mod_cast H.two_le_e
  have hB : (2 : ℝ) ^ (-(R.e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hlo : (2 : ℝ) ^ (2 : ℝ) ≤ (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hs : 8 / 5 ≤ Real.sqrt (H.d : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have h8 : 32 / 5 ≤ H.rdE := by
    refine le_trans ?_ (factRd R H).1
    rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at hlo
    nlinarith
  have := Real.pi_lt_d2
  unfold Host.v
  linarith

theorem mass_pos (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) :
    0 < Formalism.HermitianLatticesTheory.mass (stdForm K M) (stdLat K M) := by
  rw [standard_form_eq_telescope_form, standard_lattice_eq_telescope_lattice]
  exact Formalism.HermitianLatticesTheory.massTelescope_std_pos K hK M

theorem mass_tel (h2b : SiegelMassRatioCM) (K : Type) [Field K] [NumberField K] [StarRing K] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    Formalism.HermitianLatticesTheory.mass (stdForm K (k + n)) (stdLat K (k + n)) =
      Formalism.HermitianLatticesTheory.mass (stdForm K k) (stdLat K k) * ∏ M ∈ Ico (k + 1) (k + n + 1), Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Formalism.HermitianLatticesTheory.mass (stdForm K (k + n + 1)) (stdLat K (k + n + 1)) /
        Formalism.HermitianLatticesTheory.mass (stdForm K (k + n)) (stdLat K (k + n)) = _ := h2b K hK (k + n + 1) (by omega)
    rw [div_eq_iff (mass_pos K hK _).ne', ih] at h
    have hI : ∏ M ∈ Ico (k + 1) (k + (n + 1) + 1), Formalism.HermitianLatticesTheory.massRatioRightSide K M =
        (∏ M ∈ Ico (k + 1) (k + n + 1), Formalism.HermitianLatticesTheory.massRatioRightSide K M) * Formalism.HermitianLatticesTheory.massRatioRightSide K (k + n + 1) :=
      Finset.prod_Ico_succ_top (by omega : k + 1 ≤ k + n + 1) _
    rw [hI]
    refine h.trans ?_
    ring

theorem idx_place (R : Ranks) (g : ℕ) (hp : g.Prime) (hg : 3 ≤ g) :
    (g : ℝ) ^ (R.k * (R.k + 1) / 2) / 2 ≤ idxColLoc g R.k ∧
    idxColLoc g R.k ≤ (g : ℝ) ^ (R.k * (R.k + 1) / 2) ∧
    (g : ℝ) ^ ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2) / 2 ≤ idxRowLoc g R.k R.m ∧
    idxRowLoc g R.k R.m ≤ (g : ℝ) ^ ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2) := by
  have : Fact g.Prime := ⟨hp⟩
  have hc : Fintype.card (ZMod g) = g := ZMod.card _
  obtain ⟨⟨θ, hθ1, hθ2, h1⟩, ⟨θ', hθ1', hθ2', h2⟩⟩ :=
    Formalism.HermitianLattices.GenusMassVolumes.local_index_formula (ZMod g) R.k R.m R.two_le_m R.m_even (by rw [hc]; exact hg)
  rw [hc] at h1 h2
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hp.pos
  have e1 : idxColLoc g R.k = (g : ℝ) ^ (R.k * (R.k + 1) / 2) * θ := by
    rw [← h1]
    unfold idxColLoc idxLoc
    rw [card_GL_subtype_eq_card_matrix _ det_eq_one_of_unitriangular]
    have := Formalism.LogVandermondeBounds.StandardLattice.cardUnitriangular (ZMod g) R.k
    rw [hc] at this
    have h3 : Nat.card {A : Matrix (Fin R.k) (Fin R.k) (ZMod g) // IsUnitri A} =
        g ^ (R.k * (R.k - 1) / 2) := this
    rw [h3, Nat.card_eq_fintype_card]
    push_cast
    rfl
  have e2 : idxRowLoc g R.k R.m = (g : ℝ) ^ ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2) * θ' := by
    have h2' : _ = (g : ℝ) ^ ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2) * θ' := h2
    rw [← h2']
    unfold idxRowLoc idxLoc
    rw [rowLevCard_holds _ _ _ hp R.two_le_m R.m_even, Nat.card_eq_fintype_card]
    push_cast
    rfl
  have p1 : (0 : ℝ) < (g : ℝ) ^ (R.k * (R.k + 1) / 2) := pow_pos hgpos _
  have p2 : (0 : ℝ) < (g : ℝ) ^ ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2) := pow_pos hgpos _
  rw [e1, e2]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem idx_ratio (R : Ranks) (g : Fin 2 → ℕ) (hp : ∀ i, (g i).Prime) (hg : ∀ i, 3 ≤ g i) :
    0 < idxColLoc (g 0) R.k ^ R.f * idxColLoc (g 1) R.k ^ R.f ∧
    0 < idxRowLoc (g 0) R.k R.m ^ R.f * idxRowLoc (g 1) R.k R.m ^ R.f ∧
    ((2 : ℝ) ^ (2 * R.f))⁻¹ * ((g 0 : ℝ) * (g 1 : ℝ)) ^ ((R.f : ℝ) * R.m * (2 * R.k + R.m - 1) / 2) ≤
      (idxRowLoc (g 0) R.k R.m ^ R.f * idxRowLoc (g 1) R.k R.m ^ R.f) /
        (idxColLoc (g 0) R.k ^ R.f * idxColLoc (g 1) R.k ^ R.f) := by
  have h4a := fun i => idx_place R (g i) (hp i) (hg i)
  have hgp : ∀ i, (0 : ℝ) < (g i : ℝ) := fun i => by exact_mod_cast (hp i).pos
  have hg1 : ∀ i, (1 : ℝ) ≤ (g i : ℝ) := fun i => by exact_mod_cast (hp i).one_lt.le
  have hc : ∀ i, 0 < idxColLoc (g i) R.k := fun i =>
    lt_of_lt_of_le (by have := hgp i; positivity) (h4a i).1
  have hr : ∀ i, 0 < idxRowLoc (g i) R.k R.m := fun i =>
    lt_of_lt_of_le (by have := hgp i; positivity) (h4a i).2.2.1
  refine ⟨by have := hc 0; have := hc 1; positivity, by have := hr 0; have := hr 1; positivity, ?_⟩
  have key := Formalism.HermitianLattices.GenusMassVolumes.index_ratio_bound R.f R.k R.m (g 0 : ℝ) (g 1 : ℝ)
    (idxColLoc (g 0) R.k ^ R.f * idxColLoc (g 1) R.k ^ R.f)
    (idxRowLoc (g 0) R.k R.m ^ R.f * idxRowLoc (g 1) R.k R.m ^ R.f)
    (fun i _ => idxColLoc (g i) R.k / (g i : ℝ) ^ (R.k * (R.k + 1) / 2))
    (fun i _ => idxRowLoc (g i) R.k R.m / (g i : ℝ) ^ ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2))
    R.two_le_m R.m_even (hg1 0) (hg1 1)
    (by
      intro i _
      obtain ⟨a1, a2, a3, a4⟩ := h4a i
      have p1 : (0 : ℝ) < (g i : ℝ) ^ (R.k * (R.k + 1) / 2) := pow_pos (hgp i) _
      have p2 : (0 : ℝ) < (g i : ℝ) ^ ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2) := pow_pos (hgp i) _
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [le_div_iff₀ p1]; linarith
      · rw [div_le_one p1]; exact a2
      · rw [le_div_iff₀ p2]; linarith
      · rw [div_le_one p2]; exact a4)
  refine (key ?_ ?_).1
  · rw [Fin.prod_univ_two]
    simp only [Finset.prod_const, Finset.card_range, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_div_cancel₀ _ (pow_pos (hgp 0) _).ne', mul_div_cancel₀ _ (pow_pos (hgp 1) _).ne']
  · rw [Fin.prod_univ_two]
    simp only [Finset.prod_const, Finset.card_range, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e0 : (g 0 : ℝ) ^ (((R.k + R.m - 1) ^ 2 + 3 * R.k + 1 + 2 * (R.m / 2 - 1)) / 2) *
        (idxRowLoc (g 0) R.k R.m / (g 0 : ℝ) ^ ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2)) =
        idxRowLoc (g 0) R.k R.m := mul_div_cancel₀ (idxRowLoc (g 0) R.k R.m)
      (pow_pos (hgp 0) ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2)).ne'
    have e1 : (g 1 : ℝ) ^ (((R.k + R.m - 1) ^ 2 + 3 * R.k + 1 + 2 * (R.m / 2 - 1)) / 2) *
        (idxRowLoc (g 1) R.k R.m / (g 1 : ℝ) ^ ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2)) =
        idxRowLoc (g 1) R.k R.m := mul_div_cancel₀ (idxRowLoc (g 1) R.k R.m)
      (pow_pos (hgp 1) ((R.r ^ 2 + 3 * R.k + 1 + 2 * R.rS) / 2)).ne'
    rw [e0, e1]

def seqOf {n : ℕ} (x : Fin n → ℚ) (i : ℕ) : ℝ := if h : i < n then ((x ⟨i, h⟩ : ℚ) : ℝ) else 0

theorem seqOf_lt {n : ℕ} (x : Fin n → ℚ) {i : ℕ} (h : i < n) : seqOf x i = ((x ⟨i, h⟩ : ℚ) : ℝ) := dif_pos h

theorem dimV_col {n : ℕ} (x : Fin n → ℚ) :
    dimV (fun i => ((x i : ℚ) : ℝ)) = Formalism.LogVandermondeBounds.StandardLattice.dimVN (seqOf x) n := by
  rw [← dim_weyl_fin_eq_nat]
  congr 1
  funext i
  rw [seqOf_lt x i.2]

theorem dimV_row {k m : ℕ} (v : Fin (k - 1) → ℚ) (b : Fin m → ℚ) :
    dimV (Fin.append (fun i => ((v i : ℚ) : ℝ)) (fun j => -((b j : ℚ) : ℝ))) =
      Formalism.LogVandermondeBounds.StandardLattice.dimVN (Formalism.LogVandermondeBounds.StandardLattice.rowPar k (seqOf v) (seqOf b)) (k - 1 + m) := by
  rw [← dim_weyl_fin_eq_nat]
  congr 1
  funext a
  induction a using Fin.addCases with
  | left i =>
    have hi : (Fin.castAdd m i).val = i.val := rfl
    unfold Formalism.LogVandermondeBounds.StandardLattice.rowPar
    rw [Fin.append_left, hi, if_pos i.2, seqOf_lt v i.2]
  | right j =>
    have hj : (Fin.natAdd (k - 1) j).val = k - 1 + j.val := rfl
    unfold Formalism.LogVandermondeBounds.StandardLattice.rowPar
    rw [Fin.append_right, hj, if_neg (by omega), Nat.add_sub_cancel_left, seqOf_lt b j.2]

theorem dimV_row_pos {R : Ranks} (p : HCParam R) :
    0 < dimV (Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ))) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hv : StrictAnti (fun i => ((p.v i : ℚ) : ℝ)) := by
    apply strictAnti_of_succ_lt_alt
    intro i j hij
    have h1 := p.v_gt_u i
    have h2 := p.u_gt_v j
    have e : (⟨i.1 + 1, by omega⟩ : Fin R.k) = ⟨j.1, by omega⟩ := by ext; simp [hij]
    rw [e] at h1
    exact_mod_cast h2.trans h1
  have hb : StrictAnti (fun j => -((p.b j : ℚ) : ℝ)) := by
    apply strictAnti_of_succ_lt_alt
    intro i j hij
    have h1 := p.gap_be i
    have h2 := p.gap_eb i (by have := j.2; omega)
    have e : (⟨i.1 + 1, by have := j.2; omega⟩ : Fin R.m) = j := by ext; simp [hij]
    rw [e] at h2
    have ht : (0 : ℚ) ≤ R.t := by positivity
    have : p.b i < p.b j := by linarith
    have : ((p.b i : ℚ) : ℝ) < ((p.b j : ℚ) : ℝ) := by exact_mod_cast this
    linarith
  refine dim_weyl_pos_of_strictAnti _ (strictAnti_fin_append _ _ hv hb fun i j => ?_)
  have h0 := p.u_last_gt (by omega) (by omega)
  have h1 := p.v_gt_u ⟨R.k - 2, by omega⟩
  have e : (⟨(⟨R.k - 2, by omega⟩ : Fin (R.k - 1)).1 + 1, by simp; omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩ := by
    ext; simp; omega
  rw [e] at h1
  have h2 : ((p.v ⟨R.k - 2, by omega⟩ : ℚ) : ℝ) ≤ ((p.v i : ℚ) : ℝ) :=
    hv.antitone (by rw [Fin.le_def]; have := i.2; simp; omega)
  have h3 : -((p.b j : ℚ) : ℝ) ≤ -((p.b ⟨0, by omega⟩ : ℚ) : ℝ) :=
    hb.antitone (by rw [Fin.le_def]; simp)
  have h4 : -((p.b ⟨0, by omega⟩ : ℚ) : ℝ) < ((p.v ⟨R.k - 2, by omega⟩ : ℚ) : ℝ) := by
    exact_mod_cast h0.trans h1
  linarith

theorem f_pos (R : Ranks) : 0 < R.f := by
  unfold Ranks.f Ranks.n
  have := R.ord_pos
  omega

def placeNo {R : Ranks} (H : Host R) (n : ℕ) : Tau R :=
  (Fintype.equivFinOfCardEq (card_Tau H)).symm ⟨n % R.f, Nat.mod_lt _ (f_pos R)⟩

theorem prod_places {R : Ranks} (H : Host R) (F : Tau R → ℝ) : ∏ ρ, F ρ = ∏ n ∈ range R.f, F (placeNo H n) := by
  rw [← Fin.prod_univ_eq_prod_range (fun n => F (placeNo H n)) R.f,
    ← Equiv.prod_comp (Fintype.equivFinOfCardEq (card_Tau H)).symm F]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold placeNo
  congr 2
  exact Fin.ext (Nat.mod_eq_of_lt i.2).symm

theorem place_data {R : Ranks} (p : HCParam R) (x Δ a B h0 b1 : ℝ) (hx : 1 ≤ x) (hΔ : 1 ≤ Δ) (hh : 0 ≤ h0)
    (hv : ∀ i : Fin (R.k - 1), ((p.v i : ℚ) : ℝ) = ((R.k - 2 - i.1 : ℕ) : ℝ) * (4 * Δ))
    (hu : ∀ (h : 0 < R.k) (h' : R.k - 1 < R.k),
      (((p.u ⟨0, h⟩ : ℚ) : ℝ) ≤ 2 * a ∧ -a ≤ ((p.u ⟨R.k - 1, h'⟩ : ℚ) : ℝ)) ∨
      (((p.u ⟨0, h⟩ : ℚ) : ℝ) = ((R.k - 2 : ℕ) : ℝ) * (4 * Δ) + R.k * (4 * Δ) + 1 / 2 ∧
        ((p.u ⟨R.k - 1, h'⟩ : ℚ) : ℝ) = -1 / 2))
    (hb : ∀ j : Fin R.m, ((p.b j : ℚ) : ℝ) = b1 + j.1 * h0 ∧ ((p.e j : ℚ) : ℝ) = ((p.b j : ℚ) : ℝ) + h0 / 2)
    (hlo : x * (R.k * (4 * Δ) + h0) ≤ b1) (hup : b1 + R.m * h0 ≤ 2 * B) :
    Formalism.LogVandermondeBounds.StandardLattice.PlaceData x Δ a B R.k R.m (seqOf p.u) (seqOf p.v) (seqOf p.b) (seqOf p.e) ∧
      ∀ j < R.m, 1 ≤ seqOf p.e j := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hx0 : 0 < x := by linarith
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have hkΔ : 1 ≤ (R.k : ℝ) * (4 * Δ) := by nlinarith
  have ht : (0 : ℚ) ≤ R.t := by positivity
  have hbj : ∀ j : Fin R.m, b1 ≤ ((p.b j : ℚ) : ℝ) := fun j => by
    rw [(hb j).1]; have : (0 : ℝ) ≤ j.1 * h0 := by positivity
    linarith
  have e1 : x * (R.k * (4 * Δ)) ≤ b1 := by nlinarith
  have e2 : x * h0 ≤ b1 := by nlinarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [seqOf_lt _ hi, hv]
    have : ((R.k - 2 - i : ℕ) : ℝ) ≤ R.k := by exact_mod_cast (by omega : R.k - 2 - i ≤ R.k)
    exact ⟨by positivity, mul_le_mul_of_nonneg_right this (by positivity)⟩
  · intro i hi
    rw [seqOf_lt _ hi, seqOf_lt _ (by omega : i < R.k - 1), hv, hv]
    have : ((R.k - 2 - i : ℕ) : ℝ) = ((R.k - 2 - (i + 1) : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : R.k - 2 - i = R.k - 2 - (i + 1) + 1)
    simp only
    rw [this]; ring
  · intro i hi
    have h1 := p.u_gt_v ⟨i, hi⟩
    have h2 := p.v_gt_u ⟨i, hi⟩
    rw [seqOf_lt _ (by omega : i < R.k), seqOf_lt _ (by omega : i + 1 < R.k), seqOf_lt _ hi]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · have h1 := p.u_last_gt (by omega) (by omega)
    rw [seqOf_lt _ (by omega : R.k - 1 < R.k), seqOf_lt _ (by omega : 0 < R.m)]
    exact_mod_cast h1
  · rw [seqOf_lt p.u (by omega : R.k - 1 < R.k), seqOf_lt p.u (by omega : 0 < R.k),
      seqOf_lt p.v (by omega : 0 < R.k - 1), seqOf_lt p.v (by omega : R.k - 2 < R.k - 1), hv, hv]
    rcases hu (by omega) (by omega) with h | ⟨h1, h2⟩
    · exact Or.inl h
    · right
      rw [h1, h2]
      simp only [Nat.sub_zero, Nat.sub_self, Nat.cast_zero]
      refine ⟨by linarith, by linarith, by ring⟩
  · intro j hj
    have g1 := p.gap_be ⟨j, hj⟩
    have g2 : p.b ⟨j, hj⟩ < p.e ⟨j, hj⟩ := by linarith
    rw [seqOf_lt _ hj, seqOf_lt _ hj]
    refine ⟨by exact_mod_cast g2, ?_⟩
    rw [(hb _).2, add_sub_cancel_left, abs_of_nonneg (by positivity), le_div_iff₀ hx0]
    have := hbj ⟨j, hj⟩
    nlinarith
  · intro j hj
    have g1 := p.gap_be ⟨j, by omega⟩
    have g2 := p.gap_eb ⟨j, by omega⟩ hj
    have g3 : (1 : ℚ) ≤ p.b ⟨j + 1, hj⟩ - p.b ⟨j, by omega⟩ := by linarith
    have g4 : p.e ⟨j, by omega⟩ < p.b ⟨j + 1, hj⟩ := by linarith
    rw [seqOf_lt p.b hj, seqOf_lt p.b (by omega : j < R.m), seqOf_lt p.e (by omega : j < R.m)]
    exact ⟨by exact_mod_cast g4, by exact_mod_cast g3⟩
  · rw [seqOf_lt _ (by omega : 0 < R.m), le_div_iff₀ hx0]
    have := hbj ⟨0, by omega⟩
    linarith
  · rw [seqOf_lt _ (by omega : R.m - 1 < R.m), (hb _).2, (hb _).1]
    have : ((R.m - 1 : ℕ) : ℝ) = R.m - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simp only [this]
    nlinarith
  · intro j hj
    rw [seqOf_lt _ hj, (hb _).2]
    have := hbj ⟨j, hj⟩
    nlinarith

theorem scale_sizes (eps cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hcD : 0 ≤ cD) (hch : 0 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      s.x * (R.k * (4 * (Delv s cD : ℝ)) + (h0v s ch : ℝ)) ≤ s.w'' R.n ∧ s.w'' R.n ≤ s.b' ∧ 0 ≤ s.b' ∧ 3 * s.b' ≤ s.b ∧
      R.m * (h0v s ch : ℝ) + 2 ≤ s.b ∧ (R.k : ℝ) ≤ s.b ∧ 2 * s.b ≤ s.a ∧ (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := by
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x2, hx2⟩ := GlobalTheory.scale_poly_comparison eps (5 + cD + ch + 2) (1 / 2) h0 (by norm_num)
  refine ⟨max 12 (max x1 x2), fun s R he hx hR => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨h12, hxa, hxb⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -⟩ := hx1 s R he hxa hR
  obtain ⟨-, -, -, c4, -, c6, -⟩ := hx2 s he hxb
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hn1 : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have hnf : (R.n : ℝ) ≤ R.f := by unfold Ranks.f; push_cast; have : (0 : ℝ) ≤ R.n := by positivity
                                   linarith
  obtain ⟨c6, c7, -⟩ := c6 R.n hn1 (hnf.trans hf)
  have hk : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hb1 : 1 ≤ s.b := Real.one_le_exp (Real.rpow_nonneg hxp.le _)
  have hb2 : 1 ≤ s.b ^ (1 - 1 / 2 : ℝ) := Real.one_le_rpow hb1 (by norm_num)
  have hb' : 0 ≤ s.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have o1 : 1 ≤ s.x ^ (5 : ℝ) := Real.one_le_rpow hx1'.le (by norm_num)
  have o2 : 1 ≤ s.x ^ cD := Real.one_le_rpow hx1'.le hcD
  have o3 : 1 ≤ s.x ^ ch := Real.one_le_rpow hx1'.le hch
  have hD : (Delv s cD : ℝ) ≤ 2 * s.x ^ cD := by
    have := (Nat.ceil_lt_add_one (show 0 ≤ s.x ^ cD by positivity)).le
    unfold Delv; linarith
  have hH : (h0v s ch : ℝ) ≤ 4 * s.x ^ ch := by
    have := (Nat.ceil_lt_add_one (show 0 ≤ s.x ^ ch by positivity)).le
    unfold h0v; push_cast; linarith
  have hy : s.x ^ (5 + cD + ch + 2) = s.x ^ (5 : ℝ) * s.x ^ cD * s.x ^ ch * (s.x * s.x) := by
    rw [Real.rpow_add hxp, Real.rpow_add hxp, Real.rpow_add hxp, Real.rpow_two, sq]
  rw [hy] at c4 c6
  obtain ⟨z, hz⟩ : ∃ z, z = s.x ^ (5 : ℝ) * s.x ^ cD * s.x ^ ch := ⟨_, rfl⟩
  rw [← hz] at c4 c6
  have o4 : 1 ≤ s.x ^ (5 : ℝ) * s.x ^ cD := one_le_mul_of_one_le_of_one_le o1 o2
  have z1 : s.x ^ (5 : ℝ) * s.x ^ cD ≤ z := hz ▸ le_mul_of_one_le_right (by linarith) o3
  have z2 : s.x ^ ch ≤ z := hz ▸ le_mul_of_one_le_left (by linarith) o4
  have z3 : s.x ^ (5 : ℝ) ≤ z := (le_mul_of_one_le_right (by linarith) o2).trans z1
  have z4 : (R.k : ℝ) * (Delv s cD : ℝ) ≤ s.x ^ (5 : ℝ) * (2 * s.x ^ cD) :=
    mul_le_mul hk hD (by positivity) (by positivity)
  have z0 : 1 ≤ z := o1.trans z3
  have hxz : 12 ≤ s.x * z := by nlinarith
  have hy12 : 12 * (s.x * z) ≤ z * (s.x * s.x) := by nlinarith
  have hw : z * (s.x * s.x) ≤ s.w'' R.n := (le_mul_of_one_le_left (by positivity) hb2).trans c6
  have h3 : 3 * s.b' ≤ s.b := by nlinarith
  have hzx : z ≤ s.x * z := le_mul_of_one_le_left (by linarith) hx1'.le
  have hmh : (R.m : ℝ) * (h0v s ch : ℝ) ≤ s.x * (4 * z) := mul_le_mul hm (by linarith) (by positivity) hxp.le
  refine ⟨?_, c7, hb', h3, by linarith, by linarith, ?_, hk⟩
  · have : (R.k * (4 * (Delv s cD : ℝ)) + (h0v s ch : ℝ)) ≤ 12 * z := by linarith
    have := mul_le_mul_of_nonneg_left this hxp.le
    linarith
  · unfold Scale.a; nlinarith

theorem bottom_len (eps : ℝ) (K : G.Consts) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hK : 1 ≤ K.La) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s * s.b' / (R.k : ℝ) ≤ s.b' := by
  obtain ⟨CN, x1, hx1⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  refine ⟨max x1 (32 * K.La * CN ^ 2), fun s R he hx hR => ?_⟩
  obtain ⟨-, -, hLa⟩ := hx1 s he (le_trans (le_max_left _ _) hx)
  obtain ⟨hLa1, hLa2⟩ := hLa K hK
  have hx2 : 32 * K.La * CN ^ 2 ≤ s.x := le_trans (le_max_right _ _) hx
  obtain ⟨⟨-, hn⟩, -, ⟨hk, -⟩, -⟩ := hR
  have hx1' : 1 < s.x := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hb : 0 < s.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hkp : (0 : ℝ) < R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk
  have hd0 : 0 < s.delta1 := Real.rpow_pos_of_pos hxp _
  have hd1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1'.le (by have := s.eps_pos; linarith)
  have hy : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hxp _
  have hlog0 : 0 ≤ Real.log s.x := Real.log_nonneg hx1'.le
  have hlog : Real.log s.x ^ 2 ≤ 4 * s.x := by
    have h := Real.log_le_rpow_div hxp.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : (s.x ^ (1 / 2 : ℝ)) ^ 2 = s.x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]; norm_num
    calc Real.log s.x ^ 2 ≤ (s.x ^ (1 / 2 : ℝ) / (1 / 2)) ^ 2 := pow_le_pow_left₀ hlog0 h 2
      _ = 4 * (s.x ^ (1 / 2 : ℝ)) ^ 2 := by ring
      _ = 4 * s.x := by rw [h2]
  have hKC : 0 ≤ K.La * CN ^ 2 := by positivity
  have hLa3 : G.La K s ≤ s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps := by
    refine hLa2.trans ?_
    rw [Real.rpow_two]
    have : K.La * CN ^ 2 * Real.log s.x ^ 2 ≤ s.x / 32 * (4 * s.x) :=
      mul_le_mul (by linarith) hlog (by positivity) (by positivity)
    nlinarith
  have hLa0 : 0 ≤ G.La K s := hy.le.trans hLa1
  have hmain : 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s ≤ R.k := by
    calc 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s
        ≤ 2 * (2 * s.x ^ (2 + 8 * s.eps)) * 1 * s.x ^ s.eps * (s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps) := by
          gcongr
      _ = s.x ^ (2 + 8 * s.eps) * s.x ^ s.eps * s.x ^ (2 : ℝ) * s.x ^ s.eps := by ring
      _ = s.x ^ (2 + 8 * s.eps + s.eps + 2 + s.eps) := by
          rw [← Real.rpow_add hxp, ← Real.rpow_add hxp, ← Real.rpow_add hxp]
      _ ≤ s.x ^ (9 / 2 + 10 * s.eps) := Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
      _ ≤ R.k := hk
  rw [div_le_iff₀ hkp]
  nlinarith

end GlobalTheory.EX.WinLow

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

noncomputable section

namespace GlobalTheory.EX.WinLow

open Formalism.MainNotions.StandardLattice Finset

private theorem roots_le {R : Ranks} (H : Host R) : NumberField.Units.torsionOrder H.E ≤ 8 * R.f ^ 2 := by
  have h := UpperTheory.torsionOrder_le_two_mul_finrank_sq H.E
  rw [finrank_E H] at h
  linarith

private theorem span_roots (eps cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hcD : 0 ≤ cD) (hch : 0 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      R.m * (h0v s ch : ℝ) + 8 * (R.f : ℝ) ^ 2 + 2 ≤ s.b := by
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x2, hx2⟩ := scale_sizes eps cD (ch + 7) h0 h1 hcD (by linarith)
  refine ⟨max 8 (max x1 x2), fun s R he hx hR => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨h8, hxa, hxb⟩ := hx
  obtain ⟨hf, -⟩ := hx1 s R he hxa hR
  obtain ⟨-, -, -, -, s5, -⟩ := hx2 s R he hxb hR
  have hxp : 0 < s.x := by linarith
  have hf' : (R.f : ℝ) ≤ s.x ^ (3 : ℕ) := by exact_mod_cast hf
  have o3 : 1 ≤ s.x ^ ch := Real.one_le_rpow (by linarith) hch
  have hH : (h0v s ch : ℝ) ≤ 4 * s.x ^ ch := by
    have := (Nat.ceil_lt_add_one (show 0 ≤ s.x ^ ch by positivity)).le
    unfold h0v; push_cast; linarith
  have hH' : 2 * (s.x ^ ch * s.x ^ (7 : ℕ)) ≤ (h0v s (ch + 7) : ℝ) := by
    have := Nat.le_ceil (s.x ^ (ch + 7))
    have e : s.x ^ (ch + 7) = s.x ^ ch * s.x ^ (7 : ℕ) := by
      rw [Real.rpow_add hxp]; norm_cast
    unfold h0v; push_cast; linarith
  have hm : (1 : ℝ) ≤ R.m := by exact_mod_cast (by have := R.two_le_m; omega : 1 ≤ R.m)
  have hf2 : (R.f : ℝ) ^ 2 ≤ s.x ^ (6 : ℕ) := by
    calc (R.f : ℝ) ^ 2 ≤ (s.x ^ (3 : ℕ)) ^ 2 := pow_le_pow_left₀ (by positivity) hf' 2
      _ = _ := by ring
  have p6 : 1 ≤ s.x ^ (6 : ℕ) := one_le_pow₀ (by linarith)
  have p7 : 8 * s.x ^ (6 : ℕ) ≤ s.x ^ (7 : ℕ) := by
    rw [pow_succ' s.x 6]; exact mul_le_mul_of_nonneg_right h8 (by positivity)
  have hz : 1 ≤ (R.m : ℝ) * s.x ^ ch := one_le_mul_of_one_le_of_one_le hm o3
  have a1 := mul_le_mul_of_nonneg_left hH (by linarith : (0 : ℝ) ≤ R.m)
  have a2 := mul_le_mul_of_nonneg_left hH' (by linarith : (0 : ℝ) ≤ R.m)
  have a3 : (R.m : ℝ) * s.x ^ ch * 4 ≤ (R.m : ℝ) * s.x ^ ch * s.x ^ (7 : ℕ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a4 : s.x ^ (7 : ℕ) ≤ (R.m : ℝ) * s.x ^ ch * s.x ^ (7 : ℕ) := le_mul_of_one_le_left (by linarith) hz
  linarith

theorem places_ok (eps : ℝ) (C : FC) (cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hC : Std C) (hcD : 0 ≤ cD)
    (hch : 0 ≤ ch) : ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ)
      (c : P.Word → Fin (P.R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c →
      ∀ u τ, Formalism.LogVandermondeBounds.StandardLattice.PlaceData s.x (Delv s cD) s.a s.b P.R.k P.R.m (seqOf (P.hcW u τ).u) (seqOf (P.hcW u τ).v)
        (seqOf (P.hcW u τ).b) (seqOf (P.hcW u τ).e) ∧ ∀ j < P.R.m, 1 ≤ seqOf (P.hcW u τ).e j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmid, -⟩ := hC
  have hLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  obtain ⟨x1, hx1⟩ := bottom_len eps C.GK h0 h1 hLa
  obtain ⟨x2, hx2⟩ := scale_sizes eps cD ch h0 h1 hcD hch
  obtain ⟨x3, hx3⟩ := span_roots eps cD ch h0 h1 hcD hch
  refine ⟨max (max x1 x2) x3, fun s P q1 a b c he hx h u τ => ?_⟩
  simp only [max_le_iff] at hx
  have hbl := hx1 s P.R he hx.1.1 h.rank
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := hx2 s P.R he hx.1.2 h.rank
  have s8 := hx3 s P.R he hx.2 h.rank
  have hf0 : (0 : ℝ) ≤ (P.R.f : ℝ) ^ 2 := by positivity
  obtain ⟨v1, v2, ⟨b1, v3, v4, v5, v6⟩, -⟩ := h.hc u
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hk := P.R.m_add_three_le_k
  have hk2 : (2 : ℝ) ≤ P.R.k := by exact_mod_cast (by omega : 2 ≤ P.R.k)
  have hD : (1 : ℝ) ≤ (Delv s cD : ℝ) := by
    have : 0 < ⌈s.x ^ cD⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    exact_mod_cast this
  have htop : (τ : P.R.GG) ∈ P.H.topPlaces → ∃ t : P.H.TT, (τ : P.R.GG) = P.R.tau1 t := by
    intro h1
    unfold Host.topPlaces at h1
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
    exact ⟨⟨t, ht⟩, e.symm⟩
  have hb1 : s.w'' P.R.n ≤ (b1 τ : ℝ) ∧ (b1 τ : ℝ) ≤ s.b + 8 * (P.R.f : ℝ) ^ 2 + 2 := by
    by_cases c1 : (τ : P.R.GG) ∈ P.H.topPlaces
    · obtain ⟨t, ht⟩ := htop c1
      obtain ⟨-, w1, w2⟩ := h.win t t.2
      have f1 : (0 : ℝ) ≤ (⌊s.b' / s.x⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.2 (by positivity)
      have f2 : ((⌊s.b' / s.x⌋ : ℤ) : ℝ) ≤ s.b' := (Int.floor_le _).trans (div_le_self s3 hx1'.le)
      rw [v4 τ t ht]
      push_cast
      constructor <;> linarith
    · by_cases c2 : (τ : P.R.GG) ∈ P.H.thickPlaces
      · have f1 := Int.le_ceil s.b
        have f2 := Int.ceil_lt_add_one s.b
        obtain ⟨e1, e2⟩ := v5 τ c2
        have e3 : ((⌈s.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast e1
        have e4 : (b1 τ : ℝ) < ((⌈s.b⌉ : ℤ) : ℝ) + (NumberField.Units.torsionOrder P.H.E : ℝ) := by exact_mod_cast e2
        have e5 : (NumberField.Units.torsionOrder P.H.E : ℝ) ≤ 8 * (P.R.f : ℝ) ^ 2 := by exact_mod_cast roots_le P.H
        constructor <;> linarith
      · have f1 := Int.le_ceil (s.w'' P.R.n)
        have f2 := Int.ceil_lt_add_one (s.w'' P.R.n)
        rw [v6 τ ⟨τ.2, c1, c2⟩]
        constructor <;> linarith
  refine place_data (P.hcW u τ) s.x (Delv s cD) s.a s.b (h0v s ch) (b1 τ) hx1'.le hD (by positivity)
    (fun i => ?_) (fun hp hp' => ?_) (fun j => ?_) (s1.trans hb1.1) (by linarith [hb1.2])
  · rw [v1 τ i]; push_cast; rfl
  · by_cases c1 : (τ : P.R.GG) ∈ P.H.topPlaces
    · left
      obtain ⟨t, ht⟩ := htop c1
      obtain ⟨⟨-, w0⟩, w1, w2⟩ := h.win t t.2
      obtain ⟨e1, e2⟩ := h.top u τ t hp ht
      have ha : 0 ≤ s.a := by linarith
      have o1 : 1 ≤ s.x ^ (Scale.A / 2) := Real.one_le_rpow hx1'.le (by norm_num [Scale.A])
      have o2 : s.a / ((P.R.k : ℝ) * s.x ^ (Scale.A / 2)) ≤ s.a / 2 :=
        div_le_div_of_nonneg_left ha (by norm_num) (by nlinarith)
      rw [e1, e2]
      push_cast
      constructor <;> linarith
    · right
      obtain ⟨e1, e2⟩ := v2 τ hp c1
      rw [e1, e2]
      push_cast
      exact ⟨rfl, rfl⟩
  · obtain ⟨e1, e2⟩ := v3 τ j
    refine ⟨?_, ?_⟩
    · rw [e1]; push_cast; rfl
    · rw [e2]; push_cast; rfl

theorem rank_consts (eps c g : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      2 * |c| ≤ R.m ∧ (R.m : ℝ) ^ 2 ≤ R.k ∧ 2 * g * (R.m : ℝ) ^ 4 ≤ R.k ∧ 1 ≤ s.L := by
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps h0 h1
  refine ⟨max x1 (max ((2 * |c|) ^ 4) ((2 * |g|) ^ 4)), fun s R he hx hR => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hxa, hxc, hxg⟩ := hx
  obtain ⟨-, hm, -, -, -, -, hL, -, -, -, -, -, -, -, -, hm1, -⟩ := hx1 s R he hxa hR
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have root : ∀ y : ℝ, 0 ≤ y → y ^ 4 ≤ s.x → y ≤ s.x ^ ((1 : ℝ) / 4) := fun y hy h => by
    have := Real.rpow_le_rpow (by positivity) h (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hy, show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num,
      Real.rpow_one] at this
  have m0 : (0 : ℝ) ≤ R.m := by positivity
  have m4 : (R.m : ℝ) ^ 4 ≤ s.x ^ 4 := pow_le_pow_left₀ m0 hm 4
  have m2 : (R.m : ℝ) ^ 2 ≤ s.x ^ 2 := pow_le_pow_left₀ m0 hm 2
  refine ⟨(root _ (by positivity) hxc).trans
    ((Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)).trans hm1), ?_, ?_, hL⟩
  · refine m2.trans (le_trans ?_ hk)
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
  · calc 2 * g * (R.m : ℝ) ^ 4 ≤ 2 * |g| * (R.m : ℝ) ^ 4 := by gcongr; exact le_abs_self g
      _ ≤ s.x ^ ((1 : ℝ) / 4) * s.x ^ 4 :=
          mul_le_mul (root _ (by positivity) hxg) m4 (by positivity) (by positivity)
      _ = s.x ^ ((1 : ℝ) / 4 + 4) := by
          rw [Real.rpow_add hxp, ← Real.rpow_natCast]; norm_num
      _ ≤ s.x ^ (9 / 2 + 10 * s.eps) := Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
      _ ≤ R.k := hk

theorem window_lower : Formalism.MainNotions.StandardLattice.SiegelMassRatioCM → ∀ (eps : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → ∀ cD : ℝ, 0 ≤ cD → ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (du : P.Word → ℕ) (Ds : ℝ), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → (∀ u, (du u : ℝ) = (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm P.H.E P.R.k) (Formalism.MainNotions.StandardLattice.stdLat P.H.E P.R.k)) * (Formalism.MainNotions.StandardLattice.idxColLoc (P.H.g 0) P.R.k ^ P.R.f * Formalism.MainNotions.StandardLattice.idxColLoc (P.H.g 1) P.R.k ^ P.R.f) * ∏ τ : Tau P.R, Formalism.MainNotions.StandardLattice.dimV (fun i : Fin P.R.k => (((P.hcW u τ).u i : ℚ) : ℝ))) → (2 / 3 : ℝ) ^ P.R.f * (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm P.H.E P.R.r) (Formalism.MainNotions.StandardLattice.stdLat P.H.E P.R.r)) * (Formalism.MainNotions.StandardLattice.idxRowLoc (P.H.g 0) P.R.k P.R.m ^ P.R.f * Formalism.MainNotions.StandardLattice.idxRowLoc (P.H.g 1) P.R.k P.R.m ^ P.R.f) * ∏ τ : Tau P.R, Formalism.MainNotions.StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ)) (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) ≤ Ds → ∀ u, (P.R.m : ℝ) * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k))) := by
  intro h2b eps C h0 h1 hC cD hcD
  refine ⟨0, fun ch hch => ?_⟩
  obtain ⟨C1, hC1⟩ := Formalism.LogVandermondeBounds.vandermonde_place_lower_bound eps 5 h0 h1 (by norm_num)
  obtain ⟨x1, hx1⟩ := places_ok eps C cD ch h0 h1 hC hcD hch
  obtain ⟨x2, hx2⟩ := scale_sizes eps cD ch h0 h1 hcD hch
  obtain ⟨x3, hx3⟩ := rank_consts eps C1 C.CGam h0 h1
  obtain ⟨x4, hx4⟩ := hostBounds eps C.P.Cpde h0 h1 hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max (max x1 x2) (max x3 x4), fun s P q1 a b c du Ds he hx h hdu hDs u => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hx
  have hpl := hx1 s P q1 a b c he a1 h u
  obtain ⟨-, -, -, -, -, -, -, hk5⟩ := hx2 s P.R he a2 h.rank
  obtain ⟨r1, r2, r3, hL⟩ := hx3 s P.R he a3 h.rank
  obtain ⟨-, -, -, -, -, rd1, -, rd2, -⟩ := hx4 s P.R P.H he a4 h.rank h.val
  subst he
  let _ := P.H.cmStar
  have hcm := host_cm P.H
  have hk := P.R.m_add_three_le_k
  have hm := P.R.two_le_m
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have hk1 : (1 : ℝ) ≤ P.R.k := by exact_mod_cast (by omega : 1 ≤ P.R.k)
  have hf1 : (1 : ℝ) ≤ P.R.f := by exact_mod_cast f_pos P.R
  have hm0 : (0 : ℝ) ≤ P.R.m := by positivity
  have hv := pi_le_v P.H
  have hv0 : 0 < P.H.v := lt_of_lt_of_le Real.pi_pos hv
  have hlv : Real.log P.H.v ≤ s.L :=
    (Real.log_le_log hv0 (by unfold Host.v; linarith)).trans rd2
  have hD : (1 : ℝ) ≤ (Delv s cD : ℝ) := by
    have : 0 < ⌈s.x ^ cD⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    exact_mod_cast this
  have hbp : 0 < s.b := Real.exp_pos _
  have hgb : ∀ i, s.b ^ 8 ≤ (P.H.g i : ℝ) := fun i =>
    (pow_le_pow_left₀ hbp.le (le_mul_of_one_le_left hbp.le hk1) 8).trans (h.val.2.2.2.2.1 i).1
  have hlg : ∀ i, 8 * s.L ≤ Real.log (P.H.g i) := fun i => by
    have := Real.log_le_log (by positivity) (hgb i)
    rw [Real.log_pow] at this
    unfold Scale.b at this
    rw [Real.log_exp] at this
    exact_mod_cast this
  have hg3 : ∀ i, 3 ≤ P.H.g i := fun i => by
    have h2 : 2 ≤ s.b := by have := Real.add_one_le_exp s.L; unfold Scale.b; linarith
    have h3 : (2 : ℝ) ^ 8 ≤ s.b ^ 8 := pow_le_pow_left₀ (by norm_num) h2 8
    have : (3 : ℝ) ≤ P.H.g i := by linarith [hgb i]
    exact_mod_cast this
  have hg1 : ∀ i, (1 : ℝ) ≤ (P.H.g i : ℝ) := fun i => by exact_mod_cast (P.H.g_prime i).one_lt.le
  obtain ⟨i1, i2, i3⟩ := idx_ratio P.R P.H.g P.H.g_prime hg3
  have hDpos : 0 < Ds := by
    refine lt_of_lt_of_le ?_ hDs
    have := mass_pos P.H.E hcm P.R.r
    exact mul_pos (by positivity) (Finset.prod_pos fun τ _ => dimV_row_pos _)
  have hmass := mass_tel h2b P.H.E hcm P.R.k (by omega) (P.R.m - 1)
  have e1 : P.R.k + (P.R.m - 1) = P.R.r := by unfold Ranks.r; omega
  have e2 : P.R.r + 1 = P.R.k - 1 + P.R.m + 1 := by unfold Ranks.r; omega
  rw [e1, e2] at hmass
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide at hmass
  rw [vInv_E, fDeg_E] at hmass
  have key := hC1 s.x s.one_lt_alt.le P.R.f P.R.m P.R.k P.H.v (Delv s cD) (P.H.g 0 : ℝ) (P.H.g 1 : ℝ)
    (fun n => seqOf (P.hcW u (placeNo P.H n)).u) (fun n => seqOf (P.hcW u (placeNo P.H n)).v)
    (fun n => seqOf (P.hcW u (placeNo P.H n)).b) (fun n => seqOf (P.hcW u (placeNo P.H n)).e)
    Ds (du u) _ _ _ _ (fun M => Formalism.HermitianLatticesTheory.lValEta P.H.E M)
    (f_pos P.R) (by omega) (by omega) hk5 hv hlv hD (hg1 0) (hg1 1) (fun n _ => (hpl _).1)
    (mass_pos P.H.E hcm P.R.k) (mass_pos P.H.E hcm P.R.r) i2 i1
    (fun M hM => by
      have hM2 : 2 ≤ M := by have := (Finset.mem_Ico.1 hM).1; omega
      refine ⟨(Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound P.H.E hcm M hM2).2.1, ?_⟩
      have := cmField_unramified_massIdentity P.H.E hcm M hM2
      rwa [fDeg_E] at this)
    hmass i3
    (by
      rw [prod_places P.H] at hDs
      simp only [dimV_row] at hDs
      simp only [P.hcW_v u, P.hcW_b u]
      exact hDs)
    (by
      have := hdu u
      rw [prod_places P.H] at this
      simp only [dimV_col] at this
      exact this)
  have hsum : 0 ≤ ∑ j ∈ range P.R.m, (1 / (P.R.f : ℝ)) *
      ∑ ρ ∈ range P.R.f, Real.log (seqOf (P.hcW u (placeNo P.H ρ)).e j * P.H.v / Real.pi) := by
    refine Finset.sum_nonneg fun j hj => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => Real.log_nonneg ?_)
    rw [one_le_div Real.pi_pos]
    exact hv.trans (le_mul_of_one_le_left hv0.le ((hpl _).2 j (Finset.mem_range.1 hj)))
  have hq : (P.R.m : ℝ) ^ 2 * s.L / P.R.k ≤ s.L := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hq0 : 0 ≤ (P.R.m : ℝ) ^ 2 * s.L / P.R.k := by positivity
  have hC2 : C1 * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) ≤ P.R.m * s.L :=
    calc _ ≤ |C1| * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |C1| * (2 * s.L) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = 2 * |C1| * s.L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right r1 (by linarith)
  have hg : (P.R.m : ℝ) * (16 * s.L) ≤ P.R.m * (Real.log (P.H.g 0) + Real.log (P.H.g 1)) :=
    mul_le_mul_of_nonneg_left (by linarith [hlg 0, hlg 1]) hm0
  have hmain : 15 * (P.R.m * s.L) ≤ 1 / ((P.R.f : ℝ) * P.R.k) * Real.log (Ds / du u) := by
    have key' : _ + _ - C1 * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) ≤ _ := key
    linarith
  have hmL : 0 < (P.R.m : ℝ) * s.L := by
    have : (2 : ℝ) ≤ P.R.m := by exact_mod_cast hm
    nlinarith
  have hdu0 : (0 : ℝ) < du u := by
    rcases (Nat.cast_nonneg (α := ℝ) (du u)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hmain
      simp only [div_zero, Real.log_zero, mul_zero] at hmain
      linarith
  have hG : 0 < GamS C s P.R := Real.exp_pos _
  rw [Real.log_mul (Real.rpow_pos_of_pos (div_pos hDpos hdu0) _).ne' (Real.rpow_pos_of_pos hG _).ne',
    Real.log_rpow (div_pos hDpos hdu0), Real.log_rpow hG]
  unfold GamS
  rw [Real.log_exp]
  have e3 : -(2 : ℝ) / (P.R.f * P.R.k) * (C.CGam * (P.R.m : ℝ) ^ 5 * P.R.f * s.L) =
      -((2 * C.CGam * (P.R.m : ℝ) ^ 4 / P.R.k) * (P.R.m * s.L)) := by
    field_simp
  have e4 : 2 * C.CGam * (P.R.m : ℝ) ^ 4 / P.R.k ≤ 1 := (div_le_one (by linarith)).2 r3
  have e5 := mul_le_mul_of_nonneg_right e4 hmL.le
  rw [e3]
  linarith

end GlobalTheory.EX.WinLow

end
