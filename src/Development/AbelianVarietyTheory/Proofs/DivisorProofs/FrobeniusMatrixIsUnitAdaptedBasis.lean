module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallModMaximalOfFrobeniusImageSmallStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogFirstBlockSmallOfFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogFirstBlockSmallOfFrobenius
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.SmallFirst

theorem coeff_single_frob {Q : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {d : ℕ}
    (f : MvPowerSeries (Fin d) Q) (i : Fin d) :
    coeff (Finsupp.single i p) (frob p s f) = s (lin f i) := by
  have h1 : frob p s f = expand p hp (map s f) := by
    rw [frob, expand, substAlgHom_apply]
  have h2 : (Finsupp.single i p : Fin d →₀ ℕ) = p • Finsupp.single i 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1, h2, coeff_expand_smul, coeff_map, lin]

theorem coeff_comb {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ ι : Type} [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (α : σ →₀ ℕ) :
    coeff α (comb b e) = ∑ l, algebraMap B Q (b l) * coeff α (e l) := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [MvPowerSeries.coeff_smul]

end GlobalTheory.QLog.SmallFirst

theorem GlobalTheory.QLog.small_first_of_frob : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) → ∀ i, ¬IsUnit (F.θ (w (Sum.inl i))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU w hw i
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsLocalRing O := ValuationRing.isLocalRing O
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set J : Ideal F.B := Ideal.comap F.θ (IsLocalRing.maximalIdeal O) with hJ
  have memJ : ∀ x, x ∈ J ↔ ¬IsUnit (F.θ x) := fun x => by
    rw [hJ, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hpJ : (p : F.B) ∈ J := by
    rw [memJ, map_natCast]; exact Fact.out
  haveI hJp : J.IsPrime := Ideal.IsPrime.comap F.θ
  set α : Fin d →₀ ℕ := Finsupp.single i p with hα

  have hc : ∀ l, ∃ cl : F.B, (p : F.Q) * coeff α (e l) = algebraMap F.B F.Q cl := by
    intro l
    obtain ⟨b, -, hb⟩ := GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hlift ⊤ (e l) (hbas.1 l) α i
    refine ⟨b, ?_⟩
    rw [← hb, hα, Finsupp.single_eq_same]
  choose cc hcc using hc
  have key : ∀ m, algebraMap F.B F.Q (∑ l, U l m * cc l) =
      (p : F.Q) * ∑ l, algebraMap F.B F.Q (U l m) * coeff α (e l) := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← hcc]; ring
  have hcol : ∀ m l, (U * blk d k (p : F.B) 1) l m = U l m * Sum.elim (fun _ => (p : F.B)) (fun _ => 1) m := by
    intro m l
    rw [blk, Matrix.mul_diagonal]
  have hR : ∀ m, (∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0) ∈ J := by
    intro m
    cases m with
    | inl i' =>
      obtain ⟨t, ht, hteq⟩ := (hU (Sum.inl i')).2 i' rfl α
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 ht
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, (hadp i').2, SmallFirst.coeff_comb] at hteq
      have hs : F.s (Pi.single (M := fun _ : Fin d => F.Q) i' 1 i) =
          algebraMap F.B F.Q (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0) := by
        by_cases h : i' = i
        · subst h; simp
        · have h' : i ≠ i' := Ne.symm h
          simp [Pi.single_apply, h', h]
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inl i')) * coeff α (e l) =
          algebraMap F.B F.Q (∑ l, U l (Sum.inl i') * cc l) := by
        rw [key, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inl, map_mul, map_natCast]; ring
      rw [hs, hsum, ← map_sub] at hteq
      have := F.frame.inj hteq
      have h2 : (∑ l, U l (Sum.inl i') * cc l) - (if (Sum.inl i' : Fin d ⊕ Fin k) = Sum.inl i then 1 else 0)
          = -(t' * p) := by rw [← this]; ring
      rw [h2]
      exact J.neg_mem (J.mul_mem_left _ hpJ)
    | inr j =>
      obtain ⟨b, -, hb⟩ := (hbas.1 (Sum.inr j)).2.1 i
      obtain ⟨t, -, hteq⟩ := (hU (Sum.inr j)).1 α
      rw [map_sub, SmallFirst.coeff_single_frob p hp0, hb, F.s_alg, SmallFirst.coeff_comb] at hteq
      have hsum : ∑ l, algebraMap F.B F.Q ((U * blk d k (p : F.B) 1) l (Sum.inr j)) * coeff α (e l) =
          ∑ l, algebraMap F.B F.Q (U l (Sum.inr j)) * coeff α (e l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hcol, Sum.elim_inr, mul_one]
      rw [hsum] at hteq
      have h3 : algebraMap F.B F.Q (∑ l, U l (Sum.inr j) * cc l) =
          algebraMap F.B F.Q ((p : F.B) * (F.σ b - t)) := by
        rw [key, map_mul, map_sub, map_natCast, ← hteq]; ring
      have h4 := F.frame.inj h3
      have hne : (Sum.inr j : Fin d ⊕ Fin k) ≠ Sum.inl i := Sum.inr_ne_inl
      rw [if_neg hne, sub_zero, h4]
      exact J.mul_mem_right _ hpJ

  have hW : ∑ m, F.σ (w m) * ∑ l, U l m * cc l ∈ J := by
    have : ∑ m, F.σ (w m) * ∑ l, U l m * cc l = ∑ l, U.mulVec (fun j => F.σ (w j)) l * cc l := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [this]
    exact J.sum_mem fun l _ => J.mul_mem_right _ ((memJ _).2 (hw l))
  have hD : ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) ∈ J :=
    J.sum_mem fun m _ => J.mul_mem_left _ (hR m)
  have hσ : F.σ (w (Sum.inl i)) ∈ J := by
    have : F.σ (w (Sum.inl i)) = (∑ m, F.σ (w m) * ∑ l, U l m * cc l) -
        ∑ m, F.σ (w m) * ((∑ l, U l m * cc l) - (if m = Sum.inl i then 1 else 0)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring
    rw [this]
    exact J.sub_mem hW hD
  obtain ⟨z, hz⟩ := F.σ_pow (w (Sum.inl i))
  have hpow : w (Sum.inl i) ^ p ∈ J := by
    have : w (Sum.inl i) ^ p = F.σ (w (Sum.inl i)) - p * z := by rw [← hz]; ring
    rw [this]
    exact J.sub_mem hσ (J.mul_mem_right _ hpJ)
  exact (memJ _).1 (hJp.mem_of_pow_mem p hpow)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogFirstBlockSmallOfFrobeniusStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLog_first_block_small_of_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) → ∀ i, ¬IsUnit (F.θ (w (Sum.inl i))) := by
  first | exact @GlobalTheory.QLog.small_first_of_frob | exact GlobalTheory.QLog.small_first_of_frob | (intros; apply GlobalTheory.QLog.small_first_of_frob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixIsUnitAdaptedBasis
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrobUnit

theorem isUnit_of_isUnit_map {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) (b : B) (hb : IsUnit (θ b)) : IsUnit b := by
  obtain ⟨u, hu⟩ := hb
  obtain ⟨b', hb'⟩ := hF.surj (↑u⁻¹ : O)
  have hx0 : θ (b * b' - 1) = 0 := by
    rw [map_sub, map_mul, hb', ← hu, map_one, Units.mul_inv, sub_self]
  obtain ⟨y, -, hy⟩ := hF.pd _ hx0
  haveI := hF.complete
  have hj : (p : B) * y ∈ (⊥ : Ideal B).jacobson :=
    IsAdicComplete.le_jacobson_bot _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton (p : B))))
  have hu1 := (Ideal.mem_jacobson_bot.1 hj) (-(-1) ^ p)
  have hgeom := mul_neg_geom_sum (-(b * b' - 1)) p
  have h2 : (1 - -(b * b' - 1)) * ∑ i ∈ Finset.range p, (-(b * b' - 1)) ^ i =
      (p : B) * y * (-(-1) ^ p) + 1 := by
    rw [hgeom, neg_pow, hy]; ring
  have h3 : IsUnit (1 - -(b * b' - 1)) := isUnit_of_mul_isUnit_left (h2 ▸ hu1)
  have h4 : (1 - -(b * b' - 1)) = b * b' := by ring
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left h3

theorem exists_pow_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (a : O) :
    ∃ r : O, r ^ p = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) (Fact.out : p.Prime).pos
  have h1 : v z ≤ 1 := by
    have := hv.map_le_one a
    rw [← hz, map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' (Fact.out : p.Prime).ne_zero).1 this
  obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
  exact ⟨r, hv.hom_inj (by rw [map_pow, hr, hz])⟩

theorem frob_matrix_isUnit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsUnit U := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e hB hA U hU
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hm : ∀ x : O, ¬IsUnit x ↔ x ∈ IsLocalRing.maximalIdeal O := fun x =>
    (IsLocalRing.mem_maximalIdeal x).symm
  have hpm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (hm _).1 (Fact.out)
  have hσ : ∀ b, ∃ z, F.σ b = b ^ p + (p : F.B) * z := fun b => by
    obtain ⟨z, hz⟩ := F.σ_pow b
    exact ⟨z, by rw [← hz]; ring⟩
  have hσm : ∀ b, F.θ b ∈ IsLocalRing.maximalIdeal O → F.θ (F.σ b) ∈ IsLocalRing.maximalIdeal O := by
    intro b hb
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add (f := _), map_pow, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hb _ (Fact.out : p.Prime).pos)
      (Ideal.mul_mem_right _ _ hpm)
  have key : ∀ w : Fin d ⊕ Fin k → F.B, (∀ l, ¬IsUnit (F.θ (U.mulVec (fun j => F.σ (w j)) l))) →
      ∀ l, ¬IsUnit (F.θ (w l)) := by
    intro w hw
    have h1 := GlobalTheory.T.quasiLog_first_block_small_of_frobenius p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU w hw
    have h2 := GlobalTheory.T.small_mod_maximal_of_frobenius_image_small p C v O hv ε hε F G d c μ' hL hμ k e hB hA U hU (fun j => w (Sum.inr j)) (by
      intro l
      rw [hm]
      have hsplit : U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) (fun j => w (Sum.inr j)) :
          Fin d ⊕ Fin k → F.B) j)) l = U.mulVec (fun j => F.σ (w j)) l -
          ∑ m, U l m * F.σ ((Sum.elim (fun i => w (Sum.inl i)) (fun _ => 0) :
            Fin d ⊕ Fin k → F.B) m) := by
        simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, ← mul_sub]
        refine Finset.sum_congr rfl fun m _ => ?_
        congr 1
        cases m <;> simp
      rw [hsplit, map_sub]
      refine Ideal.sub_mem _ ((hm _).1 (hw l)) ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Ideal.sum_mem _ fun m _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ (hσm _ ?_)
      cases m with
      | inl i => simpa using (hm _).1 (h1 i)
      | inr j => simp)
    intro l
    cases l with
    | inl i => exact h1 i
    | inr j => exact h2 j
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_of_isUnit_map F.frame
  rw [RingHom.map_det]
  by_contra hdet
  set M := (U.map F.θ).map (IsLocalRing.residue O) with hMdef
  have hM : M.det = 0 := by
    rw [show M = (IsLocalRing.residue O).mapMatrix (F.θ.mapMatrix U) from rfl, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 hdet)
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hlift : ∀ l, ∃ b : F.B, IsLocalRing.residue O (F.θ b) ^ p = x l := by
    intro l
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (x l)
    obtain ⟨r, hr⟩ := exists_pow_eq (p := p) hv a
    obtain ⟨b, hb⟩ := F.frame.surj r
    exact ⟨b, by rw [hb, ← map_pow, hr, ha]⟩
  choose w hw using hlift
  have hres : ∀ b, IsLocalRing.residue O (F.θ (F.σ b)) = IsLocalRing.residue O (F.θ b) ^ p := by
    intro b
    obtain ⟨z, hz⟩ := hσ b
    rw [hz, map_add (f := _), map_pow, map_mul, map_natCast, map_add (f := _), map_pow, map_mul,
      (IsLocalRing.residue_eq_zero_iff _).2 hpm, zero_mul, add_zero]
  have hk := key w (by
    intro l
    rw [hm, ← IsLocalRing.residue_eq_zero_iff]
    have := congrFun hx l
    simp only [Matrix.mulVec, dotProduct, hMdef, Matrix.map_apply, Pi.zero_apply] at this ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simpa [hres, hw] using this)
  apply hx0
  funext l
  rw [← hw l, (IsLocalRing.residue_eq_zero_iff _).2 ((hm _).1 (hk l)), zero_pow (Fact.out : p.Prime).ne_zero,
    Pi.zero_apply]

end GlobalTheory.FrobUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixIsUnitAdaptedBasisStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_matrix_isUnit_adapted_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsUnit U := by
  first | exact @GlobalTheory.FrobUnit.frob_matrix_isUnit | exact GlobalTheory.FrobUnit.frob_matrix_isUnit | (intros; apply GlobalTheory.FrobUnit.frob_matrix_isUnit <;> assumption)
end
