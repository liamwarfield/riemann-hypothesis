module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterCoordinatesSeriesOnePlace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.PrvFOfOrbitLetterBounds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorLowerBoundOfPlaceBoundWitt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundOverSecondEmbeddingAnyBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundOverSecondEmbeddingAnyBasePoint
noncomputable section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical Formalism.MainNotions.OrbitPlaces PI.OrbBoundFW

namespace GlobalTheory.TwU

theorem orbitBound_overSecondEmbedding_anyBasePoint_alt : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  intro D L X K ce E C6 C hA hS hC p _ h _hc0 _hP hp u i hi t ep sg be hep hsg h1 h2 h3 h4 Th hB0
  have hAdm := admissible_of_jet_bounds h u i (true, t) Th ep sg be hep hsg h1 h2 h3 h4 hB0
  have hCor := (hA.1 _ hAdm).2 (L.sc.a ^ 2) (setting_sq hS h hp u hi (true, t) Th) D.R.k (wOrb D p i (true, t))
    (eOrb E p u i (true, t)) (three_le_k D) (wOrb_pos hS p hi (true, t)) (eOrb_bounds hS p u hi (true, t))
    (dl_off h u i (true, t) Th) (dl_on h u i (true, t) Th)
  refine kvalGe_mono hCor ?_
  have hg : 0 ≤ ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s :=
    Finset.sum_nonneg fun s _ => orbit_local_term_nonneg _ s
  have hw := sum_Wc_le hS h u hi (true, t) Th
  have hl := loss_le hS hC h hp hi (true, t)
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five
  have hgam : Formalism.MainNotions.product_zeroth_first_parts.gam p = Formalism.MainNotions.G.gam p := rfl
  have hgpos : 0 ≤ Formalism.MainNotions.G.gam p := by
    unfold Formalism.MainNotions.G.gam
    apply div_nonneg (by linarith)
    nlinarith
  have hsw : 0 ≤ ∑ s, wOrb D p i (true, t) s := Finset.sum_nonneg fun s _ => (wOrb_pos hS p hi (true, t) s).le
  have hc6 : C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) ≤ ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right hC.c6 hsw
  have hgw : Formalism.MainNotions.G.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) ≤
      Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hgpos
  have hi1 : i + 1 - 1 = i := by omega
  rw [hi1] at hl
  have hF : FOrb D (i + 1) p (true, t) = lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s) := rfl
  have hE : errF L K ce (i + 1) p (true, t) = Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
      ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) +
      ((nP D p : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
          (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
        (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
          K.dl2 * (topsOrb D p (true, t) : ℝ) * Real.logb p (2 * L.sc.a) ^ 2)) := by
    unfold errF; simp only [wOrb]; ring
  rw [hi1] at hE
  show FOrb D (i + 1) p (true, t) - errF L K ce (i + 1) p (true, t) ≤
    (∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s +
      lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s)) - C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) -
      Formalism.MainNotions.product_zeroth_first_parts.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) -
      C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1))
  rw [hF, hE, hgam]
  linarith

end GlobalTheory.TwU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundOverSecondEmbeddingAnyBasePointStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitBound_overSecondEmbedding_anyBasePoint : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  first | exact @GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | exact GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | (intros; apply GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffApplyDPIvOfKvalGe
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.KvalAgree

section Val

variable {p : ℕ} [Fact p.Prime]

open Formalism.L2.G.Pend (k0ToC wToC witt_fraction_to_Cp_algebraMap norm_k0ToC_le_iff norm_p_C norm_wToC_unit)

theorem exists_norm_eq_zpow (z : FormalGroupSystem.K0 p) (hz : z ≠ 0) : ∃ e : ℤ, ‖k0ToC p z‖ = (p : ℝ) ^ e := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := FormalGroupSystem.WW p) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hz
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 (WittVector.irreducible p (k := FormalGroupSystem.kb p))
  obtain ⟨l, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 (WittVector.irreducible p (k := FormalGroupSystem.kb p))
  refine ⟨(k : ℤ) - l, ?_⟩
  rw [map_div₀, witt_fraction_to_Cp_algebraMap, witt_fraction_to_Cp_algebraMap, norm_div, hu, hw, map_mul, map_mul, map_pow, map_pow, map_natCast, norm_mul, norm_mul,
    norm_wToC_unit, norm_wToC_unit, norm_pow, norm_pow, norm_p_C, one_mul, one_mul, zpow_sub₀ hp0, zpow_natCast, zpow_natCast,
    inv_pow, inv_pow]
  field_simp

theorem mem_of_norm_le (z : FormalGroupSystem.K0 p) (g : ℝ) (h : ‖k0ToC p z‖ ≤ (p : ℝ) ^ (-g)) :
    ∃ a : FormalGroupSystem.WW p, z = (p : FormalGroupSystem.K0 p) ^ ⌈g⌉ * algebraMap (FormalGroupSystem.WW p) (FormalGroupSystem.K0 p) a := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  obtain ⟨e, he⟩ := exists_norm_eq_zpow z hz
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpK : (p : FormalGroupSystem.K0 p) ≠ 0 := by
    intro h0
    have h1 := congrArg (k0ToC p) h0
    rw [map_natCast, map_zero] at h1
    exact Formalism.L2.G.Pend.pC_ne h1
  rw [he, ← Real.rpow_intCast] at h
  have h1 : (e : ℝ) ≤ -g := (Real.rpow_le_rpow_left_iff hp1).1 h
  have hce : ⌈g⌉ ≤ -e := Int.ceil_le.2 (by push_cast; linarith)
  have hn : ‖k0ToC p (z / (p : FormalGroupSystem.K0 p) ^ ⌈g⌉)‖ ≤ 1 := by
    rw [map_div₀, map_zpow₀, map_natCast, norm_div, norm_zpow, norm_p_C, he, inv_zpow, div_inv_eq_mul, ← zpow_add₀ hp0]
    exact zpow_le_one_of_nonpos₀ hp1.le (by omega)
  obtain ⟨a, ha⟩ := (norm_k0ToC_le_iff p _).1 hn
  refine ⟨a, ?_⟩
  rw [ha]
  field_simp

end Val

section Mat

theorem det_col_alt {R : Type} [CommRing R] {h r : ℕ} (M : Fin h → Fin r → R) (J : Fin h → Fin r) :
    Matrix.det (Matrix.of fun i k : Fin h => M i (J k)) = 0 ∨
      ∃ (e : Fin h ↪o Fin r) (u : ℤˣ), Matrix.det (Matrix.of fun i k : Fin h => M i (J k)) =
        ((u : ℤ) : R) * Matrix.det (Matrix.of fun i k : Fin h => M i (e k)) := by
  by_cases hJ : Function.Injective J
  · right
    have hm : Monotone (J ∘ Tuple.sort J) := Tuple.monotone_sort J
    have hs : StrictMono (J ∘ Tuple.sort J) := hm.strictMono_of_injective (hJ.comp (Tuple.sort J).injective)
    refine ⟨OrderEmbedding.ofStrictMono _ hs, Equiv.Perm.sign (Tuple.sort J), ?_⟩
    have h1 := Matrix.det_permute' (Tuple.sort J) (Matrix.of fun i k : Fin h => M i (J k))
    have h2 : (Matrix.of fun i k : Fin h => M i (J k)).submatrix id (Tuple.sort J) =
        Matrix.of fun i k : Fin h => M i (OrderEmbedding.ofStrictMono _ hs k) := by
      ext i k
      simp
    rw [h2] at h1
    rw [h1, ← mul_assoc]
    have h3 : (((Equiv.Perm.sign (Tuple.sort J) : ℤˣ) : ℤ) : R) * (((Equiv.Perm.sign (Tuple.sort J) : ℤˣ) : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [h3, one_mul]
  · left
    simp only [Function.Injective, not_forall] at hJ
    obtain ⟨a, b, hab, hne⟩ := hJ
    exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hab])

end Mat

section Lin

open Formalism.L2.G.Pend (k0ToC)

theorem applyD_eq_sum {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc)
    (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    applyD P f = ∑ n ∈ S, ((∏ x ∈ n.support, ((n x).factorial : Kc)) * MvPowerSeries.coeff n f) •
      MvPolynomial.map (Int.castRingHom Kc) (AddMonoidAlgebra.coeff P n) := by
  unfold applyD
  refine Finset.sum_subset hS fun n _ hn => ?_
  rw [MvPolynomial.notMem_support_iff.1 hn]
  simp

theorem applyD_add {σ τ Kc : Type} [Field Kc] (P Q : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    applyD (P + Q) f = applyD P f + applyD Q f := by
  rw [applyD_eq_sum (P + Q) f _ (MvPolynomial.support_add (p := P) (q := Q)),
    applyD_eq_sum P f (P.support ∪ Q.support) Finset.subset_union_left,
    applyD_eq_sum Q f (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), smul_add]

theorem applyD_zero {σ τ Kc : Type} [Field Kc] (f : MvPowerSeries σ Kc) :
    applyD (0 : MvPolynomial σ (MvPolynomial τ ℤ)) f = 0 := by
  simp [applyD]

theorem applyD_neg {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    applyD (-P) f = -applyD P f := by
  have h := applyD_add (-P) P f
  rw [neg_add_cancel, applyD_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 : ℕ} {p : ℕ} [Fact p.Prime]

theorem applyAt0_eq_sum (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[p]) (P : MvPolynomial (product_zeroth_first_parts.XZ Lt N0 N1) ℤ)
    (S : Finset (product_zeroth_first_parts.XZ Lt N0 N1 →₀ ℕ)) (hS : P.support ⊆ S) :
    product_zeroth_first_parts.applyAt0 N0 N1 p Th P = ∑ μ ∈ S, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
      (((AddMonoidAlgebra.coeff P μ : ℤ) : ℂ_[p]) *
        ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[p])) *
        MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th) := by
  unfold product_zeroth_first_parts.applyAt0
  refine Finset.sum_subset hS fun n _ hn => ?_
  rw [MvPolynomial.notMem_support_iff.1 hn]
  simp

theorem applyAt0_add (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[p]) (P Q : MvPolynomial (product_zeroth_first_parts.XZ Lt N0 N1) ℤ) :
    product_zeroth_first_parts.applyAt0 N0 N1 p Th (P + Q) = product_zeroth_first_parts.applyAt0 N0 N1 p Th P + product_zeroth_first_parts.applyAt0 N0 N1 p Th Q := by
  rw [applyAt0_eq_sum Th (P + Q) _ (MvPolynomial.support_add (p := P) (q := Q)),
    applyAt0_eq_sum Th P (P.support ∪ Q.support) Finset.subset_union_left,
    applyAt0_eq_sum Th Q (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← map_add (f := _), MvPolynomial.coeff_add, Int.cast_add, add_mul, add_mul]

def psi {σ τ : Type} (zi : Lt × Fin N0 × Fin N1 → σ) (fi : Lt × ℕ × Fin N0 → τ) :
    MvPolynomial (product_zeroth_first_parts.XZ Lt N0 N1) ℤ →+* MvPolynomial σ (MvPolynomial τ ℤ) :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (Sum.elim (fun x => MvPolynomial.C (MvPolynomial.X (fi x))) (fun y => MvPolynomial.X (zi y)))

theorem prod_X_pow {α σ R : Type} [CommSemiring R] (g : α → σ) (m : α →₀ ℕ) :
    (m.prod fun a k => (MvPolynomial.X (g a) : MvPolynomial σ R) ^ k) =
      MvPolynomial.monomial (Finsupp.mapDomain g m) 1 := by
  rw [MvPolynomial.monomial_eq,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp

theorem psi_monomial {σ τ : Type} (zi : Lt × Fin N0 × Fin N1 → σ) (fi : Lt × ℕ × Fin N0 → τ) (μ : product_zeroth_first_parts.XZ Lt N0 N1 →₀ ℕ)
    (c : ℤ) : psi zi fi (MvPolynomial.monomial μ c) =
      MvPolynomial.monomial (Finsupp.mapDomain zi (Finsupp.sumFinsuppEquivProdFinsupp μ).2)
        (MvPolynomial.monomial (Finsupp.mapDomain fi (Finsupp.sumFinsuppEquivProdFinsupp μ).1) c) := by
  obtain ⟨⟨m1, m2⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective μ
  simp only [Equiv.apply_symm_apply]
  have h0 : Finsupp.sumFinsuppEquivProdFinsupp.symm (m1, m2) = m1.sumElim m2 := rfl
  rw [h0]
  unfold psi
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_sumElim]
  have h1 : (m1.prod ((fun (i : product_zeroth_first_parts.XZ Lt N0 N1) (k : ℕ) =>
      (Sum.elim (fun x => (MvPolynomial.C (MvPolynomial.X (fi x)) : MvPolynomial σ (MvPolynomial τ ℤ)))
        (fun y => MvPolynomial.X (zi y))) i ^ k) ∘ Sum.inl)) =
      MvPolynomial.C (MvPolynomial.monomial (Finsupp.mapDomain fi m1) (1 : ℤ)) := by
    rw [← prod_X_pow fi m1]
    simp [Finsupp.prod, map_prod, map_pow]
  have h2 : (m2.prod ((fun (i : product_zeroth_first_parts.XZ Lt N0 N1) (k : ℕ) =>
      (Sum.elim (fun x => (MvPolynomial.C (MvPolynomial.X (fi x)) : MvPolynomial σ (MvPolynomial τ ℤ)))
        (fun y => MvPolynomial.X (zi y))) i ^ k) ∘ Sum.inr)) =
      MvPolynomial.monomial (Finsupp.mapDomain zi m2) 1 := by
    rw [← prod_X_pow zi m2]
    rfl
  rw [h1, h2]
  have h3 : (Int.castRingHom (MvPolynomial σ (MvPolynomial τ ℤ))) c = MvPolynomial.C (MvPolynomial.C c) := by
    simp
  rw [h3, ← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.C_mul_monomial, mul_one]

theorem map_applyD_psi {σ τ : Type} (zi : Lt × Fin N0 × Fin N1 → σ) (fi : Lt × ℕ × Fin N0 → τ) (hzi : Function.Injective zi)
    (f : MvPowerSeries σ (FormalGroupSystem.K0 p)) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[p])
    (hTh : ∀ m, MvPowerSeries.coeff m Th = k0ToC p (MvPowerSeries.coeff (Finsupp.mapDomain zi m) f))
    (G : MvPolynomial (product_zeroth_first_parts.XZ Lt N0 N1) ℤ) :
    MvPolynomial.map (k0ToC p) (applyD (psi zi fi G) f) = MvPolynomial.rename fi (product_zeroth_first_parts.applyAt0 N0 N1 p Th G) := by
  induction G using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add (f := _), applyD_add, applyAt0_add, map_add (f := _), map_add (f := _), hP, hQ]
  | monomial μ c =>
    rw [psi_monomial, applyD_eq_sum _ f _ MvPolynomial.support_monomial_subset,
      applyAt0_eq_sum Th _ _ MvPolynomial.support_monomial_subset, Finset.sum_singleton, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, MvPolynomial.coeff_monomial, if_pos rfl, MvPolynomial.map_monomial,
      MvPolynomial.smul_monomial, MvPolynomial.map_monomial, MvPolynomial.rename_monomial]
    congr 1
    have hP : k0ToC p (∏ x ∈ (Finsupp.mapDomain zi (Finsupp.sumFinsuppEquivProdFinsupp μ).2).support,
        (((Finsupp.mapDomain zi (Finsupp.sumFinsuppEquivProdFinsupp μ).2) x).factorial : FormalGroupSystem.K0 p)) =
        ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[p])) := by
      rw [map_prod]
      simp only [map_natCast]
      exact Finsupp.prod_mapDomain_index_inj (h := fun _ (k : ℕ) => (k.factorial : ℂ_[p])) hzi
    rw [smul_eq_mul, map_mul, map_mul, hP, ← hTh]
    simp only [eq_intCast, map_intCast]
    ring

end Lin

section Main

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl)

theorem nuv_eq_zero (s : Fin (X.G.P.n' v)) {i : ℕ} (hi : NN X.G.P.m X.t (j + 1) < i) : X.nuv v (j + 1) s i = 0 := by
  have h1 : X.G.P.m + 1 ≤ NN X.G.P.m X.t (j + 1) := by
    unfold NN
    omega
  unfold Sys.nuv nu
  rw [if_neg (by omega), if_neg (by omega)]

theorem colHt_eq (nD : YoungDiagram) (s : Fin (X.G.P.n' v))
    (hnu : ∀ r, (((nD.rowLen r : ℕ) : ℤ)) = X.nuv v (j + 1) s (r + 1)) (c : ℕ) :
    X.colHt v (j + 1) s c = nD.colLen c := by
  have hle : nD.colLen c ≤ NN X.G.P.m X.t (j + 1) := by
    by_contra hlt
    push_neg at hlt
    have h2 : c < nD.rowLen (NN X.G.P.m X.t (j + 1)) :=
      YoungDiagram.mem_iff_lt_rowLen.1 (YoungDiagram.mem_iff_lt_colLen.2 hlt)
    have h3 := hnu (NN X.G.P.m X.t (j + 1))
    rw [nuv_eq_zero X j v s (Nat.lt_succ_self _)] at h3
    omega
  unfold Sys.colHt
  have hF : ((Finset.Icc 1 (NN X.G.P.m X.t (j + 1))).filter fun i => (c : ℤ) < X.nuv v (j + 1) s i) =
      Finset.Icc 1 (nD.colLen c) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      rw [← hnu r] at h3
      have h4 : c < nD.rowLen r := by exact_mod_cast h3
      have h5 := YoungDiagram.mem_iff_lt_colLen.1 (YoungDiagram.mem_iff_lt_rowLen.2 h4)
      omega
    · rintro ⟨h1, h2⟩
      obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
      refine ⟨⟨h1, by omega⟩, ?_⟩
      rw [← hnu r]
      have h4 : (r, c) ∈ nD := YoungDiagram.mem_iff_lt_colLen.2 (by omega)
      exact_mod_cast YoungDiagram.mem_iff_lt_rowLen.1 h4
  rw [hF]
  simp

def colDet (s : Fin (X.G.P.n' v)) (h : ℕ) (J : ℕ → Fin (NN X.G.P.m X.t (j + 1))) :
    MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ) :=
  Matrix.det (Matrix.of fun (i i' : Fin h) =>
    ∑ a : Fin (NN X.G.P.m X.t j),
      MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : X.FrI j)) *
        MvPolynomial.X (⟨v, (s, a, J i'.val)⟩ : X.ZA j))

variable [NeZero (X.G.P.n' v)]

def zi : ZMod (X.G.P.n' v) × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)) → X.ZA j :=
  fun y => ⟨v, (toFin y.1, y.2)⟩

def fi : ZMod (X.G.P.n' v) × ℕ × Fin (NN X.G.P.m X.t j) → X.FrI j :=
  fun x => ⟨v, (toFin x.1, x.2)⟩

theorem toFin_injective {n : ℕ} [NeZero n] : Function.Injective (toFin : ZMod n → Fin n) := by
  intro a b h
  exact ZMod.val_injective n (congrArg Fin.val h)

theorem zi_injective : Function.Injective (zi X j v) := by
  rintro ⟨s, y⟩ ⟨s', y'⟩ h
  simp only [zi, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at h
  rw [toFin_injective h.1, h.2]

theorem fi_injective : Function.Injective (fi X j v) := by
  rintro ⟨s, y⟩ ⟨s', y'⟩ h
  simp only [fi, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq] at h
  rw [toFin_injective h.1, h.2]

theorem psi_minor (s : ZMod (X.G.P.n' v)) (h : ℕ) (e : Fin h ↪o Fin (NN X.G.P.m X.t (j + 1))) :
    psi (zi X j v) (fi X j v) (product_zeroth_first_parts.minorXZ (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) s h e) =
      Matrix.det (Matrix.of fun (i k : Fin h) => ∑ a : Fin (NN X.G.P.m X.t j),
        MvPolynomial.C (MvPolynomial.X (⟨v, (toFin s, i.val, a)⟩ : X.FrI j)) *
          MvPolynomial.X (⟨v, (toFin s, a, e k)⟩ : X.ZA j)) := by
  unfold product_zeroth_first_parts.minorXZ
  rw [RingHom.map_det]
  congr 1
  ext1 i k
  simp [psi, zi, fi]

theorem colDet_alt (s : ZMod (X.G.P.n' v)) (h : ℕ) (J : ℕ → Fin (NN X.G.P.m X.t (j + 1))) :
    colDet X j v (toFin s) h J = 0 ∨ ∃ (e : Fin h ↪o Fin (NN X.G.P.m X.t (j + 1))) (u : ℤˣ),
      colDet X j v (toFin s) h J = ((u : ℤ) : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) *
        psi (zi X j v) (fi X j v) (product_zeroth_first_parts.minorXZ (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) s h e) := by
  rcases det_col_alt (fun (i : Fin h) (b : Fin (NN X.G.P.m X.t (j + 1))) => ∑ a : Fin (NN X.G.P.m X.t j),
      (MvPolynomial.C (MvPolynomial.X (⟨v, (toFin s, i.val, a)⟩ : X.FrI j)) *
        MvPolynomial.X (⟨v, (toFin s, a, b)⟩ : X.ZA j) : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)))
      (fun k => J k.val) with h0 | ⟨e, u, h1⟩
  · exact Or.inl h0
  · exact Or.inr ⟨e, u, by rw [psi_minor]; exact h1⟩

end Main

open Formalism.L2.G.Pend (k0ToC) in
theorem coeff_applyD_PIv_of_KvalGe : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) [NeZero (X.G.P.n' v)] (nu : ZMod (X.G.P.n' v) → YoungDiagram), (∀ s r, (((nu s).rowLen r : ℕ) : ℤ) = X.nuv v (j + 1) (toFin s) (r + 1)) → ∀ (f : MvPowerSeries (X.ZA j) (FormalGroupSystem.K0 p)) (g : ℝ), product_zeroth_first_parts.KvalGe (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) p nu (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) f))) g → ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), ∃ a : FormalGroupSystem.WW p, AddMonoidAlgebra.coeff (applyD (X.PIv j I v) f) n = (p : FormalGroupSystem.K0 p) ^ ⌈g⌉ * algebraMap (FormalGroupSystem.WW p) (FormalGroupSystem.K0 p) a := by
  intro p _ X j v _ nu hnu f g hK I n
  have hTh : ∀ m, MvPowerSeries.coeff m (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) f))) =
      k0ToC p (MvPowerSeries.coeff (Finsupp.mapDomain (zi X j v) m) f) := by
    intro m
    rw [MvPowerSeries.coeff_map]
    congr 1
    show MvPowerSeries.coeff (Finsupp.mapDomain _ (Finsupp.mapDomain _ m)) f = _
    rw [← Finsupp.mapDomain_comp]
    rfl
  have hrow : ∀ s : ZMod (X.G.P.n' v), (X.nuv v (j + 1) (toFin s) 1).toNat = (nu s).rowLen 0 := by
    intro s
    rw [show (1 : ℕ) = 0 + 1 from rfl, ← hnu s 0, Int.toNat_natCast]
  have hbij : Function.Bijective (toFin : ZMod (X.G.P.n' v) → Fin (X.G.P.n' v)) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨toFin_injective, by simp [ZMod.card]⟩
  have hP : X.PIv j I v = ∏ s : ZMod (X.G.P.n' v), ∏ c : Fin ((nu s).rowLen 0),
      colDet X j v (toFin s) ((nu s).colLen c) (I v (toFin s) c) := by
    unfold Sys.PIv
    symm
    refine Fintype.prod_bijective toFin hbij _ _ fun s => ?_
    rw [hrow s, Finset.prod_range]
    refine Finset.prod_congr rfl fun c _ => ?_
    show _ = colDet X j v (toFin s) (X.colHt v (j + 1) (toFin s) c) (I v (toFin s) c)
    rw [colHt_eq X j v (nu s) (toFin s) (hnu s)]
  by_cases hz : ∃ (s : ZMod (X.G.P.n' v)) (c : Fin ((nu s).rowLen 0)),
      colDet X j v (toFin s) ((nu s).colLen c) (I v (toFin s) c) = 0
  · obtain ⟨s, c, h0⟩ := hz
    have h1 : X.PIv j I v = 0 := by
      rw [hP]
      exact Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero (Finset.mem_univ c) h0)
    rw [h1, applyD_zero]
    exact ⟨0, by simp⟩
  · push_neg at hz
    have hch := fun (s : ZMod (X.G.P.n' v)) (c : Fin ((nu s).rowLen 0)) =>
      (colDet_alt X j v s ((nu s).colLen c) (I v (toFin s) c)).resolve_left (hz s c)
    choose e u he using hch
    have hG : X.PIv j I v = (((∏ s, ∏ c, u s c : ℤˣ) : ℤ) : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) *
        psi (zi X j v) (fi X j v) (product_zeroth_first_parts.Gxz (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) nu (fun s c => e s c)) := by
      rw [hP]
      unfold product_zeroth_first_parts.Gxz
      simp only [he, map_prod, Finset.prod_mul_distrib, Units.coe_prod, Int.cast_prod]
    have hkey : ∃ a : FormalGroupSystem.WW p, AddMonoidAlgebra.coeff (applyD (psi (zi X j v) (fi X j v)
        (product_zeroth_first_parts.Gxz (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) nu (fun s c => e s c))) f) n =
        (p : FormalGroupSystem.K0 p) ^ ⌈g⌉ * algebraMap (FormalGroupSystem.WW p) (FormalGroupSystem.K0 p) a := by
      apply mem_of_norm_le
      rw [← MvPolynomial.coeff_map, map_applyD_psi (zi X j v) (fi X j v) (zi_injective X j v) f _ hTh]
      by_cases hn : ∃ m, Finsupp.mapDomain (fi X j v) m = n
      · obtain ⟨m, rfl⟩ := hn
        rw [MvPolynomial.coeff_rename_mapDomain _ (fi_injective X j v)]
        exact hK (fun s c => e s c) m
      · rw [MvPolynomial.coeff_rename_eq_zero _ _ _ (fun w hw => absurd ⟨w, hw⟩ hn), norm_zero]
        positivity
    obtain ⟨a, ha⟩ := hkey
    rcases Int.units_eq_one_or (∏ s, ∏ c, u s c) with h1 | h1
    · refine ⟨a, ?_⟩
      rw [hG, h1]
      simpa using ha
    · refine ⟨-a, ?_⟩
      rw [hG, h1]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul, applyD_neg,
        MvPolynomial.coeff_neg, ha, map_neg, mul_neg]

end GlobalTheory.KvalAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockRowsOfFills
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockRowsOfFills
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory

theorem fock_rows_of_fills : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (Y : LatInst D), FillsAll hT Y → (Y.Fl u w hg).t = D.R.t → ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (i : ℕ), i < D.R.m → ∀ r : ℕ, ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) s (r + 1) : ℤ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) r else 0 := by
  intro D u w hg hT Y hF ht v s i hi r
  have hk : (D.gat u w hg).P.m + 1 = D.R.k := hT.gat_k u w hg
  have hw : ∀ b (hb : b < D.R.m), (((Y.Fl u w hg).w v (b + 1) s : ℤ) : ℝ) =
      ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℝ) - kaJ D (b + 1) := by
    intro b hb
    rw [hF u w hg v s (b + 1) (by simp [SizeData₂.lifts]; omega)]
    simp [wj, hb, D.hcW_e]
  have hwS : DV.wSz D (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) = ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨i, hi⟩ : ℝ) := by
    simp [DV.wSz, show 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m by omega, D.hcW_e]
  unfold FormalGroupSystem.nu FormalGroupSystem.NN
  rw [ht]
  by_cases h1 : r < D.R.k
  · rw [if_pos (by omega), if_pos (show r < D.R.N i by simp [Ranks.N]; omega)]
    unfold FormalGroupSystem.lamI
    rw [dite_eq_left (by omega)]
    unfold DV.nuRow DV.srcPar
    rw [dite_eq_left h1, hwS]
    have hl : (((D.gat u w hg).P.lam0 v s ⟨r + 1 - 1, by omega⟩ : ℤ) : ℚ) =
        (D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).u ⟨r, h1⟩ - ((D.R.k : ℚ) - 1) / 2 + r := by
      rw [hT.gat_lam, (D.fm u).lam_eq 0 (Nat.zero_le _)]
      simp [hcToWeightQ, rhoVec, Ranks.N, h1]
      ring
    have hlR := congrArg (Rat.cast : ℚ → ℝ) hl
    push_cast at hlR ⊢
    rw [hlR, hw i hi]
    simp only [kaJ, Ranks.N, Nat.add_sub_cancel]
    push_cast
    ring
  · rw [if_neg (by omega)]
    obtain ⟨q, rfl⟩ : ∃ q, r = D.R.k + q := ⟨r - D.R.k, by omega⟩
    have hrk : D.R.k + q + 1 - ((D.gat u w hg).P.m + 2) = q := by omega
    rw [hrk]
    have ht1 : 0 < D.R.t + 1 := Nat.succ_pos _
    have hM : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + (D.R.t + 1) := by ring
    have hNi : D.R.N i = D.R.k + i * (D.R.t + 1) := rfl
    by_cases h2 : q < i * (D.R.t + 1)
    · have hb : q / (D.R.t + 1) < i := by
        rw [Nat.div_lt_iff_lt_mul ht1]; exact h2
      rw [if_pos (by omega), if_pos (by omega)]
      unfold DV.nuRow DV.srcPar
      rw [dite_eq_right h1]
      simp only [Nat.add_sub_cancel_left]
      rw [dite_eq_left (by omega), hwS]
      have hr : q = q / (D.R.t + 1) * (D.R.t + 1) + q % (D.R.t + 1) := by
        have := Nat.div_add_mod q (D.R.t + 1); rw [mul_comm] at this; omega
      have hrR : (q : ℝ) = ((q / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1) + ((q % (D.R.t + 1) : ℕ) : ℝ) := by
        exact_mod_cast hr
      push_cast
      rw [hw _ (by omega), hw i hi]
      simp only [kaJ, Ranks.N]
      push_cast
      rw [hrR]
      ring
    · rw [if_neg (show ¬ D.R.k + q < D.R.N i by omega)]
      by_cases h3 : q < i * (D.R.t + 1) + (D.R.t + 1)
      · have hb : q / (D.R.t + 1) = i := by
          apply le_antisymm
          · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul ht1, Nat.succ_mul]; omega
          · rw [Nat.le_div_iff_mul_le ht1]; omega
        rw [if_pos (by omega), hb]
        simp
      · rw [if_neg (by omega)]
        simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockRowsOfFillsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_nu_cast_eq_ite_lt_N : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (Y : LatInst D), FillsAll hT Y → (Y.Fl u w hg).t = D.R.t → ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (i : ℕ), i < D.R.m → ∀ r : ℕ, ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) s (r + 1) : ℤ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) r else 0 := by
  first | exact @GlobalTheory.fock_rows_of_fills | exact GlobalTheory.fock_rows_of_fills | (intros; apply GlobalTheory.fock_rows_of_fills <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalModelBoundPlaceOverSecondEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU.LowF

theorem kval_orbit (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D)
    (hA : OrbitPlaces.OrbitLetterBoundsAll 11 1) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge 11 1 K ce)
    (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p) (h0 : IsResidueClassZero D p) (hne : hP D p ≠ 0)
    (hX : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (t : HH D)
    [NeZero (nP D p)] (B : OmBasis p (nP D p)) (be : MvPowerSeries (Fin 2) (K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx (nP D p) (D.R.N i) (D.R.N (i + 1)) ⊕ Eidx (nP D p) (D.R.N i) (D.R.N (i + 1))) (K0 p))
    (hU : IntS p (inParam p U)) :
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun s : ZMod (nP D p) => E.nu u i (OrbitPlaces.orbMap D p (true, t) s))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U)))
      (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  obtain ⟨bv, h1, h2, h3, h4, hb⟩ := GlobalTheory.T.exists_letterCoordinates_series_onePlace_alt p h.five (nP D p) h.even B be hbe
  obtain ⟨U', hU', e⟩ := hb _ _ U hU
  exact GlobalTheory.T.orbitBound_overSecondEmbedding_anyBasePoint D L X K ce E 11 1 hA hS hC p h h0 hne hX u i hi t 1 (-1) bv (by simp) (Or.inr rfl) h1 h2 h3 h4 _
    ⟨U', hU', e⟩

theorem kval_general (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D)
    (hA : OrbitPlaces.OrbitLetterBoundsAll 11 1) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge 11 1 K ce)
    (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p) (h0 : IsResidueClassZero D p) (hne : hP D p ≠ 0)
    (hX : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (t : HH D)
    (n r0 r1 : ℕ) [NeZero n] (hn : n = nP D p) (h0' : r0 = D.R.N i) (h1' : r1 = D.R.N (i + 1))
    (B : OmBasis p n) (be : MvPowerSeries (Fin 2) (K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx n r0 r1 ⊕ Eidx n r0 r1) (K0 p)) (hU : IntS p (inParam p U)) :
    product_zeroth_first_parts.KvalGe r0 r1 p (fun s : ZMod n => E.nu u i (posPl D p (true, t) s.val))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U)))
      (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  subst hn h0' h1'
  exact kval_orbit D L X K ce E hA hS hC p h h0 hne hX u i hi t B be hbe U hU

theorem lowBound_of_series_bound_one_place {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl)
    [NeZero (X.G.P.n' v)] (nu : ZMod (X.G.P.n' v) → YoungDiagram) (g : ℝ)
    (hcc : MvPowerSeries.constantCoeff be = 0)
    (hnu : ∀ s r, (((nu s).rowLen r : ℕ) : ℤ) = X.nuv v (j + 1) (toFin s) (r + 1))
    (hK : ∀ U : MvPowerSeries (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) ⊕
        Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (K0 p), IntS p (inParam p U) →
      product_zeroth_first_parts.KvalGe (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) p nu
        (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne (X.om v) be U))) g) :
    IsPlaceCofactorValuationLowerBound X be j v g := by
  intro U hU I n
  obtain ⟨hU1, e⟩ := restr_onePlace p X be j v U hcc hU
  refine GlobalTheory.KvalAgree.coeff_applyD_PIv_of_KvalGe p X j v nu hnu _ g ?_ I n
  rw [e]
  exact hK _ hU1

theorem lowAt_F : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D), LatTied hT X Y → FillsAll hT Y → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n → ∀ (Lv : Levels (Y.Fl u w hg)) (Ch : Chain Lv) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om)), BeProp (D.what₂.places.resChar w) Y5.be → ∀ (v : Fin (D.gat u w hg).P.nV) (t : HH D), (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) → (∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, t) s.val)) → ∀ i < D.R.m, Y5.LowAt i v (FOrb D (i + 1) (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce (i + 1) (D.what₂.places.resChar w) (true, t)) := by
  intro D u w hg L hT X Y K ce E hTied hFill hA hS hC hX Lv Ch std vp unif eO eO_spec dG dG_spec om Y5 hBe v t hn hpos i hi
  have h0 : IsResidueClassZero D (D.what₂.places.resChar w) := hg.2.2.1
  have hne := (GlobalTheory.T.servedPrime_properties D _ hg.1 h0 hg.2.2.2.1).1
  have hstd := std v
  have hOK : OrbitPlaces.OrbOK D (D.what₂.places.resChar w) := ⟨hg.2.1, hn ▸ hstd.even, hn ▸ hstd.two_le⟩
  have hcc : MvPowerSeries.constantCoeff Y5.be = 0 := by
    by_contra hc
    have := (hBe.ab 0 (by simpa using hc)).1
    simp at this
  haveI : NeZero ((D.gat u w hg).P.n' v) := ⟨by have := hstd.two_le; omega⟩
  have ht : (Y.Fl u w hg).t = D.R.t := (hTied u w hg).2.1
  have hk := hT.gat_k u w hg
  have hN : ∀ j, NN (D.gat u w hg).P.m (Y.Fl u w hg).t j = D.R.N j := fun j => by
    simp only [NN, Ranks.N, ht]
    omega
  refine GlobalTheory.T.lowAt_of_placeCofactorValuationLowerBound _ _ Y5 i v _ hcc ?_
  refine lowBound_of_series_bound_one_place (Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om) Y5.be i v (fun s => E.nu u i (posPl D (D.what₂.places.resChar w) (true, t) s.val)) _ hcc ?_ ?_
  · intro s r
    have h1 := GlobalTheory.T.formalGroup_nu_cast_eq_ite_lt_N D u w hg hT Y hFill ht v (toFin s) i hi r
    have h2 := E.nu_row u i hi (posPl D (D.what₂.places.resChar w) (true, t) s.val) r
    have h3 := hpos (toFin s)
    rw [h3] at h1
    have h4 : (((E.nu u i (posPl D (D.what₂.places.resChar w) (true, t) s.val)).rowLen r : ℕ) : ℝ) =
        ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) (toFin s) (r + 1) : ℤ) : ℝ) := by
      rw [h2, h1]; rfl
    exact_mod_cast h4
  · intro U' hU1
    exact kval_general D L X K ce E hA hS hC _ hOK h0 hne hX u i hi t _ _ _ hn
      (hN i) (hN (i + 1)) _ _ hBe _ hU1

end GlobalTheory.TwU.LowF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalModelBoundPlaceOverSecondEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_model_bound_place_over_second_embedding : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D), LatTied hT X Y → FillsAll hT Y → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n → ∀ (Lv : Levels (Y.Fl u w hg)) (Ch : Chain Lv) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om)), BeProp (D.what₂.places.resChar w) Y5.be → ∀ (v : Fin (D.gat u w hg).P.nV) (t : HH D), (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) → (∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, t) s.val)) → ∀ i < D.R.m, Y5.LowAt i v (FOrb D (i + 1) (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce (i + 1) (D.what₂.places.resChar w) (true, t)) := by
  first | exact @GlobalTheory.TwU.LowF.lowAt_F | exact GlobalTheory.TwU.LowF.lowAt_F | (intros; apply GlobalTheory.TwU.LowF.lowAt_F <;> assumption)
end
