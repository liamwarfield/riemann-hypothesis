module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfSteps
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

section NabAux

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}


open Classical in
def colCoef {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) (ℓ : LtN Dw n) : k :=
  ∑ j : Fin n, if ℓ = ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ then B lam.1.1.1 lam.1.2 j else 0

theorem sum_colCoef_smul {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ)
    (lam : Let cx) {M : Type} [AddCommGroup M] [Module k M] (x : LtN Dw n → M) :
    ∑ ℓ, colCoef B cx lam ℓ • x ℓ =
      ∑ j : Fin n, B lam.1.1.1 lam.1.2 j • x ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ := by
  classical
  simp only [colCoef, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2, j⟩ : LtN Dw n)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem polyP_eq_aeval {k : Type} [Field k] {n : ℕ} (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    polyP B cx = MvPolynomial.aeval (fun lam : Let cx => ∑ ℓ, MvPolynomial.C (colCoef B cx lam ℓ) *
      (MvPolynomial.X ℓ : MvPolynomial (LtN Dw n) k)) (polyH k cx) := by
  classical
  unfold polyP polyH
  rw [map_prod, ← Finset.prod_filter_of_ne (p := fun f => cx f ≠ 0)
    (fun f _ hf h0 => hf (by rw [h0, pow_zero])),
    Finset.prod_subtype (p := fun f => cx f ≠ 0) (F := inferInstance) _ (by simp)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_rename, detPow, map_pow, AlgHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext1 a b
  simp only [GlobalTheory.CombMinor.cMat, Matrix.transpose_apply, Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply,
    MvPolynomial.aeval_X, Function.comp_apply, MvPolynomial.C_mul']
  rw [sum_colCoef_smul]

theorem map_polyP {k k' : Type} [Field k] [Field k'] (φ : k →+* k') {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) :
    MvPolynomial.map φ (polyP B cx) = polyP (fun f b j => φ (B f b j)) cx := by
  unfold polyP
  rw [map_prod]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext1 a b
  simp [GlobalTheory.CombMinor.cMat]

theorem subst_colCoef_expPt {k : Type} [Field k] {v : AddValuation k (WithTop ℝ)} {d n : ℕ} (G : LogFGL v d)
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → k) (cx : Lt1 Dw → ℕ) (u : Lt1 Dw → Fin d → k) (Φ : PS k n d) :
    subst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ • (X lam : MvPowerSeries (Let cx) k))
      (subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
        (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) Φ) =
    subst (fun q : Fin n × Fin d => expPt G (fun e => ∑ lam : Let cx,
      (B lam.1.1.1 lam.1.2 q.1 * u ⟨lam.1.1.1.1, Fin.castLE (rk_le _) lam.2⟩ e) •
        (X lam : MvPowerSeries (Let cx) k)) q.2) Φ := by
  have ht : HasSubst (fun ℓ : LtN Dw n => ∑ lam : Let cx, colCoef B cx lam ℓ •
      (X lam : MvPowerSeries (Let cx) k)) := hasSubst_of_constantCoeff_zero (by simp)
  have hw : ∀ (j : Fin n) (e : Fin d), constantCoeff (∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = j then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) = 0 := by
    intro j e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun ℓ _ => by rw [constantCoeff_smul, constantCoeff_X, smul_zero]
  have hs : HasSubst (fun q : Fin n × Fin d => expPt G (fun e => ∑ ℓ : LtN Dw n,
      (if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0) • (X ℓ : MvPowerSeries (LtN Dw n) k)) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  refine (subst_comp_subst_apply hs ht Φ).trans (congrArg (fun s => subst s Φ) (funext fun q => ?_))
  refine (subst_expPt G ht (hw q.1) q.2).trans (congrArg (fun s => expPt G s q.2) (funext fun e => ?_))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← coe_substAlgHom ht, map_sum, map_smul]
  simp only [coe_substAlgHom, subst_X ht, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := sum_colCoef_smul B cx lam
    (fun ℓ : LtN Dw n => if ℓ.2.2 = q.1 then u ⟨ℓ.1, ℓ.2.1⟩ e else 0)
  simp only [smul_eq_mul] at h
  rw [Finset.sum_congr rfl fun ℓ _ => mul_comm _ _, h]
  simp

end NabAux

theorem nabSt_of : InvDerSt → LinSt → FrameSt → NabSt := by
  intro hI hL hF E _ _ _ H Dw l Xo c _ T io y Ch p _ X cx n B k g
  let _ := io.toAlgebra
  let _ : Algebra T.Fr X.C := X.ιF.toAlgebra
  have hfr := (hF X.C (vX_vp X) (chD Ch.ch) T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (gauge_chart Ch X) H.w0 n).2.1 k
  have hinv := hI X.C (vX_vp X) (chD Ch.ch) (lawX Ch X) (fgl Ch X).F_int n (LtN Dw n) (fun ℓ => ℓ.2.2)
    (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx)) (g * frameX Ch X n ^ k)
  have hP : MvPolynomial.map X.ιF (polyT B cx) = polyP (fun f b j => jX X (B f b j)) cx := map_polyP _ _ _
  unfold nabX nabValN
  rw [hfr]
  refine Eq.trans hinv ?_
  rw [hP, polyP_eq_aeval, hL]
  exact congrArg (derivAt0 (polyH X.C cx))
    (subst_colCoef_expPt (fgl Ch X) (fun f b j => jX X (B f b j)) cx (lieVec Ch X) (g * frameX Ch X n ^ k))

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaOperatorFrameSeriesOfStepsStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaOperatorFrameSeries_of_steps : InvDerSt → LinSt → FrameSt → NabSt := by
  first | exact @GlobalTheory.IsoTriv.nabSt_of | exact GlobalTheory.IsoTriv.nabSt_of | (intros; apply GlobalTheory.IsoTriv.nabSt_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingReducedResidueFieldBijectiveUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingReducedResidueFieldBijectiveUnramified
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg

theorem exists_inv_of_not_dvd_discr (E : Type) [Field E] [NumberField E] {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] {Fr : Type} [Field Fr] [Algebra V Fr]
    [DecidableEq (E →+* ℂ)] (hinj : Function.Injective (algebraMap V Fr)) {F : Type} [Field F] (j : F →+* ℂ)
    (io : F →+* Fr)
    (φ : (E →+* ℂ) → (E →+* F)) (hφ : ∀ σ x, j (φ σ x) = σ x)
    (χ : (E →+* ℂ) → (𝓞 E →+* V)) (hχ : ∀ σ (a : 𝓞 E), algebraMap V Fr (χ σ a) = io (φ σ (a : E)))
    (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V)) (hd : ¬ (g : ℤ) ∣ discr E) :
    ∃ Cm : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → V,
      (∀ σ τ, ∑ i, χ σ (RingOfIntegers.basis E i) * Cm i τ = if σ = τ then 1 else 0) ∧
      (∀ i i', ∑ τ, Cm i τ * χ τ (RingOfIntegers.basis E i') = if i = i' then 1 else 0) := by
  classical
  let bs := RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let e' : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →+* ℂ) := e.trans (RingHom.equivRatAlgHom E ℂ).symm
  let A : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) V :=
    fun i k => χ (e' k) (bs i)
  have hAij : ∀ i k, A i k = χ (e' k) (bs i) := fun _ _ => rfl
  let AF : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) F :=
    fun i k => φ (e' k) (bs i : E)
  have hAF : AF.map j = Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => (bs i : E)) e := by
    ext i k
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply,
      Equiv.symm_symm]
    show j (φ (e' k) (bs i : E)) = (e k) (bs i : E)
    rw [hφ]
    rfl
  have hdF : AF.det ^ 2 = ((discr E : ℤ) : F) := by
    apply j.injective
    rw [map_pow, RingHom.map_det, RingHom.mapMatrix_apply, hAF,
      ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, map_intCast]
    have hb : (fun i => (bs i : E)) = ⇑(integralBasis E) := funext fun i => (integralBasis_apply E i).symm
    rw [hb, ← coe_discr, map_intCast]
  have hdV : A.det ^ 2 = ((discr E : ℤ) : V) := by
    apply hinj
    rw [map_pow, RingHom.map_det, map_intCast]
    have hA : (algebraMap V Fr).mapMatrix A = io.mapMatrix AF := by
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hAij, AF, hχ]
      rfl
    rw [hA, ← RingHom.map_det, ← map_pow, hdF, map_intCast]
  have hu : IsUnit A.det := by
    have h := isUnit_of_not_dvd g hg hgV _ hd
    rw [← hdV] at h
    exact (isUnit_pow_iff two_ne_zero).1 h
  refine ⟨fun i τ => A⁻¹ (e'.symm τ) i, ?_, ?_⟩
  · intro σ τ
    have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul A hu) (e'.symm τ)) (e'.symm σ)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij, Equiv.apply_symm_apply] at h1
    rw [show (∑ i, χ σ (bs i) * A⁻¹ (e'.symm τ) i) = ∑ i, A⁻¹ (e'.symm τ) i * χ σ (bs i) from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : σ = τ
    · subst h; simp
    · rw [if_neg (fun h' => h (e'.symm.injective h').symm), if_neg h]
  · intro i i'
    have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i') i
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij] at h1
    rw [← Equiv.sum_comp e' (fun τ => A⁻¹ (e'.symm τ) i * χ τ (bs i'))]
    simp only [Equiv.symm_apply_apply]
    rw [show (∑ k, A⁻¹ k i * χ (e' k) (bs i')) = ∑ k, χ (e' k) (bs i') * A⁻¹ k i from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : i = i'
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]

theorem red_bijective (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p)
    (hp : UnramIn E p) : Function.Bijective (red io X) := by
  classical
  haveI : IsDomain X.O := X.ints.hom_inj.isDomain _
  obtain ⟨Cm, hAC, hCA⟩ := exists_inv_of_not_dvd_discr E (V := X.O) (Fr := X.C) X.ints.hom_inj
    (c.F.val : c.F →+* ℂ) (X.ιF.comp io) (embF c) (fun σ x => by simp [embF])
    (embO io X) (fun σ a => algebraMap_embO io X σ a) p Fact.out X.nonunit.out hp
  set b := RingOfIntegers.basis E
  let Cr : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → ResidueField X.O := fun i τ => residue X.O (Cm i τ)
  have hAC' : ∀ σ τ, ∑ i, red io X σ (b i) * Cr i τ = if σ = τ then 1 else 0 := by
    intro σ τ
    have := congrArg (residue X.O) (hAC σ τ)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  have hCA' : ∀ i i', ∑ τ, Cr i τ * red io X τ (b i') = if i = i' then 1 else 0 := by
    intro i i'
    have := congrArg (residue X.O) (hCA i i')
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  refine ⟨fun σ τ hst => ?_, fun χ => ?_⟩
  · by_contra hne
    have h1 := hAC' σ τ
    rw [if_neg hne, hst, hAC' τ τ, if_pos rfl] at h1
    exact one_ne_zero h1
  · let ρ : 𝓞 E →+* Module.End (ResidueField X.O) (ResidueField X.O) :=
      (Algebra.lmul (ResidueField X.O) (ResidueField X.O)).toRingHom.comp χ
    obtain ⟨mσ, hm, hs⟩ := ((decomp_of_inv ρ (red io X) b Cr hAC' hCA').1 1)
    obtain ⟨σ, hσ⟩ : ∃ σ, mσ σ ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      simp [h] at hs
    refine ⟨σ, RingHom.ext fun a => ?_⟩
    have : χ a * mσ σ = red io X σ a * mσ σ := hm σ a
    exact (mul_right_cancel₀ hσ this).symm

end GlobalTheory.PrimePart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingReducedResidueFieldBijectiveUnramifiedStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingReducedResidueField_bijective_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), UnramIn E p → Function.Bijective (red io X) := by
  first | exact @GlobalTheory.PrimePart.red_bijective | exact GlobalTheory.PrimePart.red_bijective | (intros; apply GlobalTheory.PrimePart.red_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRetractionOfLimitSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRetractionOfLimitSteps
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open NumberField IsDedekindDomain MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem mv_sum_smul_X {C : Type} [Field C] {d : ℕ} {σ : Type} [Fintype σ] (A : Matrix (Fin d) (Fin d) C)
    (s : σ → C) (g : σ → Fin d → C) (e : Fin d) :
    mv A (fun e' => ∑ ℓ, (s ℓ * g ℓ e') • (MvPowerSeries.X ℓ : MvPowerSeries σ C)) e =
      ∑ ℓ, (s ℓ * A.mulVec (g ℓ) e) • (MvPowerSeries.X ℓ : MvPowerSeries σ C) := by
  simp only [mv, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun e' _ => ?_
  rw [mul_left_comm]

theorem subst_expPt_sum_mv {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d n : ℕ} {σ κ : Type} [Fintype κ]
    (G : LogFGL v d) (w : Fin n → Fin d → MvPowerSeries σ C) (hw : ∀ j e, constantCoeff (w j e) = 0)
    (r : κ → Fin n) (A : κ → Matrix (Fin d) (Fin d) C) (i : Fin d) :
    subst (fun q : Fin n × Fin d => expPt G (w q.1) q.2)
        (expPt G (∑ b, mv (A b) (lgPt G fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C))) i) =
      expPt G (fun e => ∑ b, mv (A b) (w (r b)) e) i := by
  have ht : HasSubst (fun q : Fin n × Fin d => expPt G (w q.1) q.2) :=
    hasSubst_of_constantCoeff_zero fun q => cc_expPt G (hw q.1) q.2
  have hl : ∀ b e, constantCoeff
      (lgPt G (fun e => (MvPowerSeries.X (r b, e) : MvPowerSeries (Fin n × Fin d) C)) e) = 0 :=
    fun b => cc_lgPt G (by simp)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [subst_expPt G ht (fun e => by
    rw [Finset.sum_apply, map_sum]; exact Finset.sum_eq_zero fun b _ => cc_mv _ (hl b) e)]
  congr 1
  funext e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, ← coe_substAlgHom ht, map_sum, coe_substAlgHom]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [subst_mv ht]
  congr 1
  funext e'
  rw [subst_lgPt G ht (by simp)]
  simp only [subst_X ht]
  exact congrFun (lgPt_expPt G (hw (r b))) e'

theorem retrSt_of : LimActSt → LimPtSt → InvSt → RetrSt := by
  intro hAct hPt hInv E _ _ _ H Dw l Xo c _ hstar T io y Ch p _ X cx n B hB
  classical
  obtain ⟨blk, hblk⟩ := hB
  have key : ∀ f : {f : Lt1 Dw // cx f ≠ 0}, ∃ ρf : Fin (rk f.1) → Fin (chD Ch.ch) → PS X.C n (chD Ch.ch),
      (∀ β i, constantCoeff (ρf β i) = 0) ∧ (∀ β i, MvIsInt (vX_vp X) (ρf β i)) ∧
      ∀ β i, subst (colPt Ch X cx B) (ρf β i) = expH Ch X cx ⟨⟨f, β⟩, i⟩ := by
    intro f
    obtain ⟨hS, ⟨r, hr⟩, hx⟩ := hblk f
    obtain ⟨φ, hφ⟩ := GlobalTheory.IsoCols.exists_lift T (io.comp (embK c f.1.1))
    have inj := IsFractionRing.injective T.V T.Fr
    have hp0 : (p : T.V) ≠ 0 := fun h => by
      have h1 := congrArg (jX X) h
      rw [map_natCast, map_zero] at h1
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h1)
    have hM : ∀ b b' (N : ℕ), ∃ a z,
        φ a = (Matrix.of fun b b' => B f.1 b (r b')) b b' + φ (p : 𝓞 E) ^ N * z := fun b b' N => by
      obtain ⟨x, -, hx2, -⟩ := hx N
      obtain ⟨z, hz⟩ := hx2 b (r b')
      exact ⟨x b (r b'), z, inj (by rw [hφ, map_natCast φ]; exact hz)⟩
    obtain ⟨M', hMM', hM'⟩ := hInv (𝓞 E) T.V φ (p : 𝓞 E) (by rw [map_natCast]; exact hp0)
      (by rw [map_natCast]; exact not_isUnit_p X) (rk f.1) _ hr hM
    obtain ⟨ε, hε⟩ := hAct E H Dw l Xo c hstar T io y Ch p X f.1.1
    choose x z hxz using hM'
    choose A hA1 hA2 using fun β' β => hε (M' β' β) (x β' β) fun N =>
      ⟨z β' β N, by rw [← map_natCast φ p, ← hxz, hφ]; rfl⟩
    have hint : ∀ β, IntLog (fgl Ch X) (∑ β', mv (A β' β)
        (lgPt (fgl Ch X) fun e => (MvPowerSeries.X (r β', e) : PS X.C n (chD Ch.ch)))) := fun β => by
      letI := io.toAlgebra
      letI : Algebra T.Fr X.C := X.ιF.toAlgebra
      exact hPt X.C (vX_vp X) _ T.Fr (𝓞 E) Ch.ch.B (isIntFB_chart Ch X) _ (Fin (rk f.1)) _
        (fun β' => intLog_lgPt_X (fgl Ch X) fun e => (r β', e)) (fun β' => A β' β)
        (fun N β' => ε N * x β' β N) fun N β' => hA1 β' β N
    have hz : ∀ f' : {f : Lt1 Dw // cx f ≠ 0}, f' ≠ f → ∀ b β', B f'.1 b (r β') = 0 := fun f' hf b β' => by
      refine (hblk f').1 b _ fun ⟨j', hj'⟩ => ?_
      by_cases hm : r β' ∈ Set.range fun j => blk ⟨f, j⟩
      · obtain ⟨j, hj⟩ := hm
        exact hf (congrArg Sigma.fst (blk.injective (hj'.trans hj.symm)))
      · rw [Matrix.det_eq_zero_of_column_eq_zero β' fun b => hS b _ hm] at hr
        exact not_isUnit_zero hr
    refine ⟨fun β => expPt (fgl Ch X) _, fun β => cc_expPt _ (hint β).1, fun β => (hint β).2, fun β i => ?_⟩
    refine (subst_expPt_sum_mv (fgl Ch X) (fun j e => ∑ ℓ : Let cx,
      (jX X (B ℓ.1.1.1 ℓ.1.2 j) * frame Ch X ℓ.1.1.1 ℓ.2 e) • (MvPowerSeries.X ℓ : MvPowerSeries (Let cx) X.C))
      (fun j e => by simp) r (fun β' => A β' β) i).trans ?_
    show expPt _ _ i = expPt (fgl Ch X) (fun e => ∑ a, frame Ch X f.1 a e •
      (MvPowerSeries.X ⟨⟨f, β⟩, a⟩ : MvPowerSeries (Let cx) X.C)) i
    congr 1
    funext e
    simp_rw [mv_sum_smul_X]
    have hc : ∀ (b : Fin (rk f.1)) (a : Fin (rk f.1)),
        ∑ β', jX X (B f.1 b (r β')) * (A β' β).mulVec (frame Ch X f.1 a) e =
          if b = β then frame Ch X f.1 a e else 0 := fun b a => by
      have h1 := congrArg (jX X) (congrFun (congrFun hMM' b) β)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum, Matrix.one_apply] at h1
      simp only [frame, hA2, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← Finset.sum_mul, ← map_mul]
      rw [show ∑ β', jX X (B f.1 b (r β') * M' β' β) = _ from h1]
      split_ifs <;> simp
    rw [Finset.sum_comm, Fintype.sum_sigma, Finset.sum_eq_single (⟨f, β⟩ : Col cx)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_smul, hc, if_pos rfl]
    · rintro ⟨f', b⟩ - hne
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← Finset.sum_smul]
      by_cases hf : f' = f
      · subst hf
        rw [hc, if_neg fun h => hne (by rw [show b = β from h]), zero_smul]
      · simp [hz f' hf]
    · exact fun h => absurd (Finset.mem_univ _) h
  choose ρf h1 h2 h3 using key
  exact ⟨fun q => ρf q.1.1 q.1.2 q.2, fun q => h1 _ _ _, fun q => h2 _ _ _, fun q => h3 _ _ _⟩

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRetractionOfLimitStepsStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnInclusionRetraction_of_limitSteps : LimActSt → LimPtSt → InvSt → RetrSt := by
  first | exact @GlobalTheory.IsoTriv.retrSt_of | exact GlobalTheory.IsoTriv.retrSt_of | (intros; apply GlobalTheory.IsoTriv.retrSt_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProof
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LinChange

open MvPowerSeries GlobalTheory.FGDepth

section Rules

variable {K : Type} [Field K] {σ : Type}

private theorem mfact_eq_prod_factorial [Fintype σ] (α : σ →₀ ℕ) :
    (mfact α : K) = ∏ x, ((α x).factorial : K) := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

theorem mfact_add_single [Fintype σ] [DecidableEq σ] (α : σ →₀ ℕ) (l : σ) :
    (mfact (α + Finsupp.single l 1) : K) = mfact α * ((α l : K) + 1) := by
  rw [mfact_eq_prod_factorial, mfact_eq_prod_factorial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
  have hrest : ∏ x ∈ Finset.univ.erase l, (((α + Finsupp.single l 1 : σ →₀ ℕ) x).factorial : K) =
      ∏ x ∈ Finset.univ.erase l, ((α x).factorial : K) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)), add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

theorem derivAt0_add' (P Q : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (P + Q) g = derivAt0 P g + derivAt0 Q g := by
  classical
  rw [derivAt0_eq_sum_of_subset (P + Q) g MvPolynomial.support_add,
    derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)),
    derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem derivAt0_smulP (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (b • P) g = b * derivAt0 P g := by
  classical
  rw [derivAt0_eq_sum_of_subset (b • P) g MvPolynomial.support_smul, derivAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem derivAt0_smulG (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 P (b • g) = b * derivAt0 P g := by
  unfold derivAt0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPowerSeries.coeff_smul]
  ring

theorem derivAt0_sumG {κ : Type} (s : Finset κ) (P : MvPolynomial σ K) (f : κ → MvPowerSeries σ K) :
    derivAt0 P (∑ i ∈ s, f i) = ∑ i ∈ s, derivAt0 P (f i) := by
  unfold derivAt0
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem derivAt0_C' (a : K) (g : MvPowerSeries σ K) :
    derivAt0 (MvPolynomial.C a) g = a * constantCoeff g := by
  rw [MvPolynomial.C_apply, DepthAdd.derivAt0_monomial, DepthAdd.mfact_zero',
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, mul_one]

theorem derivAt0_mul_X [Fintype σ] (P : MvPolynomial σ K) (l : σ) (g : MvPowerSeries σ K) :
    derivAt0 (P * MvPolynomial.X l) g = derivAt0 P (pderiv l g) := by
  classical
  have hP : P * MvPolynomial.X l =
      ∑ α ∈ P.support, MvPolynomial.monomial (α + Finsupp.single l 1) (P.coeff α) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [show (MvPolynomial.X l : MvPolynomial σ K) = MvPolynomial.monomial (Finsupp.single l 1) 1 from rfl,
      MvPolynomial.monomial_mul, mul_one]
  rw [hP, DepthAdd.derivAt0_sum]
  conv_rhs => unfold derivAt0
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [DepthAdd.derivAt0_monomial, MvPowerSeries.coeff_pderiv, mfact_add_single]
  ring

private theorem constantCoeff_subst_of_constantCoeff_zero' {K ι Λ : Type} [Field K] [Finite ι] (A : ι → MvPowerSeries Λ K)
    (hA : ∀ l, constantCoeff (A l) = 0) (Ψ : MvPowerSeries ι K) :
    constantCoeff (subst A Ψ) = constantCoeff Ψ := by
  have hs : HasSubst A := hasSubst_of_constantCoeff_zero hA
  have h := constantCoeff_subst_eq_zero hs hA (f := Ψ - C (constantCoeff Ψ)) (by simp)
  rw [subst_sub hs, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

private theorem pderiv_sum_smul_X_eq_C {K ι Λ : Type} [Field K] [Fintype Λ] [DecidableEq Λ] (β : Λ → ι → K)
    (lam : Λ) (l : ι) :
    pderiv lam (∑ lam', β lam' l • (X lam' : MvPowerSeries Λ K)) = C (β lam l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single lam]
  · rw [Derivation.map_smul, pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
  · intro b _ hb
    rw [Derivation.map_smul, pderiv_X_of_ne hb, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ lam) h

end Rules

end GlobalTheory.IsoTriv.LinChange

namespace GlobalTheory.IsoTriv

open MvPowerSeries GlobalTheory.FGDepth GlobalTheory.IsoTriv.LinChange

theorem linSt_holds : LinSt := by
  unfold LinSt
  intro K _ _ ι Λ _ _ β P
  classical
  have hA0 : ∀ l : ι, constantCoeff (∑ lam, β lam l • (X lam : MvPowerSeries Λ K)) = 0 := by
    intro l
    simp [MvPowerSeries.smul_eq_C_mul]
  induction P using MvPolynomial.induction_on
  · rename_i a
    intro Ψ
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, derivAt0_C', derivAt0_C',
      constantCoeff_subst_of_constantCoeff_zero' _ hA0]
  · rename_i p q hp hq
    intro Ψ
    rw [map_add (f := _), derivAt0_add', derivAt0_add', hp, hq]
  · rename_i p lam hp
    intro Ψ
    have hterm : ∀ l : ι, MvPolynomial.aeval
        (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
          (MvPolynomial.C (β lam l) * MvPolynomial.X l) =
        β lam l • (MvPolynomial.aeval
          (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
            MvPolynomial.X l) := by
      intro l
      rw [MvPolynomial.smul_eq_C_mul]
      ring
    rw [map_mul]
    simp only [MvPolynomial.aeval_X]
    rw [Finset.mul_sum]
    simp_rw [hterm]
    rw [DepthAdd.derivAt0_sum, derivAt0_mul_X,
      ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hA0, derivAt0_sumG]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [derivAt0_smulP, derivAt0_mul_X, hp, pderiv_sum_smul_X_eq_C, mul_comm _ (C (β lam l)), ← MvPowerSeries.smul_eq_C_mul,
      derivAt0_smulG]

end GlobalTheory.IsoTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProofStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof : LinSt := by
  first | exact @GlobalTheory.IsoTriv.linSt_holds | exact GlobalTheory.IsoTriv.linSt_holds | (intros; apply GlobalTheory.IsoTriv.linSt_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonGaugeBiadditiveOfLogSumActionLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonGaugeBiadditiveOfLogSumActionLinear
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.GaugeBiadd

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.LawLog
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section

variable {C : Type} [Field C] {d : ℕ} {σ : Type}

def famPt {n : ℕ} (x : Fin n → Fin d → MvPowerSeries σ C) : Fin n × Fin d → MvPowerSeries σ C :=
  fun q => x q.1 q.2

theorem hs_famPt {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0) :
    HasSubst (famPt x) :=
  hasSubst_of_constantCoeff_zero fun q => hx q.1 q.2

theorem constantCoeff_vecCons_pair_eq_zero {τ : Type} {x y : Fin d → MvPowerSeries τ C} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (j : Fin 2) (i : Fin d) :
    constantCoeff ((![x, y] : Fin 2 → Fin d → MvPowerSeries τ C) j i) = 0 := by
  fin_cases j
  exacts [hx i, hy i]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt C d j i) = 0 := by simp [pt]

theorem constantCoeff_germEvalPair_eq_zero {n : ℕ} {x y : Pt C n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) {f : PS C 2 d} (hf : constantCoeff f = 0) :
    constantCoeff (ev ![x, y] f) = 0 :=
  constantCoeff_subst_eq_zero (hs_famPt (constantCoeff_vecCons_pair_eq_zero hx hy)) (fun q => constantCoeff_vecCons_pair_eq_zero hx hy q.1 q.2) hf

theorem cc_comp1 {n : ℕ} {x : Pt C n d} (hx : ∀ i, constantCoeff (x i) = 0)
    {φ : Pt C 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin d) :
    constantCoeff (comp1 φ x i) = 0 := by
  have h : ∀ (j : Fin 1) i, constantCoeff ((![x] : Fin 1 → Pt C n d) j i) = 0 := fun j i => by
    fin_cases j; exact hx i
  exact constantCoeff_subst_eq_zero (hs_famPt h) (fun q => h q.1 q.2) (hφ i)

theorem subst_famPt_pt {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    (j : Fin n) : (fun i => (subst (famPt x) (pt C d j i) : MvPowerSeries σ C)) = x j :=
  funext fun i => subst_X (hs_famPt hx) _

theorem subst_pointFamily_germEvalPair {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    {a b : Pt C n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (f : PS C 2 d) :
    (subst (famPt x) (ev ![a, b] f) : MvPowerSeries σ C) =
      subst (famPt ![fun i => (subst (famPt x) (a i) : MvPowerSeries σ C), fun i => subst (famPt x) (b i)]) f := by
  refine (subst_comp_subst_apply (hs_famPt (constantCoeff_vecCons_pair_eq_zero ha hb)) (hs_famPt hx) f).trans ?_
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> rfl

theorem subst_famPt_comp1 {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    (φ : Pt C 1 d) (j : Fin n) :
    (fun i => (subst (famPt x) (comp1 φ (pt C d j) i) : MvPowerSeries σ C)) =
      fun i => subst (fun q : Fin 1 × Fin d => x j q.2) (φ i) := by
  have h : ∀ (l : Fin 1) i, constantCoeff ((![pt C d j] : Fin 1 → Pt C n d) l i) = 0 := fun l i => by
    fin_cases l; exact cc_pt j i
  funext i
  refine (subst_comp_subst_apply (hs_famPt h) (hs_famPt hx) (φ i)).trans ?_
  congr 1
  funext ⟨l, e⟩
  fin_cases l
  exact subst_X (hs_famPt hx) _

theorem subst_elim_twoVars {x y : Fin d → MvPowerSeries σ C} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (f : PS C 2 d) :
    (subst (Sum.elim x y) (subst (twoVars C d) f) : MvPowerSeries σ C) = subst (famPt ![x, y]) f := by
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero (by rintro (i | i); exacts [hx i, hy i])
  rw [subst_comp_subst_apply hs_twoVars hs]
  congr 1
  funext ⟨j, i⟩
  rw [twoVars, subst_X hs]
  fin_cases j <;> simp [famPt]

theorem logUnit_subst [CharZero C] {v : AddValuation C (WithTop ℝ)} {n : ℕ}
    {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0) (hI : ∀ j i, MvIsInt v (x j i))
    {U f : PS C n d} (hU : MvIsInt v U) (hf : constantCoeff f = 0) (e : U = FB.expS C f) :
    LogUnit v (subst (famPt x) f : MvPowerSeries σ C) := by
  refine ⟨constantCoeff_subst_eq_zero (hs_famPt hx) (fun q => hx q.1 q.2) hf, ?_⟩
  have h := ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v hU (a := famPt x) (fun q => hI q.1 q.2) (fun q => hx q.1 q.2)
  rw [e] at h
  unfold FB.expS PowerSeries.subst at h
  rw [subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const (hs_famPt hx)] at h
  exact h

end

theorem biadd_of_add_of_act : AddSt → ActSt → BiaddSt := by
  intro hAdd hAct C _ _ v d R _ _ O _ _ B hB h H σ _ w w' z hw hw' hz
  have hc : constantCoeff h = 0 := GlobalTheory.GaugeBaseChange.const_of_axis H.ax0
  have hF : ∀ i, constantCoeff (B.FK C i) = 0 := GlobalTheory.GaugeBaseChange.gp_FK B
  have hA : ∀ a i, constantCoeff (B.actK C a i) = 0 := fun a => GlobalTheory.GaugeBaseChange.gp_actK B a
  have cw := cc_expPt (fglOf hB) hw.1
  have cw' := cc_expPt (fglOf hB) hw'.1
  have cz := cc_expPt (fglOf hB) hz.1
  have hadd : expPt (fglOf hB) (w + w') =
      fun i => subst (famPt ![expPt (fglOf hB) w, expPt (fglOf hB) w']) (B.FK C i) := by
    rw [(hAdd C v d (fglOf hB) σ).2.1 w w' hw.1 hw'.1]
    funext i
    exact subst_elim_twoVars cw cw' (B.FK C i)
  have cA : ∀ {n : ℕ} (j l : Fin n) i, constantCoeff (addOf (B.FK C) (pt C d j) (pt C d l) i) = 0 :=
    fun j l i => constantCoeff_germEvalPair_eq_zero (cc_pt j) (cc_pt l) (hF i)
  have sA : ∀ {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (_ : ∀ j i, constantCoeff (x j i) = 0) (j l : Fin n),
      (fun i => (subst (famPt x) (addOf (B.FK C) (pt C d j) (pt C d l) i) : MvPowerSeries σ C)) =
        fun i => subst (famPt ![x j, x l]) (B.FK C i) := fun hx j l => by
    funext i
    unfold addOf
    rw [subst_pointFamily_germEvalPair hx (cc_pt j) (cc_pt l), subst_famPt_pt hx, subst_famPt_pt hx]
  refine ⟨constantCoeff_subst_eq_zero (hs_famPt (constantCoeff_vecCons_pair_eq_zero cw cz)) (fun q => constantCoeff_vecCons_pair_eq_zero cw cz q.1 q.2) hc, ?_, ?_,
    fun a => ?_⟩
  · have hx : ∀ (j : Fin 3) i, constantCoeff ((![expPt (fglOf hB) w, expPt (fglOf hB) w', expPt (fglOf hB) z] :
        Fin 3 → Fin d → MvPowerSeries σ C) j i) = 0 := fun j i => by
      fin_cases j; exacts [cw i, cw' i, cz i]
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hw.2 i, hw'.2 i, hz.2 i]) hB.2.2.1
      (by rw [map_sub, map_add (f := _), constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cA _ _) (cc_pt _) hc]; simp) H.ph1
    rw [subst_sub (hs_famPt hx), subst_add (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _), subst_pointFamily_germEvalPair hx (cA _ _) (cc_pt _), sA hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [hadd]
    exact k
  · have hx : ∀ (j : Fin 3) i, constantCoeff ((![expPt (fglOf hB) z, expPt (fglOf hB) w, expPt (fglOf hB) w'] :
        Fin 3 → Fin d → MvPowerSeries σ C) j i) = 0 := fun j i => by
      fin_cases j; exacts [cz i, cw i, cw' i]
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hz.2 i, hw.2 i, hw'.2 i]) hB.2.2.2.1
      (by rw [map_sub, map_add (f := _), constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cc_pt _) (cA _ _) hc]; simp) H.ph2
    rw [subst_sub (hs_famPt hx), subst_add (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _), subst_pointFamily_germEvalPair hx (cc_pt _) (cA _ _), sA hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [hadd]
    exact k
  · have hx := constantCoeff_vecCons_pair_eq_zero cw cz
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hw.2 i, hz.2 i]) (hB.2.2.2.2 a)
      (by rw [map_sub, constantCoeff_germEvalPair_eq_zero (cc_comp1 (cc_pt _) (hA _)) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_comp1 (cc_pt _) (hA _)) hc]; simp) (H.ad a)
    rw [subst_sub (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_comp1 (cc_pt _) (hA _)) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_comp1 (cc_pt _) (hA _)), subst_famPt_comp1 hx, subst_famPt_comp1 hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [(hAct C v d R O B hB σ a).1 w hw.1, (hAct C v d R O B hB σ (star a)).1 z hz.1]
    exact k

end GlobalTheory.IsoTriv.GaugeBiadd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonGaugeBiadditiveOfLogSumActionLinearStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonGaugeBiadditive_of_logSum_actionLinear : AddSt → ActSt → BiaddSt := by
  first | exact @GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act | exact GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act | (intros; apply GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act <;> assumption)
end
end
