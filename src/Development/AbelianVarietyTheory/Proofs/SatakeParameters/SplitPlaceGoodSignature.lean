module

public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftOfEachRow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitLiftOfLiftParam
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
noncomputable section

namespace GlobalTheory.Proof.SplitPlaceGoodSignature

open NumberField Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem isSplitPl_of_not_isConjPl (w : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E))
    (h : ¬ IsConjPl H w w) : IsSplitPl H w := by
  by_contra hs
  apply h
  let c : 𝓞 H.E →+* 𝓞 H.E := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  have hc : ∀ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y = c x := fun x y hy =>
    RingOfIntegers.ext hy
  have hle : w.asIdeal ≤ w.asIdeal.comap c := by
    intro x hx
    by_contra hx'
    exact hs ⟨x, hx, fun y hy => by rw [hc x y hy]; exact hx'⟩
  have heq : w.asIdeal = w.asIdeal.comap c :=
    w.isMaximal.eq_of_le (Ideal.comap_ne_top c w.isPrime.ne_top) hle
  intro x y hy
  rw [hc x y hy, ← Ideal.mem_comap, ← heq]

variable (N : NData R H what₂) (A : NAut N)

theorem typePlSplit : TypePlSplit N A := fun k v =>
  isSplitPl_of_not_isConjPl _ (A.plGw_nconj k v v)

theorem isoLoc_lift (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by
  rw [Check.iso_char N A hL, Check.iso_append]
  rfl

theorem goodRow_iff_goodSig {i : N.Loc} {σ : what₂.FT} {Sig : List (Part A.CG)}
    (h : ∀ w, IsSplitPl H w → isoLoc N A Sig w = A.locW i σ w) :
    N.goodRow σ ↔ goodSig N A Sig := by
  have hl : ∀ k, (fun v => A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))) = N.lab k σ := by
    intro k
    funext v
    rw [h _ (typePlSplit N A k v), A.lab_loc i k σ v]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [hl k]

theorem isoLoc_eq_of_hasParamX (hL : ParamLaws N A) {i : N.Loc} (hloc : LocOfPt N A i) {x : N.X i}
    {Sig Sig' : List (Part A.CG)} (h : HasParamX N A i x Sig) (h' : HasParamX N A i x Sig')
    (w : PlE H) (hw : IsSplitPl H w) : isoLoc N A Sig w = isoLoc N A Sig' w := by
  obtain ⟨P, hP, hB⟩ := h
  obtain ⟨P', hP', hB'⟩ := h'
  have e := hloc P P' x hP hP' w hw
  rw [← hB.2.2.2.1 w hw, ← hB'.2.2.2.1 w hw, isoLoc_lift N A hL, isoLoc_lift N A hL] at e
  exact (hL w).2.2.2.2 _ _ _ ((hL w).2.2.2.1 _ _ _ (A.locG_dim _ w) e)

theorem goodPart_of_lifts (i : N.Loc) (h1 : ThetaOne N A) (hL : ParamLaws N A)
    (hlift : LiftParam N A i) (hpt : PtLocal N A i) (hloc : LocOfPt N A i) : GoodPart N A i := by
  unfold GoodPart goodPartM
  apply le_antisymm
  · refine iSup₂_le fun σ hσ => ?_
    obtain ⟨hg, Sig₀, hW₀, x₀, hx₀⟩ := hσ
    by_cases hb : what₂.isot (N.j i) σ = ⊥
    · rw [hb]; exact bot_le
    obtain ⟨P, hP⟩ := h1 i σ hb
    obtain ⟨Sig, hW, hB⟩ := hlift σ P hP
    obtain ⟨y, hy⟩ := hpt P x₀ fun w hw => by
      obtain ⟨p, hp, hp'⟩ := hx₀ w hw
      refine ⟨p, ?_, hp'⟩
      rw [hp, ← hB.2.2.2.1 w hw.1, isoLoc_lift N A hL, isoLoc_lift N A hL, hW₀.2.2 w hw.1,
        hW.2.2 w hw.1]
    have hX : HasParamX N A i y Sig := ⟨P, hy, hB⟩
    have hZ : y ∈ ZgoodN N A i := by
      refine ⟨⟨P, hy, _, hB, ?_⟩, Sig, hX, (goodRow_iff_goodSig N A hW.2.2).1 hg⟩
      exact List.mem_map.2 ⟨muPart N A i, by simp, rfl⟩
    refine le_iSup₂_of_le y hZ (le_iSup₂_of_le Sig hX ?_)
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | HasParamW N A i σ Sig}) =>
      what₂.isot (N.j i) σ) σ hW le_rfl
  · refine iSup₂_le fun x hx => iSup₂_le fun Sig hX => ?_
    unfold MjSig
    refine iSup₂_le fun σ hW => ?_
    obtain ⟨-, Sig', hX', hg⟩ := hx
    have hgood : N.goodRow σ := (goodRow_iff_goodSig N A (i := i) fun w hw =>
      (isoLoc_eq_of_hasParamX N A hL hloc hX' hX w hw).trans (hW.2.2 w hw)).2 hg
    have hat : AtM N A i σ := by
      obtain ⟨P, hP, hB⟩ := hX
      refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
      rw [hB.2.2.2.1 w hw.1]
      exact A.pt_loc i P x hP w hw
    exact le_iSup₂_of_le (f := fun σ (_ : σ ∈ {σ | N.goodRow σ ∧ AtM N A i σ}) =>
      what₂.isot (N.j i) σ) σ ⟨hgood, hat⟩ le_rfl

end GlobalTheory.Proof.SplitPlaceGoodSignature
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JInvNormLeOne
open GlobalTheory GlobalTheory.CMCurves

namespace GlobalTheory.ThLoc

theorem cm1 : Formalism.L2.Th1.CM.JInvariantIntegrality := by
  intro d L _ hd hL
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [Formalism.L2.Th1.CM.jInv, g₂_cube_div_eq_modularJ ha h]
  refine isIntegral_modularJ_of_mul_mem (α := Formalism.L2.Th1.CM.omegaK d) (fun m hm => ?_) fun x hx ↦ ?_
  · have := congrArg Complex.im hm
    have h0 : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    simp [Formalism.L2.Th1.CM.omegaK] at this
    omega
  · have key : ∀ y : ℂ, y ∈ Submodule.span ℤ {(τ : ℂ), 1} ↔ a * y ∈ L.lattice := fun y ↦ by
      rw [h, Submodule.mem_span_pair]
      simp [mul_right_inj' ha]
    rw [key] at hx ⊢
    simpa [mul_left_comm] using hL _ hx

end GlobalTheory.ThLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.UnitaryDoubleCoset

section Abstract

variable {O L : Type} [CommRing O] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.UnitaryDoubleCoset.cT_map (ι : O →+* L) {c : O →+* O} {σ : L →+* L}
    (hι : ∀ x, σ (ι x) = ι (c x)) (M : Matrix n n O) :
    _root_.Formalism.UG.cT σ (M.map ι) = (_root_.Formalism.UG.cT c M).map ι := by
  ext i j
  simp [_root_.Formalism.UG.cT, hι]

omit [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.UnitaryDoubleCoset.cT_cT {c : O →+* O} (hc : ∀ x, c (c x) = x)
    (M : Matrix n n O) : _root_.Formalism.UG.cT c (_root_.Formalism.UG.cT c M) = M := by
  ext i j
  simp [_root_.Formalism.UG.cT, hc]

private theorem cT_aeval_eq_aeval_cT_map (c : O →+* O) (B : Matrix n n O) (q : Polynomial O) :
    _root_.Formalism.UG.cT c (Polynomial.aeval B q) = Polynomial.aeval (_root_.Formalism.UG.cT c B) (q.map c) := by
  induction q using Polynomial.induction_on with
  | C a =>
    ext i j
    by_cases hij : i = j
    · subst hij; simp [_root_.Formalism.UG.cT, Polynomial.aeval_C, Matrix.algebraMap_matrix_apply]
    · simp [_root_.Formalism.UG.cT, Polynomial.aeval_C, Matrix.algebraMap_matrix_apply, hij, Ne.symm hij]
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.map_add (f := _), ← hp, ← hq]
    simp [_root_.Formalism.UG.cT, Matrix.map_add (f := _), Matrix.transpose_add]
  | monomial m a hm =>
    rw [pow_succ, ← mul_assoc, mul_comm _ Polynomial.X, Polynomial.map_mul,
      map_mul (Polynomial.aeval B) Polynomial.X, map_mul (Polynomial.aeval (_root_.Formalism.UG.cT c B)), ← hm,
      Polynomial.map_X, Polynomial.aeval_X, Polynomial.aeval_X]
    have hcomm : Polynomial.aeval B (Polynomial.C a * Polynomial.X ^ m) * B =
        B * Polynomial.aeval B (Polynomial.C a * Polynomial.X ^ m) := by
      have := congrArg (Polynomial.aeval B) (mul_comm (Polynomial.C a * Polynomial.X ^ m) Polynomial.X)
      simpa only [map_mul, Polynomial.aeval_X] using this
    simp only [_root_.Formalism.UG.cT, ← Matrix.transpose_mul, ← Matrix.map_mul, hcomm]

theorem _root_.GlobalTheory.UnitaryDoubleCoset.exists_poly_norm {c : O →+* O} (hc : ∀ x, c (c x) = x)
    (hN : ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) →
      ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X)
    {B : Matrix n n O} (hB : _root_.Formalism.UG.cT c B = B) (hu : IsUnit B) :
    ∃ p : Polynomial O, _root_.Formalism.UG.cT c (Polynomial.aeval B p) * Polynomial.aeval B p = B := by
  have hmap : B.charpoly.map c = B.charpoly := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose]
    conv_rhs => rw [← hB]
    rfl
  have hunit : IsUnit (B.charpoly.coeff 0) := by
    have hdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hu
    rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  obtain ⟨p, q, hpq⟩ := hN B.charpoly (Matrix.charpoly_monic B) hmap hunit
  refine ⟨p, ?_⟩
  have h1 := congrArg (Polynomial.aeval B) hpq
  rw [map_mul, Matrix.aeval_self_charpoly, zero_mul, map_sub, Polynomial.aeval_X, sub_eq_zero] at h1
  rw [cT_aeval_eq_aeval_cT_map, hB, ← map_mul, mul_comm, h1]

theorem _root_.GlobalTheory.UnitaryDoubleCoset.exists_unitary_factors (ι : O →+* L) {c : O →+* O} {σ : L →+* L}
    (hι : ∀ x, σ (ι x) = ι (c x))
    (hc : ∀ x, c (c x) = x)
    (hN : ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) →
      ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X)
    {g g' : GL n L} (hg : g ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L)) (hg' : g' ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L))
    (h k : GL n O) (e : g' = _root_.Formalism.UG.bc ι h * g * _root_.Formalism.UG.bc ι k) :
    ∃ k₁ ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L) ⊓ (_root_.Formalism.UG.bc ι).range, ∃ k₂ ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L),
      (∃ M : Matrix n n O, (k₂ : Matrix n n L) = M.map ι) ∧ g' = k₁ * g * k₂ := by
  have hmul : ∀ {R : Type} [CommRing R] (τ : R →+* R) (A B : Matrix n n R),
      _root_.Formalism.UG.cT τ (A * B) = _root_.Formalism.UG.cT τ B * _root_.Formalism.UG.cT τ A := by
    intro R _ τ A B
    simp [_root_.Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hone : ∀ {R : Type} [CommRing R] (τ : R →+* R), _root_.Formalism.UG.cT τ (1 : Matrix n n R) = 1 := by
    intro R _ τ
    simp [_root_.Formalism.UG.cT]

  have hinv : ∀ u : GL n L, _root_.Formalism.UG.cT σ (u : Matrix n n L) * u = 1 →
      _root_.Formalism.UG.cT σ (u : Matrix n n L) = ((u⁻¹ : GL n L) : Matrix n n L) ∧
        _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L) = u := by
    intro u hu
    have h1 : _root_.Formalism.UG.cT σ (u : Matrix n n L) = ((u⁻¹ : GL n L) : Matrix n n L) := by
      calc _root_.Formalism.UG.cT σ (u : Matrix n n L) = _root_.Formalism.UG.cT σ (u : Matrix n n L) * (u * ↑u⁻¹) := by
            rw [Units.mul_inv, mul_one]
        _ = ((u⁻¹ : GL n L) : Matrix n n L) := by rw [← mul_assoc, hu, one_mul]
    refine ⟨h1, ?_⟩
    have h2 : _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L) * ((u⁻¹ : GL n L) : Matrix n n L) = 1 := by
      have h3 := hmul σ (u : Matrix n n L) ((u⁻¹ : GL n L) : Matrix n n L)
      rw [Units.mul_inv, hone, h1] at h3
      exact h3.symm
    calc _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L)
        = _root_.Formalism.UG.cT σ ((u⁻¹ : GL n L) : Matrix n n L) * (((u⁻¹ : GL n L) : Matrix n n L) * u) := by
          rw [Units.inv_mul, mul_one]
      _ = u := by rw [← mul_assoc, h2, one_mul]
  have hg1 : _root_.Formalism.UG.cT σ (g : Matrix n n L) * g = 1 := by simpa [_root_.Formalism.UG.UJ] using hg
  have hg'1 : _root_.Formalism.UG.cT σ (g' : Matrix n n L) * g' = 1 := by simpa [_root_.Formalism.UG.UJ] using hg'
  have hbc : ∀ u : GL n O, ((_root_.Formalism.UG.bc ι u : GL n L) : Matrix n n L) = (u : Matrix n n O).map ι := by
    intro u
    simp [_root_.Formalism.UG.bc]

  set H := _root_.Formalism.UG.cT c (h : Matrix n n O) * h with hHdef
  have hH : _root_.Formalism.UG.cT c H = H := by
    rw [hHdef, hmul, _root_.GlobalTheory.UnitaryDoubleCoset.cT_cT hc]
  have hHu : IsUnit H := by
    refine IsUnit.mul (IsUnit.of_mul_eq_one (_root_.Formalism.UG.cT c ((h⁻¹ : GL n O) : Matrix n n O)) ?_) h.isUnit
    rw [← hmul, Units.inv_mul, hone]
  obtain ⟨p, hp⟩ := _root_.GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc hN hH hHu
  set P := Polynomial.aeval H p with hPdef
  have hPu : IsUnit P := isUnit_of_mul_isUnit_right (hp.symm ▸ hHu)
  set k₁ : GL n L := _root_.Formalism.UG.bc ι (h * hPu.unit⁻¹) with hk₁def
  have hk₁ : k₁ ∈ _root_.Formalism.UG.UJ σ (1 : Matrix n n L) := by
    have hO : _root_.Formalism.UG.cT c ((h * hPu.unit⁻¹ : GL n O) : Matrix n n O) *
        ((h * hPu.unit⁻¹ : GL n O) : Matrix n n O) = 1 := by
      rw [Units.val_mul, hmul]
      calc _root_.Formalism.UG.cT c ((hPu.unit⁻¹ : GL n O) : Matrix n n O) * _root_.Formalism.UG.cT c (h : Matrix n n O) *
            ((h : Matrix n n O) * ((hPu.unit⁻¹ : GL n O) : Matrix n n O))
          = _root_.Formalism.UG.cT c ((hPu.unit⁻¹ : GL n O) : Matrix n n O) * (_root_.Formalism.UG.cT c P * P) *
            ((hPu.unit⁻¹ : GL n O) : Matrix n n O) := by
            rw [hp, hHdef]; simp only [mul_assoc]
        _ = _root_.Formalism.UG.cT c (P * ((hPu.unit⁻¹ : GL n O) : Matrix n n O)) *
            (P * ((hPu.unit⁻¹ : GL n O) : Matrix n n O)) := by
            rw [hmul]; simp only [mul_assoc]
        _ = 1 := by rw [hPu.mul_val_inv, hone, one_mul]
    show _root_.Formalism.UG.cT σ (k₁ : Matrix n n L) * 1 * k₁ = 1
    rw [mul_one, hk₁def, hbc, _root_.GlobalTheory.UnitaryDoubleCoset.cT_map ι hι, ← Matrix.map_mul, hO,
      Matrix.map_one _ (map_zero ι) (map_one ι)]
  refine ⟨k₁, ⟨hk₁, ⟨_, rfl⟩⟩, g⁻¹ * k₁⁻¹ * g',
    mul_mem (mul_mem (inv_mem hg) (inv_mem hk₁)) hg', ?_, by group⟩

  obtain ⟨hGc, hGic⟩ := hinv g hg1
  obtain ⟨hG'c, -⟩ := hinv g' hg'1
  have eM : (g' : Matrix n n L) = (h : Matrix n n O).map ι * g * (k : Matrix n n O).map ι := by
    rw [e, Units.val_mul, Units.val_mul, hbc, hbc]
  have hkk : (k : Matrix n n O).map ι * (↑k⁻¹ : Matrix n n O).map ι = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hhh : (↑h⁻¹ : Matrix n n O).map ι * (h : Matrix n n O).map ι = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]

  have hHg : (h : Matrix n n O).map ι * g = g' * (↑k⁻¹ : Matrix n n O).map ι := by
    rw [eM, mul_assoc _ _ ((↑k⁻¹ : Matrix n n O).map ι), hkk, mul_one]
  have hhm : (h : Matrix n n O).map ι =
      g' * (↑k⁻¹ : Matrix n n O).map ι * ((g⁻¹ : GL n L) : Matrix n n L) := by
    rw [← hHg, mul_assoc, Units.mul_inv, mul_one]
  set Hk := _root_.Formalism.UG.cT c ((k⁻¹ : GL n O) : Matrix n n O) * ((k⁻¹ : GL n O) : Matrix n n O)
    with hHkdef
  have hconj : H.map ι * g = g * Hk.map ι := by
    rw [hHdef, hHkdef, Matrix.map_mul, Matrix.map_mul, ← _root_.GlobalTheory.UnitaryDoubleCoset.cT_map ι hι,
      ← _root_.GlobalTheory.UnitaryDoubleCoset.cT_map ι hι, mul_assoc, hHg, ← mul_assoc]
    conv_lhs => rw [hhm, hmul, hmul, hG'c, hGic]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  clear_value Hk P H
  have hsemi : ∀ q : Polynomial O, (Polynomial.aeval H q).map ι * g =
      g * (Polynomial.aeval Hk q).map ι := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      simp only [Polynomial.aeval_C, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero ι)]
      ext i j
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _), Matrix.map_add _ (map_add ι), Matrix.map_add _ (map_add ι), add_mul,
        mul_add, hp, hq]
    | monomial m a hm =>
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval H) _ Polynomial.X,
        map_mul (Polynomial.aeval Hk) _ Polynomial.X, Polynomial.aeval_X, Polynomial.aeval_X,
        Matrix.map_mul, Matrix.map_mul, mul_assoc, hconj, ← mul_assoc, hm, mul_assoc]
  refine ⟨Polynomial.aeval Hk p * k, ?_⟩
  rw [Units.val_mul, Units.val_mul, hk₁def, ← map_inv, hbc, mul_inv_rev, inv_inv, Units.val_mul,
    hPu.unit_spec, Matrix.map_mul, eM, Matrix.map_mul]
  have hcancel : ((g⁻¹ : GL n L) : Matrix n n L) * (P.map ι * (↑h⁻¹ : Matrix n n O).map ι) *
      ((h : Matrix n n O).map ι * g * (k : Matrix n n O).map ι) =
      ((g⁻¹ : GL n L) : Matrix n n L) * (P.map ι * g) * (k : Matrix n n O).map ι := by
    simp only [mul_assoc]
    rw [← mul_assoc ((↑h⁻¹ : Matrix n n O).map ι), hhh, one_mul]
  rw [hcancel, hPdef, hsemi p, ← mul_assoc, Units.inv_mul, one_mul]

end Abstract

theorem doubleCoset_unitary_of_GL (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (σ : v.adicCompletion K →+* v.adicCompletion K) (n : ℕ) (hσσ : ∀ x, σ (σ x) = x)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hx : ∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) :
    ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)),
    ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)),
    ∀ h ∈ GLint (Fin n) (Ov K v), ∀ k ∈ GLint (Fin n) (Ov K v), g' = h * g * k →
      ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v),
      ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v),
        g' = k₁ * g * k₂ := by
  rintro g hg g' hg' _ ⟨h, rfl⟩ _ ⟨k, rfl⟩ e
  have := isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
    finite_residueField_adicCompletionIntegers v
  let c : v.adicCompletionIntegers K →+* v.adicCompletionIntegers K :=
    (σ.comp (v.adicCompletionIntegers K).subtype).codRestrict (v.adicCompletionIntegers K) fun x => by
      show Valued.v (σ x) ≤ 1
      rw [hσ]; exact x.2
  have hcv : ∀ x, ((c x : v.adicCompletionIntegers K) : v.adicCompletion K) = σ x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hσσ x)
  have hI : ∀ x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K),
      c x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    intro x hx hu
    exact hx (by simpa [hc] using hu.map c)
  have hω : ∃ ω, IsUnit (ω - c ω) := by
    obtain ⟨x, hx1, hx2⟩ := hx
    refine ⟨⟨x, hx1⟩, ?_⟩
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    show Valued.v (x - σ x) = 1
    rw [Valuation.map_sub_swap, hx2]
  obtain ⟨k₁, hk₁, k₂, hk₂, ⟨M, hM⟩, e'⟩ :=
    exists_unitary_factors (O := Ov K v) (Ov K v).subtype (c := c) (σ := σ) (fun _ => rfl) hc
      (GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution (v.adicCompletionIntegers K) _ c hc hI hω) hg hg' h k e
  refine ⟨k₁, hk₁, k₂, ⟨hk₂, ?_⟩, e'⟩
  refine GlobalTheory.UnitarySwap.mem_GLint_of_unitary (J := 1) hσ (one_mem _) hk₂ fun i j => ?_
  rw [hM]
  exact (M i j).2

end GlobalTheory.UnitaryDoubleCoset
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleCStatement
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_mem_integralUnitary_doubleCoset_of_GLn_doubleCoset : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (σ : v.adicCompletion K →+* v.adicCompletion K) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)), ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)), ∀ h ∈ GLint (Fin n) (Ov K v), ∀ k ∈ GLint (Fin n) (Ov K v), g' = h * g * k → ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v), ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v), g' = k₁ * g * k₂ := by
  first | exact @GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL | exact GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL | (intros; apply GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL <;> assumption)
end
end
