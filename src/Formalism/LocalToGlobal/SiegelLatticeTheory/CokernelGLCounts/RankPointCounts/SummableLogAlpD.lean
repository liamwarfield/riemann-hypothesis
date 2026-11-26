module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlpBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SummableLogAlpD
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.DataInst

variable {D : D7} (X : HidaSetting D)

theorem alX_eq (hEta : EtaTie X) (u u' : D.what₂.Word) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    alX X u u' v = alpD u u' (plEquiv X v) := by
  have haP : ∀ T : ℕ, aP (E := X.B.I.E) v D.R.k X.B.I.n T = aPD (plEquiv X v) T := by
    intro T
    unfold aP aPD
    have hI : Finset.Icc (if ((T : 𝓞 X.B.I.F) ∈ v.asIdeal) then D.R.k else D.R.k + 1) X.B.I.n =
        Finset.Icc (if ((T : 𝓞 D.host.F) ∈ (plEquiv X v).asIdeal) then D.R.k else D.R.k + 1) D.R.r := by
      rw [X.n_eq]
      by_cases hm : ((T : 𝓞 X.B.I.F) ∈ v.asIdeal)
      · rw [if_pos hm, if_pos ((natCast_mem_plEquiv X v T).2 hm)]
      · rw [if_neg hm, if_neg (fun h => hm ((natCast_mem_plEquiv X v T).1 h))]
    rw [hI]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hEta v, absNorm_plEquiv]
  unfold alX alpD Tw
  rw [haP, haP]
  by_cases h : TypAt X v
  · rw [if_pos h, if_pos ((typAt_iff X v).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((typAt_iff X v).2 h'))]

theorem summable_log_alpD (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word) :
    (∀ p, 0 < alpD u u' p) ∧ Summable fun p => Real.log (alpD u u' p) := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  have hα := Formalism.L2.SG.IntegralApproximation.AlpBound_holds D
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have hαb := hα hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  refine ⟨hal0, ?_⟩
  refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
  have h2 := Real.log_le_log (hal0 p) (hαb p).2
  rw [Real.log_exp] at h1 h2
  have ha' : a p = (Formalism.L2.SG.DataCut.qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹ := rfl
  constructor <;> linarith

theorem prod_split {β : Type} (f : β → ℝ) (s : Finset β) (hpos : ∀ v, 0 < f v)
    (hlog : Summable fun v => Real.log (f v)) :
    (∏ p : ↥s, f p.1) * ∏' v : {v // v ∉ s}, f v.1 = ∏' v, f v := by
  have hls : Summable (fun v : {v // v ∉ s} => Real.log (f v.1)) :=
    hlog.comp_injective (i := fun v : {v // v ∉ s} => v.1) Subtype.val_injective
  have hO : ∏' v : {v // v ∉ s}, f v.1 = Real.exp (∑' v : {v // v ∉ s}, Real.log (f v.1)) :=
    (Real.rexp_tsum_eq_tprod (f := fun v : {v // v ∉ s} => f v.1) (fun v => hpos v.1) hls).symm
  have hT : ∏ p : ↥s, f p.1 = Real.exp (∑ p : ↥s, Real.log (f p.1)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => (Real.exp_log (hpos _)).symm
  have hsplit : ∑ p : ↥s, Real.log (f p.1) + ∑' v : {v // v ∉ s}, Real.log (f v.1) = ∑' v, Real.log (f v) := by
    rw [Finset.sum_coe_sort s (fun x => Real.log (f x))]
    exact hlog.sum_add_tsum_compl (s := s)
  rw [hO, hT, ← Real.exp_add, hsplit, Real.rexp_tsum_eq_tprod hpos hlog]

theorem locOf_al_eq (hEta : EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) :
    (locOf X u u' ψ).al = ∏' q, alpD u u' q := by
  obtain ⟨hpos, hlog⟩ := summable_log_alpD hk u u'
  have he : ∀ v, alX X u u' v = alpD u u' (plEquiv X v) := alX_eq X hEta u u'
  have hxpos : ∀ v, 0 < alX X u u' v := fun v => (he v).symm ▸ hpos _
  have hxlog : Summable fun v => Real.log (alX X u u' v) := by
    have h1 : Summable fun v => Real.log (alpD u u' (plEquiv X v)) := (plEquiv X).summable_iff.2 hlog
    exact h1.congr fun v => by rw [he v]
  have hS := prod_split (alX X u u') (Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1)) hxpos hxlog
  have hR : ∏' v, alX X u u' v = ∏' q, alpD u u' q := by
    rw [tprod_congr he]
    exact (plEquiv X).tprod_eq (alpD u u')
  rw [← hR, ← hS]
  rfl

end Formalism.L2.SG.Pf.AlTie

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem AlTieC_of {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hEta : AlTie.EtaTie X) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq := by
  unfold AlTieC
  exact AlTie.locOf_al_eq X hEta hk u u' ψ

theorem AlTieC_of_loc {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (hL : Formalism.L2.SG.Pf.LocCP.LocTied D) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) :
    AlTieC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq :=
  AlTieC_of X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (AlTie.etaTie_of X hL) hk

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBAt
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Minors

variable {K : Type*} [CommRing K]

theorem sum_castLE {N l : ℕ} (h : l ≤ N) (f : Fin N → K) (hf : ∀ k : Fin N, l ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k' : Fin l, f (Fin.castLE h k') := by
  have hsub : (Finset.univ : Finset (Fin l)).map (Fin.castLEEmb h) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub (fun k _ hk => ?_), Finset.sum_map]
  · rfl
  · apply hf
    by_contra hlt
    push_neg at hlt
    exact hk (Finset.mem_map.2 ⟨⟨k.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem submatrix_loUni_mul {N l : ℕ} (h : l ≤ N) (L A U : Matrix (Fin N) (Fin N) K) (hL : IsLoUni L)
    (hU : IsUpUni U) :
    (L * A * U).submatrix (Fin.castLE h) (Fin.castLE h) =
      L.submatrix (Fin.castLE h) (Fin.castLE h) * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        U.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hin : ∀ m : Fin N, ∑ k, L (Fin.castLE h i) k * A k m =
      ∑ k' : Fin l, L (Fin.castLE h i) (Fin.castLE h k') * A (Fin.castLE h k') m := fun m =>
    sum_castLE h _ fun k hk => by
      rw [(hL _ _).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le (by simpa using i.isLt) hk)), zero_mul]
  simp only [hin]
  exact sum_castLE h _ fun m hm => by
    rw [(hU _ _).1 (Fin.lt_iff_val_lt_val.2 (lt_of_lt_of_le (by simpa using j.isLt) hm)), mul_zero]

theorem det_sub_loUni {N l : ℕ} (h : l ≤ N) (L A U : Matrix (Fin N) (Fin N) K) (hL : IsLoUni L) (hU : IsUpUni U) :
    ((L * A * U).submatrix (Fin.castLE h) (Fin.castLE h)).det = (A.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  rw [submatrix_loUni_mul h L A U hL hU, Matrix.det_mul, Matrix.det_mul]
  have h1 : (L.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    have hb : (L.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular OrderDual.toDual := by
      intro i j hij
      exact (hL _ _).1 (Fin.lt_iff_val_lt_val.2 (by
        simpa using Fin.lt_iff_val_lt_val.1 (OrderDual.toDual_lt_toDual.1 hij)))
    rw [Matrix.det_of_lowerTriangular _ hb]
    exact Finset.prod_eq_one fun i _ => (hL _ _).2 rfl
  have h2 : (U.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    have hb : (U.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
      intro i j hij
      exact (hU _ _).1 (Fin.lt_iff_val_lt_val.2 (by simpa using Fin.lt_iff_val_lt_val.1 hij))
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_eq_one fun i _ => (hU _ _).2 rfl
  rw [h1, h2, one_mul, mul_one]

theorem det_sub_ZhatOM {r l : ℕ} (h : l ≤ r + 1) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ((ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (∏ b : Fin l, ((-1 : K) ^ (r - b.val))) * (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  have e : (ZhatOM Z).submatrix (Fin.castLE h) (Fin.castLE h) =
      Z.submatrix (Fin.castLE h) (Fin.castLE h) * Matrix.diagonal fun b : Fin l => (-1 : K) ^ (r - b.val) := by
    ext a b
    simp [ZhatOM, Matrix.mul_diagonal, mul_comm]
  rw [e, Matrix.det_mul, Matrix.det_diagonal, mul_comm]

end Minors

theorem conjF_eq_star {D : Formalism.BasicNotions.D7} (x : D.host.E) : D.conjF x = star x :=
  (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm

theorem atPtG_holds {D : Formalism.BasicNotions.D7} (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : AtPtG u u' F0 what₂ := by
  intro γ w hat
  obtain ⟨F', -, hG, L, U, hL, hU, hZ⟩ := hat
  have N_eq : ∀ (l : ℕ) (h : l ≤ D.R.rS + 1),
      leadMinorE (ZhatL (lf D F0) F') l * star (leadMinorE (ZhatL (lf D F0) F') l) =
        Dmin w l * D.conjF (Dmin w l) := by
    intro l h
    have e1 : ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det =
        (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) *
          ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      rw [← det_sub_loUni h L (ptMat w) U hL hU, ← hZ]
      exact det_sub_ZhatOM h _
    have hss : (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) *
        (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun b _ => by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have hst : star (∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val))) =
        ∏ b : Fin l, ((-1 : D.host.E) ^ (D.R.rS - b.val)) := by
      rw [star_prod]
      exact Finset.prod_congr rfl fun b _ => by rw [star_pow, star_neg, star_one]
    have hD : Dmin w l = ((ptMat w).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      unfold Dmin
      rw [dite_eq_left h]
    have hM : leadMinorE (ZhatL (lf D F0) F') l =
        ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det := by
      unfold leadMinorE
      rw [dite_eq_left h]
    rw [hD, hM, conjF_eq_star, e1, star_mul', hst]
    linear_combination (-(((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det *
      star ((ZhatL (lf D F0) F').submatrix (Fin.castLE h) (Fin.castLE h)).det)) * hss
  have key : Gval (lf D F0) F' = Gpt (D.mem u).A.T (D.mem u').A.T w := by
    rw [CntLocal.gz_eq]
    unfold CntLocal.GZ Gpt
    rw [N_eq (D.R.rS + 1) le_rfl, N_eq D.R.rS (Nat.le_succ _)]
  rw [← key]
  exact hG

theorem dnInDens_of {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hN : NormRepElig u u' F0 what₂) (hrows : IsRowReps D F0 what₂) :
    DnInDens u u' F0 what₂ := by
  intro γ w hγ
  have hex := hN γ w hγ
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dite_eq_left hex]
  obtain ⟨⟨hPD, hmk⟩, hadm, -, -, -⟩ := hex.choose_spec
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam (hrows.1 γ.lam γ.mem)
  have hGt := TermDef.Gt_mk hTF.1 ⟨_, hPD⟩
  have hGen := TermDef.isGen_mk (gS D) hTF.2.2.2.1 ⟨_, hPD⟩
  rw [hmk] at hGt hGen
  refine ⟨γ.lam, γ.mem, hex.choose.2.1, ⟨hPD.1, hPD.2.1, ?_⟩, hadm, hGen.1 hγ.1.1, hPD.2.2, hz.symm⟩
  exact fun h => hγ.1.2 (hGt.trans h)

end Formalism.L2.SG.LsDatumB
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBTup
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Tup

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {T T' : ℕ}

theorem fL_eq (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) :
    fL M δ T T' p w τ O = hL M δ T T' p w O * kL M δ T T' p w τ O := by
  by_cases h1 : IsLCls M δ T T' p w O <;> simp [fL, hL, kL, h1]

theorem gL_eq (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) :
    gL M δ T T' p w τ O = hL M δ T T' p w O * eL M δ T T' p w τ O := by
  by_cases h1 : IsLCls M δ T T' p w O <;>
    by_cases h2 : thL M δ T T' p w (repL M δ T T' p w O) = τ <;> simp [gL, hL, eL, h1, h2]

theorem eL_zero_or_one (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS))
    (O : Set (MatP D p)) : eL M δ T T' p w τ O = 0 ∨ eL M δ T T' p w τ O = 1 := by
  unfold eL
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem base_factors {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {θ : Option ((M p).Cls D.R.rS)}
    (hf : ∀ τ O, fL M δ T T' p w τ O = if O = x0L M δ T T' p w ∧ τ = θ then 1 else 0)
    (hg : ∀ τ O, gL M δ T T' p w τ O = if O = x0L M δ T T' p w ∧ τ = θ then 1 else 0) :
    hL M δ T T' p w (x0L M δ T T' p w) = 1 ∧ kL M δ T T' p w θ (x0L M δ T T' p w) = 1 ∧
      eL M δ T T' p w θ (x0L M δ T T' p w) = 1 := by
  have g1 := hg θ (x0L M δ T T' p w)
  rw [if_pos ⟨rfl, rfl⟩, gL_eq] at g1
  have he : eL M δ T T' p w θ (x0L M δ T T' p w) = 1 := by
    rcases eL_zero_or_one (M := M) (δ := δ) (T := T) (T' := T') p w θ (x0L M δ T T' p w) with h | h
    · rw [h, mul_zero] at g1
      exact absurd g1 zero_ne_one
    · exact h
  rw [he, mul_one] at g1
  have f1 := hf θ (x0L M δ T T' p w)
  rw [if_pos ⟨rfl, rfl⟩, fL_eq, g1, one_mul] at f1
  exact ⟨g1, f1, he⟩

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem partnerTupleSum_of {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hC : CoefProd M δ u u' F0 what₂) (hN : PartnerCount M δ u u' F0 what₂) : PartnerTupleSum M δ u u' F0 what₂ := by
  intro γ w hγ w' hG' hk
  obtain ⟨hres, hcnt⟩ := hN γ w hγ w' hG' hk
  refine ⟨hres, fun x => ?_⟩
  obtain ⟨S, hS⟩ := hU w' hG'
  have hRf := hR γ w hγ
  have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
      hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p) = 1 ∧
        kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p) = 1 := by
    intro p hp
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hth : thT M δ γ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
    have hx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w' := by
      by_contra h
      exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
    rw [hx, hth]
    have hb := base_factors (fun τ O => ((hS p hpS).2 τ O).1) (fun τ O => ((hS p hpS).2 τ O).2)
    exact ⟨hb.1, hb.2.1⟩
  have hfunc : (fun γ' : {γ' : TermDef.Term D u u' F0 what₂ //
      (Corank.TermScal D γ γ' ∧ EligAt γ' w') ∧ locT M δ γ' = x.1} =>
        PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ'.1 w') =
      fun γ' => (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p)) *
        ((PairVal.orbT D u u' F0 what₂ γ'.1 (zT γ'.1)).ncard : ℂ) := by
    funext γ'
    rw [hC γ'.1 w' γ'.2.1.2, γ'.2.2]
  rw [hfunc]
  have hv : (∏ᶠ p, fL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p)) =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w' (x.1 p)) *
        ∏ᶠ p, kL M δ (D.mem u).A.T (D.mem u').A.T p w' (thT M δ γ p) (x.1 p) := by
    rw [← finprod_mul_distrib]
    · exact finprod_congr fun p => fL_eq p w' _ _
    · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
      by_contra h
      exact (Function.mem_mulSupport.1 hp) (hone p h).1
    · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
      by_contra h
      exact (Function.mem_mulSupport.1 hp) (hone p h).2
  rw [hv]
  exact (hcnt x).mul_left _

theorem fiberTupleSum_of {L : CntLocal.LocSp D M} {θ0 : ∀ p, Option ((M p).Cls D.R.rS)}
    (hU : LocUnram M δ u u' θ0) (hR : ThRestricted M δ u u' F0 what₂ θ0)
    (hC : CoefProd M δ u u' F0 what₂) (hN : FiberCount M δ L u u' F0 what₂) : FiberTupleSum M δ L u u' F0 what₂ := by
  intro nc hnc ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  obtain ⟨hres, hcnt⟩ := hN nc hnc ϖ hϖ w hG γ₀ w₀ hγ₀ hk
  refine ⟨hres, fun x => ?_⟩
  obtain ⟨S, hS⟩ := hU w hG
  have hRf := hR γ₀ w₀ hγ₀
  have hone : ∀ p ∉ S ∪ hRf.toFinset ∪ x.2.toFinset,
      hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p) = 1 ∧
        eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p) = 1 := by
    intro p hp
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hth : thT M δ γ₀ p = θ0 p := by
      by_contra h
      exact hp (Finset.mem_union_left _ (Finset.mem_union_right _ (hRf.mem_toFinset.2 h)))
    have hx : x.1 p = x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
      by_contra h
      exact hp (Finset.mem_union_right _ (x.2.mem_toFinset.2 h))
    rw [hx, hth]
    have hb := base_factors (fun τ O => ((hS p hpS).2 τ O).1) (fun τ O => ((hS p hpS).2 τ O).2)
    exact ⟨hb.1, hb.2.2⟩
  have hfunc : (fun γ : {γ : TermDef.Term D u u' F0 what₂ //
      (EligAt γ w ∧ kind w = kind w₀ ∧ thT M δ γ = thT M δ γ₀) ∧ locT M δ γ = x.1} =>
        (PairVal.massTerm γ.1 : ℂ) * PairVal.cAt (PairVal.vRdef D u u' F0 what₂ δ M) γ.1 w) =
      fun γ => (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
        ((PairVal.massTerm γ.1 : ℂ) * ((PairVal.orbT D u u' F0 what₂ γ.1 (zT γ.1)).ncard : ℂ)) := by
    funext γ
    rw [hC γ.1 w γ.2.1.1, γ.2.2]
    ring
  rw [hfunc]
  have hv : (n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
      (∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) =
      (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
        ((n0 nc (D.mem u).A.T (D.mem u').A.T w : ℂ) * (dnT M δ L ϖ γ₀ : ℂ) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) := by
    rw [show (∏ᶠ p, gL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p)) =
        (∏ᶠ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (x.1 p)) *
          ∏ᶠ p, eL M δ (D.mem u).A.T (D.mem u').A.T p w (thT M δ γ₀ p) (x.1 p) from by
      rw [← finprod_mul_distrib]
      · exact finprod_congr fun p => gL_eq p w _ _
      · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
        by_contra h
        exact (Function.mem_mulSupport.1 hp) (hone p h).1
      · refine (S ∪ hRf.toFinset ∪ x.2.toFinset).finite_toSet.subset fun p hp => ?_
        by_contra h
        exact (Function.mem_mulSupport.1 hp) (hone p h).2]
    ring
  rw [hv]
  exact (hcnt x).mul_left _

end Tup

end Formalism.L2.SG.LsDatumB
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SpanAtMono
noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hJ_add_r {n : ℕ} (ε : Fin n → Bool) (a y z : Fin n → ℂ) : hJ ε a (y + z) = hJ ε a y + hJ ε a z := by
  unfold hJ
  rw [Matrix.mulVec_add, dotProduct_add]

theorem hJ_smul_r {n : ℕ} (ε : Fin n → Bool) (a y : Fin n → ℂ) (c : ℂ) : hJ ε a (c • y) = c * hJ ε a y := by
  unfold hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_zero_r {n : ℕ} (ε : Fin n → Bool) (a : Fin n → ℂ) : hJ ε a 0 = 0 := by
  unfold hJ
  rw [Matrix.mulVec_zero, dotProduct_zero]

theorem hJ_sum_r {n : ℕ} {ι : Type} [Fintype ι] (ε : Fin n → Bool) (a : Fin n → ℂ) (c : ι → ℂ)
    (y : ι → Fin n → ℂ) : hJ ε a (∑ i, c i • y i) = ∑ i, c i * hJ ε a (y i) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

section Pts

variable {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F)

abbrev psiV (p : (VS D).V) : Fin X.B.I.n → ℂ := rv X.B.I v (X.crd p)

theorem psiV_add (p q : (VS D).V) : psiV X v (p + q) = psiV X v p + psiV X v q := by
  simp only [psiV, rv]
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp [HidaSetting.crd, crdOf]

theorem psiV_smul (c : D.host.E) (p : (VS D).V) : psiV X v (c • p) = embS D (X.pl v) c • psiV X v p := by
  unfold psiV rv HidaSetting.crd crdOf
  rw [← Matrix.mulVec_smul]; congr 1; funext i
  simp [X.φ_eq]

def psiHom : (VS D).V →+ (Fin X.B.I.n → ℂ) := AddMonoidHom.mk' (psiV X v) (psiV_add X v)

theorem psiV_sum {ι : Type} (J : Finset ι) (f : ι → (VS D).V) : psiV X v (∑ i ∈ J, f i) = ∑ i ∈ J, psiV X v (f i) := by exact map_sum (psiHom X v) f J

theorem psiV_zero : psiV X v 0 = 0 := by exact map_zero (psiHom X v)

theorem hJ_psiV (p q : (VS D).V) :
    hJ (X.B.I.ε v) (psiV X v p) (psiV X v q) = embS D (X.pl v) ((VS D).hT p q) :=
  Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q

theorem psiV_span (y : Fin X.B.I.n → ℂ) : ∃ c : Fin X.B.I.n → ℂ, y = ∑ i, c i • psiV X v (X.bas i) := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  refine ⟨X.B.I.P v *ᵥ y, ?_⟩
  have h1 : ∀ i, psiV X v (X.bas i) = (X.B.I.P v)⁻¹ *ᵥ (fun k => if i = k then (1 : ℂ) else 0) := by
    intro i
    unfold psiV rv HidaSetting.crd crdOf
    congr 1
    funext k
    by_cases h : i = k <;> simp [h]
  simp only [h1, ← Matrix.mulVec_smul]
  rw [← Matrix.mulVec_sum, ← pi_eq_sum_univ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu,
    Matrix.one_mulVec]

theorem cplx_comb {ι : Type} [Fintype ι] (g : ι → (VS D).V) (U : Submodule D.host.E (VS D).V) (c : ι → ℂ)
    (hc : ∀ p ∈ U, ∑ i, c i * embS D (X.pl v) ((VS D).hT p (g i)) = 0) :
    ∑ i, c i • psiV X v (g i) ∈ spanAt X v (perpS (VS D) U ⊓ Submodule.span D.host.E (Set.range g)) := by
  letI : Algebra D.host.E ℂ := (embS D (X.pl v)).toAlgebra
  let b := Module.Basis.ofVectorSpace D.host.E ℂ
  let J := Finset.univ.biUnion (fun i : ι => (b.repr (c i)).support)
  let s : Module.Basis.ofVectorSpaceIndex D.host.E ℂ → ι → D.host.E := fun j i => b.repr (c i) j
  let w : Module.Basis.ofVectorSpaceIndex D.host.E ℂ → (VS D).V := fun j => ∑ i, s j i • g i
  have hw : ∀ j, w j ∈ perpS (VS D) U ⊓ Submodule.span D.host.E (Set.range g) := by
    intro j
    refine ⟨fun p hp => ?_,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩
    have h1 : ∑ i, (VS D).hT p (g i) • c i = 0 := by
      rw [← hc p hp]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    have h2 := congrArg (fun z => b.repr z j) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
    show (VS D).hT p (w j) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [w, map_sum, map_smul, smul_eq_mul]
    rw [← h2]; refine Finset.sum_congr rfl fun i _ => ?_; simp only [s]; ring
  have hc' : ∀ i, c i = ∑ j ∈ J, embS D (X.pl v) (s j i) * b j := by
    intro i
    conv_lhs => rw [← b.linearCombination_repr (c i)]
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun i => (b.repr (c i)).support) (Finset.mem_univ i))]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    · intro j _; simp
  have hsum : ∑ i, c i • psiV X v (g i) = ∑ j ∈ J, b j • psiV X v (w j) := by
    simp only [w, psiV_sum, psiV_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc' i, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w j, hw j, rfl⟩)

theorem spanAt_mono {U U' : Submodule D.host.E (VS D).V} (h : U ≤ U') : spanAt X v U ≤ spanAt X v U' := by
  unfold spanAt
  exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.mpr h))

theorem cplx_part1 {r : ℕ} {T : D.host.E} (F : FlagG (VS D) r T) (V0 : Submodule D.host.E (VS D).V)
    (hsup : perpS (VS D) V0 ⊔ F.X = F.XplusPerp) (y : Fin X.B.I.n → ℂ)
    (hy : ∀ p ∈ F.Xplus, hJ (X.B.I.ε v) (psiV X v p) y = 0) :
    ∃ x ∈ spanAt X v F.X, ∀ p ∈ V0, hJ (X.B.I.ε v) (psiV X v p) (y - x) = 0 := by
  obtain ⟨c, rfl⟩ := psiV_span X v y
  have hmem := cplx_comb X v X.bas F.Xplus c (fun p hp => by
    rw [← hy p hp, hJ_sum_r]
    exact Finset.sum_congr rfl fun i _ => by rw [hJ_psiV])
  have hmem' := spanAt_mono X v (inf_le_left.trans (le_of_eq rfl) :
    perpS (VS D) F.Xplus ⊓ Submodule.span D.host.E (Set.range X.bas) ≤ F.XplusPerp) hmem
  rw [← hsup] at hmem'
  refine Submodule.span_induction (p := fun y _ => ∃ x ∈ spanAt X v F.X,
      ∀ p ∈ V0, hJ (X.B.I.ε v) (psiV X v p) (y - x) = 0) ?_ ?_ ?_ ?_ hmem'
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, ha, x, hx, rfl⟩ := Submodule.mem_sup.1 hw
    refine ⟨psiV X v x, Submodule.subset_span ⟨x, hx, rfl⟩, fun p hp => ?_⟩
    show hJ (X.B.I.ε v) (psiV X v p) (psiV X v (a + x) - psiV X v x) = 0
    rw [psiV_add, add_sub_cancel_right, hJ_psiV, ha p hp, map_zero]
  · exact ⟨0, Submodule.zero_mem _, fun p _ => by rw [sub_zero, hJ_zero_r]⟩
  · rintro y1 y2 - - ⟨x1, hx1, h1⟩ ⟨x2, hx2, h2⟩
    refine ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, fun p hp => ?_⟩
    rw [show y1 + y2 - (x1 + x2) = (y1 - x1) + (y2 - x2) by abel, hJ_add_r, h1 p hp, h2 p hp, add_zero]
  · rintro a y1 - ⟨x1, hx1, h1⟩
    refine ⟨a • x1, Submodule.smul_mem _ _ hx1, fun p hp => ?_⟩
    rw [← smul_sub, hJ_smul_r, h1 p hp, mul_zero]

theorem cplx_part3 {r : ℕ} {T : D.host.E} (F : FlagG (VS D) r T) (V0 I : Submodule D.host.E (VS D).V)
    (hinf : perpS (VS D) V0 ⊓ F.X = I) (y : Fin X.B.I.n → ℂ) (hyX : y ∈ spanAt X v F.X)
    (hy : ∀ p ∈ V0, hJ (X.B.I.ε v) (psiV X v p) y = 0) : y ∈ spanAt X v I := by
  have hle : spanAt X v F.X ≤ Submodule.span ℂ (Set.range fun a => psiV X v (F.e a)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, hp, rfl⟩
    refine Submodule.span_induction (p := fun p _ => psiV X v p ∈
      Submodule.span ℂ (Set.range fun a => psiV X v (F.e a))) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a, rfl⟩; exact Submodule.subset_span ⟨a, rfl⟩
    · rw [psiV_zero]; exact Submodule.zero_mem _
    · intro x1 x2 _ _ h1 h2; rw [psiV_add]; exact Submodule.add_mem _ h1 h2
    · intro a x1 _ h1; rw [psiV_smul]; exact Submodule.smul_mem _ _ h1
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hyX)
  have hmem := cplx_comb X v F.e V0 c (fun p hp => by
    rw [← hy p hp, hJ_sum_r]
    exact Finset.sum_congr rfl fun i _ => by rw [hJ_psiV])
  rw [← hinf]
  exact hmem

end Pts

def NFRat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
      perpS (VS D) (fixedSubspaceOfRepresentative X q) ⊓ (lf D (X.Fu u)).fl.X = Isp (lf D (X.Fu u)).fl (frq X q).fl ∧
      perpS (VS D) (fixedSubspaceOfRepresentative X q) ⊔ (lf D (X.Fu u)).fl.X = (lf D (X.Fu u)).fl.XplusPerp ∧
      perpS (VS D) (fixedSubspaceOfRepresentative X q) ⊔ (frq X q).fl.X = (frq X q).fl.XplusPerp

theorem cplxNF_of (h : NFRat) : CplxNF := by
  intro D X u u' Λ Λ' q hrel hG v
  obtain ⟨h1, h2, h3⟩ := h D X u u' Λ Λ' q hrel hG
  exact ⟨cplx_part1 X v _ _ h2, cplx_part1 X v _ _ h3, cplx_part3 X v _ _ _ h1⟩

end PI.SchurPlaces
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClmEqZeroOfSpan
noncomputable section

open scoped InnerProductSpace
open Matrix Formalism.MainNotions.S

namespace PI.SchurPlaces

section Tens

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem eq_of_inner_span (tens : (∀ i, V i) → W) (hspan : Submodule.span ℂ (Set.range tens) = ⊤) {a b : W}
    (h : ∀ z, ⟪tens z, a⟫_ℂ = ⟪tens z, b⟫_ℂ) : a = b := by
  have h2 : ∀ w ∈ Submodule.span ℂ (Set.range tens), ⟪w, a - b⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      rw [inner_sub_right, h z, sub_self]
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  have h3 := h2 (a - b) (by rw [hspan]; exact Submodule.mem_top)
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

theorem prod_upd_left (y z : ∀ i, V i) (i₀ : ι) (b : V i₀) :
    ∏ i, ⟪Function.update y i₀ b i, z i⟫_ℂ = ⟪b, z i₀⟫_ℂ * ∏ i ∈ Finset.univ.erase i₀, ⟪y i, z i⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem prod_upd_right (y z : ∀ i, V i) (i₀ : ι) (c : V i₀) :
    ∏ i, ⟪y i, Function.update z i₀ c i⟫_ℂ = ⟪y i₀, c⟫_ℂ * ∏ i ∈ Finset.univ.erase i₀, ⟪y i, z i⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

variable (tens : (∀ i, V i) → W) (hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
  (hspan : Submodule.span ℂ (Set.range tens) = ⊤)

include hin hspan in
theorem tens_upd_add (x : ∀ i, V i) (i₀ : ι) (p q : V i₀) :
    tens (Function.update x i₀ (p + q)) = tens (Function.update x i₀ p) + tens (Function.update x i₀ q) := by
  refine eq_of_inner_span tens hspan fun z => ?_
  rw [inner_add_right, hin, hin, hin, prod_upd_right, prod_upd_right, prod_upd_right, inner_add_right, add_mul]

include hin hspan in
theorem tens_upd_smul (x : ∀ i, V i) (i₀ : ι) (c : ℂ) (p : V i₀) :
    tens (Function.update x i₀ (c • p)) = c • tens (Function.update x i₀ p) := by
  refine eq_of_inner_span tens hspan fun z => ?_
  rw [inner_smul_right, hin, hin, prod_upd_right, prod_upd_right, inner_smul_right, mul_assoc]

def insertLocal (x : ∀ i, V i) (i₀ : ι) : V i₀ →ₗ[ℂ] W where
  toFun p := tens (Function.update x i₀ p)
  map_add' p q := tens_upd_add tens hin hspan x i₀ p q
  map_smul' c p := tens_upd_smul tens hin hspan x i₀ c p

end Tens

theorem clm_eq_zero_of_span {W W' : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [NormedAddCommGroup W']
    [InnerProductSpace ℂ W'] {S : Set W'} (hS : Submodule.span ℂ S = ⊤) (P : W' →L[ℂ] W) (h : ∀ w ∈ S, P w = 0) :
    P = 0 := by
  ext w
  have h1 : (P : W' →ₗ[ℂ] W) = ((0 : W' →L[ℂ] W) : W' →ₗ[ℂ] W) :=
    LinearMap.ext_on hS (fun v hv => by simp [h v hv])
  exact LinearMap.congr_fun h1 w

theorem jm_allPos' (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  unfold Formalism.REAL.Jm allPos
  simp

theorem memU_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  simp only [UJset, Set.mem_setOf_eq, Formalism.REAL.inUJ, jm_allPos', Matrix.mul_one]

theorem memU_mul {k : ℕ} {a b : Matrix (Fin k) (Fin k) ℂ} (ha : a ∈ UJset (allPos k)) (hb : b ∈ UJset (allPos k)) :
    a * b ∈ UJset (allPos k) := by
  rw [memU_iff] at *
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha, Matrix.one_mul, hb]

theorem memU_star {k : ℕ} {a : Matrix (Fin k) (Fin k) ℂ} (ha : a ∈ UJset (allPos k)) : aᴴ ∈ UJset (allPos k) := by
  rw [memU_iff] at *
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 ha

theorem memU_rinv {k : ℕ} {a : Matrix (Fin k) (Fin k) ℂ} (ha : a ∈ UJset (allPos k)) : a * aᴴ = 1 :=
  mul_eq_one_comm.1 ((memU_iff a).1 ha)

theorem memU_one (k : ℕ) : (1 : Matrix (Fin k) (Fin k) ℂ) ∈ UJset (allPos k) := by
  rw [memU_iff]; simp

private theorem inner_apply_eq_inner_conjTranspose_apply_of_isHCTypeU {k : ℕ} {u : Fin k → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin k) (Fin k) ℂ → H →L[ℂ] H} (hσ : IsHCTypeU k u σ) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ UJset (allPos k)) (v w : H) : ⟪v, σ h w⟫_ℂ = ⟪σ hᴴ v, w⟫_ℂ := by
  obtain ⟨_, _, ⟨⟨h1, hmul⟩, hnorm, _⟩, _⟩ := hσ
  have hs : hᴴ ∈ UJset (allPos k) := memU_star hh
  have e : hᴴ * h = 1 := (memU_iff h).mp hh
  have hinv : σ hᴴ (σ h w) = w := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hs _ hh, e, h1, ContinuousLinearMap.one_apply]
  let L : H →ₗᵢ[ℂ] H := ⟨(σ hᴴ : H →ₗ[ℂ] H), fun x => hnorm _ hs x⟩
  have key := L.inner_map_map v (σ h w)
  change ⟪σ hᴴ v, σ hᴴ (σ h w)⟫_ℂ = _ at key
  rw [hinv] at key
  exact key.symm

private theorem inner_tens_apply_eq_inner_update_adjoint {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (tens : (∀ i, V i) → W) (hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hspan : Submodule.span ℂ (Set.range tens) = ⊤) (i₀ : ι) (f g : V i₀ →L[ℂ] V i₀)
    (hfg : ∀ a b, ⟪a, f b⟫_ℂ = ⟪g a, b⟫_ℂ) (T : W →L[ℂ] W)
    (hT : ∀ z, T (tens z) = tens (Function.update z i₀ (f (z i₀)))) (y : ∀ i, V i) (w : W) :
    ⟪tens y, T w⟫_ℂ = ⟪tens (Function.update y i₀ (g (y i₀))), w⟫_ℂ := by
  have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [hT, hin, hin, prod_upd_right, prod_upd_left, hfg]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), inner_add_right, inner_add_right, ha, hb]
  | smul c a _ ha => rw [map_smul, inner_smul_right, inner_smul_right, ha]

theorem schurCoreA_of (h7 : Formalism.MainNotions.NonGenericAndKTwoTheorems.adm7) : SchurCoreA := by
  classical
  unfold SchurCoreA
  intro k ι _ V V' _ _ _ _ _ _ W W' _ _ _ _ _ _ tens tens' hin hspan hin' hspan' π π' lam lam' hπ hπ' i₀ hne C hC P hP
  have hπ1 : ∀ i, π i 1 = 1 := fun i => by
    obtain ⟨_, _, ⟨⟨h1, _⟩, _⟩, _⟩ := hπ i
    exact h1
  have hπ'1 : ∀ i, π' i 1 = 1 := fun i => by
    obtain ⟨_, _, ⟨⟨h1, _⟩, _⟩, _⟩ := hπ' i
    exact h1
  have hπ'mul : ∀ a ∈ UJset (allPos k), ∀ b ∈ UJset (allPos k), π' i₀ (a * b) = π' i₀ a ∘L π' i₀ b := by
    obtain ⟨_, _, ⟨⟨_, hm⟩, _⟩, _⟩ := hπ' i₀
    exact hm
  have key : ∀ h ∈ UJset (allPos k), ∀ (y : ∀ i, V i) (y' : ∀ i, V' i),
      ⟪tens y, P (tens' (Function.update y' i₀ (π' i₀ (C i₀ * h * (C i₀)ᴴ) (y' i₀))))⟫_ℂ =
        ⟪tens (Function.update y i₀ (π i₀ hᴴ (y i₀))), P (tens' y')⟫_ℂ := by
    intro h hh y y'
    have hM : ∀ i, Function.update (fun _ => (1 : Matrix (Fin k) (Fin k) ℂ)) i₀ h i ∈ UJset (allPos k) := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        simpa using hh
      · rw [Function.update_of_ne hi]
        exact memU_one k
    obtain ⟨A, B, hA, hB, hAB⟩ := hP _ hM
    have hA' : ∀ z, A (tens z) = tens (Function.update z i₀ (π i₀ h (z i₀))) := by
      intro z
      rw [hA]
      congr 1
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp
      · simp [Function.update_of_ne hi, hπ1]
    have hB' : ∀ z, B (tens' z) = tens' (Function.update z i₀ (π' i₀ (C i₀ * h * (C i₀)ᴴ) (z i₀))) := by
      intro z
      rw [hB]
      congr 1
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp
      · simp [Function.update_of_ne hi, memU_rinv (hC i), hπ'1]
    rw [← hB', ← ContinuousLinearMap.comp_apply P B, ← hAB, ContinuousLinearMap.comp_apply]
    exact inner_tens_apply_eq_inner_update_adjoint tens hin hspan i₀ (π i₀ h) (π i₀ hᴴ) (fun a b => inner_apply_eq_inner_conjTranspose_apply_of_isHCTypeU (hπ i₀) hh a b) A hA' y _
  have main : ∀ (x : ∀ i, V i) (x' : ∀ i, V' i), ⟪tens x, P (tens' x')⟫_ℂ = 0 := by
    intro x x'
    obtain ⟨Q, hQ⟩ : ∃ Q : V' i₀ →L[ℂ] V i₀, ∀ p q,
        ⟪p, Q q⟫_ℂ = ⟪tens (Function.update x i₀ p), P (tens' (Function.update x' i₀ q))⟫_ℂ := by
      let S : V i₀ →L[ℂ] W := LinearMap.toContinuousLinearMap (insertLocal tens hin hspan x i₀)
      let S' : V' i₀ →L[ℂ] W' := LinearMap.toContinuousLinearMap (insertLocal tens' hin' hspan' x' i₀)
      refine ⟨ContinuousLinearMap.adjoint S ∘L P ∘L S', fun p q => ?_⟩
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
      rfl
    have hint : ∀ h ∈ UJset (allPos k), Q ∘L π' i₀ (C i₀ * h * (C i₀)ᴴ) = π i₀ h ∘L Q := by
      intro h hh
      ext q
      apply ext_inner_left ℂ
      intro p
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hQ, inner_apply_eq_inner_conjTranspose_apply_of_isHCTypeU (hπ i₀) hh, hQ]
      have e := key h hh (Function.update x i₀ p) (Function.update x' i₀ q)
      simp only [Function.update_idem, Function.update_self] at e
      exact e
    have hc := hC i₀
    have hR : ∀ h ∈ UJset (allPos k), (Q ∘L π' i₀ (C i₀)) ∘L π' i₀ h = π i₀ h ∘L (Q ∘L π' i₀ (C i₀)) := by
      intro h hh
      have hch : C i₀ * h ∈ UJset (allPos k) := memU_mul hc hh
      have hchc : C i₀ * h * (C i₀)ᴴ ∈ UJset (allPos k) := memU_mul hch (memU_star hc)
      have e : C i₀ * h = C i₀ * h * (C i₀)ᴴ * C i₀ := by
        rw [Matrix.mul_assoc (C i₀ * h), (memU_iff _).mp hc, Matrix.mul_one]
      rw [ContinuousLinearMap.comp_assoc, ← hπ'mul _ hc _ hh, e, hπ'mul _ hchc _ hc,
        ← ContinuousLinearMap.comp_assoc Q, hint h hh, ContinuousLinearMap.comp_assoc (π i₀ h)]
    have hR0 : Q ∘L π' i₀ (C i₀) = 0 :=
      h7 k (lam i₀) (lam' i₀) (V i₀) (V' i₀) (π i₀) (π' i₀) (hπ i₀) (hπ' i₀) hne _ hR
    have hQ0 : Q = 0 := by
      have e1 : π' i₀ (C i₀) ∘L π' i₀ (C i₀)ᴴ = 1 := by
        rw [← hπ'mul _ hc _ (memU_star hc), memU_rinv hc, hπ'1]
      calc Q = Q ∘L (π' i₀ (C i₀) ∘L π' i₀ (C i₀)ᴴ) := by
            rw [e1]
            ext
            simp
        _ = (Q ∘L π' i₀ (C i₀)) ∘L π' i₀ (C i₀)ᴴ := (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = 0 := by rw [hR0, ContinuousLinearMap.zero_comp]
    have e2 := hQ (x i₀) (x' i₀)
    rw [Function.update_eq_self, Function.update_eq_self, hQ0] at e2
    simpa using e2.symm
  apply clm_eq_zero_of_span hspan' P
  rintro w ⟨x', rfl⟩
  exact eq_of_inner_span (a := P (tens' x')) (b := 0) tens hspan (fun x => by rw [main x x', inner_zero_right])

end PI.SchurPlaces
end
end
