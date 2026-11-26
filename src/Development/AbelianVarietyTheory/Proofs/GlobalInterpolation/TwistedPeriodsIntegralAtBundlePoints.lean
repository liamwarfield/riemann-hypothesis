module

public import Formalism.LocalToGlobal.HermitianForms.TiedBrRep
public import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
public import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPerTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainData
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsView

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistOfIntegralRows
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistsReductionPlaceTuples
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistsReductionPlaceTuples
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField

namespace GlobalTheory.PerRedU

theorem perTwAt_of_perDecTw {D : D7} {Dx : DivX D} {T : TwForms D} (hD : DGamDef D) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (h : Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) :
    ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
        ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ →
          y = 0 ∨ -ur D w (Formalism.MainNotions.WeilJacquetShalikaLaw.vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ) := by
  intro x hx F hF _
  obtain ⟨pc, hs, hi⟩ := h
  choose y hy hv using hi x hx F hF
  refine ⟨∑ c, ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c, ?_, fun w hw => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hs, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, map_inv₀, map_natCast, hy c]
  · refine Finset.sum_induction _ (fun t => t = 0 ∨ -ur D w (Formalism.MainNotions.WeilJacquetShalikaLaw.vDG D u w) ≤ (vAdd (D.plEq w) t : ℝ))
      (fun a b ha hb => Formalism.MainNotions.WeightDegreeSizes.pair_add_ge D w ha hb) (Or.inl rfl) fun c _ => ?_
    rcases hv c w hw with h0 | h0
    · left; rw [h0, mul_zero]
    by_cases hy0 : y c = 0
    · left; rw [hy0, mul_zero]
    right
    have hn0 : ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [Formalism.MainNotions.OrbitPlaces.vAdd_mul w (inv_ne_zero hn0) hy0, Formalism.MainNotions.OrbitPlaces.vAdd_inv w hn0]
    have hb := Formalism.MainNotions.DIV.HookProducts.AdmPerTw.vAdd_dvd_le (D := D) w (D.mem u).C.DGam_pos.ne'
      (Formalism.MainNotions.DIV.HookProducts.AdmPerTw.card_stabilizer_dvd₂ hD T u μ c)
    have h0' : (0 : ℝ) ≤ (vAdd (D.plEq w) (y c) : ℝ) := by exact_mod_cast h0
    unfold Formalism.MainNotions.WeilJacquetShalikaLaw.vDG
    push_cast
    linarith

theorem exists_muAt_of_usedT {D : D7} {μ : D.what₂.Tup} (hU : Formalism.MainNotions.LocalQuadraticParts.UsedT D μ) (hμ : μ ≠ D.what₂.mu0) :
    ∃ w, μ = D.what₂.muAt w :=
  hU.resolve_left hμ

theorem admissiblePeriodTwists_of_periodDecompositions {D : D7} {Dx : DivX D} {T : TwForms D}
    (h : ∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) :
    Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T :=
  fun hD u μ hU hμ => perTwAt_of_perDecTw hD (h u μ hμ (exists_muAt_of_usedT hU hμ))

theorem main : ∀ (D : D7) (Dx : DivX D) (T : TwForms D), (∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) → Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T :=
  fun _ _ _ h => admissiblePeriodTwists_of_periodDecompositions h

end GlobalTheory.PerRedU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistsReductionPlaceTuplesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissiblePeriodTwists_reduction_placeTuples : ∀ (D : D7) (Dx : DivX D) (T : TwForms D), (∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) → Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T := by
  first | exact @GlobalTheory.PerRedU.main | exact GlobalTheory.PerRedU.main | (intros; apply GlobalTheory.PerRedU.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodDecompositionOfClasswiseTwistedPair
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodDecompositionOfClasswiseTwistedPair
noncomputable section

namespace GlobalTheory.PerRedTw

section Copied

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw _root_.Formalism.L2.Forms Matrix NumberField
open scoped BigOperators

theorem exists_orthonormal_frame_twisted (D : D7) : ∃ o : FrP D, o.IsON := by
  classical
  let _ := D.host.cmStar
  have hY : ∀ τ, ∃ Y : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ,
      IsUnit Y.det ∧ Yᴴ * (gramP D).map (embT D τ) * Y = 1 := by
    intro τ
    have hs := D.sp.X'_sig (embT D τ)
    rw [D.X'_posDef (embT D τ)] at hs
    dsimp only at hs
    obtain ⟨e, P, hP⟩ := hs
    have hJ : Formalism.UG.Jpq D.sp.X'.rank 0 = 1 := by
      ext i j
      rcases i with i | i
      · rcases j with j | j
        · simp [Formalism.UG.Jpq, Matrix.one_apply]
        · exact j.elim0
      · exact i.elim0
    have hcT : Formalism.UG.cT (starRingEnd ℂ) P.1 = P.1ᴴ := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [hcT, hJ] at hP
    let f : Fin D.sp.X'.rank ≃ Fin (D.R.N D.R.m - 1) := finCongr (rankP D)
    let g : Fin (D.R.N D.R.m - 1) ≃ Fin D.sp.X'.rank ⊕ Fin 0 := f.symm.trans e
    have hG : ((gramP D).map (embT D τ)).submatrix g.symm g.symm = (D.sp.X'.gram.map (embT D τ)).reindex e e := by
      ext i j
      simp [g, f, gramP, Matrix.reindex_apply, Matrix.submatrix_apply]
    refine ⟨P.1.submatrix g g, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self]; exact Matrix.isUnits_det_units P
    · have h1 : (gramP D).map (embT D τ) = (((gramP D).map (embT D τ)).submatrix g.symm g.symm).submatrix g g := by
        ext i j; simp
      rw [Matrix.conjTranspose_submatrix, h1, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hG, hP]
      exact Matrix.submatrix_one_equiv g
  choose Y hYu hY using hY
  exact ⟨⟨Y, hYu⟩, fun τ => Or.inl (hY τ)⟩

theorem nfAll_zero_tw {D : D7} (n : ℕ) (lam : D.what₂.Tau → DomWeight n) : nfAll lam 0 0 = 0 := by
  simp [nfAll, Formalism.REAL.fockF]

end Copied

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Forms Formalism.MainNotions.RT.PeriodPointConditions GlobalTheory.PerQ

attribute [local instance] MemberForms.clsPFin

variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
  {Tw : TwForms D} {Y : DivX D}

theorem eW_rep_o_tw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (o : FrP D)
    (z : (D.PTw u μ).Wrow) (hz : z ∈ (Tw.fm u μ).ptC) (c : (Tw.fm u μ).clsP) :
    ∃ Q ∈ CSpan (Tw.fm u μ).sg,
      (t.pt.val u μ hμ).eW z c = fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) Q := by
  have hF := ((t.pt.val u μ hμ).ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) ((t.pt.cls u μ hμ).y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ CSpan (Tw.fm u μ).sg := by
    have := CSpan_shW (Tw.fm u μ).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgTG at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : (t.pt.val u μ hμ).eW z c = fnOf _ (shiftOf (sgTG (Tw.fm u μ))) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hM : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (o.2 τ).ringInverse
  refine ⟨_, ?_, he.trans (fnOf_change _ _ _ _ hM Q0)⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hQ0')

open Classical in
theorem eW_resCTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) :
    (t.pt.val u μ hμ).eW (resCTw t u μ hμ c z) = fun c' => if c' = c then (t.pt.val u μ hμ).eW z c' else 0 := by
  classical
  unfold resCTw
  rw [LinearEquiv.apply_symm_apply]

theorem petersson_eq_sum_restrict_twist (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (a b : (D.PTw u μ).Wrow) (ha : a ∈ (Tw.fm u μ).ptC) (hb : b ∈ (Tw.fm u μ).ptC) :
    (Tw.fm u μ).ipP a b = ∑ c, (Tw.fm u μ).ipP (resCTw t u μ hμ c a) (resCTw t u μ hμ c b) := by
  classical
  obtain ⟨o, ho⟩ := exists_orthonormal_frame_twisted D
  choose P hP hPe using eW_rep_o_tw t u μ hμ o a ha
  choose Q hQ hQe using eW_rep_o_tw t u μ hμ o b hb
  rw [(t.pt.val u μ hμ).ipP o ho a b P Q hP hQ hPe hQe]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hP' : ∀ c', (if c' = c then P c' else 0) ∈ CSpan (Tw.fm u μ).sg := fun c' => by
    split_ifs
    · exact hP c'
    · exact Submodule.zero_mem _
  have hQ' : ∀ c', (if c' = c then Q c' else 0) ∈ CSpan (Tw.fm u μ).sg := fun c' => by
    split_ifs
    · exact hQ c'
    · exact Submodule.zero_mem _
  have hPe' : ∀ c', (t.pt.val u μ hμ).eW (resCTw t u μ hμ c a) c' =
      fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) (if c' = c then P c' else 0) := fun c' => by
    rw [eW_resCTw]
    dsimp only
    split_ifs
    · exact hPe c'
    · exact (map_zero _).symm
  have hQe' : ∀ c', (t.pt.val u μ hμ).eW (resCTw t u μ hμ c b) c' =
      fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) (if c' = c then Q c' else 0) := fun c' => by
    rw [eW_resCTw]
    dsimp only
    split_ifs
    · exact hQe c'
    · exact (map_zero _).symm
  rw [(t.pt.val u μ hμ).ipP o ho _ _ _ _ hP' hQ' hPe' hQe', Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    simp [hc', nfAll_zero_tw]
  · intro h; exact absurd (Finset.mem_univ c) h

open Classical in
def pcTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) (G : (D.PTw u μ).Mt) : ℂ :=
  if z ∈ (Tw.fm u μ).ptC then pcLTw t u μ hμ c z G
  else if h : Nonempty (Tw.fm u μ).clsP then
    (if c = Classical.choice h then ((Nat.card ((Tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) * (D.PTw u μ).period z G else 0)
  else 0

theorem perDecTw_of_at (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (h : PerDecTwT Y t u μ hμ) : Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ := by
  classical
  have hcard : ∀ c, ((Nat.card ((Tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) ≠ 0 := fun c =>
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨pcTw t u μ hμ, fun z G => ?_, fun x hx F hF c => ?_⟩
  · by_cases hz : z ∈ (Tw.fm u μ).ptC
    · have hG : t.ptE.jM u μ G ∈ (Tw.fm u μ).ptC := ((t.ptE.per u μ hμ).2.1) G
      rw [((t.ptE.per u μ hμ).2.2) z G, petersson_eq_sum_restrict_twist t u μ hμ _ _ hG hz]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [pcTw, if_pos hz, pcLTw]
      rw [← mul_assoc, inv_mul_cancel₀ (hcard c), one_mul]
    · by_cases hne : Nonempty (Tw.fm u μ).clsP
      · rw [Finset.sum_eq_single (Classical.choice hne)]
        · simp only [pcTw, if_neg hz, dif_pos hne, ↓reduceIte]
          rw [← mul_assoc, inv_mul_cancel₀ (hcard _), one_mul]
        · intro c _ hc
          simp only [pcTw, if_neg hz, dif_pos hne, if_neg hc, mul_zero]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · have hE : IsEmpty (Tw.fm u μ).clsP := not_nonempty_iff.mp hne
        have hz0 : z = 0 := (t.pt.val u μ hμ).eW.injective (funext fun c => hE.elim c)
        subst hz0
        simp
  · obtain ⟨y, hy, hv⟩ := h x hx F hF c
    have hz : (Tw.fm u μ).ptEmb x ∈ (Tw.fm u μ).ptC := (((t.pt.val u μ hμ).rat _).1 ⟨x, rfl⟩).1
    refine ⟨y, ?_, hv⟩
    simp only [pcTw, if_pos hz]
    exact hy

theorem reduction_perDecTw : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (tp : Formalism.L2.Host.TupTied D cf nch) (C : ColsTiedSym D) (Tw : TwForms D) (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (Y : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0), GlobalTheory.PerQ.PerDecTwT Y t u μ hμ → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ :=
  fun _ _ _ _ _ _ t _ u μ hμ h => perDecTw_of_at t u μ hμ h

end GlobalTheory.PerRedTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodDecompositionOfClasswiseTwistedPairStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPeriodDecomposition_of_classwiseTwistedPairingIntegral : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (tp : Formalism.L2.Host.TupTied D cf nch) (C : ColsTiedSym D) (Tw : TwForms D) (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (Y : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0), GlobalTheory.PerQ.PerDecTwT Y t u μ hμ → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ := by
  first | exact @GlobalTheory.PerRedTw.reduction_perDecTw | exact GlobalTheory.PerRedTw.reduction_perDecTw | (intros; apply GlobalTheory.PerRedTw.reduction_perDecTw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerDecTwTOfStd
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerTwClose

theorem perDecTwT_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.PerQ.RowInt I l Z → ∀ (cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch) (C : ColsTiedSym (I.rec7 l Z)) (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)) (Y : DivX (I.rec7 l Z)), I.StdTw l Z l0 t → ∀ u a ha, GlobalTheory.PerQ.PerDecTwT Y t u a ha := by
  intro B X I hI l Z l0 hR cf nch tp C t Y hS u a ha x hx F hF c
  have hP := (t.ptE.per u a ha).2.2
  classical
  have hres : ∀ z, GlobalTheory.PerQ.resCTw t u a ha c z = fun c' => if c' = c then z c' else 0 := by
    intro z
    apply (t.pt.val u a ha).eW.injective
    rw [GlobalTheory.PerQ.resCTw, LinearEquiv.apply_symm_apply]
    funext c' s
    have e1 := hS.2.2.eW u a ha (fun c' => if c' = c then z c' else 0) c' s s rfl
    have e2 := hS.2.2.eW u a ha z c' s s rfl
    refine Eq.trans ?_ e1.symm
    split_ifs
    all_goals first | exact e2 | rfl | (exfalso; contradiction)
  obtain ⟨y, hy, hyv⟩ := hR.tw u a F hF c
  have hyQ : y ∈ nabAt B.fields.emb (I.perIn u a).sgT ((I.perIn u a).S'.Lsh c.1 ((I.perIn u a).S'.rep c)) := by
    have := GlobalTheory.PeriodOnStep.Lsh_eq_N ((I.stX a).rep c).1.1.deco
    show y ∈ nabAt _ _ (((I.stX a).rep c).1.1.deco.1.Lsh)
    rw [this]; exact hy
  obtain ⟨b, hb⟩ := @GlobalTheory.T.classPairing_integral_form_row_isIntegral _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL _ _ (I.perIn u a) (l.ch u a) (l.per u a) (B.hcW u)
    (l.fmL u a).famP (((I.rec7 l Z).eMtTw u a).symm F) (t.ptE.jM u a (((I.rec7 l Z).eMtTw u a).symm F))
    (fun w => hP w _) c (fun p q => Classical.propDecidable (p = q)) y hyQ hyv x hx
  refine ⟨(b : B.fields.K), ?_, fun w _ => ?_⟩
  · show B.embLL (b : B.fields.K) = _
    rw [hb, GlobalTheory.PerQ.pcLTw, hres, hres]
    rfl
  · by_cases h0 : (b : B.fields.K) = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      unfold vAdd
      have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := (I.rec7 l Z).what₂.LL) ((I.rec7 l Z).plEq w) b
      have h2 := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 h0) one_ne_zero).2 h
      rw [WithZero.log_one] at h2
      exact neg_nonneg.mpr h2

end GlobalTheory.PerTwClose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistOfIntegralRows
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerTwClose

theorem twistedPeriodAdmissible_of_rowInt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.PerQ.RowInt I l Z → ∀ (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → ∀ Y : DivX (I.rec7 l Z), Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (I.rec7 l Z) Y (I.tw l l0 Z) := by
  intro B X I hOk hPins l Z l0 hRow nch tp hxi Y
  obtain ⟨C, hC, hLv⟩ := GlobalTheory.T.exists_standardColumnComparisons_trueColumns I hOk hPins l Z
  obtain ⟨t, ht⟩ := GlobalTheory.T.trueColumnChoice_exists_standardChainData I hOk hPins l Z l0 nch tp C hxi hC hLv
  have hT := GlobalTheory.PerTwClose.perDecTwT_of_std I hOk l Z l0 hRow (I.cf l Z) nch tp C t Y ht
  refine GlobalTheory.T.admissiblePeriodTwists_reduction_placeTuples (I.rec7 l Z) Y (I.tw l l0 Z) ?_
  intro u μ hμ _
  exact GlobalTheory.T.twistedPeriodDecomposition_of_classwiseTwistedPairingIntegral (I.rec7 l Z) (I.cf l Z) nch tp C (I.tw l l0 Z) t Y u μ hμ (hT u μ hμ)

end GlobalTheory.PerTwClose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodTwistOfIntegralRowsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_period_twist_of_integral_rows : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l), GlobalTheory.PerQ.RowInt I l Z → ∀ (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → ∀ Y : DivX (I.rec7 l Z), Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (I.rec7 l Z) Y (I.tw l l0 Z) := by
  first | exact @GlobalTheory.PerTwClose.twistedPeriodAdmissible_of_rowInt | exact GlobalTheory.PerTwClose.twistedPeriodAdmissible_of_rowInt | (intros; apply GlobalTheory.PerTwClose.twistedPeriodAdmissible_of_rowInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodsIntegralAtBundlePoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

theorem row_aPerTw_of_overCols : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints Q Lk := by
  intro Q hQ Bd Lk
  have h : Row0 Q H_aPerTw := by
    refine validForConstructedPointClasses_eventuallyWorkingClass (R := fun D O => Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D O.X O.ex.tw) (EvP.of_all fun _ K _ β hβ => ?_)
    refine GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView (fun D O => Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D O.X O.ex.tw) ?_ K β (hQ _ _ _ _ _ hβ)
    intro B f T w Z O nch cv _ _
    obtain ⟨tp, htp⟩ := cv.tup
    rw [cv.tw_eq]
    exact GlobalTheory.T.admissible_period_twist_of_integral_rows w.I w.ok w.pins w.l Z w.l0 cv.rowInt nch tp htp O.X
  exact Row0.row h Lk

end GlobalTheory.Fc.PeriodEntriesOverColumns
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedPeriodsIntegralAtBundlePointsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPeriods_integral_at_bundlePoints : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.TwistedPeriodAtBundlePoints Q Lk := by
  first | exact @GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPerTw_of_overCols | exact GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPerTw_of_overCols | (intros; apply GlobalTheory.Fc.PeriodEntriesOverColumns.row_aPerTw_of_overCols <;> assumption)
end
