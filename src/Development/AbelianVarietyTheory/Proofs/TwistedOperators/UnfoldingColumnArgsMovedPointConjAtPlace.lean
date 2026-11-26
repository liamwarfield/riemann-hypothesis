module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.StdFrames

namespace GlobalTheory.TopLevelInv

section ColCoord

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {D : D7}

theorem map_mt_cpt_colCoord (w : Pl D.host.E) (V : HSp D) (g : GA D V) :
    Matrix.map (Formalism.L2.Theta.mt V g) ((cpt w).comp (toEAf D)) = (loc w (Lev.finE V g)).val := rfl

theorem frAt_actO_colCoord (w : Pl D.host.E) {S T : HSp D} (β' : GL (Fin T.rank) (Lev.EAf D))
    (β : GL (Fin S.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) (x : WO S T) :
    GlobalTheory.FunObj.frAt w β' β (actO S T g h x) =
      (loc w (β'⁻¹ * Lev.finE T h * β')).val * GlobalTheory.FunObj.frAt w β' β x *
        (loc w (β⁻¹ * Lev.finE S g * β))⁻¹.val := by
  have e0 : ∀ y : WO S T, GlobalTheory.FunObj.frAt w β' β y =
      (loc w β'⁻¹).val * Matrix.map y ((cpt w).comp (toEAf D)) * (loc w β).val := by
    intro y
    rw [GlobalTheory.FunObj.frAt, GlobalTheory.FunObj.Comparison₂.fr, Matrix.map_mul, Matrix.map_mul]
    rfl
  have e1 : Matrix.map (actO S T g h x) ((cpt w).comp (toEAf D)) =
      (loc w (Lev.finE T h)).val * Matrix.map x ((cpt w).comp (toEAf D)) * (loc w (Lev.finE S g))⁻¹.val := by
    rw [actO, Matrix.map_mul, Matrix.map_mul, map_mt_cpt_colCoord, map_mt_cpt_colCoord, map_inv, map_inv]
  rw [e0, e0, e1]
  simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have hA : ∀ {c : Type} [Fintype c] (Y : Matrix (Fin T.rank) c (Kw w)), (loc w β').val * ((loc w β')⁻¹.val * Y) = Y := by
    intro c _ Y; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hB : (loc w β).val * ((loc w β)⁻¹.val * ((loc w (Lev.finE S g))⁻¹.val * (loc w β).val)) =
      (loc w (Lev.finE S g))⁻¹.val * (loc w β).val := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [hA, hB]

theorem loc_finE_u_colCoord {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (ht : t ∈ U) {X : Node} (hX : DefNode D.R.m X) {w : Pl D.host.E}
    (hw : w ∈ locPl G t) : loc w (Lev.finE (G.V X) (S.N.u X).1) = 1 := by
  classical
  obtain ⟨P', a, ⟨⟨es, hes, rfl⟩, -⟩, hsupp, hoff⟩ := S.N.u_supp X hX
  have hnot : ¬ Off S.N.S w := by
    intro h0
    have h3 := S.N.off w h0
    rcases Finset.mem_union.1 hw with h | h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      exact h3.1 ((G.pl.under_w hv).symm ▸ hv)
    · exact h3.2.1 t ht w h rfl
  obtain ⟨q, hq, hqw⟩ : ∃ q ∈ S.N.S, ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    unfold Off at hnot; push_neg at hnot; exact hnot
  have hz : cpt w (toEAf D ((∑ PP ∈ P', es PP) + cA D (∑ PP ∈ P', es PP))) = 0 := by
    have hA : ∀ PP ∈ P', cpt w (toEAf D (es PP)) = 0 := fun PP hPP =>
      (cpt_of_isIdemAt (hes PP hPP)).2 _ fun e => hoff PP hPP q hq (e ▸ hqw)
    have hB : ∀ PP ∈ P', cpt w (sg D (toEAf D (es PP))) = 0 := by
      intro PP hPP
      refine cpt_sg_eq_zero ((cpt_of_isIdemAt (hes PP hPP)).2 _ fun e => hoff PP hPP q hq ?_)
      rw [← e]; exact (natCast_mem_cP w q).2 hqw
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), toEAf_cA, map_sum]
    rw [Finset.sum_eq_zero hA, Finset.sum_eq_zero hB, add_zero]
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have h1 := congrArg (fun z => cpt w (toEAf D z)) (hsupp i j)
  simp only [map_mul, hz, zero_mul] at h1
  have h2 : cpt w (toEAf D (Formalism.L2.Theta.mt (G.V X) (S.N.u X).1 i j)) = cpt w (toEAf D ((1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) (AE D)) i j)) := by
    have := h1.symm
    rw [Matrix.sub_apply, map_sub, map_sub, sub_eq_zero] at this
    exact this
  change cpt w (toEAf D (Formalism.L2.Theta.mt (G.V X) (S.N.u X).1 i j)) = (1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) (Kw w)) i j
  rw [h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem submatrix_cast_mul_colCoord {K : Type} [CommRing K] {r n n' p r' p' : ℕ} (M : Matrix (Fin r) (Fin n) K)
    (N : Matrix (Fin n) (Fin p) K) (f : Fin r' → Fin r) (h : n' = n) (g : Fin p' → Fin p) :
    M.submatrix f (Fin.cast h) * N.submatrix (Fin.cast h) g = (M * N).submatrix f g :=
  Matrix.submatrix_mul_equiv M N f (finCongr h) g

end ColCoord

end GlobalTheory.TopLevelInv

namespace GlobalTheory.TopLevelInv

theorem conj_inv_inv_colCoord {Γ : Type} [Group Γ] (b f : Γ) : (b⁻¹ * f⁻¹ * b)⁻¹ = b⁻¹ * f * b := by group

theorem conj_inv_colCoord {Γ : Type} [Group Γ] (b f : Γ) : b⁻¹ * f⁻¹ * b = (b⁻¹ * f * b)⁻¹ := by group


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem colAt_movedPt_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), ∀ w ∈ locPl G t,
    ∀ x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      S.colAt t w (movedPt t j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) x) = colMove j (kapAt S t j hj k w) (S.colAt t w x) := by
  intro D T L sc G W U S t ht j hj k w hw x
  have hu := loc_finE_u_colCoord S ht (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega) hw
  set k' : FinPt G (.top (j + 1)) := (S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) with hk'def
  have hk : ∀ β : GL (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D),
      loc w (β⁻¹ * Lev.finE (G.V (.top (j + 1))) (k' : GA D (G.V (.top (j + 1)))) * β) =
      loc w (β⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * β) := by
    intro β
    simp only [hk'def, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hu, inv_one, one_mul, mul_one]
  have hκ : (kapAt S t j hj k w).val =
      (loc w ((S.βp (j + 1))⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * S.βp (j + 1))).val.submatrix
        (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := rfl
  have hκi : (kapAt S t j hj k w)⁻¹.val =
      (loc w ((S.βp (j + 1))⁻¹ * Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))) * S.βp (j + 1)))⁻¹.val.submatrix
        (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := by
    have h0 : (kapAt S t j hj k w)⁻¹.val =
        (loc w ((S.βp (j + 1))⁻¹ * (Lev.finE (G.V (.top (j + 1))) (k : GA D (G.V (.top (j + 1)))))⁻¹ *
          S.βp (j + 1))).val.submatrix (Fin.cast (topRank_eq G t w hj.le)) (Fin.cast (topRank_eq G t w hj.le)) := by
      rw [kapAt, ← map_inv]; rfl
    rw [h0, conj_inv_colCoord, map_inv]
  funext i
  rcases eq_or_ne i (j + 1) with rfl | h1
  · rw [colAt_eq S t w _ hj]
    simp only [movedPt, Function.update_self]
    rw [frAt_actO_colCoord]
    simp only [colMove, Function.update_self]
    rw [colAt_eq S t w x hj, hκ, inv_one, map_one, mul_one, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul,
      map_inv (Lev.finE (G.V (.top (j + 1)))), ← map_inv (loc w), conj_inv_inv_colCoord, hk, submatrix_cast_mul_colCoord]
  rcases eq_or_ne i j with rfl | h2
  · rw [colAt_eq S t w _ (show i < D.R.m by omega)]
    rw [movedPt, Function.update_of_ne (show (⟨i, by omega⟩ : Fin D.R.m) ≠ ⟨i + 1, hj⟩ by simp [Fin.ext_iff]),
      Function.update_self]
    rw [frAt_actO_colCoord]
    simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_self, colAt_eq S t w x (show i < D.R.m by omega), hκi, inv_one,
      map_one, mul_one, inv_mul_cancel, map_one, inv_one, Units.val_one, Matrix.mul_one,
      map_inv (Lev.finE (G.V (.top (i + 1)))), conj_inv_colCoord, map_inv (loc w), hk, submatrix_cast_mul_colCoord]
  by_cases hi : i < D.R.m
  · have hm : movedPt t j hj k' x ⟨i, hi⟩ = x ⟨i, hi⟩ := by
      rw [movedPt, Function.update_of_ne (show (⟨i, hi⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ by simp [Fin.ext_iff, h1]),
        Function.update_of_ne (show (⟨i, hi⟩ : Fin D.R.m) ≠ ⟨j, by omega⟩ by simp [Fin.ext_iff, h2])]
    simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_of_ne h2, colAt_eq S t w _ hi, colAt_eq S t w x hi, hm]
  · simp only [colMove]
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
    simp only [GridChoice.colAt, dif_neg hi]

end GlobalTheory.TopLevelInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingColumnArgs_movedPoint_conj_atPlace : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))), ∀ w ∈ locPl G t,
    ∀ x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)),
      S.colAt t w (movedPt t j hj ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) x) = colMove j (kapAt S t j hj k w) (S.colAt t w x) := by
  first | exact @GlobalTheory.TopLevelInv.colAt_movedPt_conj | exact GlobalTheory.TopLevelInv.colAt_movedPt_conj | (intros; apply GlobalTheory.TopLevelInv.colAt_movedPt_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfield
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem integral_eq_sum_of_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKt : μ K ≠ ⊤) {S : Set G} (hS : IsCompact S)
    (hSK : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) (f : G → ℂ) (hf : ∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) :
    ∃ t : Finset (G ⧸ K), ∫ g in S, f g ∂μ = ∑ Q ∈ t, f Q.out * μ.real K := by
  classical
  set q : G → G ⧸ K := QuotientGroup.mk

  have hcov : S ⊆ ⋃ s ∈ S, s • (K : Set G) := fun s hs =>
    Set.mem_biUnion hs ⟨1, one_mem K, by simp⟩
  obtain ⟨b, hbS, hbf, hb⟩ := hS.elim_finite_subcover_image (fun s _ => hKo.smul s) hcov
  have hfin : (q '' S).Finite := by
    refine (hbf.image q).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg, hy⟩ := Set.mem_iUnion₂.1 (hb hs)
    refine ⟨g, hg, ?_⟩
    obtain ⟨y, hy, rfl⟩ := hy
    simp only [smul_eq_mul, q]
    exact (QuotientGroup.mk_mul_of_mem g hy).symm
  have hout : ∀ Q ∈ q '' S, Q.out ∈ S := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hh]; exact hSK s hs h h.2
  obtain ⟨T, hT⟩ : ∃ T : Finset (G ⧸ K), ∀ Q, Q ∈ T ↔ Q ∈ q '' S :=
    ⟨hfin.toFinset, fun Q => hfin.mem_toFinset⟩
  have hSeq : S = ⋃ Q ∈ T, Q.out • (K : Set G) := by
    ext g
    simp only [Set.mem_iUnion, hT, exists_prop]
    constructor
    · intro hg
      refine ⟨q g, ⟨g, hg, rfl⟩, ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨h⁻¹, (h⁻¹).2, ?_⟩
      simp [q, hh, mul_assoc]
    · rintro ⟨Q, hQ, y, hy, rfl⟩
      exact hSK _ (hout Q hQ) y hy
  have hconst : ∀ Q ∈ q '' S, ∀ y ∈ Q.out • (K : Set G), f y = f Q.out := by
    rintro Q hQ _ ⟨y, hy, rfl⟩
    exact hf _ (hout Q hQ) y hy
  refine ⟨T, ?_⟩
  rw [hSeq, integral_biUnion_finset]
  · refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [hT] at hQ
    rw [setIntegral_congr_fun (hKo.smul _).measurableSet (hconst Q hQ), setIntegral_const,
      measureReal_def, measure_smul, ← measureReal_def, Complex.real_smul, mul_comm]
  · exact fun Q _ => (hKo.smul _).measurableSet
  · intro Q _ Q' _ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', he⟩
    apply hne
    have h1 : q (Q.out * y) = Q := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy]; exact QuotientGroup.out_eq' Q
    have h2 : q (Q'.out * y') = Q' := by
      simp only [q]; rw [QuotientGroup.mk_mul_of_mem _ hy']; exact QuotientGroup.out_eq' Q'
    simp only [smul_eq_mul] at he
    rw [← h1, ← h2, he]
  · intro Q hQ
    rw [hT] at hQ
    refine (integrableOn_congr_fun (hconst Q hQ) (hKo.smul _).measurableSet).2 ?_
    refine integrableOn_const ?_
    rw [measure_smul]; exact hKt

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory
open scoped Pointwise

theorem measureReal_eq_inv_natCast {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] {J K : Subgroup G}
    (hJc : IsCompact (J : Set G)) (hJ1 : μ J = 1) (hKo : IsOpen (K : Set G)) (hKJ : K ≤ J) :
    ∃ n : ℕ, μ.real K = (n : ℝ)⁻¹ := by
  have hKt : μ K ≠ ⊤ := ((measure_mono (show (K : Set G) ⊆ J from hKJ)).trans_lt (by simp [hJ1])).ne
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv μ K hKo hKt hJc (fun s hs k hk => J.mul_mem hs (hKJ hk))
    (fun _ => (1 : ℂ)) (fun _ _ _ _ => rfl)
  rw [setIntegral_const, measureReal_def, hJ1, Finset.sum_const, nsmul_eq_mul, one_mul] at ht
  simp only [ENNReal.toReal_one, one_smul] at ht
  refine ⟨t.card, eq_inv_of_mul_eq_one_right ?_⟩
  exact_mod_cast ht.symm

def rightStab {G : Type} [Group G] (S : Set G) : Subgroup G where
  carrier := {k | ∀ g, g ∈ S ↔ g * k ∈ S}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [ha g, hb (g * a), mul_assoc]
  inv_mem' := fun {a} ha g => by rw [ha (g * a⁻¹), inv_mul_cancel_right]

theorem isOpen_rightStab {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {S : Set G}
    (hSc : IsCompact S) (hSo : IsOpen S) : IsOpen (rightStab S : Set G) := by
  obtain ⟨V, hV, hSV⟩ := compact_open_separated_mul_right hSc hSo subset_rfl
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem hV (inv_mem_nhds_one G hV)) ?_)
  rintro k ⟨hk, hk'⟩ g
  refine ⟨fun hg => hSV (Set.mul_mem_mul hg hk), fun hg => ?_⟩
  have := hSV (Set.mul_mem_mul hg hk')
  rwa [mul_inv_cancel_right] at this

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A' : Type} [Fintype A'] [DecidableEq A']

def matBall (x : Matrix A' A' k) (c : kˣ) : Set (Matrix A' A' k) :=
  {y | ∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)}

theorem matBall_eq_preimage (x : Matrix A' A' k) (c : kˣ) :
    matBall x c = ⋂ i, ⋂ j, (fun y : Matrix A' A' k => (y i j - x i j) / (c : k)) ⁻¹' (𝒪[k] : Set k) := by
  have h0 : 0 < valuation k (c : k) := zero_lt_iff.2 (by simp)
  ext y
  simp only [matBall, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
    Valuation.mem_integer_iff, map_div₀, div_le_one₀ h0]

theorem isOpen_matBall (x : Matrix A' A' k) (c : kˣ) : IsOpen (matBall x c) := by
  rw [matBall_eq_preimage]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    IsOpen.preimage (by fun_prop) Valuation.isOpen_integer

theorem isCompact_matBall (x : Matrix A' A' k) (c : kˣ) : IsCompact (matBall x c) := by
  have hc : (c : k) ≠ 0 := c.ne_zero
  have e : matBall x c = (fun A : Matrix A' A' k => (c : k) • A + x) '' {A | ∀ i j, A i j ∈ 𝒪[k]} := by
    ext y
    constructor
    · intro hy
      refine ⟨fun i j => (y i j - x i j) / (c : k), fun i j => ?_, ?_⟩
      · have := (matBall_eq_preimage x c ▸ hy : y ∈ _)
        simp only [Set.mem_iInter, Set.mem_preimage] at this
        exact this i j
      · ext i j
        show (c : k) * ((y i j - x i j) / (c : k)) + x i j = y i j
        rw [mul_div_cancel₀ _ hc, sub_add_cancel]
    · rintro ⟨A, hA, rfl⟩ i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_right, map_mul]
      exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hA i j))
  rw [e]
  exact isCompact_intMatrix.image (by fun_prop)

theorem isCompact_isOpen_glBall (x : Matrix A' A' k) (c : kˣ) (hdet : ∀ y ∈ matBall x c, y.det ≠ 0) :
    IsCompact {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} ∧
    IsOpen {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} := by
  have e : {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} =
      (fun g : GL A' k => g.val) ⁻¹' matBall x c := rfl
  rw [e]
  refine ⟨?_, (isOpen_matBall x c).preimage Units.continuous_val⟩
  rw [isEmbedding_val_GL.isInducing.isCompact_iff]
  convert isCompact_matBall x c using 1
  ext y
  refine ⟨fun ⟨g, hg, hgy⟩ => hgy ▸ hg, fun hy => ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero y (hdet y hy), hy, rfl⟩⟩

end GlobalTheory.GLBallInt

namespace GlobalTheory.GLBallInt
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

theorem integral_glBall_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (ν : kˣ →* ℂˣ) (z : ℂ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u z ∈ F) → ∀ (c : kˣ) (x : Matrix A' A' k), (∀ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)) → y.det ≠ 0) → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
  intro k _ _ _ _ _ _ A' _ _ F J hJo hJK ν z ϖ e _ hcond hνF hapF c x hdet
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨hSc, hSo⟩ := isCompact_isOpen_glBall x c hdet
  set S := {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)} with hSdef
  set K : Subgroup (GL A' k) := J ⊓ GlobalTheory.SplitFlip.glLatCong (ϖ ^ e) (stdLat k A') ⊓ rightStab S with hKdef
  have hKo : IsOpen (K : Set (GL A' k)) := by
    simp only [hKdef, Subgroup.coe_inf]
    exact (hJo.inter (GlobalTheory.FunObj.GivenAdm.isOpen_glLatCong _)).inter (isOpen_rightStab hSc hSo)
  have hKJ : K ≤ J := inf_le_left.trans inf_le_left
  have hJc : IsCompact (J : Set (GL A' k)) := isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK
  have hKt : haarVol J K ≠ ⊤ :=
    ((measure_mono (show (K : Set (GL A' k)) ⊆ J from hKJ)).trans_lt (by simp [haarVol_self hJo hJK])).ne
  have hinv : ∀ s ∈ S, ∀ k' ∈ K, ((ν (gdet (s * k')) : ℂ) * apow (gdet (s * k')) z) =
      (ν (gdet s) : ℂ) * apow (gdet s) z := by
    intro s _ k' hk
    have hu : gdet k' ∈ unitCong (ϖ ^ e) :=
      GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2
    rw [gdet_mul, map_mul, Units.val_mul, apow_mul, hcond _ hu, apow_of_valuation_eq_one hu.1]
    simp
  obtain ⟨t, ht⟩ := integral_eq_sum_of_rightInv (haarVol J) K hKo hKt hSc
    (fun s hs k' hk => ((Subgroup.mem_inf.1 hk).2 s).1 hs) (fun g => (ν (gdet g) : ℂ) * apow (gdet g) z) hinv
  rw [ht]
  obtain ⟨n, hn⟩ := measureReal_eq_inv_natCast (haarVol J) hJc (haarVol_self hJo hJK) hKo hKJ
  refine Subfield.sum_mem _ fun Q _ => F.mul_mem (F.mul_mem (hνF _) (hapF _)) ?_
  rw [hn]
  push_cast
  exact F.inv_mem (natCast_mem F n)

end GlobalTheory.GLBallInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_detChar_invertibleMatrixBall_mem_subfield : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A' : Type} [Fintype A'] [DecidableEq A'] (F : Subfield ℂ) {J : Subgroup (GL A' k)}, IsOpen (J : Set (GL A' k)) → J ≤ KO k A' → ∀ (ν : kˣ →* ℂˣ) (z : ℂ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, (ν u : ℂ) ∈ F) → (∀ u : kˣ, apow u z ∈ F) → ∀ (c : kˣ) (x : Matrix A' A' k), (∀ y : Matrix A' A' k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k (c : k)) → y.det ≠ 0) → ∫ g in {g : GL A' k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k (c : k)}, (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol J) ∈ F := by
  first | exact @GlobalTheory.GLBallInt.integral_glBall_mem | exact GlobalTheory.GLBallInt.integral_glBall_mem | (intros; apply GlobalTheory.GLBallInt.integral_glBall_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneLessEqTopBesselLevelPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneLessEqTopBesselLevelPeriod
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iA {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem coreMat_iB {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = midCol d h := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem besselDecomposition_vector_eq {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (a : D.host.E) :
    (besDec d h).i₀ *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => a) =
      a • (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z := by
  show coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, coreMat_iB]
  show midCol d h *ᵥ (fun _ : Fin 1 => a) = _
  funext k
  simp [midCol, Matrix.mulVec, dotProduct, HermitianOrthogonalExtensionData.besDat, mul_comm]

theorem ratV_smul' {n : ℕ} (a : D.host.E) (v : Fin n → D.host.E) : ratV (a • v) = incA D a • ratV v := by
  funext i
  simp [ratV]

section Diag

variable {S S₀ : HSp D} {σ : ℕ} (d1 : HypDec S S₀ σ) (l : Fin σ → D.host.E)

theorem diagI_mul (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, mul_inv_cancel₀ (hl a), map_one]

theorem diagI_mul' (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)⁻¹) ⬝ (diagonal fun a => incA D (l a)) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, inv_mul_cancel₀ (hl a), map_one]

variable (hl : ∀ a, l a ≠ 0)

theorem jX_diag : (diagDec d1 l hl).jX = d1.jX ⬝ diagonal fun a => incA D (l a) := by
  show rat (d1.e * diagonal l) = _
  rw [rat_mul]; congr 1; exact diagonal_map (map_zero _)

theorem pX_diag_jX : (diagDec d1 l hl).pX ⬝ d1.jX = diagonal fun a => incA D (l a)⁻¹ := by
  have e := (diagDec d1 l hl).pX_jX
  rw [jX_diag, ← Matrix.mul_assoc] at e
  calc (diagDec d1 l hl).pX ⬝ d1.jX
        = (diagDec d1 l hl).pX ⬝ d1.jX ⬝ (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) := by
          rw [Matrix.mul_assoc ((diagDec d1 l hl).pX ⬝ d1.jX), diagI_mul l hl, Matrix.mul_one]
    _ = _ := by rw [e, Matrix.one_mul]

theorem blockX_diag (n : GA D S) (T : Mx D σ σ) (e1 : mt S n ⬝ d1.jX = d1.jX + d1.jX ⬝ T) :
    blockX (diagDec d1 l hl) n =
      1 + (diagonal fun a => incA D (l a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (l a)) := by
  rw [blockX, jX_diag, ← Matrix.mul_assoc (mt S n), e1, Matrix.add_mul, Matrix.mul_add]
  simp only [← Matrix.mul_assoc]
  rw [pX_diag_jX, diagI_mul' l hl]

theorem coefX_diag (n : GA D S) (z z₀ : Fin S₀.rank → D.host.E) (w : Fin S.rank → D.host.E) (a : D.host.E)
    (b : Fin σ → AE D) (hw : d1.i₀ *ᵥ z₀ = w) (hz : d1.i₀ *ᵥ z = a • w)
    (e2 : mt S n *ᵥ ratV w = ratV w + d1.jX *ᵥ b) :
    coefX (diagDec d1 l hl) z n = incA D a • ((diagonal fun a => incA D (l a)⁻¹) *ᵥ b) := by
  have hzs : (diagDec d1 l hl).j0 *ᵥ ratV z = incA D a • ratV w := by
    rw [HypDec.j0, ← ratV_mulVec]
    show ratV (d1.i₀ *ᵥ z) = _
    rw [hz, ratV_smul']
  have hw' : ratV w = (diagDec d1 l hl).j0 *ᵥ ratV z₀ := by
    rw [HypDec.j0, ← ratV_mulVec]
    show ratV w = ratV (d1.i₀ *ᵥ z₀)
    rw [hw]
  rw [coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzs, Matrix.mulVec_smul, e2, Matrix.mulVec_smul,
    Matrix.mulVec_add, hw', Matrix.mulVec_mulVec, (diagDec d1 l hl).pX_j0, Matrix.zero_mulVec, zero_add,
    Matrix.mulVec_mulVec, pX_diag_jX]

end Diag

theorem incA_inv_mul_pow (i : ℕ) :
    incA D (D.host.xi0 ^ i)⁻¹ * incA D (D.host.xi0 ^ (i + 1)) = incA D D.host.xi0 := by
  rw [← map_mul, pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), one_mul]

theorem up_sum {σ : ℕ} (T : Mx D σ σ) :
    upSum ((diagonal fun a => incA D (lam σ a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (lam σ a))) =
      ∑ i : Fin σ, ∑ j : Fin σ, if j.1 = i.1 + 1 then incA D D.host.xi0 * T i j else 0 := by
  simp only [upSum, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · have e := incA_inv_mul_pow (D := D) i
    rw [show lam (D := D) σ j = D.host.xi0 ^ ((i : ℕ) + 1) by rw [lam, hij],
      show lam (D := D) σ i = D.host.xi0 ^ (i : ℕ) from rfl]
    linear_combination T i j * e
  · rfl

theorem ell_sum {σ : ℕ} (b : Fin σ → AE D) :
    ell D σ ⬝ᵥ (incA D (D.host.xi0 ^ σ) • ((diagonal fun a => incA D (lam σ a)⁻¹) *ᵥ b)) =
      ∑ i : Fin σ, if i.1 + 1 = σ then incA D D.host.xi0 * b i else 0 := by
  simp only [ell, dotProduct, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have e := incA_inv_mul_pow (D := D) i
    rw [hi] at e
    calc (1 : AE D) * (incA D (D.host.xi0 ^ σ) * (incA D (lam σ i)⁻¹ * b i))
        = (incA D (D.host.xi0 ^ (i : ℕ))⁻¹ * incA D (D.host.xi0 ^ σ)) * b i := by
          rw [one_mul, ← mul_assoc, mul_comm (incA D (D.host.xi0 ^ σ))]; rfl
      _ = incA D D.host.xi0 * b i := by rw [e]
  · exact zero_mul _

theorem simpleSum_lam {σ : ℕ} (T : Mx D σ σ) (b : Fin σ → AE D) :
    upSum (1 + (diagonal fun a => incA D (lam σ a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (lam σ a))) +
        ell D σ ⬝ᵥ (incA D (D.host.xi0 ^ σ) • ((diagonal fun a => incA D (lam σ a)⁻¹) *ᵥ b)) =
      GlobalTheory.BesselChar.superSum (fun _ => incA D D.host.xi0) T b := by
  rw [upSum_add, upSum_one, zero_add, up_sum, ell_sum]
  rfl

theorem psiBes_diag (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1)
    (n : GA D B) (hn : n ∈ NFlag B ((besDec d h).e * diagonal (lam σ))) :
    psiBes ψ (diagDec (besDec d h) (lam σ) (lam_ne σ)) 1
      (vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ) n =
      besChar ψ (d.besDat (neg_ne_zero.2 one_ne_zero) σ h) n := by
  have hn' : n ∈ NFlag B (besDec d h).e := (nFlag_diag _ (lam σ) (lam_ne σ)) ▸ hn
  obtain ⟨T, b, -, h1, h2⟩ : ∃ (T : Mx D σ σ) (b : Fin σ → AE D), GlobalTheory.BesselChar.StrictUp T ∧
      mt B n ⬝ (besDec d h).jX = (besDec d h).jX + (besDec d h).jX ⬝ T ∧
      mt B n *ᵥ ratV (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z =
        ratV (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z + (besDec d h).jX *ᵥ b :=
    GlobalTheory.BesselChar.exists_coords (d.besDat (neg_ne_zero.2 one_ne_zero) σ h) n hn'
  rw [GlobalTheory.BesselChar.besChar_eq ψ _ n T b h1 h2]
  rw [psiBes, simpleSum, blockX_diag _ _ _ n T h1,
    coefX_diag _ _ _ n _ _ _ _ b (by rw [besselDecomposition_vector_eq d h 1, one_smul]) (besselDecomposition_vector_eq d h _) h2,
    simpleSum_lam, map_one, one_mul, psiE]
  rfl

theorem integral_tr {S : HSp D} {N N' : Subgroup (GA D S)} (hN : N = N') (ν : Measure N) (𝓝 : Set N)
    (f : GA D S → ℂ) : ∫ n in trSet hN 𝓝, f n.1 ∂(trMeas hN ν) = ∫ n in 𝓝, f n.1 ∂ν := by
  subst hN
  rfl

end GlobalTheory.RowChain.TopPer

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem embA_top (G : GridData L sc) (h : GA D (G.V (.top 0))) :
    GlobalTheory.MixPer.embA (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) h = embTop G h :=
  (embRel_iff _ h _).1 (GlobalTheory.CharLaws.embRel_embA _ _ _ (coreMat_iA _ _).symm h)

end GlobalTheory.RowChain.TopPer

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem embA_topLev (G : GridData L sc) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (h : GA D (G.V (.top 0))) :
    GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h = embTop G h :=
  embA_top G h

theorem psiBes_topLev (G : GridData L sc) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (ψ : AddChar (AF D.host.F) ℂ)
    (n : GA D (G.V (.grid D.R.m 0))) (hn : n ∈ flagN (topLev G hM).d) :
    psiBes ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n = besChar ψ G.besTop n :=
  psiBes_diag ψ (G.rowDec 0 (by have := D.R.two_le_m; omega)) (by have := top_idx (D := D); omega) n hn

theorem bplus_eq_topLev_per : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    (M : GlobalTheory.FunObj.Vol G) (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)),
    Bplus Wl M φ F = (GlobalTheory.RowChain.topLev G hM).per Wl.ψ φ F := by
  intro D T L sc G Wl t M hM φ F
  have hN : NFlag (G.V (.grid D.R.m 0)) G.besTop.e = flagN (topLev G hM).d :=
    (nFlag_diag (rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2)
      (by have := top_idx (D := D); omega)).e (lam _) (lam_ne _)).symm
  have hper : (topLev G hM).per Wl.ψ φ F = ∫ h in M.fd (.top 0), ∫ n in trSet hN M.fdN,
      GlobalTheory.MixPer.besFun Wl.ψ 1 (topLev G hM).d (topLev G hM).o (topLev G hM).ζ φ F h n ∂(trMeas hN M.νN) ∂M.ν (.top 0) :=
    rfl
  rw [hper]
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  refine (integral_tr hN M.νN M.fdN fun g => φ h * F (g * embTop G h) * star (besChar Wl.ψ G.besTop g)).symm.trans ?_
  refine integral_congr_ae (ae_of_all _ fun n => ?_)
  show φ h * F (n.1 * embTop G h) * star (besChar Wl.ψ G.besTop n.1) =
    φ h * F ((show GA D (topLev G hM).V from n.1) * GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h) *
      star (psiBes Wl.ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n.1)
  rw [embA_topLev G hM h, psiBes_topLev G hM Wl.ψ n.1 n.2]
  rfl

end GlobalTheory.RowChain.TopPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneLessEqTopBesselLevelPeriodStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCorankOneLess_eq_topBesselLevel_period : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : GlobalTheory.FunObj.Vol G)
    (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)),
    Bplus Wl M φ F = (GlobalTheory.RowChain.topLev G hM).per Wl.ψ φ F := by
  first | exact @GlobalTheory.RowChain.TopPer.bplus_eq_topLev_per | exact GlobalTheory.RowChain.TopPer.bplus_eq_topLev_per | (intros; apply GlobalTheory.RowChain.TopPer.bplus_eq_topLev_per <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSelfDualLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSelfDualLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.AlgPair

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem alg_star {a : ℂ} (ha : a ∈ algebraicClosure ℚ ℂ) : star a ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff] at ha ⊢
  exact ha.algHom ((Complex.conjAe.restrictScalars ℚ).toAlgHom)

theorem fin_neg {x : WO S T} (hx : x.map (infPart D) = 0) : (-x).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.zero_apply] at h ⊢
  rw [RingHom.map_neg, h, neg_zero]

theorem fin_add {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hx i) j
  have h' := congrFun (congrFun hy i) j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at h h' ⊢
  rw [RingHom.map_add (f := _), h, h', add_zero]

variable {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem thetaInner_zero_left (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 0 G = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_left μ 𝓕 0 0 G
  simpa using h

theorem thetaInner_zero_right (G : WO S T → ℂ) : GlobalTheory.RawLift.thetaIP μ 𝓕 G 0 = 0 := by
  have h := GlobalTheory.RawLift.thetaInner_smul_right μ 𝓕 0 G 0
  simpa using h

theorem sum_left (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {G : WO S T → ℂ}
    (hG : IsThetaFunO ψ S T G) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 (∑ p, c p • g p) G = ∑ p, star (c p) * GlobalTheory.RawLift.thetaIP μ 𝓕 (g p) G := by
  intro n
  induction n with
  | zero =>
    intro c g _
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_left G⟩
  | succ n ih =>
    intro c g hg
    obtain ⟨ht, he⟩ := ih (fun p => c p.succ) (fun p => g p.succ) (fun p => hg p.succ)
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_left hψ hcv _ (hg 0) ht hG, he]⟩

theorem sum_right (hψ : IsStdChar D ψ (-1)) (hcv : IsCovolOne (ratL T S) μ 𝓕) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ {n : ℕ} (c : Fin n → ℂ) (g : Fin n → WO S T → ℂ), (∀ p, IsThetaFunO ψ S T (g p)) →
    IsThetaFunO ψ S T (∑ p, c p • g p) ∧
      GlobalTheory.RawLift.thetaIP μ 𝓕 f (∑ p, c p • g p) = ∑ p, c p * GlobalTheory.RawLift.thetaIP μ 𝓕 f (g p) := by
  intro n
  induction n with
  | zero =>
    intro c g _
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, thetaInner_zero_right f⟩
  | succ n ih =>
    intro c g hg
    obtain ⟨ht, he⟩ := ih (fun p => c p.succ) (fun p => g p.succ) (fun p => hg p.succ)
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul _ (hg 0)) ht,
      by rw [GlobalTheory.VacSchurFin.thetaInner_right hψ hcv _ hf (hg 0) ht, he]⟩

variable {θ : InfFam D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
  {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {v : WO S T → ℂ}

theorem vac_translate (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {u : WO S T}
    (hu : u.map (infPart D) = 0) : GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have hlat := hv.2.lat
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  by_cases hmem : u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
  · obtain ⟨ε, hε, hεv⟩ := h3 v hlat u hmem
    have hself : GlobalTheory.RawLift.thetaIP μ 𝓕 v v = 1 := by
      rw [GlobalTheory.RawLift.thetaInner_self]
      have hn := hv.2.norm.2 (μ, 𝓕) hcv
      simp only [nrm2] at hn
      rw [hn, Complex.ofReal_one]
    rw [hεv v hlat, GlobalTheory.RawLift.thetaInner_smul_right, hself, mul_one]
    rcases hε with rfl | rfl
    · exact one_mem _
    · exact neg_mem (one_mem _)
  · have hne : ∃ u' ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        ψ (symplO S T u u') ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hmem ((h1 u hu).2 hcon)
    obtain ⟨u', hu', hψu⟩ := hne
    obtain ⟨ε, hε, hεv⟩ := h3 v hlat u' hu'
    have hεv' := hεv v hlat
    have comm := GlobalTheory.SplitScalar.heisO_comm ψ S T u u' v
    rw [hεv', GlobalTheory.VacSchurFin.heisO_smul'] at comm
    have inv := GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv hvt (laws.1 u v hvt) u'
    rw [hεv'] at inv
    have hεε : star ε * ε = 1 := by
      rcases hε with h | h <;> rw [h] <;> simp only [star_one, star_neg, one_mul, neg_mul_neg]
    have hfix : ψ (symplO S T u u') * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) =
        GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) := by
      conv_lhs => rw [← inv, ← GlobalTheory.RawLift.thetaInner_smul_right, ← comm, GlobalTheory.RawLift.thetaInner_smul_left,
        GlobalTheory.RawLift.thetaInner_smul_right, ← mul_assoc, hεε, one_mul]
    have h0 : (ψ (symplO S T u u') - 1) * GlobalTheory.RawLift.thetaIP μ 𝓕 v (heisO ψ S T u v) = 0 := by
      rw [sub_mul, hfix, one_mul, sub_self]
    rw [(mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hψu)]
    exact zero_mem _

theorem translates (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hcv : IsCovolOne (ratL T S) μ 𝓕) {x y : WO S T}
    (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    GlobalTheory.RawLift.thetaIP μ 𝓕 (heisO ψ S T x v) (heisO ψ S T y v) ∈ algebraicClosure ℚ ℂ := by
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have e1 : heisO ψ S T (-x) (heisO ψ S T x v) = ψ (symplOH S T (-x) x) • v := by
    rw [GlobalTheory.SplitScalar.heisO_heisO, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero]
  have e2 : heisO ψ S T (-x) (heisO ψ S T y v) = ψ (symplOH S T (-x) y) • heisO ψ S T (-x + y) v :=
    GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) y v
  rw [← GlobalTheory.VacSchurFin.thetaInner_heisenberg hψ hcv (laws.1 x v hvt) (laws.1 y v hvt) (-x), e1, e2,
    GlobalTheory.RawLift.thetaInner_smul_left, GlobalTheory.RawLift.thetaInner_smul_right]
  refine mul_mem (alg_star (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hx))
    (mul_mem (GlobalTheory.BotFourier.psiH_mem hψ hS hT (fin_neg hx) hy) ?_)
  exact vac_translate hv hS hT hcv (fin_add (fin_neg hx) hy)

theorem thetaIP_algComb : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F F' : WO S T → ℂ,
    GlobalTheory.MovedAlg.IsAlgComb ψ S T v F → GlobalTheory.MovedAlg.IsAlgComb ψ S T v F' → IsAlgebraic ℚ (GlobalTheory.RawLift.thetaIP μ 𝓕 F F') := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT μ 𝓕 hcv F F' hF hF'
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨m, c', w', hc', hw', rfl⟩ := hF'
  have hψ : IsStdChar D ψ (-1) := hv.1
  have hvt : IsThetaFunO ψ S T v := hv.2.theta
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hth : ∀ x, IsThetaFunO ψ S T (heisO ψ S T x v) := fun x => laws.1 x v hvt
  have hR := (sum_right hψ hcv (hth 0) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).1
  rw [(sum_left hψ hcv hR c (fun p => heisO ψ S T (w p) v) fun p => hth _).2, ← mem_algebraicClosure_iff]
  refine Subalgebra.sum_mem _ fun p _ => mul_mem (alg_star (mem_algebraicClosure_iff.2 (hc p))) ?_
  rw [(sum_right hψ hcv (hth (w p)) c' (fun q => heisO ψ S T (w' q) v) fun q => hth _).2]
  exact Subalgebra.sum_mem _ fun q _ =>
    mul_mem (mem_algebraicClosure_iff.2 (hc' q)) (translates hv hS hT hcv (hw p) (hw' q))

end GlobalTheory.AlgPair

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSelfDualLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_self_dual_lattices : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ F F' : WO S T → ℂ,
    GlobalTheory.MovedAlg.IsAlgComb ψ S T v F → GlobalTheory.MovedAlg.IsAlgComb ψ S T v F' → IsAlgebraic ℚ (GlobalTheory.RawLift.thetaIP μ 𝓕 F F') := by
  first | exact @GlobalTheory.AlgPair.thetaIP_algComb | exact GlobalTheory.AlgPair.thetaIP_algComb | (intros; apply GlobalTheory.AlgPair.thetaIP_algComb <;> assumption)
end
end
