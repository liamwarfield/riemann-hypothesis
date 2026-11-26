module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelConjBaseLatticeUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvReductionMulFlagTranslationMemRowLevelGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvReductionMulFlagTranslationMemRowLevelGroup
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

theorem inv_mul_mem_pi {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) (a b : ∀ i, G i)
    (h : ∀ i, (a i)⁻¹ * b i ∈ H i) : a⁻¹ * b ∈ Subgroup.pi Set.univ H := fun i _ => h i

theorem reindex_finCongr_rfl {κ : Type} [CommRing κ] {a : ℕ} (y : GL (Fin a) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ (finCongr (rfl : a = a))).toMonoidHom y = y := by
  apply Units.ext
  ext i j
  rfl

theorem coarse_eq_blkOf {a r t m : ℕ} (hn : a = r + m * t) (i : Fin a) :
    Formalism.L2.Col.coarse r (List.replicate m t) i.val = Formalism.L2.DIV.blkOf r t i := by
  unfold Formalism.L2.DIV.blkOf
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        simp at hn
        omega
      · exact h0
    rw [Formalism.L2.Col.blkIdx_replicate ht m _ (by omega)]

theorem coarseBlockIndex_eq_twoBlock {a r b : ℕ} (hn : a = r + b) (i : Fin a) :
    Formalism.L2.Col.coarse r [b] i.val = Formalism.L2.DIV.blk2 r i := by
  unfold Formalism.L2.DIV.blk2
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have : i.val - r < b := by omega
    simp [Formalism.L2.Col.blkIdx, this]

theorem reindex_inv_mul_diag_mem_HK {κ : Type} [CommRing κ] {a n r t m : ℕ} (h : a = n) (hn : n = r + m * t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) :
    (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y)⁻¹ *
        Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HK n κ r (List.replicate m t) := by
  subst h
  rw [reindex_finCongr_rfl]
  have hy' : y ∈ Formalism.L2.Col.blockUT _ κ r (List.replicate m t) := by
    intro i j hij
    apply hy
    have hij' : Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val := hij
    rw [coarse_eq_blkOf hn, coarse_eq_blkOf hn] at hij'
    exact hij'
  have hy2 : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := Formalism.L2.DIV.blockTri_blkOf_le r t hy
  refine Formalism.L2.Col.mem_HK.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hy')
    (Formalism.L2.Col.diagEmb_mem_blockUT hrn _ _), fun i j hi hj => ?_⟩
  let Y : Formalism.L2.Col.blockUT _ κ r (List.replicate m t) := ⟨y, hy'⟩
  let Dd : Formalism.L2.Col.blockUT _ κ r (List.replicate m t) :=
    ⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn (List.replicate m t) (Formalism.L2.DIV.upperLeftBlock hra y)⟩
  have hD : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Dd = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val]
    ext i' j'
    exact Formalism.L2.Col.diagMat_of_lt _ (show (Fin.castLE hrn i').val < r from i'.2) (show (Fin.castLE hrn j').val < r from j'.2)
  have hY : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) Y = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val, Formalism.L2.DIV.upper_block_val_submatrix hra hy2]
    rfl
  have h1 : Formalism.L2.Col.blk0 _ κ hrn (List.replicate m t) (Y⁻¹ * Dd) = 1 := by
    rw [map_mul, map_inv, hD, hY, inv_mul_cancel]
  have h2 := congrArg (fun g : GL (Fin r) κ => (g : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩) h1
  simp only [Formalism.L2.Col.blockZero_val, Units.val_one] at h2
  have h3 : ((y⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) : GL _ κ) : Matrix _ _ κ) i j =
      (1 : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩ := h2
  rw [h3]
  simp only [Matrix.one_apply, Fin.ext_iff]

theorem reindex_inv_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    (Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y)⁻¹ * 1 ∈ Formalism.L2.Col.blockUT n κ r [b] := by
  subst h
  rw [reindex_finCongr_rfl, mul_one]
  refine Subgroup.inv_mem _ ?_
  intro i j hij
  apply hy
  have hij' : Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val := hij
  rw [coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn] at hij'
  exact hij'

end GlobalTheory.Mem.R3.RowDeco

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd


set_option maxHeartbeats 1000000 in
theorem inv_redG_mul_g0Hat_mem_grp : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
      (hz : RowAd.ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      (((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩)⁻¹ :
        Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
        Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
          (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))))) ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
  intro X px I U L eG hI hL hG t q hz
  apply inv_mul_mem_pi
  intro w
  show _ ∈ (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H
  rw [redG_ptE X I L hL t q hz w]
  have hQ := RowAct.parLev_of_Q X.toD7.sp.X' L.βX (L.datXt t) q
  by_cases hw : w.1 ∈ (X.B.primes px).vGs
  · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ w hw]
    have hPg : w.1 ∈ L.Pg := by rw [hL.Pg]; exact hw
    have hPg' : w.1 ∈ (L.datXt t).Pg := hPg
    have hy := Formalism.L2.DIV.parLev_g hQ hPg'
    have hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w =
        Formalism.L2.Col.diagEmb (𝓞 X.B.fields.E ⧸ w.1.asIdeal) (Formalism.L2.Col.r_le_X' X.B.R) (g ⟨w.1, hw⟩) := fun g => by
      rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_mem _ w hw]
      rfl
    rw [hg0]
    have hgg : ∀ z, (eG.symm z) ⟨w.1, hw⟩ = z ⟨w.1, hPg⟩ := fun z => by
      rw [← hG (eG.symm z) w.1 hw hPg, MulEquiv.apply_symm_apply]
    have key := reindex_inv_mul_diag_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr
      (Formalism.L2.Col.r_le_X' X.B.R) _ hy
    convert key using 3 <;> first | rfl | exact heq_of_eq (hgg _) | exact hgg _
  · have hwQ : w.1 ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      classical
      exact (Finset.mem_union.1 w.2).resolve_left hw
    have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      simp only [ColIn.Q, tup_ixOf]
    have hQt : w.1 ∈ L.Q t := by
      rw [hL.Q t, e]
      exact hwQ
    have hQt' : w.1 ∈ (L.datXt t).Q := hQt
    have hy := Formalism.L2.DIV.parLev_q hQ hQt'
    rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ w hw]
    have hg0 : ∀ g : Gc X.B px, Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g w = 1 := fun g => by
      rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_not _ w hw]
    rw [hg0]
    exact reindex_inv_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hy

end GlobalTheory.Mem.R3.RowDeco
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvReductionMulFlagTranslationMemRowLevelGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_reduction_mul_flagTranslation_mem_rowLevelGroup : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
      (hz : RowAd.ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      (((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩)⁻¹ :
        Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
        Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
          (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))))) ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
  first | exact @GlobalTheory.Mem.R3.RowDeco.inv_redG_mul_g0Hat_mem_grp | exact GlobalTheory.Mem.R3.RowDeco.inv_redG_mul_g0Hat_mem_grp | (intros; apply GlobalTheory.Mem.R3.RowDeco.inv_redG_mul_g0Hat_mem_grp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugatedChartDataLocalLevelAtQ
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugatedChartDataLocalLevelAtQ
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem dc_mul_inv_bij {G : Type} [Group G] (Γ K K' : Subgroup G) (b : G) (hK : ∀ x, x ∈ K' ↔ b⁻¹ * x * b ∈ K)
    {ι : Type} (z : ι → G) (hz : Function.Bijective fun i => (Quotient.mk'' (z i) : ClassSet Γ K)) :
    Function.Bijective fun i => (Quotient.mk'' (z i * b⁻¹) : ClassSet Γ K') := by
  constructor
  · intro i j hij
    obtain ⟨h, hh, k, hk, e⟩ := (@DoubleCoset.eq _ _ Γ K' _ _).1 hij
    refine hz.1 ((@DoubleCoset.eq _ _ Γ K _ _).2 ⟨h, hh, b⁻¹ * k * b, (hK k).1 hk, ?_⟩)
    calc z j = (z j * b⁻¹) * b := by group
      _ = h * z i * (b⁻¹ * k * b) := by rw [e]; group
  · intro w
    induction w using Quotient.inductionOn' with
    | h x =>
      obtain ⟨i, hi⟩ := hz.2 (Quotient.mk'' (x * b))
      obtain ⟨h, hh, k, hk, e⟩ := (@DoubleCoset.eq _ _ Γ K _ _).1 hi
      refine ⟨i, (@DoubleCoset.eq _ _ Γ K' _ _).2 ⟨h, hh, b * k * b⁻¹, (hK _).2 ?_, ?_⟩⟩
      · have : b⁻¹ * (b * k * b⁻¹) * b = k := by group
        rw [this]
        exact hk
      · calc x = (x * b) * b⁻¹ := by group
          _ = (h * z i * k) * b⁻¹ := by rw [e]
          _ = h * (z i * b⁻¹) * (b * k * b⁻¹) := by group

theorem mem_range_qdStab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
    (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (p : DecoF E n ST SG Q) (γ : URat hc n) :
    γ ∈ (qdStab (hc := hc) (Θ := Θ) H p).range ↔ ∃ g : UF E n × H × Θ.grp, ufGL E n g.1 = γ.1 ∧ g • p = p := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.1, ?_, a.2⟩
    rw [← qdf_ratHom_stab (hc := hc) H p a, ha, ufGL_ratHom]
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨⟨g, hg2⟩, (ratHom_bijective hc n).1 ?_⟩
    exact (qdf_ratHom_stab (hc := hc) H p ⟨g, hg2⟩).trans
      (ufGL_inj hc n (hg1.trans (ufGL_ratHom hc n γ).symm))

theorem chartQ_exists : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ} (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal) (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG) (hidx : (baseLb E n ST).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f)) (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) →* ℂˣ) {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n) (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) (hbT : ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q) {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c)) (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ)) (hlat : ∀ c, lat c = (s c).deco.1.L) (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c)) (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1), ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J), Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧ (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔ ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧ (∀ c, Function.Injective (SI c)) ∧ (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧ lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧ (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ → lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧ (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q K _ Hw π T f hB hTπ hST hcard hSG hidx lam Θ q hO hQT σ₀ b hbU hbV hbL hbT hbO J hJ bad hb
    cl stab _ lat s y hy hd hs hlat st hinj hr hchr
  subst hJ hb
  classical
  let S := stepOfQ hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀
  have hbT' : ∀ v, (T : 𝓞 F) ∈ v.asIdeal →
      (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v := by
    intro v hv
    rw [S.UlocAlt v hv]
    exact hbT v ((mem_plUnder_iff_norm hc hST T hTπ v).2 hv)
  obtain ⟨S', hLb, hU, hchi⟩ := GlobalTheory.T.exists_stepLevel_conj_baseLatticeUnitary S b hbU hbV hbT' hbO
  have hlam : ∃ m : ℕ, 0 < m ∧ ∀ h, lam h ^ m = 1 := by
    haveI : Finite (GLG (E := E) (n := n) (SG := SG)) := inferInstance
    refine ⟨Nat.card (Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))), Nat.card_pos, fun h => ?_⟩
    rw [← map_pow, pow_card_eq_one', map_one]
  obtain ⟨m, hm, hM⟩ := stepOfQ_chi_fin hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀ hlam hchr
  let e := Equiv.ofBijective _ hs
  let s' : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → DecoF E n ST SG Q := fun c => s (e.symm c)
  have hs' : ∀ c, (Quotient.mk'' (s' c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ) = c :=
    fun c => e.apply_symm_apply c
  let y' : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → UAd hc n := fun c => ⟨y (e.symm c), hy _⟩
  have hy' : ∀ c, FrOver q (y' c).1 (s' c) := fun c => hd _
  let C := recClsFy q (qdf_frLat q) qdf_frExists s' hs' y' hy'
  have hm' : ∀ c a, st c a ∈ URat hc n := fun c a => by
    obtain ⟨g, hg, -⟩ := (hr c _).1 ⟨a, rfl⟩
    rw [← hg]
    exact ufGL_mem hc n _
  have hYU : ∀ c, y c * b⁻¹ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) :=
    fun c => mul_mem (hy c) (inv_mem hbU)
  refine ⟨S', fun c => ⟨y c * b⁻¹, hYU c⟩, fun c => (st c).codRestrict _ (hm' c), ?_, fun c x => ?_,
    fun c a a' h => hinj c (congrArg Subtype.val h), fun c γ => ?_, hLb, hU, fun x z h => hchi x z h, ?_,
    fun _ => rfl, fun _ _ => rfl⟩
  ·
    have hC : ∀ c, C.y (e c) = ⟨y c, hy c⟩ := fun c => Subtype.ext (congrArg y (e.symm_apply_apply c))
    have hz := C.y_bij.comp e.bijective
    have hz' : Function.Bijective fun c => (Quotient.mk'' (⟨y c, hy c⟩ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E)
        (FiniteAdeleRing (𝓞 F) F)) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf
          (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        ((levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))) := by
      convert hz using 2 with c
      simp only [Function.comp_apply, hC]
    exact dc_mul_inv_bij ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf
          (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        ((levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        (S'.U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) ⟨b, hbU⟩ (fun x => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hU, mem_map_conj]
      rfl) _ hz'
  ·
    have h := decoRaw_carries hc n ST SG (hy c) x
    rw [← rlc_decoOf_val hc n ST SG (hy c), (hd c).1, ← hlat] at h
    refine (h.trans ?_)
    rw [hLb]
    show _ ↔ ((y c * b⁻¹)⁻¹ : GL (Fin n) _).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hbL _).symm
  ·
    have h := C.stabI_range (e c) γ.1 γ.2
    change (⟨γ.1, γ.2⟩ : URat hc n) ∈ (qdStab (hc := hc) (Θ := Θ) (Subgroup.pi Set.univ Hw) (s (e.symm (e c)))).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈
        (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj (y (e.symm (e c)))).toMonoidHom at h
    rw [e.symm_apply_apply, mem_range_qdStab, ← hr] at h
    refine Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, congrArg Subtype.val ha⟩, fun ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩ (h.trans ?_)
    rw [hU, mem_map_conj, mem_map_conj, mem_map_conj]
    show _ ↔ b⁻¹ * ((y c * b⁻¹)⁻¹ * _ * (y c * b⁻¹)) * b ∈ _
    have e2 : ∀ g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), b⁻¹ * ((y c * b⁻¹)⁻¹ * g * (y c * b⁻¹)) * b = (y c)⁻¹ * g * y c :=
      fun g => by group
    rw [e2]
    exact Iff.rfl
  ·
    refine ⟨m, hm, fun κ => ?_⟩
    have h1 : ∀ x, x ∈ S'.U → b⁻¹ * x * b ∈ S.U := fun x hx => by
      rw [hU, mem_map_conj] at hx
      exact hx
    have hk : b⁻¹ * κ.1 * b ∈ S.U := h1 κ.1 κ.2
    rw [hchi κ ⟨_, hk⟩ (by show κ.1 = b * (b⁻¹ * κ.1 * b) * b⁻¹; group), hM]

end GlobalTheory.Mem.Col2.ChEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugatedChartDataLocalLevelAtQStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugated_chartData_localLevel_at_Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ} (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal) (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG) (hidx : (baseLb E n ST).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f)) (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) →* ℂˣ) {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n) (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) (hbT : ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q) {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c)) (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ)) (hlat : ∀ c, lat c = (s c).deco.1.L) (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c)) (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1), ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J), Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧ (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔ ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧ (∀ c, Function.Injective (SI c)) ∧ (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧ lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧ (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ → lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧ (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.chartQ_exists | exact GlobalTheory.Mem.Col2.ChEx.chartQ_exists | (intros; apply GlobalTheory.Mem.Col2.ChEx.chartQ_exists <;> assumption)
end
end
