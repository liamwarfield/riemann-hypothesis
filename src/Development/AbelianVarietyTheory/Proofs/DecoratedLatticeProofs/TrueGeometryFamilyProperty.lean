module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceUpperBoundAllMembers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexValue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFamilyProperty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamPlaced

section Prim

open GlobalTheory.FinPl

theorem incA_mul_mem_intAt {D : D7} (v : GlobalTheory.FinPl.Pl D) (c : D.host.E) (N : ℤ) (hint : IsIntegral ℤ (N • c))
    (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) {a : AE D} (ha : a ∈ intAt D (· = v)) : incA D c * a ∈ intAt D (· = v) := by
  have hN : N ≠ 0 := fun h => hv (by rw [h]; simp)
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 hN
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← AeUnit.idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, AeUnit.inv_smul_singleV_mem v N hv, ⟨N • c, hint⟩, ?_⟩
  exact AeUnit.tmul_eq_inv_smul_tmul N hNF _ c

theorem prim_std {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : ∀ x, x ∈ L ↔ ∀ i, IsIntegral ℤ (x i)) (v : GlobalTheory.FinPl.Pl D)
    (z : Fin S.rank → D.host.E) (hz : ∀ i, IsIntegral ℤ (z i)) (i₀ : Fin S.rank) (π' : D.host.E) (hπ' : IsIntegral ℤ π') (N : ℤ)
    (hπ : z i₀ * π' = (N : D.host.E)) (hv : (N : 𝓞 D.host.F) ∉ v.asIdeal) (a : AE D) (ha : a ∈ idAt D (· = v)) :
    a • ratV z ∈ GlobalTheory.FinPl.latV S L (· = v) ↔ a ∈ intAt D (· = v) := by
  have hL' : ∀ x : Fin S.rank → D.host.E, x ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = x i := fun x => by
    rw [hL x]
    exact ⟨fun h i => ⟨⟨x i, h i⟩, rfl⟩, fun h i => by obtain ⟨b, hb⟩ := h i; exact hb ▸ b.2⟩
  have hN : N ≠ 0 := fun h => hv (by rw [h]; simp)
  have hNE : (N : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hN
  have hz0 : z i₀ ≠ 0 := fun h => hNE (by rw [← hπ, h, zero_mul])
  have h1 : ((1 : ℤ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    rw [Int.cast_one]; exact fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  rw [GlobalTheory.FinPl.Model.mem_latV_std S L hL' v]
  constructor
  · intro h
    have hi : a * incA D (z i₀) ∈ intAt D (· = v) := h i₀
    have hint : IsIntegral ℤ (N • (z i₀)⁻¹) := by
      have : N • (z i₀)⁻¹ = π' := by
        rw [zsmul_eq_mul, ← hπ, mul_comm (z i₀), mul_assoc, mul_inv_cancel₀ hz0, mul_one]
      rw [this]; exact hπ'
    have h2 := incA_mul_mem_intAt v (z i₀)⁻¹ N hint hv hi
    rwa [mul_comm a, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hz0, map_one, one_mul] at h2
  · intro h i
    show a * incA D (z i) ∈ intAt D (· = v)
    rw [mul_comm]
    exact incA_mul_mem_intAt v (z i) 1 (by rw [one_smul]; exact hz i) h1 h

end Prim

end GlobalTheory.FamPlaced
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegreeHypothesisAllMembers
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.HypAt

theorem del_lo {x eps k f CD cD : ℝ} (hx : 1 ≤ x) (he : eps ≤ 1) (hk0 : 0 ≤ f) (hfk : f ≤ k)
    (hk : k ≤ x ^ (5 : ℝ)) (hCD : 0 ≤ CD) (hc : 11 * CD ≤ cD) :
    (k * f * x ^ eps) ^ CD ≤ ((⌈x ^ cD⌉₊ : ℕ) : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hk0' : 0 ≤ k := le_trans hk0 hfk
  have h1 : x ^ eps ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx he
  have h2 : k * f ≤ x ^ (5 : ℝ) * x ^ (5 : ℝ) := mul_le_mul hk (le_trans hfk hk) hk0 (by positivity)
  have h3 : k * f * x ^ eps ≤ x ^ (11 : ℝ) := by
    have : x ^ (11 : ℝ) = x ^ (5 : ℝ) * x ^ (5 : ℝ) * x ^ (1 : ℝ) := by
      rw [← Real.rpow_add' hx0 (by norm_num), ← Real.rpow_add' hx0 (by norm_num)]; norm_num
    rw [this]
    exact mul_le_mul h2 h1 (by positivity) (by positivity)
  calc (k * f * x ^ eps) ^ CD ≤ (x ^ (11 : ℝ)) ^ CD := Real.rpow_le_rpow (by positivity) h3 hCD
    _ = x ^ (11 * CD) := by rw [← Real.rpow_mul hx0]
    _ ≤ x ^ cD := Real.rpow_le_rpow_of_exponent_le hx hc
    _ ≤ _ := Nat.le_ceil _

theorem evP_hypL (A B : Formalism.MainNotions.Inhab.FC → ℝ) : EvP fun κ K => ∀ β : BPt K,
    (∀ u : β.D.what₂.Word, β.O.L.sc.b ^ ((1 / 2 : ℝ) * (β.D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr β.D u ∧
      Formalism.MainNotions.S.Tr β.D u ≤ β.O.L.sc.b ^ (κ.C.CTu * (β.D.R.m : ℝ))) →
    GlobalTheory.Core.Deg.HypL β.D β.O.L.sc.L (max (A κ.C) (8 * κ.C.CGam)) (max (B κ.C) 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2)
      κ.C.CTu := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  have hCD3 : (3 : ℝ) ≤ max (B C) 40 := le_trans (by norm_num) (le_max_right _ _)
  have hCD0 : (0 : ℝ) < max (B C) 40 := by linarith
  refine ⟨max c1 (11 * max (B C) 40), fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD (le_trans (le_max_left _ _) hcD)
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch hch
  obtain ⟨x2, hNo⟩ := GlobalTheory.Diag.PG.NodeParameters.nodes_of_parameters eps he he52
  obtain ⟨x3, hH⟩ := GlobalTheory.T.hypotheses_of_global_rows_and_nodes eps (max (B C) 40) he he52 hCD3 (max (A C) (8 * C.CGam)) (max (B C) 40)
    (C.P.CYL + 1) hCD0 le_rfl
  refine ⟨max (max x1 x2) (max x3 ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)), fun K hK hx β hW => ?_⟩
  obtain ⟨hC, hcD', hch', heps, -⟩ := hK
  have hsc : β.O.L.sc = K.s := β.sc
  have hx' : max (max x1 x2) (max x3 ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)) ≤ β.O.L.sc.x := by rw [hsc]; exact hx
  have hse : β.O.L.sc.eps = eps := by rw [hsc]; exact heps
  have hv : Val C cD ch β.O.L := by
    rw [show C = K.C from hC.symm, show cD = K.cD from hcD'.symm, show ch = K.ch from hch'.symm]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx') hv
    (GlobalTheory.Plug.hostArith_bpt β)
  have hx1 : 1 < β.O.L.sc.x := β.O.L.sc.one_lt_alt
  have hX : max 2 (5 / (eps / 100)) ≤ S.XX β.O.L := by
    unfold S.XX szTh
    rw [hse]
    have h0 : (0 : ℝ) ≤ max 2 (5 / (eps / 100)) := le_trans (by norm_num) (le_max_left _ _)
    have hp : 0 < eps / 100 := by positivity
    have hyP : (max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹ ≤ β.O.L.sc.x :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx'
    have := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hyP hp.le
    rwa [Real.rpow_inv_rpow h0 hp.ne'] at this
  have G0 := GlobalTheory.Diag.PG.Model0.globalRows_of_sizeData β.O.L N.params N.sizes ((le_max_left _ _).trans hX)
    (by unfold szTh; rw [hse]; exact (le_max_right _ _).trans hX) N.params.CCount N.params.CCount_pos le_rfl
  have e2 : N.params.CYL = C.P.CYL := congrArg (fun l : List ℝ => l.getD 19 0) N.params_K
  rw [hse, e2] at G0
  have hDel : ((β.D.s.Del : ℚ) : ℝ) = ((⌈β.O.L.sc.x ^ cD⌉₊ : ℕ) : ℝ) := by
    rw [hv.Del_eq]; unfold Delv; push_cast; rfl
  have hDl : ((β.D.R.k : ℝ) * (β.D.R.f : ℝ) * β.O.L.sc.x ^ eps) ^ max (B C) 40 ≤ ((β.D.s.Del : ℚ) : ℝ) := by
    rw [hDel]
    exact del_lo hx1.le (by linarith) (by positivity) G0.nums.fk G0.nums.k_hi hCD0.le
      (le_trans (le_max_right _ _) hcD)
  have G : GlobalTheory.Diag.PG.Glob0 β.D β.O.L.sc.x eps (max (B C) 40) (C.P.CYL + 1) :=
    ⟨⟨G0.nums.m_lo, G0.nums.mf, G0.nums.fk, G0.nums.k_lo, G0.nums.k_hi, G0.nums.lrd_lo, G0.nums.lrd_hi, hDl,
      G0.nums.Del_hi⟩, G0.g_win, G0.gap, G0.cloud, G0.off, G0.rd_lo⟩
  have hNd := hNo β.D β.O.L N.params N.sizes hse (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx')
  have hL : β.O.L.sc.L = β.O.L.sc.x ^ eps := by rw [← hse]; rfl
  have h8 : 8 * β.O.L.CGam ≤ max (A C) (8 * C.CGam) := by rw [N.CGam_eq]; exact le_max_right _ _
  exact GlobalTheory.Core.Deg.hypL_of (hH β.O.L.sc.x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx') β.D β.O.L
    (1 / 2) C.CTu hL h8 G hNd hW)

end GlobalTheory.Core.HypAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLevelComparison
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLevPrime

section Comp

set_option synthInstance.maxHeartbeats 200000

variable {D : D7}

theorem prV_comm (v : GlobalTheory.FinPl.Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rfl
  | add a b ha hb =>
    simp only [map_add (f := _)]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_congr (v : GlobalTheory.FinPl.Pl D) {y y' : AE D} (h : GlobalTheory.FinPl.compAt D v y = GlobalTheory.FinPl.compAt D v y') :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = Formalism.UG.prV (E := D.host.E) v (toEAf D y') := by
  unfold GlobalTheory.FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  generalize finPart D y' = z' at h ⊢
  refine (prV_comm v z).trans (Eq.trans ?_ (prV_comm v z').symm)
  rw [h]

theorem bc_eq_one_of_off (V : HSp D) {n : ℕ} (hn : V.rank = n) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : P v)
    {g : GA D V} (hg : g ∈ GlobalTheory.FinPl.grpOff V P) {x : GL (Fin n) (EF D)} (hx : x.1 = finM V hn g) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  subst hn
  have h := (GlobalTheory.FinPl.SetCut.mem_grpOff_iff_parts V P g).1 hg i j v hv
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  have e : x.1 i j = toEAf D (Formalism.L2.Theta.mt V g i j) := by rw [hx]; rfl
  rw [e, prV_toEAf_congr v h]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]

end Comp

section Level

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}

theorem exists_splitPt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))
    (hv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) : ∃ i, v = (p i).v := by
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  obtain ⟨w, hw, rfl⟩ := (GlobalTheory.NormPlaces.places_dvd_iff (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl
    (l.pr.piT_norm u) hne v).1 hv
  obtain ⟨e, he⟩ := hS.1
  refine ⟨e.symm ⟨w, hw⟩, ?_⟩
  have h := he (e.symm ⟨w, hw⟩)
  rw [e.apply_symm_apply] at h
  exact (GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under _ h).symm


set_option maxHeartbeats 2000000 in
theorem uloc_le_of_std (hOk : I.Ok) (hP : TC.Pins B X) {a a' : I.ι} {Ch Ch' : ℕ → Type} {A : TwDat I l Z u a Ch}
    {A' : TwDat I l Z u a' Ch'} (hA : A.Is) (hA' : A'.Is)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k} {β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)}
    {Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)} {L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j)}
    (hS : StdT I l Z u p β Q L) (J : List ι) (hn : J.Nodup) (hall : ∀ i, i ∈ J) (j : ℕ) (hj : j ≤ B.R.m) (b : Ch j) (b' : Ch' j)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ∃ i, v = (p i).v) :
    (A.K j hj b).lev.Uloc v ≤ (A'.K j hj b').lev.Uloc v := by
  intro h hh
  obtain ⟨x, hxU, hxv⟩ : ∃ x ∈ (A.K j hj b).lev.U, Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) x = h := by
    refine ⟨Formalism.UG.P.afsplitU v h 1, ?_, Formalism.UG.P.afsplit_right1 v h 1⟩
    rw [(A.K j hj b).lev.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ h 1 ((A.K j hj b).lev.Uloc_le v hh) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · rw [hw, Formalism.UG.P.afsplit_right1 v h 1]; exact hh
    · have hxw : Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
          Units.val_one, Units.val_one]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [hxw]; exact one_mem _
  obtain ⟨g, hgC, hg⟩ := GlobalTheory.ChartLevRead.exists_finM_GfC _ (rankN (I.rec7 l Z) j hj) ⟨x, (((A.K j hj b).lev.U_eq x).1 hxU).1⟩
  have hgU : g ∈ A.U j b := (hA.U j hj b g).2 ⟨hgC, ⟨x, hxU⟩, hg.symm⟩
  obtain ⟨g', hg', κ', hκ', hκe⟩ := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a Ch A hA k ι p β Q L hS J hn hall j hj b).2 g hgU
  have hst := (GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hOk hP l Z u a' Ch' A' hA' k ι p β Q L hS J hn hall j hj b').1
  have hprod : (J.map fun i => (β j i).gl (g' i)).prod ∈ A'.U j b' := Subgroup.list_prod_mem _ fun y hy => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact (hst i _ (hg' i)).1
  obtain ⟨-, y, hy⟩ := (hA'.U j hj b' _).1 hprod
  obtain ⟨z, hz⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl κ'
  have e : x = y.1 * z.1 := by
    apply Units.ext
    have hg2 : finM _ (rankN (I.rec7 l Z) j hj) g = x.1 := hg
    rw [Units.val_mul, hy, hz, ← hg2, hκe]
    exact GlobalTheory.AdForm.StabMove.finM_mul _ _ _ _
  have hz1 := bc_eq_one_of_off _ (rankN (I.rec7 l Z) j hj) (v := v) hv hκ' hz
  rw [← hxv, e, map_mul, hz1, mul_one]
  exact (((A'.K j hj b').lev.U_eq _).1 y.2).2 v

end Level


end GlobalTheory.PenLevPrime
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainStepIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvHaarVolumeToRealEqRelIndexIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvHaarVolumeToRealEqRelIndexIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped ENNReal

namespace GlobalTheory.HaarIdx

open MeasureTheory

theorem inv_toReal_eq_relIndex {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ] (μ : Measure Γ) [μ.IsMulLeftInvariant]
    (K H : Subgroup Γ) (hHK : H ≤ K) (hH : MeasurableSet (H : Set Γ)) (hK : μ (K : Set Γ) = 1)
    (hn : H.relIndex K ≠ 0) : ((μ (H : Set Γ)).toReal)⁻¹ = (H.relIndex K : ℝ) := by
  have hmeas : ∀ g : Γ, AEMeasurable (fun x => g * x) μ :=
    fun g => (measurable_const_mul g).aemeasurable
  have hpre : ∀ g : Γ, μ ((fun x => g * x) ⁻¹' (H : Set Γ)) = μ H := by
    intro g
    rw [← Measure.map_apply_of_aemeasurable (hmeas g) hH, map_mul_left_eq_self μ g]
  set L := H.subgroupOf K
  haveI : L.FiniteIndex := ⟨hn⟩
  haveI : Fintype (K ⧸ L) := Fintype.ofFinite _
  let C : (K ⧸ L) → Set Γ := fun q => (fun x => ((q.out : K) : Γ)⁻¹ * x) ⁻¹' (H : Set Γ)
  have hcov : (K : Set Γ) = ⋃ q, C q := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, C]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : K) : K ⧸ L), ?_⟩
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L (⟨x, hx⟩ : K)
      rw [hh]
      have : (((⟨x, hx⟩ : K) * (h : K) : K) : Γ)⁻¹ * x = ((h : K) : Γ)⁻¹ := by
        simp [_root_.mul_inv_rev, mul_assoc]
      rw [this]
      exact H.inv_mem (Subgroup.mem_subgroupOf.mp h.2)
    · rintro ⟨q, hq⟩
      have h1 : ((q.out : K) : Γ)⁻¹ * x ∈ K := hHK hq
      have h2 : ((q.out : K) : Γ) ∈ K := (q.out : K).2
      have := K.mul_mem h2 h1
      simpa [mul_assoc] using this
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) C) := by
    intro q q' hqq'
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro y hy hy'
    simp only [Set.mem_preimage, SetLike.mem_coe, C] at hy hy'
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    change (QuotientGroup.mk q.out : K ⧸ L) = QuotientGroup.mk q'.out
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := H.mul_mem hy (H.inv_mem hy')
    simpa [_root_.mul_inv_rev, mul_assoc] using this
  have hnull : ∀ q, NullMeasurableSet (C q) μ := fun q =>
    (hmeas _).nullMeasurableSet_preimage hH
  have hsum : μ (K : Set Γ) = (Fintype.card (K ⧸ L) : ℝ≥0∞) * μ H := by
    rw [hcov, measure_iUnion₀ hdisj hnull, tsum_fintype]
    simp [C, hpre, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (K ⧸ L) : ℕ) = H.relIndex K := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hK, hcard] at hsum
  have hne : μ (H : Set Γ) ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by exact_mod_cast hn)] at hsum; exact ENNReal.one_ne_top hsum
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one] at hr
  have hpos : (μ (H : Set Γ)).toReal ≠ 0 := by
    intro h; rw [h, mul_zero] at hr; exact one_ne_zero hr
  field_simp
  linarith [hr]

end GlobalTheory.HaarIdx

namespace GlobalTheory


theorem QTw.QExt.m_inv_toReal_eq_relIndex : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GlobalTheory.QTw.QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : GlobalTheory.QTw.QExt G χ) (j : ℕ) (H : Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)), H ≤ KO G.k _ → MeasurableSet (H : Set (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)) → H.relIndex (KO G.k _) ≠ 0 → ((((E.m j H).toReal)⁻¹ : ℝ) : ℂ) = (H.relIndex (KO G.k _) : ℂ) := by
  intro D c v B PP G χ E j H hHK hH hn
  letI : MeasurableSpace (Matrix (XIx (Fin D.R.k) (Fin D.R.t) j) (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := G.k)
  haveI : BorelSpace (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : MeasurableMul (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k) := ⟨
    fun g => (continuous_const.mul continuous_id).measurable,
    fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI := (E.haar j).1
  rw [HaarIdx.inv_toReal_eq_relIndex (E.m j) _ H hHK hH (E.haar j).2 hn]
  push_cast
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvHaarVolumeToRealEqRelIndexIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_haarVolume_toReal_eq_relIndex_integral : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : GlobalTheory.QTw.QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : GlobalTheory.QTw.QExt G χ) (j : ℕ) (H : Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)), H ≤ KO G.k _ → MeasurableSet (H : Set (GL (XIx (Fin D.R.k) (Fin D.R.t) j) G.k)) → H.relIndex (KO G.k _) ≠ 0 → ((((E.m j H).toReal)⁻¹ : ℝ) : ℂ) = (H.relIndex (KO G.k _) : ℂ) := by
  first | exact @GlobalTheory.QTw.QExt.m_inv_toReal_eq_relIndex | exact GlobalTheory.QTw.QExt.m_inv_toReal_eq_relIndex | (intros; apply GlobalTheory.QTw.QExt.m_inv_toReal_eq_relIndex <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.Fam
namespace VolMid

theorem index_pi_univ' {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod_of_pi {ι : Type} [Fintype ι] {G : Type} [Group G] {M : ι → Type} [∀ i, Group (M i)]
    (φ : G →* ((i : ι) → M i)) (Up U : Subgroup G) (K H : ∀ i, Subgroup (M i))
    (hK : ∀ g ∈ Up, ∀ i, φ g i ∈ K i) (hs : ∀ x : (i : ι) → M i, (∀ i, x i ∈ K i) → ∃ g ∈ Up, φ g = x)
    (hU : ∀ g, g ∈ U ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i) : U.relIndex Up = ∏ i, (H i).relIndex (K i) := by
  let ψ : Up →* ((i : ι) → K i) :=
    { toFun := fun g i => ⟨φ g.1 i, hK g.1 g.2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨g, hg, e⟩ := hs (fun i => (x i).1) (fun i => (x i).2)
    exact ⟨⟨g, hg⟩, by ext i; simp [ψ, e]⟩
  have e : U.subgroupOf Up = (Subgroup.pi Set.univ fun i => (H i).subgroupOf (K i)).comap ψ := by
    ext g
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_pi, hU, g.2, ψ]
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ hψ, index_pi_univ']
  rfl

end VolMid

open VolMid

end GlobalTheory.Fam
end
end
