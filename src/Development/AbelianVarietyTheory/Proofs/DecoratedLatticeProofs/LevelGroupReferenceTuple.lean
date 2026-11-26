module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobalRowsOfSizeParameters
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalHypothesesOfRowsAndWindow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselSecondStepFlatSupportRamified

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.BaseLevel

open NumberField IsDedekindDomain GlobalTheory.Mem.Col2 _root_.Formalism.L2.Forms GlobalTheory.SeeSaw GlobalTheory.SeeSaw.TopLevel

theorem levFn_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r t s : ℕ} (h : r ≤ n)
    (β) {SG Q : Finset (Pl E)} (P : LevelP SG r ℂ) (cg cg' : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ) (xq : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ)
    (e : ∀ c, c < s → ∀ PP ∈ SG, cg (c + 1) PP = cg' (c + 1) PP) (g) :
    levFn (F := F) β ⟨r, h, t, s, SG, Q, P, cg, xq⟩ g = levFn (F := F) β ⟨r, h, t, s, SG, Q, P, cg', xq⟩ g := by
  unfold levFn
  congr 2
  refine Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c hc => ?_
  exact congrArg (fun f : (kP PP)ˣ →* ℂˣ => f _) (e c (Finset.mem_range.1 hc) PP hPP)

theorem isRes_unique {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem isRes_chiC (h : I.Ok) (j : Fin B.R.m) (PP : Pl (I.rec7 l Z).host.E) (hw : PP ∈ (B.primes X).vGs) :
    IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (chiC I j PP)⁻¹ := by
  intro a k u hk hu
  have ht := (h.ch_tied.mu0 j).atg ⟨PP, hw⟩ k a u hk hu
  have e : ∀ (j : Fin B.R.m) (P : HeightOneSpectrum (𝓞 B.fields.E)) (hw : P ∈ (B.primes X).vGs),
      Formalism.L2.Col.chiP I.Ch P j = I.Ch.chi j ⟨P, hw⟩ := by
    intro j P hw
    unfold Formalism.L2.Col.chiP
    rw [dif_pos hw]
    simp [Formalism.L2.Col.chiAt, Formalism.L2.Col.extChi]
  refine Units.ext (Eq.trans ?_ ht.symm)
  have e2 := (chiC_apply I j PP u).trans (congrArg (fun f : _ →* B.LLˣ => B.embLL ((f u : B.LLˣ) : B.LL)) (e j PP hw))
  exact (Units.val_inv_eq_inv_val _).trans ((congrArg (·⁻¹) e2).trans
    ((map_inv₀ B.embLL _).symm.trans (congrArg B.embLL (Units.val_inv_eq_inv_val _).symm)))


set_option maxHeartbeats 2000000 in
theorem topLev_datY (ok : I.Ok) (pins : TC.Pins B X) (v : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) (hF : I.StdF l Z v F) (hr : (I.rec7 l Z).R.r ≤ (I.rec7 l Z).sp.X'.rank)
    (P' : LevelP (B.primes X).vGs B.R.r ℂ) (cg : ℕ → ∀ PP : Pl B.fields.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl B.fields.E, (kP PP)ˣ →* ℂˣ)
    (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (I.Ps w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (I.Ps w).H),
      ((P'.chi g : ℂˣ) : ℂ) = ∏ w, B.embLL (((I.Ps w).lam ⟨g.1 w, hg w⟩ : B.fields.Kˣ) : B.fields.K))
    (hcg : ∀ (j : Fin B.R.m), ∀ PP ∈ (B.primes X).vGs, IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (cg ((j : ℕ) + 1) PP)⁻¹) :
    GlobalTheory.Core.Rk.Top.TopLev F.clsP
      (levS (I.rec7 l Z).sp.X' 1 (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr (B.primes X).vGs ∅ P' cg ξ Frm.B))
      (levChi (I.rec7 l Z).sp.X' 1 (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr (B.primes X).vGs ∅ P' cg ξ Frm.B)) := by
  have hK := hF.what₂
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I ok pins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  obtain ⟨c', -⟩ := F.clsP.y_bij.2 (Quotient.mk'' 1)
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hR := rd_all I hK c'
  have hLb : F.clsP.lev.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  have key := @lev_iff B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ F.clsP.lev hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs I.Ps (Formalism.L2.Col.chiAt I.Ch) B.embLL hR
    P' (fun i => chiC I (i - 1)) (fun PP => (ξ PP)⁻¹) hH hchi
    (fun i PP a => by
      have e : Formalism.L2.Col.chiP I.Ch PP.1 = Formalism.L2.Col.chiAt I.Ch PP := dif_pos PP.2
      show B.embLL ((Formalism.L2.Col.chiP I.Ch PP.1 i a : B.LLˣ) : B.LL) = _
      rw [e])
  have hc : ∀ c, c < B.R.m → ∀ PP ∈ (B.primes X).vGs, cg (c + 1) PP = chiC I (c + 1 - 1) PP := fun c hc PP hPP =>
    inv_injective (isRes_unique (D := I.rec7 l Z) (hcg ⟨c, hc⟩ PP hPP) (isRes_chiC I l Z ok ⟨c, hc⟩ PP hPP))
  refine ⟨fun h => ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).1.2 κ.2⟩⟩, fun h κ hκ => ?_⟩
  · obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' h)
    exact ⟨⟨y, (key _ y hy).1.1 hh.2⟩, hh.1, hy⟩
  · refine Eq.trans ?_ ((key _ κ.1 hκ.2).2 κ.2)
    exact congrArg Units.val (levFn_congr (F := B.fields.F) hr 1 P' cg (fun i => chiC I (i - 1)) (fun PP => (ξ PP)⁻¹) hc _)


set_option maxHeartbeats 2000000 in
theorem topLev_levPOf (ok : I.Ok) (pins : TC.Pins B X) (v : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) (hF : I.StdF l Z v F) (hr : (I.rec7 l Z).R.r ≤ (I.rec7 l Z).sp.X'.rank)
    (Pg Q : Finset (Pl (I.rec7 l Z).host.E)) (β : GL (Fin (I.rec7 l Z).sp.X'.rank) (EAf (I.rec7 l Z)))
    (hPg : Pg = (B.primes X).vGs) (hQ : Q = ∅) (hβ : β = 1) (eG : R3.Gc B X ≃* G0 Pg (I.rec7 l Z).R.r)
    (hG : ∀ (g : R3.Gc B X) (P : Pl (I.rec7 l Z).host.E) (h : P ∈ (B.primes X).vGs) (h' : P ∈ Pg), eG g ⟨P, h'⟩ = g ⟨P, h⟩)
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hcg : ∀ (j : Fin B.R.m), ∀ PP ∈ Pg, IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (cg ((j : ℕ) + 1) PP)⁻¹) :
    GlobalTheory.Core.Rk.Top.TopLev F.clsP
      (levS (I.rec7 l Z).sp.X' β (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr Pg Q
        (levPOf (D := I.rec7 l Z) eG B.embLL (R3.lev1 I) (R3.chr1 I)) cg ξ Frm.B))
      (levChi (I.rec7 l Z).sp.X' β (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr Pg Q
        (levPOf (D := I.rec7 l Z) eG B.embLL (R3.lev1 I) (R3.chr1 I)) cg ξ Frm.B)) := by
  subst hPg hQ hβ
  have he : ∀ g w, eG.symm g w = g w := fun g w =>
    (hG (eG.symm g) w.1 w.2 w.2).symm.trans (congrFun (eG.apply_symm_apply g) w)
  refine topLev_datY I l Z ok pins v F hF hr _ cg ξ (fun g => ?_) (fun g hg => ?_) hcg
  · exact ⟨fun h w => he g w ▸ h w (Set.mem_univ w), fun h w _ => (he g w).symm ▸ h w⟩
  · have e := Formalism.L2.Col.LevFam.chr_apply (X := B.fields) I.Ps ⟨eG.symm g.1, g.2⟩
    refine (congrArg (fun x : B.fields.Kˣ => B.embLL (x : B.fields.K)) e).trans ?_
    show B.embLL ((∏ w, _ : B.fields.Kˣ) : B.fields.K) = _
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact congrArg (fun x => B.embLL (((I.Ps w).lam x : B.fields.Kˣ) : B.fields.K)) (Subtype.ext (he g.1 w))

def PairDataBaseTupleLevelEqualsClassLevel {D : D7} {O : Obj D} (x : R3.TwIn O.ex) {u : D.what₂.Word} (K₀ : ClsPTied u) : Prop :=
  ∀ t : x.T, x.Y.tup t = D.what₂.mu0 →
    GlobalTheory.Core.Rk.Top.TopLev K₀ (levS _ x.R.βX (datXP x.R.toRealDat (x.R.toRealDat.levR x.F.lv2 true) t))
      (levChi _ x.R.βX (datXP x.R.toRealDat (x.R.toRealDat.levR x.F.lv2 true) t))




end GlobalTheory.Fam.BaseLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TraceLowerBoundAllMembers
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThrEAddOneLt
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.DsigSize

theorem thrE_add_one_lt {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) :
    Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
  have hn := Formalism.MainNotions.nS_cast D
  have h6 := Formalism.MainNotions.six_le_n D
  rw [← hn] at h6 ⊢
  set n : ℝ := ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ)
  have hthr : Formalism.MainNotions.GapDS.thrE (epsSH D.R) ≤ 4 * n ^ 3 :=
    Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by linarith only [h6])
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have hmf : D.R.m ^ 4 ≤ D.R.f := by unfold StandingHypotheses at hH; exact hH.2.2.1
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast le_trans this hmf
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hn3 : 1 ≤ n ^ 3 := one_le_pow₀ (by linarith only [h6])
  have hn16 : 6 ≤ n ^ 16 :=
    (show (6 : ℝ) ≤ 6 ^ 16 by norm_num).trans (pow_le_pow_left₀ (by norm_num) h6 16)
  calc
    _ < 4 * n ^ 3 + 2 := by linarith only [hthr]
    _ ≤ 6 * n ^ 3 := by linarith only [hn3]
    _ ≤ n ^ 16 * n ^ 3 := mul_le_mul_of_nonneg_right hn16 (by positivity)
    _ = n ^ 19 := (pow_add n 16 3).symm
    _ ≤ n ^ 19 * (D.R.f : ℝ) ^ 5 := le_mul_of_one_le_right (by positivity) hf5
    _ ≤ (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5) :=
      le_mul_of_one_le_left (by positivity) hCL
    _ = Cl * n ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by ac_rfl

theorem dsigHC : Formalism.L2.SG.Pf.SzHypFD.DsigHC := by
  intro D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ
  exact GlobalTheory.dsig_eq_fdegHC_of_gap D hT τ _ (Formalism.MainNotions.BridgeLemma.szh_hc hH τ) (Formalism.MainNotions.BridgeLemma.szh_gap hH τ)
    (thrE_add_one_lt hH hCL)

end GlobalTheory.DsigSize
end
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.LevLow

theorem cloudUnit_lower {x eps k f CD cD : ℝ} (hx : 1 ≤ x) (he : eps ≤ 1) (hk0 : 0 ≤ f) (hfk : f ≤ k)
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

theorem Dstar_mass (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    X.toD7.what₂.Dstar = StandardLattice.massI X.toD7 X.toD7.R.r * StandardLattice.idxSig X.toD7 (X.toD7.host.g 0) (X.toD7.host.g 1) *
      ∏ τ, X.toD7.dsig τ := by
  have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
  rw [e, hO.sizes.2]
  unfold DsPre
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

theorem admissibleRanks_of_mass_formula (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D)
    (hD : D.what₂.Dstar = StandardLattice.massI D D.R.r * StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ τ, D.dsig τ) :
    LocalBesselAndTopKernel.FamilyMidVolume D := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  intro V _ _ _ _ h L _
  refine ⟨fun hL u => ?_, fun hL => ?_⟩
  · have e := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
      (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
    have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.k := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.k)
    rw [em, ← Formalism.MainNotions.J.idxColTie_holds D]
    exact e
  · have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.r := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.r)
    rw [em, ← Formalism.MainNotions.J.idxRowTie_holds D, hD]

theorem eventually_le_trace : EvP fun _ K => ∀ β : BPt K, LocalBesselAndTopKernel.FamilyMidVolume β.D → (∀ u, GlobalTheory.Core.Rk.RankMu β.D u) →
    ∀ u : β.D.what₂.Word, β.O.L.sc.b ^ ((1 / 2 : ℝ) * (β.D.R.m : ℝ)) ≤ Formalism.MainNotions.S.Tr β.D u := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨max c1 (11 * 40), fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD (le_trans (le_max_left _ _) hcD)
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch hch
  obtain ⟨x2, hNo⟩ := GlobalTheory.Diag.PG.NodeParameters.nodes_of_parameters eps he he52
  obtain ⟨x3, hP⟩ := GlobalTheory.T.diagonal_hypotheses_of_rows_and_window GlobalTheory.Mass.siegelMassRatio_holds GlobalTheory.DsigSize.dsigHC eps 40 he he52 (by norm_num)
    (8 * C.CGam) 40 (C.P.CYL + 1) 0 le_rfl le_rfl
  refine ⟨max (max x1 x2) (max x3 ((max 2 (5 / (eps / 100))) ^ (eps / 100)⁻¹)), fun K hK hx β hAdm hMu => ?_⟩
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
  have hDl : ((β.D.R.k : ℝ) * (β.D.R.f : ℝ) * β.O.L.sc.x ^ eps) ^ (40 : ℝ) ≤ ((β.D.s.Del : ℚ) : ℝ) := by
    rw [hDel]
    exact cloudUnit_lower hx1.le (by linarith) (by positivity) G0.nums.fk G0.nums.k_hi (by norm_num)
      (le_trans (le_max_right _ _) hcD)
  have G : GlobalTheory.Diag.PG.Glob0 β.D β.O.L.sc.x eps 40 (C.P.CYL + 1) :=
    ⟨⟨G0.nums.m_lo, G0.nums.mf, G0.nums.fk, G0.nums.k_lo, G0.nums.k_hi, G0.nums.lrd_lo, G0.nums.lrd_hi, hDl,
      G0.nums.Del_hi⟩, G0.g_win, G0.gap, G0.cloud, G0.off, G0.rd_lo⟩
  have hNd := hNo β.D β.O.L N.params N.sizes hse (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx')
  have hL : β.O.L.sc.L = β.O.L.sc.x ^ eps := by rw [← hse]; rfl
  have h8 : 8 * β.O.L.CGam ≤ 8 * C.CGam := by rw [N.CGam_eq]
  have hW : GlobalTheory.Diag.PG.DuWin β.D 3 := GlobalTheory.Diag.PG.duWin_three_of_count β.D (fun u' => by
    have h := hMu u'
    unfold GlobalTheory.Core.Rk.RankMu at h
    rw [GlobalTheory.Core.Rk.d0_eq] at h
    exact h)
  obtain ⟨⟨-, hHS, -⟩, -, -, -⟩ := hP β.O.L.sc.x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx') β.D β.O.L
    hL h8 β.p.pt.xa.ties hAdm G hNd hW
  have hH := GlobalTheory.Core.Deg.hypL_of hHS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT, -, -⟩ := hH
  exact fun u => (hT u).1

end GlobalTheory.Core.LevLow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurScalarLemma
noncomputable section

namespace GlobalTheory.TopVal.Scalar

section Alg

open Formalism.BasicNotions _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms Matrix GlobalTheory.CoefSpace

theorem schur {G W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] (ρ : G → Module.End ℂ W)
    (hirr : ∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) (T : Module.End ℂ W)
    (hT : ∀ h w, T (ρ h w) = ρ h (T w)) : ∃ a : ℂ, ∀ w, T w = a • w := by
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue T
  refine ⟨a, fun w => ?_⟩
  have h := (hirr (T.eigenspace a) fun h => ?_).resolve_left ha
  · exact Module.End.mem_eigenspace_iff.1 (h ▸ Submodule.mem_top)
  · rintro _ ⟨x, hx, rfl⟩
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [hT, Module.End.mem_eigenspace_iff.1 hx, map_smul]

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem exists_ext {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (c : VV K lam →ₛₗ[σ] W) : ∃ c' : VV ℂ lam →ₗ[ℂ] W, ∀ w, c' (bcVV σ lam w) = c w := by
  let b := Module.Basis.mk (bcVV_indep σ lam) (bcVV_span σ lam).ge
  refine ⟨b.constr ℂ fun i => c (bVV K lam i), fun w => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (bVV K lam).sum_repr w, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : bcVV σ lam (bVV K lam i) = b i := (Module.Basis.mk_apply (bcVV_indep σ lam) (bcVV_span σ lam).ge i).symm
  rw [map_smulₛₗ (bcVV σ lam), map_smul, e, Module.Basis.constr_basis, map_smulₛₗ c]

theorem ext_bc {K W : Type} [Field K] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (lam : ι → DomWeight n)
    {f g : VV ℂ lam →ₗ[ℂ] W} (h : ∀ w, f (bcVV σ lam w) = g (bcVV σ lam w)) : f = g :=
  LinearMap.ext_on_range (bcVV_span σ lam) fun _ => h _

theorem fnOf_actP (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (P : Pol ℂ ι n)
    (y y' : Frames G) (h : ∀ τ, y'.1 τ = (g τ : Matrix (Fin n) (Fin n) ℂ)ᵀ * y.1 τ) :
    fnOf G (shiftOf lam) 1 (actP lam g P) y = fnOf G (shiftOf lam) 1 P y' := by
  have e := Formalism.L2.Col.evFr_actP G (RingHom.id ℂ) lam g P
  rw [Formalism.L2.Col.evFr_eq_fnOf] at e
  simp only [MvPolynomial.map_id] at e
  rw [e]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, h]
  rfl

theorem exists_equiv (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    {V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Frames G → ℂ))
    (hinj : Function.Injective j) (hr : LinearMap.range j = ValC G lam) :
    ∃ φ : V ≃ₗ[ℂ] VV ℂ lam, ∀ v, j v = fnOf G (shiftOf lam) 1 (φ v).1 := by
  have hf : Function.Injective (fnOf G (shiftOf lam) 1) :=
    Formalism.L2.Col.fnOf_injective G _ 1 (fun τ => by simp) ⟨fun _ => 1, fun τ => by simp⟩
  have hr' : LinearMap.range j = (VV ℂ lam).map (fnOf G (shiftOf lam) 1) := by
    rw [hr, ValC, GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]
  refine ⟨(LinearEquiv.ofInjective j hinj).trans ((LinearEquiv.ofEq _ _ hr').trans
    (Submodule.equivMapOfInjective _ hf (VV ℂ lam)).symm), fun v => ?_⟩
  exact (congrArg Subtype.val ((Submodule.equivMapOfInjective _ hf (VV ℂ lam)).apply_symm_apply
    (LinearEquiv.ofEq _ _ hr' (LinearEquiv.ofInjective j hinj v)))).symm

end Alg

section Group

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.DefLift GlobalTheory.CoefSpace GlobalTheory.DefiniteMult Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {θ : InfFam D} {c : CoefA V}
  {pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ}

theorem infGL_fin {h : GA D V} (hh : h ∈ GfC V) : infGL θ V h = 1 := by
  have h1 : infHom V h = 1 := hh
  rw [infGL, MonoidHom.comp_apply, h1, map_one]

theorem eqv_real (hθ : IsInfFam θ) (hc : c.Is) (lam : D.what₂.Tau → DomWeight V.rank) (f : VV ℂ lam →ₗ[ℂ] c.W)
    (hf : ∀ γ ∈ GQ V, ∀ x, f (rhoK lam (infGL θ V γ) x) = c.ρ γ (f x)) {u : GA D V} (hu : u ∈ GinfC V) (x : VV ℂ lam) :
    f (rhoK lam (infGL θ V u) x) = c.ρ u (f x) := by
  by_contra hne
  have h0 : ∀ f' : (coefA θ V lam 1).W →ₗ[ℂ] c.W, Continuous f' := fun f' => f'.continuous_of_finiteDimensional
  have h1 : Continuous fun h : GA D V => f (rhoK lam (infGL θ V h) x) := (h0 f).comp (coefA_cont lam 1 hθ x)
  obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _ (isOpen_ne_fun h1 (hc.2.2.1 (f x))) hne
  refine hU ?_
  rw [map_mul, infGL_fin hk, mul_one, map_mul, hc.1 k hk, mul_one]
  exact hf γ hγ x

theorem infGL_rat (hθ : IsInfFam θ) {K : Type} [Field K] (σ : K →+* ℂ) (emb : D.what₂.Tau → D.host.E →+* K)
    (hemb : ∀ τ x, σ (emb τ x) = tauE D τ x) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (hγ : Bridge.IsRatMat V γ γE) :
    infGL θ V γ = fun τ => Formalism.UG.bc σ (embGL emb γE τ) := by
  funext τ
  refine Units.ext (Matrix.ext fun a b => ?_)
  have h1 : ((matHom V (γ : GA D V)).1 a b) = incA D (γE.1 a b) := by
    rw [show matHom V (γ : GA D V) = _ from hγ]
    rfl
  show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((matHom V (γ : GA D V)).1 a b)) = σ (emb τ (γE.1 a b))
  rw [h1, hemb, ← (hθ τ).1]
  exact congrArg (θ τ) ((Algebra.TensorProduct.map_tmul _ _ _ _).trans (by rw [map_one]; rfl))


open Classical in
theorem eqv_transpose (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr)
    (lam : D.what₂.Tau → DomWeight V.rank) (φ : SmT M →ₗ[ℂ] VV ℂ lam)
    (hφ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      (φ (PiTensorProduct.tprod ℂ (Function.update v τ w))).1 =
        actP lam (invTrK (infGL θ V (atTau θ V τ g))) (φ (PiTensorProduct.tprod ℂ v)).1)
    (f : VV ℂ lam →ₗ[ℂ] c.W) (hf : ∀ w v, pr (f w) v = pairBK lam (φ v) w) {u : GA D V} (hu : u ∈ GinfC V) (x : VV ℂ lam) :
    f (rhoK lam (infGL θ V u) x) = c.ρ u (f x) := by
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  let U : Submonoid (GA D V) :=
    { carrier := {h | ∀ x, f (rhoK lam (infGL θ V h⁻¹) x) = c.ρ h⁻¹ (f x)}
      one_mem' := fun x => by rw [inv_one, map_one, map_one, map_one]; rfl
      mul_mem' := fun {a b} ha hb x => by
        rw [_root_.mul_inv_rev, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha] }
  have key := real_le hθ U (fun τ g hg x => ?_) (inv_mem hu) x
  · rwa [inv_inv] at key
  refine (pair_bijective hθ hp hc hpr).1 (PiTensorProduct.ext (MultilinearMap.ext fun v => ?_))
  let y : M.sm τ := ⟨M.rep τ g (v τ), Submodule.eq_top_iff'.1 (m τ).2.1 _⟩
  have h1 := hpr.2 τ g hg (c.ρ (atTau θ V τ g)⁻¹ (f x)) v y rfl
  rw [GlobalTheory.DefiniteEnd.rho_inv_cancel] at h1
  show pr _ (PiTensorProduct.tprod ℂ v) = pr _ (PiTensorProduct.tprod ℂ v)
  rw [← h1, hf, hf, pairBK_apply, pairBK_apply, hφ τ g hg v y rfl,
    ← pairingBInvariantK_holds ℂ _ _ lam (infGL θ V (atTau θ V τ g)), ← rhoK_coe lam (infGL θ V (atTau θ V τ g)), rhoK_mul, ← map_mul,
    mul_inv_cancel, map_one, rhoK_one]


open Classical in
theorem exists_scalar (hθ : IsInfFam θ) (hp : AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) {n : ℕ} (hn : V.rank = n)
    (lam : D.what₂.Tau → DomWeight n) {K : Type} [Field K] (σ : K →+* ℂ) (emb : D.what₂.Tau → D.host.E →+* K)
    (hemb : ∀ τ x, σ (emb τ x) = tauE D τ x) (cv : VV K lam →ₛₗ[σ] c.W)
    (hcv : ∀ (γ : GQ V) γE (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → GlobalTheory.Mem.R3.MatEq γE g →
      ∀ v, cv (rhoV emb lam g v) = c.ρ γ.1 (cv v)) (h0 : cv ≠ 0)
    (G G' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (o : Frames G') (ho : (fun τ => (o.1 τ)⁻¹) = 1)
    (j : SmT M →ₗ[ℂ] (Frames G → ℂ)) (hinj : Function.Injective j) (hr : LinearMap.range j = ValC G lam)
    (heqv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      ∀ y y' : Frames G, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr hn) (finCongr hn))) y' y →
        j (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = j (PiTensorProduct.tprod ℂ v) y') :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ w v, pr (cv w) v =
      a * pairB lam (Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)) (MvPolynomial.map σ w.1) := by
  subst hn
  obtain ⟨φ, hφ⟩ := exists_equiv G lam j hinj hr
  have hf : Function.Injective (fnOf G (shiftOf lam) 1) :=
    Formalism.L2.Col.fnOf_injective G _ 1 (fun τ => by simp) ⟨fun _ => 1, fun τ => by simp⟩
  have hpol : ∀ v, Formalism.L2.Col.polOf G' (shiftOf lam) o (j v) = (φ v).1 := fun v => by
    have h := Formalism.L2.Col.polOf_fnOf G' (shiftOf lam) o (φ v).1
    rw [ho] at h
    rw [hφ]
    exact h
  haveI : FiniteDimensional ℂ (VV ℂ lam) := Module.Finite.of_basis (bVV ℂ lam)
  have hB : (pairBK (K := ℂ) lam).flip.Nondegenerate := LinearMap.flip_nondegenerate.mpr (pairingBNondegenerate_holds ℂ _ _ lam)
  let e := LinearEquiv.ofBijective pr (pair_bijective hθ hp hc hpr)
  let f : VV ℂ lam ≃ₗ[ℂ] c.W := (LinearMap.BilinForm.toDual _ hB).trans (φ.dualMap.trans e.symm)
  have hfp : ∀ w v, pr (f w) v = pairBK lam (φ v) w := fun w v =>
    LinearMap.congr_fun (e.apply_symm_apply (φ.dualMap (LinearMap.BilinForm.toDual _ hB w))) v
  have h2 : ∀ u ∈ GinfC V, ∀ x, f (rhoK lam (infGL θ V u) x) = c.ρ u (f x) := fun u hu x => by
    refine eqv_transpose hθ hp hc hpr lam φ.toLinearMap (fun τ g hg v w hw => hf (funext fun y => ?_)) f.toLinearMap hfp hu x
    have ha : IsAtTau θ V τ g (atTau θ V τ g) := by
      have hex := (GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ g hg).exists
      rw [atTau, dite_eq_left hex]
      exact hex.choose_spec
    set A := infGL θ V (atTau θ V τ g) with hA
    let y' : Frames G := ⟨fun ρ => ((A ρ)⁻¹ : GL (Fin V.rank) ℂ).1 * y.1 ρ, fun ρ => by
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).mul (y.2 ρ)⟩
    rw [fnOf_actP G lam _ _ y y' fun ρ => by rw [invTrK_coe, Matrix.transpose_transpose]]
    have := heqv τ g hg v w hw y y' fun ρ => by
      have e1 : Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ
          (g.reindex (finCongr rfl) (finCongr rfl)) ρ = (A ρ).1 := by
        by_cases hρ : ρ = τ
        · subst hρ
          rw [Function.update_self]
          exact ha.2.1.symm
        · rw [Function.update_of_ne hρ]
          exact (ha.2.2 ρ hρ).symm
      rw [e1]
      show y.1 ρ = (A ρ).1 * (((A ρ)⁻¹ : GL (Fin V.rank) ℂ).1 * y.1 ρ)
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [hφ, hφ] at this
    exact this
  obtain ⟨c', hc'⟩ := exists_ext σ lam cv
  have h1 : ∀ u ∈ GinfC V, ∀ x, c' (rhoK lam (infGL θ V u) x) = c.ρ u (c' x) := fun u hu x => by
    refine eqv_real hθ hc lam c' (fun γ hγ x => ?_) hu x
    obtain ⟨γE, -, hE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hE' : Bridge.IsRatMat V ⟨γ, hγ⟩ γE := hE.symm
    refine LinearMap.congr_fun (ext_bc σ lam (f := c' ∘ₗ rhoK lam (infGL θ V γ)) (g := c.ρ γ ∘ₗ c') fun w => ?_) x
    have e2 : rhoK lam (infGL θ V γ) (bcVV σ lam w) = bcVV σ lam (rhoV emb lam γE w) := by
      refine Subtype.ext ?_
      show actP lam (infGL θ V γ) (MvPolynomial.map σ w.1) = MvPolynomial.map σ (actP lam (embGL emb γE) w.1)
      rw [GlobalTheory.CoefSpace.map_actP, ← infGL_rat hθ σ emb hemb ⟨γ, hγ⟩ γE hE']
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e2, hc', hc']
    exact hcv ⟨γ, hγ⟩ γE γE hE' ⟨rfl, fun i j i' j' hi hj => by rw [Fin.ext hi, Fin.ext hj]⟩ w
  haveI := hc.2.2.2.1
  obtain ⟨a, ha⟩ := schur (fun h => c.ρ h) hc.2.2.2.2 (c' ∘ₗ f.symm.toLinearMap) fun h w => by
    obtain ⟨u, hu, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
    obtain ⟨x, rfl⟩ := f.surjective w
    show c' (f.symm (c.ρ (u * k) (f x))) = c.ρ (u * k) (c' (f.symm (f x)))
    rw [map_mul, hc.1 k hk, mul_one, ← h2 u hu, f.symm_apply_apply, f.symm_apply_apply, h1 u hu]
  have ha' : ∀ w, cv w = a • f (bcVV σ lam w) := fun w => by
    rw [← ha, ← hc']
    exact congrArg c' (f.symm_apply_apply _).symm
  refine ⟨a, fun h => h0 (LinearMap.ext fun w => by rw [ha', h, zero_smul]; rfl), fun w v => ?_⟩
  rw [ha', map_smul, LinearMap.smul_apply, hfp, smul_eq_mul, pairBK_apply, hpol]
  rfl

end Group

end GlobalTheory.TopVal.Scalar

end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawSupportOffLevelOfLatticeShape
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawSupportOffLevelOfLatticeShape
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem offOfShape_of_supp (h1 : SuppFirst D) (h2 : SuppSecond D) : OffOfShape D := by
  intro c v k _ _ _ _ ι o hc hv hS t w ht hQ hU j σ h Φ₁ Φ₂ hΦ₁ hΦ₂
  have hD : DblShape (t.sBF j (σ + 1) h) (t.sFB j σ h)
      (⟨v.N j, o.M j (σ + 1) h, v.N (j + 1), (c.x (j + 1)).L, v.N (j + 1 + 1), o.M (j + 1 + 1) σ (idx_step h)⟩ :
        DblLat (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))) (offP v w) o.q
      ⟨o.β j, o.β₀ j (σ + 1) h, o.Q j⟩ ⟨o.β (j + 1), o.Q (j + 1)⟩
      ⟨o.β (j + 1 + 1), o.β₀ (j + 1 + 1) σ (idx_step h), o.Q (j + 1 + 1)⟩ :=
    { inj := hS.pre.inj
      mem := fun i => ⟨fun hg => Finset.disjoint_left.1 hv.disj hg ((hS.pre.tP _).2 ⟨i, rfl⟩),
        fun hg => Finset.disjoint_left.1 hQ hg ((hS.pre.tP _).2 ⟨i, rfl⟩)⟩
      good := fun x _ => (hS.good x).bf j (σ + 1) h
      adapt := fun x _ => (hS.good x).fb j σ h
      unr := fun x hx => ⟨hU.bf j (σ + 1) h x hx, hU.fb j σ h x hx⟩
      split := fun x _ hx => by
        obtain ⟨LL, a, b⟩ := (hS.split x fun hx' => by
          obtain ⟨i, hi⟩ := (hS.pre.tP x).1 hx'
          exact hx i hi).core (j + 1 + 1) σ (idx_step h)
        exact ⟨(c.x (j + 1 + 1)).L, LL, (hc.x _ (by omega)).sd, a, b⟩
      gl := fun i => hS.glued j (σ + 1) h i
      gl' := fun i => hS.glued (j + 1 + 1) σ (idx_step h) i
      mid := fun i => hS.pre.latT (j + 1) (by omega) i }
  have A := h1 c.ψ (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) _ _ _ _ (offP v w) hD.good
    (fun x hx => (hD.unr x hx).1) (hv.sd (j + 1) (by omega)) Φ₁ hΦ₁
  have B := h2 k ι o.p _ _ _ o.q c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ (offP v w) _ _ _ hD
    (hv.sd (j + 1 + 1) (by omega)) Φ₁ Φ₂ hΦ₁ hΦ₂
  have one : ∀ (S : HSp D) (L : Lat S), InK S L (offP v w) 1 := fun S L =>
    ⟨one_mem _, fun y _ => by simp [Formalism.L2.Theta.mt]⟩
  rw [← (ht.sBF j (σ + 1) h).1, ← (ht.sFB j σ h).1]
  refine ⟨fun κ hκ => ⟨A.1 1 κ (one _ _) hκ, B.1 κ 1 hκ (one _ _)⟩, fun κ hκ => B.1 1 κ (one _ _) hκ,
    (A.2 1 (one_mem _)).1, fun φ hφ h₂ => (B.2 1 (one_mem _)).2 1 (one_mem _) φ ?_ h₂⟩
  rw [hS.ram] at hφ
  exact hφ

theorem offOfShape_all : ∀ D : D7, OffOfShape D := fun D => offOfShape_of_supp (GlobalTheory.T.besselToJacobiFirstStepFlatMapSupport_all D) (GlobalTheory.T.jacobiToBessel_second_step_flat_support_ramified D)

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawSupportOffLevelOfLatticeShapeStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_support_off_level_of_lattice_shape : ∀ D : D7, GlobalTheory.SeeSaw.OffOfShape D := by
  first | exact @GlobalTheory.SeeSaw.offOfShape_all | exact GlobalTheory.SeeSaw.offOfShape_all | (intros; apply GlobalTheory.SeeSaw.offOfShape_all <;> assumption)
end
end
