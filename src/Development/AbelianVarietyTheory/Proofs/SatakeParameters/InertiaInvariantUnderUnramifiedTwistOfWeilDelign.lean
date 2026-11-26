module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelign
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelign
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.IneUnrTwist

open Formalism.MainNotions Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct

theorem wd_inePol_twist {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} (a χ : WD h) (h1 : χ.lpDim = 1)
    (hu : χ.unr) {s : G E Ω} (hs : s ∈ Ine (F := E) B) : (a.lpChar χ).inePol s = a.inePol s := by
  induction a using WD.ind with | hP n a => ?_
  induction χ using WD.ind with | hP m c => ?_
  rw [WD.lpDim_mk] at h1
  rw [WD.unr_mk] at hu
  rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hs, WD.inePol_of_mem_Ine _ hs, WD.charPol_mk, WD.charPol_mk,
    WDRep.tensor_ρ, hu.2]
  let e : (Fin m → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by simpa using h1)
  let E' := (TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) e).trans (TensorProduct.rid ℂ _)
  rw [← LinearEquiv.charpoly_conj E']
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [E', LinearEquiv.conj_apply]

theorem main : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := fun D T w a χ h1 hu s hs => by
  rw [T.inePol w _ s hs, T.inePol w _ s hs, T.char w a χ h1]
  exact wd_inePol_twist _ _ ((T.dim w χ).trans h1) ((T.unr w χ).1 hu) hs

end GlobalTheory.IneUnrTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelignStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaInvariantUnderUnramifiedTwist_of_weilDeligne : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := by
  first | exact @GlobalTheory.IneUnrTwist.main | exact GlobalTheory.IneUnrTwist.main | (intros; apply GlobalTheory.IneUnrTwist.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvParamsOfRows
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.RowsLed


open Formalism.MainNotions.Inhab _root_.Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB in
set_option maxHeartbeats 1000000 in
theorem ev_exists_sizeData_untwisted : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0) →
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ Nonempty (ParameterChoice' X.toD7 L) := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  exact ⟨L, e1, ⟨M.params⟩⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem aj_untw {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    ∀ v, (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (w.D Z).what₂.Aj j v = 0 := by
  intro v hv j h1 h2
  have hn : v ∉ Wt := fun h => (V4.Model.mem_iff t.mu v).1 h hv
  have hc : (w.D Z).what₂.places.conj v ∉ Wt := fun h =>
    (V4.Model.mem_iff t.mu _).1 h (((w.st Z).W.muAt_conj v).trans hv)
  have a := t.untw v hn j h1 h2
  have b := t.untw _ hc j h1 h2
  unfold Rows.Data.Aj
  rw [hv, a.1, a.2, b.1]
  rfl

theorem ev_exists_sizeData_of_rows : GlobalTheory.Mem.Top.Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)), RowsT K w Z Wt p0 → K.Over B.toPre → ∃ L : SizeData₂ (w.D Z), L.sc = K.s ∧ Nonempty (ParameterChoice' (w.D Z) L) :=
  V4.Model.ev_imp ev_exists_sizeData_untwisted fun _ H _ _ _ w Z _ _ t hO => H (w.st Z) hO t.etaF (aj_untw t)

end GlobalTheory.Mem.RowsLed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.XdInert

theorem gidx_facts : ∀ (D : D7) (T p : ℕ), GIdx D.host T p →
    5 ≤ p ∧ GL3Theta.InertK D p ∧ Nat.Coprime T p ∧ ∀ i, p ≠ D.host.g i := by
  intro D T p h
  obtain ⟨hp, h5, hc, hn, hl, hT⟩ := h
  refine ⟨h5, ?_, ?_, ?_⟩
  · exact (GlobalTheory.TwU.Served.served_facts D p hp hc hn).2.1
  · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hT).symm
  · intro i hi
    exact hl (hi ▸ D.host.g_level i)

end GlobalTheory.TwU.XdInert
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetUnitaryAdelicPointGramStepNormOne
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem det_unitary_adelic_point_gram_step_norm_one : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), Matrix.GeneralLinearGroup.det x.1 ∈ Formalism.L2.DIV.U1 (sigD D) := by
  intro D i hi x
  exact Formalism.L2.DIV.det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) x.1 x.2

end GlobalTheory.TwV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReindexRenamePointDetLatK
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem reindex_rename_point_det_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N n : ℕ} (h : N = n) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (y : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb : Submodule (𝓞 E) (Fin N → E)), Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = y ∧ Matrix.GeneralLinearGroup.det (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = Matrix.GeneralLinearGroup.det y ∧ HEq ((latK sp (J.reindex (finCongr h) (finCongr h)) a (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) (Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E)))).map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N n h J a y Lb
  subst h
  have hr : ∀ {A : Type} [CommRing A] (g : GL (Fin N) A), Formalism.L2.PairingIndexBounds.F.reGL (finCongr (rfl : N = N)) g = g := by
    intro A _ g
    ext i j
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  have hJ : J.reindex (finCongr (rfl : N = N)) (finCongr (rfl : N = N)) = J := by
    ext i j
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, hr]
  · rw [hr]
  · apply heq_of_eq
    rw [hJ, hr, map_reE_rfl, map_reE_rfl]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassC0PrimeNotExceptional
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.HalfDiffInt

theorem prime_not_dvd_discr (D : D7) {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d) :
    ¬ p ∣ (discr D.host.E).natAbs :=
  UpperTheory.Ram.not_dvd_natAbs_discr D.host hp h2 hq hd

theorem absNorm_dvd_discr (D : D7) : Ideal.absNorm D.host.𝔟 ∣ (discr D.host.E).natAbs := by
  have htow := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow D.host.K (𝓞 D.host.K)
    D.host.E (𝓞 D.host.E)
  rw [htow, D.host.𝔟_spec.1, map_mul, mul_assoc]
  exact Dvd.intro _ rfl

theorem absNorm_coprime (D : D7) {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d) :
    Nat.Coprime (Ideal.absNorm D.host.𝔟) p := by
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  exact prime_not_dvd_discr D hp h2 hq hd (dvd_trans h (absNorm_dvd_discr D))

theorem inv_integral_off (D : D7) {p : ℕ} (hp : p.Prime) (h2 : p ∉ D.host.small) (hq : p ≠ D.host.q) (hd : p ≠ D.host.d) :
    ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧
      (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro a ha
  have hcop := absNorm_coprime D hp h2 hq hd
  have hne : D.host.𝔟 ≠ ⊥ := by
    intro hb
    rw [hb, Ideal.absNorm_bot, Nat.coprime_zero_left] at hcop
    exact hp.one_lt.ne' hcop
  refine ⟨Ideal.absNorm D.host.𝔟, hcop, ?_⟩
  have ha' : a ∈ ((D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
    have : a ∈ D.host.AA0 := ha
    rwa [Host.AA0] at this
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hne)] at ha'
  have hs := ha' _ (FractionalIdeal.mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 D.host.E)) (P := D.host.E)
    (Ideal.absNorm_mem D.host.𝔟))
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).1 hs
  refine ⟨x, ?_⟩
  rw [hx, map_natCast, mul_comm]

theorem class_c0_prime_not_exceptional {R : Ranks} (H : Host R) {p : ℕ} (h : H.cls p = .inertClass) : p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d :=
  let k := (primeClass_eq_inert_iff H.toHostRaw).1 h
  ⟨k.1, k.2.1, k.2.2.1⟩

end GlobalTheory.TwV.HalfDiffInt

namespace GlobalTheory.TwV

theorem halfDiffInv_integral_at_split : ∀ (D : D7) (T p : ℕ), GIdx D.host T p → (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) := by
  intro D T p hg
  obtain ⟨h2, hq, hd⟩ := HalfDiffInt.class_c0_prime_not_exceptional D.host hg.2.2.1
  exact HalfDiffInt.inv_integral_off D hg.1 h2 hq hd

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatK
noncomputable section

namespace GlobalTheory.SDCompan

section Gen

open Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.GlobalTheoryTheory.Comp _root_.Formalism.L2.KerInert
open scoped TensorProduct

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {N : ℕ}

omit [StarRing E] in
theorem latAd_eq (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.latAd y Lb = Formalism.UG.CS.globLat y Lb :=
  Submodule.span_eq (Formalism.UG.CS.globLat y Lb)

theorem compan_eq (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Λ = Λ ⊔ Ideal.span {a} • dl sp.cm.sig J Λ := rfl

theorem compan_zero (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J 0 Λ = Λ := by
  rw [compan_eq, Ideal.span_singleton_eq_bot.2 rfl, Submodule.bot_smul, sup_bot_eq]

theorem mem_toStd (J : Matrix (Fin N) (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)) (y : Fin N → E) :
    y ∈ Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M ↔
      (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J).symm (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J x) = x :=
      LinearEquiv.symm_apply_apply _ x
    simpa using (this ▸ hx)
  · intro h
    exact ⟨_, h, by simp⟩

theorem isSD_toStd (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    {M : Submodule (𝓞 E) (Fin N → E)} (hM : IsLat M) (hsd : dl sp.cm.sig J M = M) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J M) := by
  have hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J (Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J) :=
    Classical.epsilon_spec hco
  set co := Formalism.L2.PairingIndexBounds.F.stdCo (sp.cm.sig : E →+* E) J with hco_def
  have key : ∀ x y, stdH E N (co x) (co y) = hform (sp.cm.sig : E →+* E) J x y := fun x y => hc x y
  refine ⟨(Module.Finite.iff_fg.1 hM.1).map _, ?_, fun y => ?_⟩
  · rw [Formalism.L2.PairingIndexBounds.F.toStd, Submodule.map_coe, LinearMap.coe_restrictScalars, ← hco_def, eq_top_iff]
    rintro v -
    have hv : co.symm v ∈ Submodule.span E (M : Set (Fin N → E)) := by rw [hM.2]; trivial
    have h1 := Submodule.apply_mem_span_image_of_mem_span (co : (Fin N → E) →ₗ[E] (Fin N → E)) hv
    simpa using h1
  · rw [mem_toStd (sp := sp), ← hco_def]
    constructor
    · intro hy x hx
      rw [mem_toStd (sp := sp), ← hco_def] at hx
      have h1 := (mem_dl sp.cm.sig J M (co.symm y)).1 (hsd.symm ▸ hy) (co.symm x) hx
      rw [← key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1
    · intro h
      rw [← hsd, mem_dl]
      intro x hx
      have h1 := h (co x) ((mem_toStd (sp := sp) J M (co x)).2 (by rw [← hco_def, LinearEquiv.symm_apply_apply]; exact hx))
      rw [← LinearEquiv.apply_symm_apply co y, key] at h1
      exact h1

theorem isSD_core (J : Matrix (Fin N) (Fin N) E)
    (hJ : ∀ M : Submodule (𝓞 E) (Fin N → E), IsLat M → IsLat (dl sp.cm.sig J M))
    (hco : ∃ co, Formalism.L2.PairingIndexBounds.F.IsOrthCo (sp.cm.sig : E →+* E) J co)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    {Lb M0 : Submodule (𝓞 E) (Fin N → E)} (hLb : IsLat Lb) (a : 𝓞 E)
    (hA : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a Lb = M0) (hM0 : IsLat M0) (hsd : dl sp.cm.sig J M0 = M0) :
    IsSDLat E N (Formalism.L2.PairingIndexBounds.F.toStd (sp.cm.sig : E →+* E) J
      (Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb))) := by
  have hG : Formalism.L2.PairingIndexBounds.F.compan (sp := sp) J a (Formalism.L2.PairingIndexBounds.F.latAd y Lb) = Formalism.UG.CS.globLat y M0 := by
    rw [latAd_eq, ← hA]
    by_cases ha : a = 0
    · subst ha
      rw [compan_zero, compan_zero]
    · rw [compan_eq, compan_eq]
      exact (glob_companion sp.cm.sig J hJ hLb ha y hy).symm
  rw [hG]
  exact isSD_toStd (sp := sp) J hco (isLat_glob hM0 y) (glob_selfdual sp.cm.sig J hJ hM0 hsd y hy)

end Gen

section Main

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem _root_.Formalism.L2.G.Pend Formalism.MainNotions _root_.Formalism.L2.Ker _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ _root_.Formalism.L2.G _root_.Formalism.L2.G.Cmp _root_.Formalism.L2.Forms _root_.Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isSDLat_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M)) → (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F), ∀ (Lb : Submodule (𝓞 E) (Fin N → E)) (a : 𝓞 E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (compan (sp := sp) J a Lb) → Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J (compan (sp := sp) J a Lb) = compan (sp := sp) J a Lb → IsSDLat E N (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N J hJ hco y hy Lb a hLb hM hsd
  exact isSD_core (sp := sp) J hJ hco y hy hLb a rfl hM hsd

end Main

end GlobalTheory.SDCompan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryPt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem exists_unitary_pt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {A : LocAt F E n G}, LocGood σ J A → ∀ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)), ∃ x, A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  intro F E _ _ _ _ _ n p G σ J A H i g
  exact ⟨_, H.isPt_sec i g, Subgroup.mul_mem _ (H.yG_mem i) (H.sec _).2⟩

end GlobalTheory.TwU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem isUnit_natCast_of_coprime_local {R : Type*} [CommRing R] [IsLocalRing R] {p s : ℕ} (hp : ¬ IsUnit (p : R))
    (hs : Nat.Coprime s p) : IsUnit (s : R) := by
  have hc : IsCoprime (s : R) (p : R) := Nat.Coprime.cast hs
  obtain ⟨a, b, hab⟩ := hc
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := a * (s : R)) (b := b * (p : R)) (by rw [hab]; exact isUnit_one) with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd (isUnit_of_mul_isUnit_right h) hp

theorem natCast_isUnit_localRing : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (v : X.Pl) (s : ℕ), Nat.Coprime s p → IsUnit (s : X.G.P.W v) :=
  fun X v _ hs => isUnit_natCast_of_coprime_local (X.G.P.setting v).p_unif.not_isUnit hs

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitDetFrameMatrixOfCharts
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isUnit_det_frameMatrix_ofCharts : ∀ {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (cp : ChartPts X D) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) (j : ℕ) (La : X.Lt j) (v : X.Pl), IsUnit ((fdOfCharts cp a bad).frM j La v).det := by
  intro p _ X D cp a bad j La v
  simp only [Formalism.L2.PairingIndexBounds.F.fdOfCharts]
  rw [Matrix.det_submatrix_equiv_self]
  erw [← RingHom.map_det]
  refine IsUnit.map _ ?_
  rw [Matrix.det_mul]
  refine IsUnit.mul ?_ ?_
  · rw [LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' _
  · exact Matrix.isUnits_det_units (cp.B j La)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValue
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValue
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem zAt_eq_zT {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ)
    {n : ℕ} (h : (X.Pj i).m + 1 = n) (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (v : Fin (X.Pj i).nV) (s : Fin ((X.Pj i).n' v)) :
    zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f v s =
      (zT X D pos f (posJ X D pos i ⟨v, s⟩)).submatrix (finCongr h) (finCongr h) := by
  subst h
  have hp : ((pos.symm (posJ X D pos i ⟨v, s⟩)).2 : ℕ) = s.val := by
    cases i <;> exact congrArg (fun x => (x.2 : ℕ)) (pos.symm_apply_apply _)
  have ho : IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 ↔ ¬ Even s.val := by
    unfold IsOddPos; rw [hp, Nat.not_even_iff_odd, Nat.odd_iff]
  unfold zAt zT reM
  by_cases hs : Even s.val
  · have : ¬ IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 := fun h' => (ho.1 h') hs
    simp [hs, this]
  · have : IsOddPos (pos.symm (posJ X D pos i ⟨v, s⟩)).2 := ho.2 hs
    simp [hs, this]

theorem ev1_eq_prod_det_pow_mul_valZ : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f : Fr1 D n), ev1 X D pos i h R f = (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R f.1 := by
  intro p _ X D pos i n h R f
  show (∏ v, ∏ s : Fin ((X.Pj i).n' v), (zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f.1 v s).det ^ (eAt (X.Pj i) v s)) *
      MvPolynomial.eval (fun x : Var (X.Pj i) => zAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) f.1 x.1 x.2.1 x.2.2.1 x.2.2.2) R = _
  congr 1
  · simp_rw [zAt_eq_zT, Matrix.det_submatrix_equiv_self]
    rw [← Equiv.prod_comp (posJ X D pos i), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    unfold eT
    rw [Equiv.symm_apply_apply]
  · unfold valZ
    congr 2
    funext x
    rw [zAt_eq_zT]
    rfl

end GlobalTheory.TwV.DelA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValueStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalStdFrames_eq_detPower_mul_blockValue : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f : Fr1 D n), ev1 X D pos i h R f = (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R f.1 := by
  first | exact @GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ | exact GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ | (intros; apply GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRows
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRows
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem sum_Icc_one_eq_sum_fin (f : ℕ → ℤ) : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, f i = ∑ r : Fin n, f (r.val + 1)
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), sum_Icc_one_eq_sum_fin f n, Fin.sum_univ_castSucc]
    simp

theorem size_first_last_rows : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → NuIs X D pos j (extNu (D.R.N (j + 1)) ν) ∧ (∀ τ, szT X D pos j τ = ∑ r, (ν τ r : ℤ)) ∧ (∀ τ, szT X D pos j τ = ∑ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ)) ∧ (∀ τ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ) ≤ cT1 X D pos j τ) ∧ ∀ τ, 0 ≤ X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) := by
  intro p _ X D pos j hN ν hν
  have hle : D.R.N j ≤ D.R.N (j + 1) := rk_le X D hN
  have hz : ∀ τ (i : ℕ), D.R.N j < i → X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 i = 0 := fun τ i hi =>
    nuv_zero X _ j _ i (hN.1 ▸ hi)
  have hext : NuIs X D pos j (extNu (D.R.N (j + 1)) ν) := by
    intro τ i
    unfold extNu
    split_ifs with h
    · exact hν τ ⟨i.val, h⟩
    · rw [hz τ _ (by omega)]; simp
  have hsz : ∀ τ, szT X D pos j τ = ∑ i ∈ Finset.Icc 1 (D.R.N (j + 1)), X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 i := by
    intro τ
    unfold szT szMu
    rw [hN.2]
  refine ⟨hext, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [hsz τ, ← Finset.sum_subset (Finset.Icc_subset_Icc_right hle) (fun i hi hni => by
      simp only [Finset.mem_Icc] at hi hni
      exact hz τ i (by omega)), sum_Icc_one_eq_sum_fin]
    exact Finset.sum_congr rfl fun r _ => hν τ r
  · intro τ
    rw [hsz τ, sum_Icc_one_eq_sum_fin]
    exact Finset.sum_congr rfl fun r _ => hext τ r
  · intro τ r
    rw [← hext τ r]
    exact nuv_le_first X _ j _ _
  · intro τ
    exact nuv_nonneg X _ j _ _

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelPartition_size_extension_firstLast_rows : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → NuIs X D pos j (extNu (D.R.N (j + 1)) ν) ∧ (∀ τ, szT X D pos j τ = ∑ r, (ν τ r : ℤ)) ∧ (∀ τ, szT X D pos j τ = ∑ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ)) ∧ (∀ τ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ) ≤ cT1 X D pos j τ) ∧ ∀ τ, 0 ≤ X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) := by
  first | exact @GlobalTheory.TwV.DelA.size_first_last_rows | exact GlobalTheory.TwV.DelA.size_first_last_rows | (intros; apply GlobalTheory.TwV.DelA.size_first_last_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceField
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceField
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem stdU_star_det_mul_det {n : ℕ} (D : D7) (M : GL (Fin n) D.host.E) (hU : StdU D M) :
    star (M : Matrix (Fin n) (Fin n) D.host.E).det * (M : Matrix (Fin n) (Fin n) D.host.E).det = 1 := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul]
  have : (M : Matrix (Fin n) (Fin n) D.host.E).conjTranspose = star (M : Matrix (Fin n) (Fin n) D.host.E) := rfl
  rw [this, hU, Matrix.det_one]

theorem stdU_inv_eq_star {n : ℕ} (D : D7) (M : GL (Fin n) D.host.E) (hU : StdU D M) :
    ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = star (M : Matrix (Fin n) (Fin n) D.host.E) := by
  have h1 : ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (M : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      = ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((M : Matrix (Fin n) (Fin n) D.host.E) * ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = star (M : Matrix (Fin n) (Fin n) D.host.E) * (M : Matrix (Fin n) (Fin n) D.host.E) * ((M⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [← Matrix.mul_assoc, h1, hU]
    _ = star (M : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem blkC_atR_read : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ {n : ℕ} (M : GL (Fin n) D.host.E), StdU D M → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (if IsOddPos s then ((((atR D M (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose) else (atR D M (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).map ι = ((M : Matrix (Fin n) (Fin n) D.host.E).map (ρ v)).map (Formalism.L2.G.Pend.tw X Kc v s) ∧ Formalism.L2.G.Pend.tw X Kc v s (ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det) = ι (embT D (pos ⟨v, s⟩) (M : Matrix (Fin n) (Fin n) D.host.E).det) ^ (if IsOddPos s then (-1 : ℤ) else 1) := by
  intro p _ X D pos Kc _ _ ι ρ hT n M hU v s
  have hT' := hT v s
  constructor
  · ext i j
    simp only [Matrix.map_apply]
    split_ifs with hs
    · have hinv : ((atR D M (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) = atR D M⁻¹ (pos ⟨v, s⟩) := by
        simp [atR, map_inv]
      rw [Matrix.transpose_apply, hinv]
      simp only [atR, Matrix.GeneralLinearGroup.map_apply]
      rw [stdU_inv_eq_star D M hU, hT', if_pos hs]
      simp [Matrix.star_apply]
    · simp only [atR, Matrix.GeneralLinearGroup.map_apply]
      rw [hT', if_neg hs]
  · split_ifs with hs
    · have h := hT' (M : Matrix (Fin n) (Fin n) D.host.E).det
      rw [if_pos hs] at h
      have h2 := hT' (star (M : Matrix (Fin n) (Fin n) D.host.E).det)
      rw [if_pos hs, star_star] at h2
      rw [← h2, zpow_neg_one]
      have h3 := congrArg (fun x => ι (embT D (pos ⟨v, s⟩) x)) (stdU_star_det_mul_det D M hU)
      simp only [map_mul, map_one] at h3
      exact (eq_inv_of_mul_eq_one_left h3)
    · rw [hT', if_neg hs, zpow_one]

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceFieldStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryBlockMatrices_read_in_placeField : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ {n : ℕ} (M : GL (Fin n) D.host.E), StdU D M → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (if IsOddPos s then ((((atR D M (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose) else (atR D M (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).map ι = ((M : Matrix (Fin n) (Fin n) D.host.E).map (ρ v)).map (Formalism.L2.G.Pend.tw X Kc v s) ∧ Formalism.L2.G.Pend.tw X Kc v s (ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det) = ι (embT D (pos ⟨v, s⟩) (M : Matrix (Fin n) (Fin n) D.host.E).det) ^ (if IsOddPos s then (-1 : ℤ) else 1) := by
  first | exact @GlobalTheory.TwV.DelA.blkC_atR_read | exact GlobalTheory.TwV.DelA.blkC_atR_read | (intros; apply GlobalTheory.TwV.DelA.blkC_atR_read <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevels
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA.LastEnt

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem succ_mul_succ_sub_one_div_succ (l t : ℕ) : ((l + 1) * (t + 1) - 1) / (t + 1) = l := by
  have h : (l + 1) * (t + 1) - 1 = t + (t + 1) * l := by rw [Nat.succ_mul]; ring_nf; omega
  rw [h, Nat.add_mul_div_left _ _ (Nat.succ_pos t), Nat.div_eq_of_lt (Nat.lt_succ_self t), zero_add]

theorem eT_zero (τ : D.what₂.Tau) : eT X D pos 0 τ =
    lamAt (X.G.P.lam0 (pos.symm τ).1) (pos.symm τ).2 (Fin.last X.G.P.m) := rfl

theorem eT_succ (l : ℕ) (τ : D.what₂.Tau) : eT X D pos (l + 1) τ =
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 (pos.symm τ).1 s) (fun i => X.Fl.w (pos.symm τ).1 i s) (l + 1))
      (pos.symm τ).2 (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) := rfl

theorem lamAt_last0 (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (X.G.P.lam0 v) s (Fin.last X.G.P.m) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else X.G.P.lam0 v s (Fin.last X.G.P.m) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [if_pos h, if_neg (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
  · rw [if_neg h, if_pos (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]

theorem lamAt_lastS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (l + 1)) s
        (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else -(X.Fl.w v (l + 1) s) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [if_pos h, if_neg (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
    unfold liftWt
    beta_reduce
    have h1 : 1 ≤ (l + 1) * (X.Fl.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [dite_eq_right (by simp only [Fin.val_last]; omega)]
    simp only [Fin.val_last]
    have h2 : X.G.P.m + (l + 1) * (X.Fl.t + 1) - (X.G.P.m + 1) = (l + 1) * (X.Fl.t + 1) - 1 := by omega
    rw [h2, succ_mul_succ_sub_one_div_succ]
  · rw [if_neg h, if_pos (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]
    unfold liftWt
    beta_reduce
    rw [dite_eq_left (by simp)]
    rfl

theorem nuv_one (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (j + 1) s 1 = X.G.P.lam0 v s 0 + X.w v (j + 1) s := by
  unfold Sys.nuv nu
  rw [if_pos ⟨le_refl 1, by omega⟩]
  unfold lamI
  rw [dite_eq_left ⟨le_refl 1, by omega⟩]
  rfl

theorem nuv_one_at_firstLevelIndex (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v 1 s (NN X.G.P.m X.t 0) = X.G.P.lam0 v s (Fin.last X.G.P.m) + X.w v 1 s := by
  unfold Sys.nuv nu NN
  rw [if_pos ⟨by omega, by omega⟩]
  unfold lamI
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 2
  ext
  simp

theorem nuv_NNS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (l + 1 + 1) s (NN X.G.P.m X.t (l + 1)) = -X.w v (l + 1) s + X.w v (l + 1 + 1) s := by
  have h1 : 1 ≤ (l + 1) * (X.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h3 : (l + 1) * (X.t + 1) + (X.t + 1) = (l + 1 + 1) * (X.t + 1) := by ring
  unfold Sys.nuv nu
  rw [if_neg (by unfold NN; omega), if_pos ⟨by unfold NN; omega, by unfold NN; omega⟩]
  have h2 : NN X.G.P.m X.t (l + 1) - (X.G.P.m + 2) = (l + 1) * (X.t + 1) - 1 := by unfold NN; omega
  rw [h2, succ_mul_succ_sub_one_div_succ]

end GlobalTheory.TwV.DelA.LastEnt


open GlobalTheory.TwV.DelA.LastEnt in
theorem GlobalTheory.TwV.DelA.eT_last_pair : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (τ : D.what₂.Tau), (eT X D pos j τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) - wT X D pos j τ) ∧ (eT X D pos (j + 1) τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else -wT X D pos j τ) := by
  intro p _ X D pos j τ
  have hc1 : cT1 X D pos j τ = X.G.P.lam0 (pos.symm τ).1 (pos.symm τ).2 0 + wT X D pos j τ :=
    nuv_one X j (pos.symm τ).1 (pos.symm τ).2
  have hw : wT X D pos j τ = X.w (pos.symm τ).1 (j + 1) (pos.symm τ).2 := rfl
  rw [hc1, eT_succ X D pos j τ, lamAt_lastS X j]
  cases j with
  | zero =>
    rw [eT_zero, lamAt_last0, nuv_one_at_firstLevelIndex, hw]
    constructor <;> split_ifs <;> ring
  | succ l =>
    rw [eT_succ X D pos l τ, lamAt_lastS X l, nuv_NNS, hw]
    constructor <;> split_ifs <;> ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (τ : D.what₂.Tau), (eT X D pos j τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) - wT X D pos j τ) ∧ (eT X D pos (j + 1) τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else -wT X D pos j τ) := by
  first | exact @GlobalTheory.TwV.DelA.eT_last_pair | exact GlobalTheory.TwV.DelA.eT_last_pair | (intros; apply GlobalTheory.TwV.DelA.eT_last_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.OrthDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem int_mem_range {t : E} (h : IsIntegral ℤ t) : t ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨t, h⟩, rfl⟩

theorem ringHom_mem_range (τ : E →+* E) {t : E} (h : t ∈ (algebraMap (𝓞 E) E).range) :
    τ t ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨r, rfl⟩ := h
  exact int_mem_range (IsIntegral.map τ.toIntAlgHom r.isIntegral_coe)

theorem exists_int_smul_mem (M : Submodule (𝓞 E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (M : Set (Fin N → E))) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : ((n₁ * n₂ : ℤ) : E) • (x + y) = n₂ • ((n₁ : E) • x) + n₁ • ((n₂ : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, smul_add]
      push_cast
      rw [mul_comm (n₂ : E)]
    rw [e]
    exact add_mem (zsmul_mem hx _) (zsmul_mem hy _)
  | smul e x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨k, hk, hki⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hke := hki e (Finset.mem_singleton_self e)
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : ((k * n : ℤ) : E) • (e • x) = (⟨k • e, hke⟩ : 𝓞 E) • ((n : E) • x) := by
      rw [← algebraMap_smul E (⟨k • e, hke⟩ : 𝓞 E), smul_smul, smul_smul]
      congr 1
      show ((k * n : ℤ) : E) * e = (k • e) * n
      push_cast
      rw [zsmul_eq_mul]
      ring
    rw [e1]
    exact M.smul_mem _ hx

theorem isLat_dl (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (σ : E →+* E) J co) (M : Submodule (𝓞 E) (Fin N → E))
    (hM : Formalism.L2.GlobalTheoryTheory.Comp.IsLat M) : Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M) := by
  classical
  set v : Fin N → Fin N → E := fun a => co.symm (Pi.single a 1) with hv
  have key : ∀ x y, Formalism.UG.hform (σ : E →+* E) J x y = ∑ b, (σ : E →+* E) (co x b) * co y b :=
    fun x y => (hc x y).symm
  have hsingle : ∀ (a : Fin N) (c : E), Pi.single a c = c • (Pi.single a (1 : E) : Fin N → E) := by
    intro a c; ext j; simp [Pi.single_apply]
  have hexp : ∀ z : Fin N → E, z = ∑ a, co z a • v a := by
    intro z
    conv_lhs => rw [← co.symm_apply_apply z, ← Finset.univ_sum_single (co z)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsingle, map_smul]
  have hcv : ∀ (c : E) a b, co (c • v a) b = if b = a then c else 0 := by
    intro c a b; simp [v, Pi.single_apply]
  have hform_v : ∀ (c : E) a x, Formalism.UG.hform (σ : E →+* E) J x (c • v a) = (σ : E →+* E) (co x a) * c := by
    intro c a x; rw [key]; simp [hcv]

  have hex : ∀ a, ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v a ∈ M := fun a =>
    exists_int_smul_mem M (by rw [hM.2]; trivial)
  choose n hn0 hnM using hex
  have hle : Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M ≤
      Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a) := by
    intro y hy
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl] at hy
    have hr : ∀ a, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (n a : E) * co y a := by
      intro a
      obtain ⟨r, hr⟩ := hy _ (hnM a)
      refine ⟨r, ?_⟩
      rw [hr, key, Finset.sum_eq_single a]
      · rw [hcv, if_pos rfl, map_intCast]
      · intro b _ hb
        rw [hcv, if_neg hb, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ a) h
    choose r hr using hr
    rw [hexp y]
    refine Submodule.sum_mem _ fun a _ => ?_
    have e3 : co y a • v a = r a • (((n a : E))⁻¹ • v a) := by
      rw [← algebraMap_smul E (r a), smul_smul, hr a, mul_comm (n a : E), mul_assoc,
        mul_inv_cancel₀ (Int.cast_ne_zero.2 (hn0 a)), mul_one]
    rw [e3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  haveI : Module.Finite (𝓞 E) (Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a)) :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_⟩

  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hM.1
  obtain ⟨m, hm0, hmi⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (s.biUnion fun x => Finset.univ.image fun b => co x b)
  have hint : ∀ a, ∀ x ∈ M, (m : E) * co x a ∈ (algebraMap (𝓞 E) E).range := by
    intro a x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      apply int_mem_range
      have := hmi (co x a) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩)
      rwa [zsmul_eq_mul] at this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), Pi.add_apply, mul_add]; exact add_mem hx hy
    | smul t x _ hx =>
      rw [← algebraMap_smul E t x, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem ⟨t, rfl⟩ hx
  have hmem : ∀ a, (m : E) • v a ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M := by
    intro a
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl]
    intro x hx
    rw [hform_v]
    have e4 : (σ : E →+* E) (co x a) * (m : E) = (σ : E →+* E) ((m : E) * co x a) := by
      rw [map_mul, map_intCast, mul_comm]
    rw [e4]
    exact ringHom_mem_range _ (hint a x hx)
  rw [eq_top_iff]
  intro z _
  rw [hexp z]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  have e5 : v a = ((m : E))⁻¹ • ((m : E) • v a) := by
    rw [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hm0), one_smul]
  rw [e5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem a))

end GlobalTheory.OrthDual

theorem GlobalTheory.isLat_dl_of_isOrthCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M) := by
  rintro R F E _ _ _ _ _ _ sp N J ⟨co, hc⟩ M hM
  exact GlobalTheory.OrthDual.isLat_dl sp.cm.sig J co hc M hM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertThetaAdmissibilityOfComplexMultiplication
namespace GlobalTheory.TwV.Lt

theorem inert_theta_admissibility_of_complex_multiplication : Formalism.L2.Th1.CM.CM2 → GlobalTheory.TwV.Lt.AdmAtEnt2 := fun h => by
  haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
  exact Formalism.L2.KerInert.AdmLoc2.admissible_entries_small_chain

end GlobalTheory.TwV.Lt
end
