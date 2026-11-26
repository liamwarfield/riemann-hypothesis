module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisDeRhamLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodMatrixAtLogZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedModificationAtE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogTeichmullerPowSemistablePeriods

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogUniformizerTiltBdRPlusCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOfInvariantMod
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.FilInv

open GlobalTheory.DRFil

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem graded_const (TT : LocTied l P AI) (K : FinExt l) (n : ℤ)
    (e : P.R.BdR) (he : e ∈ (P.PD K).Fil n)
    (hg : ∀ g, (P.PD K).actdR g e - e ∈ (P.PD K).Fil (n + 1)) :
    ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil n ∧
      e - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil (n + 1) := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  by_cases hn : n = 0
  · subst hn
    rw [zero_add] at hg ⊢
    obtain ⟨y, hy, ey⟩ := GlobalTheory.MemLoc.invariants_finExt l K (Θ.θ e) (fun g hg' => by
      have h := (theta_sub_iff Θ K ((P.PD K).Fil_G _ _ _ he) he).1 (hg ⟨g, hg'⟩)
      rwa [P.PD_actdR, Θ.θ_act _ _ ((fil_iff _ _ _ _).1 he), GlobalTheory.MemLoc.locAinf_actC] at h)
    refine ⟨⟨y, hy⟩, alg_mem_fil_zero K _, ?_⟩
    rw [theta_sub_iff Θ K he (alg_mem_fil_zero K _), ← ey]
    exact (Θ.θ_Om y).symm
  · obtain ⟨κ, -, -, h0, h⟩ := graded_invariants TT Θ K n e he hg
    rw [h0 hn] at h
    exact ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rwa [map_zero]⟩

theorem const_of_invariant_mod : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a b : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a → (∀ g, (P.PD K).actdR g x - x ∈ (P.PD K).Fil b) → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧ x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil b := by
  intro l _ P AI TT K a b x hx hg
  have hFa : Antitone fun a => (P.PD K).Fil a :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have h0 : ∀ m, m ≤ a → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧
      x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m := fun m hm =>
    ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rw [map_zero, sub_zero]; exact hFa hm hx⟩
  rcases le_total b a with hba | hab
  · exact h0 b hba
  have key : ∀ m, a ≤ m → m ≤ b → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧
      x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m := by
    intro m hm
    induction m, hm using Int.leInduction with
    | base => exact fun _ => h0 a le_rfl
    | succ m hm ih =>
      intro hmb
      obtain ⟨c, hc, hxc⟩ := ih (by omega)
      obtain ⟨d, hd, hxd⟩ := graded_const TT K m _ hxc (fun g => by
        rw [map_sub, AlgEquiv.commutes, sub_sub_sub_cancel_right]
        exact hFa hmb (hg g))
      refine ⟨c + d, ?_, ?_⟩
      · rw [map_add (f := _)]
        exact Submodule.add_mem _ hc (hFa hm hd)
      · rwa [map_add, ← sub_sub]
  exact key b hab le_rfl

end GlobalTheory.FilInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogUniformizerTiltBdRPlusCocycle
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LogFlatLam

variable {l : ℕ} [Fact l.Prime]

theorem eD_smul_tB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l} (hF : Fits T C)
    (z : ℤ_[l]) :
    T.eD (P.ιB ((z : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l z) * C.j C.t) := by
  rw [map_smul, Algebra.smul_def, map_mul, T.zD, hF.ι, hF.t, Core.tB, C.ι_j, map_mul, GlobalTheory.RingIface.zD_eq_alg]
  simp only [aDp, RingHom.comp_apply]

theorem exists_mem_FilD_neg (C : Core l) (x : Per.BdR l) : ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ)) := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨n, y, hy⟩ := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.2 C.ε he x
  refine ⟨n, (GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l C.ε he _ x).2 ⟨y, ?_⟩⟩
  simpa using hy

theorem const_eq_zero_of_mem_Fil_one {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (K : FinExt l) (c : ↥K.1) (hc : algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil 1) : c = 0 := by
  have h1 := (T.fil K 1 _).1 hc
  have e : algebraMap ↥K.1 P.R.BdR c = algebraMap (Om l) P.R.BdR (c : Om l) := rfl
  rw [e, hF.o] at h1
  obtain ⟨z, hz, hze⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).1 (by exact_mod_cast h1)
  have hz' : z = C.o (c : Om l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 hze
  have h0 : Per.θD l z = 0 := by
    have := (GlobalTheory.MemLoc.thetaD_onto_ker l).2
    rw [← this] at hz
    exact hz
  rw [hz', C.o_sec.th] at h0
  have : (c : Om l) = 0 := (algebraMap (Om l) ℂ_[l]).injective (by simpa using h0)
  exact Subtype.ext this

end GlobalTheory.LogFlatLam

namespace GlobalTheory.LogFlatLam

variable {l : ℕ} [Fact l.Prime]

theorem σD_alg (g : GQ l) (x : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g x) :=
  GlobalTheory.RingIface.sigD_alg l g x

theorem σDp_alg (g : GQ l) (a : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) :=
  GlobalTheory.RingIface.sigDp_alg l g a

theorem σDp_aDp (g : GQ l) (a : Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply, σDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

end GlobalTheory.LogFlatLam


open GlobalTheory.LogFlatLam in
theorem GlobalTheory.LogFlatLam.exists_lam : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) → (∀ g, bk.FixFlat g → c g = 0) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∃ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) ∧ (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) := by
  rintro l _ K bk P AI T C hF b c ⟨hact, -⟩ - happrox
  obtain ⟨ι, hιC, hιg⟩ := GlobalTheory.BstLog.iota_exists l P AI T
  have hinj := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1
  set yA := ι (Polynomial.X + Polynomial.C b) with hyA
  have hy : ∀ g : ↥(GK K), P.actQdR (g : GQ l) yA = yA + P.ιB ((c g : ℚ_[l]) • P.tB) := by
    intro g
    rw [hyA, ← hιg, hact g, map_add (f := _), hιC]
  have hKc : ∀ (g : ↥(GK K)) (d : ↥K.1), P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR d) =
      algebraMap ↥K.1 P.R.BdR d := by
    intro g d
    rw [← P.PD_actdR K g, AlgEquiv.commutes]
  obtain ⟨n, hn⟩ := exists_mem_FilD_neg C (T.eD yA)
  have hn' : yA ∈ (P.PD K).Fil (-(n : ℤ)) := (T.fil K _ _).2 hn
  have hg1 : ∀ g : ↥(GK K), (P.PD K).actdR g yA - yA ∈ (P.PD K).Fil 1 := by
    intro g
    rw [P.PD_actdR, hy, add_sub_cancel_left]
    refine (T.fil K 1 _).2 ?_
    rw [eD_smul_tB hF]
    exact_mod_cast (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).2
      ⟨_, Ideal.mul_mem_left _ _ (GlobalTheory.MemLoc.core_t_unit_fil l C).2.1, rfl⟩
  obtain ⟨c0, -, hc0⟩ := GlobalTheory.FilInv.const_of_invariant_mod l P AI T K (-(n : ℤ)) 1 yA hn' hg1
  set lamA := yA - algebraMap ↥K.1 P.R.BdR c0 with hlamA
  obtain ⟨lam, hlam1, hlamE⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).1 (by exact_mod_cast (T.fil K 1 lamA).1 hc0)
  have hequiv : ∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t := by
    intro g
    apply hinj
    rw [map_add (f := _), ← σD_alg, hlamE, ← T.actD, hlamA, map_sub, hKc, hy]
    simp only [map_sub, map_add (f := _), eD_smul_tB hF]
    ring
  refine ⟨lam, hequiv, fun m => ?_⟩
  obtain ⟨k, s, hEs, hs⟩ := happrox m
  refine ⟨k, s, hEs, ?_⟩
  set x := aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam with hx
  set xA := T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) x) with hxA
  have hxA' : T.eD xA = algebraMap (Per.BdRp l) (Per.BdR l) x := by rw [hxA, RingEquiv.apply_symm_apply]
  have hx1 : xA ∈ (P.PD K).Fil 1 := by
    refine (T.fil K 1 _).2 ?_
    rw [hxA']
    refine (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).2 ⟨x, ?_, rfl⟩
    refine Ideal.sub_mem _ (((GlobalTheory.AinfEPow.ePow_facts l K bk 1).2.2.1 _).2 ?_) (Ideal.mul_mem_left _ _ hlam1)
    rw [pow_one]
    exact map_dvd _ hEs
  have hxg : ∀ g : ↥(GK K), (P.PD K).actdR g xA - xA ∈ (P.PD K).Fil (m : ℤ) := by
    intro g
    refine (T.fil K _ _).2 ?_
    rw [map_sub, P.PD_actdR, T.actD, hxA', σD_alg, ← map_sub]
    refine (GlobalTheory.BdRQuot.mem_FilD_nat m _).2 ⟨_, ?_, rfl⟩
    have e : Per.σDp (g : GQ l) x - x = aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) := by
      rw [hx, map_sub, map_mul, map_pow, map_natCast, σDp_aDp, hequiv, map_sub]
      ring
    rw [e]
    exact hs g
  obtain ⟨c', hc'1, hc'm⟩ := GlobalTheory.FilInv.const_of_invariant_mod l P AI T K 1 (m : ℤ) xA hx1 hxg
  have hc'0 : c' = 0 := const_eq_zero_of_mem_Fil_one hF K c' hc'1
  rw [hc'0, map_zero, sub_zero] at hc'm
  have h := (T.fil K _ _).1 hc'm
  rw [hxA'] at h
  obtain ⟨z, hz, hze⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat m _).1 h
  rw [← hinj hze]
  exact hz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogUniformizerTiltBdRPlusCocycleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_uniformizerTilt_bdRPlus_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) → (∀ g, bk.FixFlat g → c g = 0) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∃ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) ∧ (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) := by
  first | (exact @GlobalTheory.LogFlatLam.exists_lam) | (exact GlobalTheory.LogFlatLam.exists_lam) | (intros; apply GlobalTheory.LogFlatLam.exists_lam  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsOverAcris
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsOverAcris
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.CrisPeriods

variable {l : ℕ} [Fact l.Prime]

private theorem padicInt_hom_ext {R : Type} [CommRing R] [IsHausdorff (Ideal.span {(l : R)}) R]
    (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {(l : R)}) inferInstance _ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)
  have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * y := by rw [← hy]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨f y - g y, ?_⟩
  have hf := congrArg f hz
  have hg := congrArg g hz
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at hf hg
  rw [hf, hg]
  ring

private theorem zA_eq_alg (z : ℤ_[l]) : Per.zA l z = algebraMap ℤ_[l] (Ainf l) z :=
  haveI : IsHausdorff (Ideal.span {(l : Ainf l)}) (Ainf l) :=
    (WittVector.isAdicCompleteIdealSpanP (p := l) (k := Per.Fl l)).toIsHausdorff
  padicInt_hom_ext (R := Ainf l) (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) z

private theorem j_alg (C : Core l) (a : Ainf l) : C.j (algebraMap (Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.MemLoc.ULaws.alg_acris, C.j_cris.on0]
  rfl

private theorem alg_alg_eq_aB (C : Core l) (a : Ainf l) :
    algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Ainf l) (Per.Acris l) a) = Per.aB l a := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [C.ι_j, j_alg, GlobalTheory.MemLoc.ULaws.iota_aB]

private theorem aB_zA (C : Core l) (z : ℤ_[l]) : Per.aB l (Per.zA l z) = Per.zB l z := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [← GlobalTheory.MemLoc.ULaws.u_padicInt C, GlobalTheory.MemLoc.ULaws.iota_aB, C.ι_u, ← C.o_sec.z]
  rfl

theorem kap_map (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a))
    (z : ℤ_[l]) (hn : ∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) :
    (GlobalTheory.SstPer.kap C bk k₀ k Mn z).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
      (l : Per.Bcris l) ^ k₀ • ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) *
        (Per.zB l z * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i := by
  have hz : ∀ w : ℤ_[l], algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Ainf l) (Per.Acris l) (Per.zA l w)) =
      Per.zB l w := fun w => (alg_alg_eq_aB C _).trans (aB_zA C w)
  have hM : (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
      (algebraMap (Per.Acris l) (Per.Bcris l)) = Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
    exact alg_alg_eq_aB C _
  have he : ∀ i ∈ Finset.range d, Per.zB l (GlobalTheory.SstPer.ecoef l k₀ k i) =
      (l : Per.Bcris l) ^ k₀ * C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) := by
    intro i hi
    rw [← (GlobalTheory.MemLoc.ULaws.u_laws l C).2.2.1, GlobalTheory.SstPer.ecoef_val (hn i (Finset.mem_range.1 hi))]
    show C.qB _ = _
    rw [GlobalTheory.SstPer.ecoefQ, map_mul, map_pow, map_natCast]
  unfold GlobalTheory.SstPer.kap
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← RingHom.mapMatrix_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [RingHom.mapMatrix_apply, map_smul_ring, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, hM,
    smul_smul]
  congr 1
  rw [map_mul, map_pow, map_mul, hz, hz, he i hi, Core.tB]
  ring

end GlobalTheory.CrisPeriods

namespace GlobalTheory.CrisPeriods

theorem periods_over_Acris_sst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∀ (k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * GlobalTheory.SstPer.kap C bk k₀ k Mn (c g))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  intro l _ K bk P AI T C _hFits d ρ U U' hUU' c₁ F hφ k k₀ Mn c hn hgal
  have hA := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).1
  obtain ⟨_, _, -, -, -, hFilt, -⟩ := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
  obtain ⟨-, hmul, -, hiff, -, -, hinj⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (xi C.ε) C.ker_theta.symm
  have AL := GlobalTheory.MemLoc.ActLaws.act_laws l
  obtain ⟨N₁, h₁⟩ := exists_lift C hA U
  obtain ⟨N₂, h₂⟩ := exists_lift C hA U'
  refine ⟨max N₁ N₂, fun N hN X X' hX hX' => ?_⟩
  obtain ⟨Z, hZ⟩ := h₁ N (le_of_max_le_left hN)
  obtain ⟨Z', hZ'⟩ := h₂ N (le_of_max_le_right hN)
  have hmi : Function.Injective
      (fun M : Matrix (Fin d) (Fin d) (Per.Acris l) => M.map (algebraMap (Per.Acris l) (Per.Bcris l))) :=
    Matrix.map_injective hinj
  have hXm : ∀ Y : Matrix (Fin d) (Fin d) bk.S,
      ((Y.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))).map C.ι =
        Y.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) := by
    intro Y
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply]
    rw [C.ι_j]
    congr 1
    exact j_alg C _
  have htN : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ^ N ∈ Per.FilD l N := by
    rw [C.ι_j, ← map_pow, hiff, hFilt]
    exact Ideal.mem_span_singleton_self _
  refine ⟨Z, Z', ?_, ?_, ?_, ?_, ?_⟩
  · apply hmi
    simp only
    rw [Matrix.map_mul, hZ, hZ', map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), smul_mul_smul_comm,
      hUU', map_pow, ← pow_add, two_mul]
  · apply hmi
    simp only
    have hZφ : (Z.map (phiA l)).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.φB l) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.2 (Z i j)).symm
    have hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
      exact alg_alg_eq_aB C _
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (phiA l C.t) =
        Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.2 C.t).symm
    rw [map_smul_ring, hZφ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hFm, hZ, map_pow, map_pow, ht,
      Matrix.smul_mul, ← hφ]
    simp only [map_mul, map_pow, map_natCast, smul_smul]
    congr 1
    ring
  · intro g
    apply hmi
    simp only
    have hZσ : (Z.map (sigA (g : GQ l))).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.σB (g : GQ l)) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ (Z i j)).symm
    have hρ : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = (ρ g).map (Per.zB l) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply]
      rw [alg_alg_eq_aB C, ← zA_eq_alg, aB_zA C]
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (sigA (g : GQ l) C.t) =
        Per.σB (g : GQ l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ C.t).symm
    rw [map_smul_ring, Matrix.map_mul, hρ, hZσ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hZ,
      kap_map C bk k₀ k Mn (c g) hn]
    simp only [map_pow, map_mul, map_natCast, ht]
    rw [Matrix.mul_smul, hgal g, Matrix.smul_mul, Matrix.mul_smul]
    simp only [smul_smul, Core.tB]
    congr 1
    ring
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) =
        ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι ((U * (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l))) i j) =
        (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX i j)
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) =
        ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z').map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι (((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) * U') i j) =
        (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX' i j)

end GlobalTheory.CrisPeriods
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsOverAcrisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_periods_over_Acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∀ (k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * GlobalTheory.SstPer.kap C bk k₀ k Mn (c g))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  first | (exact @GlobalTheory.CrisPeriods.periods_over_Acris_sst) | (exact GlobalTheory.CrisPeriods.periods_over_Acris_sst) | (intros; apply GlobalTheory.CrisPeriods.periods_over_Acris_sst  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableExpCocycleCoboundaryModFil
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableExpCocycleCoboundaryModFil
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer.Cob

theorem padicInt_hom_ext_pt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [CharP R l] [PerfectRing R l]
    (f g : ℤ_[l] →+* WittVector l R) (x : ℤ_[l]) : f x = g x := by
  refine sub_eq_zero.1 (IsHausdorff.haus
    (inferInstance : IsHausdorff (Ideal.span {(l : WittVector l R)}) (WittVector l R)) _ fun n => ?_)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
  have hx : x = (x.appr n : ℤ_[l]) + y * (l : ℤ_[l]) ^ n := by rw [hy]; ring
  have h : f x - g x = (f y - g y) * (l : WittVector l R) ^ n := by
    have hf := congrArg f hx
    have hg := congrArg g hx
    simp only [map_add (f := _), map_mul, map_pow, map_natCast] at hf hg
    rw [hf, hg]
    ring
  rw [SModEq.zero, h, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def texp {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S) (x : S) :
    Matrix (Fin d) (Fin d) S :=
  ∑ n ∈ Finset.range d, (ψ ((n.factorial : ℚ)⁻¹) * x ^ n) • N ^ n

theorem texp_eq_exp {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S)
    (hN : N ^ d = 0) (x : S) :
    letI : Algebra ℚ S := ψ.toAlgebra
    texp ψ N x = IsNilpotent.exp (x • N) := by
  letI : Algebra ℚ S := ψ.toAlgebra
  have h : (x • N) ^ d = 0 := by rw [smul_pow, hN, smul_zero]
  rw [IsNilpotent.exp_eq_sum h, texp]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_pow, ← algebraMap_smul S ((n.factorial : ℚ)⁻¹), smul_smul]
  rfl

theorem texp_mul {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S)
    (hN : N ^ d = 0) (x y : S) : texp ψ N x * texp ψ N y = texp ψ N (x + y) := by
  letI : Algebra ℚ S := ψ.toAlgebra
  have hn : ∀ w : S, IsNilpotent (w • N) := fun w => ⟨d, by rw [smul_pow, hN, smul_zero]⟩
  rw [texp_eq_exp ψ N hN, texp_eq_exp ψ N hN, texp_eq_exp ψ N hN, add_smul,
    IsNilpotent.exp_add_of_commute (((Commute.refl N).smul_left x).smul_right y) (hn x) (hn y)]

theorem sum_eq_smul_texp {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S)
    (A x : S) :
    ∑ n ∈ Finset.range d, (A * ψ ((n.factorial : ℚ)⁻¹) * x ^ n) • N ^ n = A • texp ψ N x := by
  rw [texp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_smul, mul_assoc]

theorem texp_cocycle {S : Type} [CommRing S] (ψ : ℚ →+* S) {d : ℕ} (N : Matrix (Fin d) (Fin d) S)
    (hN : N ^ d = 0) (A B q p v z Y : S) (hpv : p * v = q) :
    (∑ n ∈ Finset.range d, (A * ψ ((n.factorial : ℚ)⁻¹) * (q * z) ^ n) • N ^ n) *
      (∑ n ∈ Finset.range d, (B * ψ ((n.factorial : ℚ)⁻¹) * (-p * (Y + v * z)) ^ n) • N ^ n) =
    A • ∑ n ∈ Finset.range d, (B * ψ ((n.factorial : ℚ)⁻¹) * (-p * Y) ^ n) • N ^ n := by
  rw [sum_eq_smul_texp, sum_eq_smul_texp, sum_eq_smul_texp, Matrix.smul_mul, Matrix.mul_smul,
    texp_mul ψ N hN, smul_smul, smul_smul, mul_comm A B]
  congr 2
  linear_combination (-z) * hpv

end GlobalTheory.SstPer.Cob

namespace GlobalTheory.SstPer.Cob

theorem map_sum_smul_pow {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (a : ℕ → R) (x : R) (M : Matrix (Fin d) (Fin d) R) :
    (∑ n ∈ Finset.range d, (a n * x ^ n) • M ^ n).map h =
      ∑ n ∈ Finset.range d, (h (a n) * h x ^ n) • (M.map h) ^ n := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← RingHom.mapMatrix_apply, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have e : h.mapMatrix ((a n * x ^ n) • M ^ n) = h (a n * x ^ n) • h.mapMatrix (M ^ n) := by
    ext i j; simp
  rw [e, map_pow, map_mul, map_pow, RingHom.mapMatrix_apply]

theorem map_smul_matrix {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ} (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map h = h c • M.map h := by
  ext i j; simp

variable {l : ℕ} [Fact l.Prime]

def qD (C : Core l) : ℚ →+* Per.BdRp l :=
  (C.o.comp (algebraMap ℚ_[l] (Om l))).comp (algebraMap ℚ ℚ_[l])

theorem aDp_zA_ecoef (C : Core l) {k₀ k n : ℕ} (h : ‖ecoefQ l k₀ k n‖ ≤ 1) :
    aDp l (Per.zA l (ecoef l k₀ k n)) =
      (l : Per.BdRp l) ^ k₀ * qD C ((n.factorial : ℚ)⁻¹) * (qD C ((l : ℚ)⁻¹) ^ k) ^ n := by
  rw [← C.o_sec.z, ecoef_val h]
  have e : ecoefQ l k₀ k n =
      algebraMap ℚ ℚ_[l] ((l : ℚ) ^ k₀ * (n.factorial : ℚ)⁻¹ * (((l : ℚ)⁻¹) ^ k) ^ n) := by
    simp only [ecoefQ, map_mul, map_pow, map_inv₀, map_natCast]
    ring
  rw [e]
  simp only [qD, RingHom.comp_apply, map_mul, map_pow, map_natCast]

end GlobalTheory.SstPer.Cob

namespace GlobalTheory.SstPer.Cob
variable {l : ℕ} [Fact l.Prime]

theorem coef_Λ (C : Core l) {K : FinExt l} (bk : BK K) {I : Ideal (Per.BdRp l)} (H : bk.S →+* Per.BdRp l ⧸ I)
    (hH : ∀ w, H (PowerSeries.C w) = Ideal.Quotient.mk I (aDp l (wA l bk.a w))) {KK L n : ℕ}
    (hn : ‖ecoefQ l KK L n‖ ≤ 1) :
    H (PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) ((-1) ^ n * ecoef l KK L n))) =
      (l : Per.BdRp l ⧸ I) ^ KK * Ideal.Quotient.mk I (qD C ((n.factorial : ℚ)⁻¹)) *
        (-(Ideal.Quotient.mk I (qD C ((l : ℚ)⁻¹)) ^ L)) ^ n := by
  rw [hH, AlgHom.commutes, padicInt_hom_ext_pt (algebraMap ℤ_[l] (Ainf l)) (Per.zA l)]
  rw [map_mul, map_pow, map_neg, map_one, map_mul, map_pow, map_neg, map_one, aDp_zA_ecoef C hn]
  simp only [map_mul, map_pow, map_natCast, map_neg, map_one]
  ring

end GlobalTheory.SstPer.Cob

namespace GlobalTheory.SstPer.Cob

theorem cocycle_cob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → Mn ^ d = 0 → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∀ m : ℕ, ∃ (kk : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ kk • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((GlobalTheory.SstPer.kap C bk k₀ k Mn (c g) * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C _ d k k₀ Mn c hk hMn hlog m
  obtain ⟨k', s, hEs, hs⟩ := hlog m
  obtain ⟨e, m', hm', hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero d) l
    (Fact.out : l.Prime).ne_one
  have hnorm : ∀ n < d, ‖ecoefQ l (e + (k' + k) * d) (k' + k) n‖ ≤ 1 :=
    fun n hn => ecoefQ_norm_le (k' + k) hm' hd hn
  let cf : ℕ → bk.S := fun n =>
    PowerSeries.C (algebraMap ℤ_[l] (Wq l bk.a) ((-1) ^ n * ecoef l (e + (k' + k) * d) (k' + k) n))
  let Λ : Matrix (Fin d) (Fin d) bk.S :=
    ∑ n ∈ Finset.range d, (cf n * s ^ n) • (Mn.map PowerSeries.C) ^ n
  refine ⟨e + (k' + k) * d, Λ, ?_, ?_⟩
  · intro i j
    rcases d with _ | d
    · exact i.elim0
    have h0 : ecoef l (e + (k' + k) * (d + 1)) (k' + k) 0 = (l : ℤ_[l]) ^ (e + (k' + k) * (d + 1)) := by
      apply Subtype.ext
      rw [ecoef_val (hnorm 0 d.succ_pos)]
      simp [ecoefQ]
    have hc0 : cf 0 = (l : bk.S) ^ (e + (k' + k) * (d + 1)) := by
      simp only [cf, pow_zero, one_mul, h0, map_pow, map_natCast]
    have hΛ : Λ - (l : bk.S) ^ (e + (k' + k) * (d + 1)) • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) bk.S) =
        ∑ n ∈ Finset.range d, (cf (n + 1) * s ^ (n + 1)) • (Mn.map PowerSeries.C) ^ (n + 1) := by
      simp only [Λ]
      rw [Finset.sum_range_succ', hc0, pow_zero, pow_zero, mul_one, add_sub_cancel_right]
    rw [hΛ, Matrix.sum_apply]
    refine Finset.dvd_sum fun n _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hEs.trans (dvd_pow_self s n.succ_ne_zero)) _) _
  · intro g i j
    let I := Per.FilP l m
    let Θ : Per.Acris l →+* Per.BdRp l ⧸ I := (Ideal.Quotient.mk I).comp C.j
    let ψ : ℚ →+* Per.BdRp l ⧸ I := (Ideal.Quotient.mk I).comp (qD C)
    let lam : Per.BdRp l ⧸ I := ψ ((l : ℚ)⁻¹)
    let φ : bk.S →+* Per.Acris l := (algebraMap (Ainf l) (Per.Acris l)).comp bk.ev
    let H0 : bk.S →+* Per.BdRp l ⧸ I := (Ideal.Quotient.mk I).comp ((aDp l).comp bk.ev)
    let H1 : bk.S →+* Per.BdRp l ⧸ I :=
      (Ideal.Quotient.mk I).comp ((aDp l).comp ((Per.σA (g : GQ l)).comp bk.ev))
    let N : Matrix (Fin d) (Fin d) (Per.BdRp l ⧸ I) := (Mn.map PowerSeries.C).map H0
    let z : Per.BdRp l ⧸ I := Ideal.Quotient.mk I (aDp l (Per.zA l (c g)) * C.j C.t)
    let Y : Per.BdRp l ⧸ I := Ideal.Quotient.mk I (aDp l (bk.ev s))
    have hj : ∀ x : Ainf l, C.j (algebraMap (Ainf l) (Per.Acris l) x) = aDp l x :=
      fun x => by
        have h := C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)
        rw [← GlobalTheory.RingIface.tower, Subalgebra.coe_algebraMap] at h
        exact h
    have hσ : ∀ x : Ainf l, sigA (g : GQ l) (algebraMap (Ainf l) (Per.Acris l) x) =
        algebraMap (Ainf l) (Per.Acris l) (Per.σA (g : GQ l) x) :=
      fun x => (GlobalTheory.CrisMaps.sigA_extends (g : GQ l)).alg x
    have hC0 : ∀ w, H0 (PowerSeries.C w) = Ideal.Quotient.mk I (aDp l (wA l bk.a w)) := fun w => by
      simp only [H0, RingHom.comp_apply, bk.ev_C]
    have hC1 : ∀ w, H1 (PowerSeries.C w) = Ideal.Quotient.mk I (aDp l (wA l bk.a w)) := fun w => by
      simp only [H1, RingHom.comp_apply, bk.ev_C, bk.gal_w]
    have m0 : (Λ.map φ).map Θ = Λ.map H0 := by
      ext a b
      simp only [Matrix.map_apply, Θ, φ, H0, RingHom.comp_apply, hj]
    have m1 : ((Λ.map φ).map (sigA (g : GQ l))).map Θ = Λ.map H1 := by
      ext a b
      simp only [Matrix.map_apply, Θ, φ, H1, RingHom.comp_apply, hσ, hj]
    have hN : N ^ d = 0 := by
      simp only [N, ← RingHom.mapMatrix_apply, ← map_pow, hMn, map_zero]
    have hN1 : (Mn.map PowerSeries.C).map H1 = N := by
      ext a b
      simp only [N, Matrix.map_apply, hC0, hC1]
    have hNk : (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map Θ = N := by
      ext a b
      simp only [N, Matrix.map_apply, hC0, Θ, RingHom.comp_apply, hj, bk.ev_C]
    have hY : H1 s = Y + (l : Per.BdRp l ⧸ I) ^ k' * z := by
      have h := (Ideal.Quotient.eq_zero_iff_mem (I := I)).2 (hs g)
      simp only [map_sub, map_mul, map_pow, map_natCast] at h
      simp only [H1, Y, z, RingHom.comp_apply, map_mul]
      linear_combination h
    have e0 : (Λ.map φ).map Θ = ∑ n ∈ Finset.range d,
        ((l : Per.BdRp l ⧸ I) ^ (e + (k' + k) * d) * ψ ((n.factorial : ℚ)⁻¹) *
          (-(lam ^ (k' + k)) * Y) ^ n) • N ^ n := by
      rw [m0]
      show (∑ n ∈ Finset.range d, (cf n * s ^ n) • (Mn.map PowerSeries.C) ^ n).map H0 = _
      rw [map_sum_smul_pow H0 cf s]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [show H0 (cf n) = _ from coef_Λ C bk H0 hC0 (hnorm n (Finset.mem_range.1 hn))]
      simp only [ψ, lam, RingHom.comp_apply]
      congr 1
      simp only [H0, Y, RingHom.comp_apply]
      ring
    have e1 : ((Λ.map φ).map (sigA (g : GQ l))).map Θ = ∑ n ∈ Finset.range d,
        ((l : Per.BdRp l ⧸ I) ^ (e + (k' + k) * d) * ψ ((n.factorial : ℚ)⁻¹) *
          (-(lam ^ (k' + k)) * (Y + (l : Per.BdRp l ⧸ I) ^ k' * z)) ^ n) • N ^ n := by
      rw [m1]
      show (∑ n ∈ Finset.range d, (cf n * s ^ n) • (Mn.map PowerSeries.C) ^ n).map H1 = _
      rw [map_sum_smul_pow H1 cf s, hN1, hY]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [show H1 (cf n) = _ from coef_Λ C bk H1 hC1 (hnorm n (Finset.mem_range.1 hn))]
      simp only [ψ, lam, RingHom.comp_apply]
      congr 1
      rw [mul_pow (-_) (Y + _)]
      ring
    have eK : (kap C bk k₀ k Mn (c g)).map Θ = ∑ n ∈ Finset.range d,
        ((l : Per.BdRp l ⧸ I) ^ k₀ * ψ ((n.factorial : ℚ)⁻¹) * (lam ^ k * z) ^ n) • N ^ n := by
      unfold kap
      rw [map_sum_smul_pow Θ (fun n => algebraMap (Ainf l) (Per.Acris l) (Per.zA l (ecoef l k₀ k n))), hNk]
      refine Finset.sum_congr rfl fun n hn => ?_
      have h1 : Θ (algebraMap (Ainf l) (Per.Acris l) (Per.zA l (ecoef l k₀ k n))) =
          (l : Per.BdRp l ⧸ I) ^ k₀ * ψ ((n.factorial : ℚ)⁻¹) * (lam ^ k) ^ n := by
        simp only [Θ, RingHom.comp_apply, hj]
        rw [aDp_zA_ecoef C (hk n (Finset.mem_range.1 hn))]
        simp only [ψ, lam, map_mul, map_pow, map_natCast, RingHom.comp_apply]
      have h2 : Θ (algebraMap (Ainf l) (Per.Acris l) (Per.zA l (c g)) * C.t) = z := by
        simp only [Θ, z, RingHom.comp_apply, map_mul, hj]
      rw [h1, h2]
      congr 1
      ring
    have hpv : lam ^ (k' + k) * (l : Per.BdRp l ⧸ I) ^ k' = lam ^ k := by
      have hl : lam * (l : Per.BdRp l ⧸ I) = 1 := by
        have h := congrArg ψ (inv_mul_cancel₀ (by exact_mod_cast (Fact.out : l.Prime).ne_zero : (l : ℚ) ≠ 0))
        rw [map_mul, map_natCast, map_one] at h
        exact h
      rw [pow_add, mul_comm (lam ^ k'), mul_assoc, ← mul_pow, hl, one_pow, mul_one]
    have hz : (kap C bk k₀ k Mn (c g) * (Λ.map φ).map (sigA (g : GQ l)) -
        (l : Per.Acris l) ^ k₀ • Λ.map φ).map Θ = 0 := by
      rw [← RingHom.mapMatrix_apply, map_sub, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
        RingHom.mapMatrix_apply, map_smul_matrix, eK, e1, e0,
        texp_cocycle ψ N hN _ _ _ _ _ z Y hpv, map_pow, map_natCast, sub_self]
    have hij := congrFun (congrFun hz i) j
    rw [Matrix.map_apply] at hij
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hij

end GlobalTheory.SstPer.Cob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableExpCocycleCoboundaryModFilStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_exp_cocycle_coboundary_mod_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → Mn ^ d = 0 → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∀ m : ℕ, ∃ (kk : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ kk • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((GlobalTheory.SstPer.kap C bk k₀ k Mn (c g) * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.Cob.cocycle_cob) | (exact GlobalTheory.SstPer.Cob.cocycle_cob) | (intros; apply GlobalTheory.SstPer.Cob.cocycle_cob  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableInvariantBdRPlusBasisApprox
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableInvariantBdRPlusBasisApprox
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer.SFil

def texp {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (x : R) :
    Matrix (Fin d) (Fin d) R :=
  ∑ i ∈ Finset.range d, (q ((i.factorial : ℚ)⁻¹) * x ^ i) • N ^ i

theorem map_sum_smul_pow {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R) (a : ℕ → R) :
    (∑ i ∈ Finset.range d, a i • N ^ i).map f = ∑ i ∈ Finset.range d, f (a i) • (N.map f) ^ i := by
  change f.mapMatrix _ = ∑ i ∈ Finset.range d, f (a i) • (f.mapMatrix N) ^ i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow]
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem texp_map {R R' : Type} [CommRing R] [CommRing R'] (q : ℚ →+* R) (q' : ℚ →+* R') (f : R →+* R') {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R) (x : R) : (texp q N x).map f = texp q' (N.map f) (f x) := by
  have e : q' = f.comp q := Subsingleton.elim _ _
  unfold texp
  rw [map_sum_smul_pow, e]
  simp only [map_mul, map_pow, RingHom.comp_apply]

theorem texp_add {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (hN : N ^ d = 0)
    (x y : R) : texp q N x * texp q N y = texp q N (x + y) := by
  letI : Algebra ℚ R := q.toAlgebra
  have h : ∀ z : R, (z • N) ^ d = 0 := fun z => by rw [smul_pow, hN, smul_zero]
  have e : ∀ z : R, texp q N z = IsNilpotent.exp (z • N) := fun z => by
    rw [IsNilpotent.exp_eq_sum (h z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, mul_smul]
    exact algebraMap_smul R ((i.factorial : ℚ)⁻¹) _
  rw [e, e, e, add_smul, IsNilpotent.exp_add_of_commute _ ⟨d, h x⟩ ⟨d, h y⟩]
  exact ((Commute.refl N).smul_left x).smul_right y

theorem texp_zero {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) :
    texp q N 0 = 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  unfold texp
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

theorem texp_sub_mem {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (I : Ideal R)
    {x y : R} (h : x - y ∈ I) (i j : Fin d) : (texp q N x - texp q N y) i j ∈ I := by
  unfold texp
  rw [← Finset.sum_sub_distrib, Matrix.sum_apply]
  refine I.sum_mem fun n _ => ?_
  rw [← sub_smul, Matrix.smul_apply, smul_eq_mul, ← mul_sub]
  exact I.mul_mem_right _ (I.mul_mem_left _ (Ideal.mem_of_dvd I (sub_dvd_pow_sub_pow x y n) h))

theorem cleared_map {S R : Type} [CommRing S] [CommRing R] (q : ℚ →+* R) (f : S →+* R) {d : ℕ}
    (N : Matrix (Fin d) (Fin d) S) {l : ℕ} (hl : l ≠ 0) (c e : ℕ) (a : ℕ → S)
    (ha : ∀ i < d, ((i.factorial : S) * (l : S) ^ (c * i)) * a i = (l : S) ^ e) (x : S) :
    (∑ i ∈ Finset.range d, (a i * x ^ i) • N ^ i).map f =
      (l : R) ^ e • texp q (N.map f) (q ((l : ℚ) ^ c)⁻¹ * f x) := by
  rw [map_sum_smul_pow]
  unfold texp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_smul]
  congr 1
  have h1 := congrArg f (ha i (Finset.mem_range.1 hi))
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 : q ((i.factorial : ℚ)⁻¹) * q ((l : ℚ) ^ c)⁻¹ ^ i * ((i.factorial : R) * (l : R) ^ (c * i)) = 1 := by
    have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
    have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    rw [← map_natCast q, ← map_natCast q l, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul, ← map_one q]
    congr 1
    rw [pow_mul, inv_pow]
    field_simp
  rw [map_mul, map_pow, mul_pow, ← h1]
  linear_combination (-(f (a i) * f x ^ i)) * h2

theorem exists_cleared {l : ℕ} [Fact l.Prime] (c d : ℕ) :
    ∃ (e : ℕ) (a : ℕ → ℤ_[l]), ∀ i < d, ((i.factorial : ℤ_[l]) * (l : ℤ_[l]) ^ (c * i)) * a i = (l : ℤ_[l]) ^ e := by
  obtain ⟨e, m, hm, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd d.factorial_ne_zero l (Fact.out : l.Prime).ne_one
  refine ⟨e + c * d, fun i => ecoef l (e + c * d) c i, fun i hi => ?_⟩
  apply Subtype.ext
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hf0 : (i.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i)
  push_cast
  rw [ecoef_val (ecoefQ_norm_le c hm hd hi)]
  unfold ecoefQ
  field_simp

theorem approx {l : ℕ} [Fact l.Prime] {S R : Type} [CommRing S] [IsDomain S] [CharZero S] [CommRing R]
    (z : ℤ_[l] →+* S) (q : ℚ →+* R) (f : S →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) S) (hN : N ^ d = 0)
    (I : Ideal R) (k k' : ℕ) (s : S) (lam : R) (h : f s - (l : R) ^ k' * lam ∈ I) :
    ∃ (e : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) S), Λ * Λ' = (l : S) ^ (2 * e) • (1 : Matrix (Fin d) (Fin d) S) ∧
      ∀ i j, (Λ.map f - (l : R) ^ e • texp q (N.map f) (-(q ((l : ℚ) ^ k)⁻¹ * lam))) i j ∈ I := by
  obtain ⟨e, a, ha⟩ := exists_cleared (l := l) (k + k') d
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have ha' : ∀ i < d, ((i.factorial : S) * (l : S) ^ ((k + k') * i)) * z (a i) = (l : S) ^ e := fun i hi => by
    simpa only [map_mul, map_pow, map_natCast] using congrArg z (ha i hi)
  refine ⟨e, ∑ i ∈ Finset.range d, (z (a i) * (-s) ^ i) • N ^ i, ∑ i ∈ Finset.range d, (z (a i) * s ^ i) • N ^ i,
    ?_, fun i j => ?_⟩
  · have hinj := IsFractionRing.injective S (FractionRing S)
    apply Matrix.map_injective hinj
    have hN' : (N.map (algebraMap S (FractionRing S))) ^ d = 0 := by
      change ((algebraMap S (FractionRing S)).mapMatrix N) ^ d = 0
      rw [← map_pow, hN, map_zero]
    change Matrix.map _ _ = Matrix.map _ _
    rw [Matrix.map_mul, cleared_map (algebraMap ℚ _) _ N hl _ _ _ ha', cleared_map (algebraMap ℚ _) _ N hl _ _ _ ha',
      Matrix.smul_mul, Matrix.mul_smul, texp_add _ _ hN', map_neg, mul_neg, neg_add_cancel, texp_zero, smul_smul,
      ← pow_add, two_mul]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  · rw [cleared_map q f N hl _ _ _ ha', ← smul_sub, Matrix.smul_apply, smul_eq_mul]
    refine I.mul_mem_left _ (texp_sub_mem q _ I ?_ i j)
    have h2 : q ((l : ℚ) ^ k)⁻¹ = q ((l : ℚ) ^ (k + k'))⁻¹ * (l : R) ^ k' := by
      have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
      rw [← map_natCast q l, ← map_pow, ← map_mul]
      congr 1
      field_simp
      ring
    have h3 := I.mul_mem_left (-q ((l : ℚ) ^ (k + k'))⁻¹) h
    convert h3 using 1
    rw [h2, map_neg]
    ring

theorem invariant_basis_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) (k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), Mn ^ d = 0 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∀ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) → ∃ Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l), (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hF d ρ U k Mn c hMn hU lam hlam happ
  obtain ⟨-, -, -, -, -, -, -, -, -, hD, hDp, -, -⟩ := ActLaws.act_laws l
  let q : ℚ →+* Per.BdRp l := C.o.comp (algebraMap ℚ (Om l))
  let a : Per.BdRp l →+* Per.BdR l := algebraMap (Per.BdRp l) (Per.BdR l)
  let w : Wq l bk.a →+* Per.BdRp l := (aDp l).comp (wA l bk.a).toRingHom
  refine ⟨texp q (Mn.map w) (-(q ((l : ℚ) ^ k)⁻¹ * lam)), fun g => ?_, fun m => ?_⟩
  · have hN : ((Mn.map w).map a) ^ d = 0 := by
      change (a.mapMatrix (w.mapMatrix Mn)) ^ d = 0
      rw [← map_pow, ← map_pow, hMn, map_zero, map_zero]
    have hNσ : ((Mn.map w).map a).map (Per.σD (g : GQ l)) = (Mn.map w).map a := by
      ext i j
      change Per.σD (g : GQ l) (a (aDp l (wA l bk.a (Mn i j)))) = a (aDp l (wA l bk.a (Mn i j)))
      rw [hD, hDp, bk.gal_w]
    have hq : ∀ x : ℚ, Per.σD (g : GQ l) (a (q x)) = a (q x) := fun x =>
      RingHom.congr_fun (Subsingleton.elim ((Per.σD (g : GQ l)).comp (a.comp q)) (a.comp q)) x
    have hqB : ∀ x : ℚ, C.ι (C.qB (x : ℚ_[l])) = a (q x) := fun x =>
      RingHom.congr_fun (Subsingleton.elim (C.ι.comp (C.qB.comp (Rat.castHom ℚ_[l]))) (a.comp q)) x
    have h1 := congrArg (fun M => Matrix.map M C.ι) (hU g)
    simp only [Matrix.map_mul] at h1
    rw [map_sum_smul_pow] at h1
    have e1 : ((ρ g).map (Per.zB l)).map C.ι = (ρ g).map (Per.zD l) := by
      ext i j
      change C.ι (Per.zB l (ρ g i j)) = Per.zD l (ρ g i j)
      rw [← T.zB, ← hF.ι, AlgHom.commutes, T.zD]
    have e2 : (U.map (Per.σB (g : GQ l))).map C.ι = (U.map C.ι).map (Per.σD (g : GQ l)) := by
      ext i j
      exact ULaws.iota_sigma C _ _
    have e3 : (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)).map C.ι = (Mn.map w).map a := by
      ext i j
      exact ULaws.iota_aB C _
    have e4 : ∑ i ∈ Finset.range d, C.ι (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) *
        (Per.zB l (c g) * C.tB) ^ i) • ((Mn.map w).map a) ^ i =
        texp (a.comp q) ((Mn.map w).map a) (a (q ((l : ℚ) ^ k)⁻¹) * a (aDp l (Per.zA l (c g)) * C.j C.t)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have e5 : (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) =
          (((i.factorial : ℚ)⁻¹ * ((l : ℚ) ^ k)⁻¹ ^ i : ℚ) : ℚ_[l]) := by
        push_cast
        rw [mul_inv, pow_mul, inv_pow]
      have e6 : C.ι (Per.zB l (c g)) = a (aDp l (Per.zA l (c g))) := by
        rw [← ULaws.u_padicInt C, C.ι_u, ← C.o_sec.z]
        rfl
      have e7 : C.ι C.tB = a (C.j C.t) := C.ι_j _
      rw [map_mul C.ι, e5, hqB, map_pow C.ι, map_mul C.ι, e6, e7]
      simp only [map_mul, map_pow, RingHom.comp_apply, mul_pow]
      ring
    rw [e1, e2, e3, e4] at h1
    change _ * (U.map C.ι * Matrix.map _ a).map _ = U.map C.ι * Matrix.map _ a
    rw [texp_map q (a.comp q) a, Matrix.map_mul, texp_map (a.comp q) (a.comp q), hNσ, ← Matrix.mul_assoc, h1,
      Matrix.mul_assoc, texp_add _ _ hN]
    congr 2
    have e8 : Per.σD (g : GQ l) (a lam) = a lam + a (aDp l (Per.zA l (c g)) * C.j C.t) :=
      (hD _ lam).trans ((congrArg a (hlam g)).trans (map_add a _ _))
    rw [map_neg a, map_mul a (q _), map_neg, map_mul (Per.σD (g : GQ l)), hq, e8]
    ring
  · obtain ⟨k', s, -, hs⟩ := happ m
    haveI : CharZero bk.S := RingHom.charZero ((Per.θD l).comp ((aDp l).comp bk.ev))
    have hN : (Mn.map (PowerSeries.C : Wq l bk.a →+* bk.S)) ^ d = 0 := by
      change ((PowerSeries.C : Wq l bk.a →+* bk.S).mapMatrix Mn) ^ d = 0
      rw [← map_pow, hMn, map_zero]
    have e1 : (Mn.map (PowerSeries.C : Wq l bk.a →+* bk.S)).map ((aDp l).comp bk.ev) = Mn.map w := by
      ext i j
      exact congrArg (aDp l) (bk.ev_C _)
    have := approx ((PowerSeries.C : Wq l bk.a →+* bk.S).comp (algebraMap ℤ_[l] (Wq l bk.a))) q
      ((aDp l).comp bk.ev) _ hN (Per.FilP l m) k k' s lam hs
    rwa [e1] at this

end GlobalTheory.SstPer.SFil

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableInvariantBdRPlusBasisApproxStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_invariant_bdRPlus_basis_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) (k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), Mn ^ d = 0 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∀ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) → ∃ Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l), (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.SFil.invariant_basis_approx) | (exact GlobalTheory.SstPer.SFil.invariant_basis_approx) | (intros; apply GlobalTheory.SstPer.SFil.invariant_basis_approx  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableLatticePeriodsAcris
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer

theorem sst_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsSst P (qRep ρ) → ∃ (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).val.map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hC d ρ hsst
  have hdr := GlobalTheory.sst_isDR l P AI T K _ (qRep ρ) hsst
  obtain ⟨H, -⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) bk.span_ev d ρ hdr
  obtain ⟨b, c, hb, hfix, hlog⟩ := GlobalTheory.T.exists_log_teichmuller_pow_semistablePeriods l K bk P AI T C hC trivial
  obtain ⟨U, U', c₁, c₃, k, F, F', Mn, hUU', hFF', hφ, hMn, hgal⟩ := GlobalTheory.T.semistable_periodMatrix_at_log_zero l K bk P AI T C hC d ρ b c hb hsst
  obtain ⟨-, hInvdR⟩ := GlobalTheory.MemLoc.fits_inv l P AI T C hC
  obtain ⟨lam, hlamg, hlamA⟩ := GlobalTheory.T.exists_log_uniformizerTilt_bdRPlus_cocycle l K bk P AI T C hC b c hb hfix hlog
  obtain ⟨Λ₀, hΛ₀g, hΛ₀A⟩ := GlobalTheory.T.semistable_invariant_bdRPlus_basis_approx l K bk P AI T C hC d (fun g => (ρ g).val) U k Mn c hMn hgal lam hlamg hlamA
  obtain ⟨e, m, hm, hdf⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero d) l (Fact.out : l.Prime).ne_one
  have hk₀ : ∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l (e + k * d) k i‖ ≤ 1 := fun i hi => GlobalTheory.SstPer.ecoefQ_norm_le k hm hdf hi
  obtain ⟨N₀, hZ⟩ := GlobalTheory.T.semistable_periods_over_Acris l K bk P AI T C hC d (fun g => (ρ g).val) U U' hUU' c₁ F hφ k (e + k * d) Mn c hk₀ hgal
  have hUUι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨N, c₂, X, X', hN, hXX', hX, hX'⟩ := GlobalTheory.T.exists_twisted_modification_at_E l K bk C hInvdR d (fun g => (ρ g).val) H (U.map C.ι) (U'.map C.ι) Λ₀ hUUι hΛ₀g hΛ₀A N₀
  obtain ⟨Z, Z', hZZ', hZφ, hZg, hZX, hZX'⟩ := hZ N hN X X' hX hX'
  refine ⟨N, c₁, c₂, c₃, e + k * d, F, F', X, X', Z, Z', fun g => GlobalTheory.SstPer.kap C bk (e + k * d) k Mn (c g), hFF', hXX', hZZ', hZφ, hZg, ?_, hZX, hZX', GlobalTheory.T.semistable_exp_cocycle_coboundary_mod_fil l K bk P AI T C hC d k (e + k * d) Mn c hk₀ hMn hlog⟩
  intro g hg
  simp only
  rw [hfix g hg]
  exact GlobalTheory.SstPer.kap_zero C bk _ k Mn

end GlobalTheory.SstPer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableLatticePeriodsAcrisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semistable_lattice_periods_acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsSst P (qRep ρ) → ∃ (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).val.map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.sst_periods) | (exact GlobalTheory.SstPer.sst_periods) | (intros; apply GlobalTheory.SstPer.sst_periods  <;> assumption)
end
