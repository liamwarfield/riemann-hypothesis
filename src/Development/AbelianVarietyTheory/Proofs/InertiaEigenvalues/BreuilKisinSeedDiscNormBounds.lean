module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBounds
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RhoZeroNormBounds

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem ρ₀_pos (bk : BK K) : 0 < bk.ρ₀ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  unfold BK.ρ₀
  exact NNReal.rpow_pos hl0

theorem ρ₀_pow (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

theorem norm_l_mul (bk : BK K) (y : bk.DA bk.ρ₀) : ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖ := by
  rw [(GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).2.1 y, div_eq_inv_mul]

theorem norm_iS_le (bk : BK K) (x : bk.S) : ‖bk.iS x‖ ≤ 1 :=
  norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (bk.ev x)

theorem norm_iS_E (bk : BK K) : ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ := by
  haveI := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).1
  have hE : bk.E = bk.Ep.eval₂ PowerSeries.C PowerSeries.X := (Polynomial.eval₂_C_X_eq_coe).symm
  rw [hE, Polynomial.hom_eval₂, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]
  have hinv : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hinv fun i hi => ?_
    obtain ⟨d, hd⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    have e : (bk.iS.comp PowerSeries.C) (bk.Ep.coeff i) * bk.iS PowerSeries.X ^ i =
        (l : bk.DA bk.ρ₀) * bk.iS (PowerSeries.C d * PowerSeries.X ^ i) := by
      rw [hd, RingHom.comp_apply, map_mul, map_mul, map_mul, map_pow, map_natCast, map_natCast, mul_assoc]
    rw [e, norm_l_mul]
    exact mul_le_of_le_one_right hinv (norm_iS_le bk _)
  · rw [bk.monic.coeff_natDegree, map_one, one_mul, ← map_pow]
    change ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev (PowerSeries.X ^ bk.Ep.natDegree))‖ ≤ _
    rw [map_pow]
    refine (norm_toDisc_pow_le _ (ρ₀_pos bk)).trans ?_
    rw [← NNReal.coe_pow, ρ₀_pow, NNReal.coe_inv, NNReal.coe_natCast]

theorem norm_iA_ker (bk : BK K) (a : Ainf l) (ha : Per.θ l a = 0) : ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ := by
  have hmem : a ∈ Ideal.span {bk.ev bk.E} := by rw [bk.span_ev]; exact ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [map_mul]
  refine (norm_mul_le _ _).trans ?_
  have h1 : ‖bk.iA c‖ ≤ 1 := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) c
  have h2 : ‖bk.iA (bk.ev bk.E)‖ ≤ (l : ℝ)⁻¹ := norm_iS_E bk
  calc ‖bk.iA c‖ * ‖bk.iA (bk.ev bk.E)‖ ≤ 1 * (l : ℝ)⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem seed_norms : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ ∧ (∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖) ∧ ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ :=
  fun _ _ _ bk => ⟨norm_iS_E bk, norm_l_mul bk, norm_iA_ker bk⟩

end GlobalTheory.BSP.RhoZeroNormBounds
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBoundsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_seedDisc_norm_bounds : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ ∧ (∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖) ∧ ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ := by
  first | exact @GlobalTheory.BSP.RhoZeroNormBounds.seed_norms | exact GlobalTheory.BSP.RhoZeroNormBounds.seed_norms | (intros; apply GlobalTheory.BSP.RhoZeroNormBounds.seed_norms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocycles
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.RedLocConst

theorem mem_span_smul_top' {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem redT_mem_Z1Q : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI a
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
  set c : LL := algebraMap O LL (ϖ ^ r) with hcdef
  have hc : c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 (pow_ne_zero _ hϖ.ne_zero)
  have hTr : IsOpen ((fun v : A.V => c • v) '' (LA.T : Set A.V)) :=
    (Homeomorph.smulOfNeZero c hc).isOpenMap _ hT
  have hsm : ∀ v : A.V, c • v = ϖ ^ r • v := fun v => by rw [hcdef, algebraMap_smul]
  have hmem : ∀ x : ↥LA.T, x ∈ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ↔
      (x : A.V) ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V) := by
    intro x
    rw [mem_span_smul_top']
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, y.2, ?_⟩
      show c • (y : A.V) = _
      rw [hsm]; rfl
    · rintro ⟨y, hy, hxy⟩
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [← hxy]
      show c • y = ϖ ^ r • y
      exact hsm y
  have ha : (a : _ → A.V) ∈ latticeCocycles LA := a.2
  obtain ⟨⟨hcont, hcoc⟩, -⟩ := ha
  have hval : ∀ g, ((redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) a) g) =
      Submodule.Quotient.mk (evT LA g a) := fun g => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g0
    refine ⟨(fun g => (a : _ → A.V) g - (a : _ → A.V) g0) ⁻¹' ((fun v : A.V => c • v) '' (LA.T : Set A.V)),
      hTr.preimage (hcont.sub continuous_const), ?_, ?_⟩
    · show (a : _ → A.V) g0 - (a : _ → A.V) g0 ∈ (fun v : A.V => c • v) '' (LA.T : Set A.V)
      rw [sub_self]; exact ⟨0, LA.T.zero_mem, smul_zero c⟩
    · intro g hg
      rw [hval, hval, Submodule.Quotient.eq, hmem]
      exact hg
  · intro g h
    change (Submodule.Quotient.mk (evT LA (g * h) a) : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) =
      Submodule.Quotient.mk (evT LA g a) + actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a))
    rw [show actQ LA _ hI g (Submodule.Quotient.mk (evT LA h a)) =
      Submodule.Quotient.mk (actT LA g (evT LA h a)) from rfl, ← Submodule.Quotient.mk_add]
    have hx : evT LA (g * h) a = evT LA g a + actT LA g (evT LA h a) :=
      Subtype.ext (hcoc g h)
    rw [hx]

end GlobalTheory.RedLocConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocyclesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  first | exact @GlobalTheory.RedLocConst.redT_mem_Z1Q | exact GlobalTheory.RedLocConst.redT_mem_Z1Q | (intros; apply GlobalTheory.RedLocConst.redT_mem_Z1Q <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqOfSubMem
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem wittVector_exists_eq_pow_add_natCast_mul (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k]
    [CharP k l] [PerfectRing k l] (w : WittVector l k) :
    ∃ a b : WittVector l k, w = a ^ l + (l : WittVector l k) * b := by

  obtain ⟨c, hc⟩ : ∃ c : k, c ^ l = w.coeff 0 := ⟨_, frobeniusEquiv_symm_pow_p k l _⟩
  set a : WittVector l k := WittVector.teichmuller l c with ha

  have h0 : ∀ i < 1, (w - a ^ l).coeff i = 0 := by
    intro i hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    change WittVector.constantCoeff (w - a ^ l) = 0
    rw [map_sub, map_pow]
    change w.coeff 0 - (WittVector.teichmuller l c).coeff 0 ^ l = 0
    rw [WittVector.teichmuller_coeff_zero, hc, sub_self]
  have hV : w - a ^ l = WittVector.verschiebung ((w - a ^ l).shift 1) :=
    WittVector.eq_iterate_verschiebung h0

  set y := (w - a ^ l).shift 1 with hy
  set b := (WittVector.frobeniusEquiv l k).symm y with hb
  have hFb : WittVector.frobenius b = y := (WittVector.frobeniusEquiv l k).apply_symm_apply y
  refine ⟨a, b, ?_⟩
  have hVb : WittVector.verschiebung y = b * (l : WittVector l k) := by
    rw [← hFb, WittVector.verschiebung_frobenius]
  calc w = (w - a ^ l) + a ^ l := by ring
    _ = b * (l : WittVector l k) + a ^ l := by rw [hV, hVb]
    _ = a ^ l + (l : WittVector l k) * b := by ring

theorem wittVector_ringHom_eq_of_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C] (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ ω ω' : WittVector l k →+* C, (∀ w, ω w - ω' w ∈ J) → ω = ω' := by
  intro l _ k _ _ _ C _ J hl hJ ω ω' h

  have key : ∀ n : ℕ, ∀ w, ω w - ω' w ∈ J ^ (n + 1) := by
    intro n
    induction n with
    | zero => intro w; simpa using h w
    | succ n ih =>
      intro w
      obtain ⟨a, b, rfl⟩ := wittVector_exists_eq_pow_add_natCast_mul l k w
      obtain ⟨d, hdJ, hda⟩ : ∃ d, d ∈ J ^ (n + 1) ∧ ω a = ω' a + d := ⟨_, ih a, by ring⟩
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (ω' a) d
      have e : ω (a ^ l + (l : WittVector l k) * b) - ω' (a ^ l + (l : WittVector l k) * b) =
          d ^ l + (l : C) * (ω' a * d * r) + (l : C) * (ω b - ω' b) := by
        simp only [map_add (f := _), map_mul, map_pow, map_natCast]
        rw [hda, hr]
        ring
      rw [e]
      have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
      refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      ·
        have hpow : d ^ l ∈ J ^ ((n + 1) * l) := by
          rw [pow_mul]
          exact Ideal.pow_mem_pow hdJ l
        exact Ideal.pow_le_pow_right (by nlinarith) hpow
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hl (Ideal.mul_mem_right r _ (Ideal.mul_mem_left _ (ω' a) hdJ))
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hl (ih b)

  refine RingHom.ext fun w => ?_
  rw [← sub_eq_zero]
  refine hJ.haus _ fun n => ?_
  rw [SModEq.zero]
  have hn : ω w - ω' w ∈ J ^ n := by
    cases n with
    | zero => simp
    | succ n => exact key n w
  simpa using Submodule.smul_mem_smul hn (Submodule.mem_top : (1 : C) ∈ ⊤)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.HerrExtClass


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 4000000 in
theorem herr_extension_class_formula : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass Formalism.MainNotions.RamifiedCoefficientChains.adm16
  intro l _ K s LL h
  show Formalism.MainNotions.RamifiedCoefficientChains.HerrExt ((HW l).W K s LL h)
  have hA := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have hU := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  obtain ⟨e, e₀, hspan, hT, hj, hN, hEE, hφ, hγ, htf⟩ := hU
  refine ⟨e, (e₀ : ((HW l).W K s LL h).one.V), ?_, ?_, ?_⟩
  · exact ⟨by rw [hN]; exact Submodule.subset_span rfl, hN, hEE, hφ, hγ, hT⟩
  · intro T Tp ι π κ hκ hcoc x c hx w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)) := ⟨_, Formalism.MainNotions.DeltaInvariantLattices.resFun_Z1T _ T _ hcκ⟩
    have hc : ∀ g : ↥((HW l).W K s LL h).GKs, ι.f ((cr : ↥((HW l).W K s LL h).GKs → T.V) g) = Tp.ρ (g : ↥(GK K)) (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ (g : ↥(GK K)))
      have e2 := ((Tp.ρ (g : ↥(GK K))).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Formalism.MainNotions.DeltaInvariantLattices.resFun, LinearMap.funLeft_apply, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ (g : ↥(GK K))) t) t
    have key := GlobalTheory.Cyc.dict_ext_Ks D HW F hA l K s LL h T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK Formalism.MainNotions.DeltaInvariantLattices.res
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
  · intro _ hp2 T Tp ι π κ hκ hcoc x c hx hδ w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles T.L) := ⟨_, hcκ⟩
    have hc : ∀ g : ↥(GK K), ι.f ((cr : ↥(GK K) → T.V) g) = Tp.ρ g (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ g)
      have e2 := ((Tp.ρ g).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ g) t) t
    have hi : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) = 2 → ∃ i : ↥K.1, i ^ 2 = -1 :=
      fun h2' => absurd h2' hp2
    have key := GlobalTheory.ExtDict.dict_K D HW F hA l K s LL h hi T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he hδ w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK
    rw [← Submodule.Quotient.mk_smul]
    rfl

end GlobalTheory.HerrExtClass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusGaloisRelationFrameAinf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusGaloisRelationFrameAinf
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.GalPhi

variable {l : ℕ} [Fact l.Prime]

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  apply inclW_injective
  rw [← frobW_inclW, ← galW_inclW, ← galW_inclW, ← frobW_inclW]
  refine WittVector.ext fun n => ?_
  simp [galW, frobW, mapAlgEquivW, mapEquivW, WittVector.map_coeff, frobenius_def]

theorem frobenius_algebraMap (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  change WittVector.frobenius (zlW l (OCb l) z) = zlW l (OCb l) z
  rw [WittVector.frobenius_eq_map_frobenius]
  simp only [zlW, RingHom.comp_apply]
  refine WittVector.ext fun n => ?_
  simp only [WittVector.map_coeff]
  exact congrArg (fun φ : ZMod l →+* OCb l => φ (((WittVector.equiv l).symm.toRingHom z).coeff n))
    (RingHom.ext_zmod ((frobenius (OCb l) l).comp (ZMod.castHom (dvd_refl l) (OCb l))) (ZMod.castHom (dvd_refl l) (OCb l)))

theorem gal_ainf {K : FinExt l} (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (hY : Y.map (inclW l) = inclW l τ ^ N • F.T)
    (g : ↥(GK K)) :
    τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) =
      Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  have hz : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW (ρ g) := by
    refine Matrix.ext fun i j => ?_; exact (inclWA l).commutes _
  have hσ : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (galW_inclW _ _).symm
  have hT : (Y.map (inclW l)).map (galW l (g : GQ l)) = inclW l (Per.σA (g : GQ l) τ) ^ N • F.T.map (galW l (g : GQ l)) := by
    rw [hY, ← galW_inclW, ← map_pow]
    refine Matrix.ext fun i j => ?_; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Matrix.ext fun i j => ?_
  apply inclW_injective
  have key : (τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l)))).map (inclW l) =
      (Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)).map (inclW l) := by
    rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
      hz, hσ, hT, Matrix.mul_smul, F.gal, hY, Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
    simp only [map_pow]
  exact congrFun (congrFun key i) j

end GlobalTheory.GalPhi


open GlobalTheory.GalPhi in
theorem GlobalTheory.GalPhi.galPhi : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), (bk.ev bk.E * τ) ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * (Y.map WittVector.frobenius).map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) (bk.ev bk.E * τ) ^ N • (Y.map WittVector.frobenius * (F.ε g).map WittVector.frobenius) := by
  intro l _ K bk τ hτ N d ρ F Y hY g
  have h := congrArg (fun M => M.map (WittVector.frobenius : Ainf l →+* Ainf l)) (gal_ainf bk τ N d ρ F Y hY g)
  rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
    map_pow, map_pow, ← σA_frobenius, hτ.1] at h
  have h1 : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (ρ g).map (algebraMap ℤ_[l] (Ainf l)) := by
    refine Matrix.ext fun i j => ?_; exact frobenius_algebraMap _
  have h2 : (Y.map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (Y.map WittVector.frobenius).map (Per.σA (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (σA_frobenius _ _).symm
  rw [h1, h2] at h
  exact h

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusGaloisRelationFrameAinfStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_galois_relation_frame_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), (bk.ev bk.E * τ) ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * (Y.map WittVector.frobenius).map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) (bk.ev bk.E * τ) ^ N • (Y.map WittVector.frobenius * (F.ε g).map WittVector.frobenius) := by
  first | exact @GlobalTheory.GalPhi.galPhi | exact GlobalTheory.GalPhi.galPhi | (intros; apply GlobalTheory.GalPhi.galPhi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfBijectiveBaseChangeQuotientJacobson
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfBijectiveBaseChangeQuotientJacobson
open TensorProduct

namespace GlobalTheory.BSP

open TensorProduct in
private theorem exists_eq_one_tmul_quotient {A : Type} [CommRing A] (I : Ideal A) {M : Type}
    [AddCommGroup M] [Module A M] (z : (A ⧸ I) ⊗[A] M) : ∃ x : M, z = (1 : A ⧸ I) ⊗ₜ[A] x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul t x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨r • x, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add z z' hz hz' =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨x', rfl⟩ := hz'
    exact ⟨x + x', by rw [TensorProduct.tmul_add]⟩

open TensorProduct in
private theorem one_tmul_quotient_eq_zero_iff_mem_smul {A : Type} [CommRing A] (I : Ideal A) {M : Type}
    [AddCommGroup M] [Module A M] (y : M) :
    (1 : A ⧸ I) ⊗ₜ[A] y = 0 ↔ y ∈ I • (⊤ : Submodule A M) := by
  have h := quotTensorEquivQuotSMul_mk_tmul (M := M) I 1 y
  rw [map_one, one_smul] at h
  rw [← (quotTensorEquivQuotSMul M I).map_eq_zero_iff, h, Submodule.Quotient.mk_eq_zero]


open TensorProduct in
theorem _root_.GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient :
    ∀ (A : Type) [CommRing A] (𝔞 : Ideal A), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] (P' : Type) [AddCommGroup P'] [Module A P'] [Module.Finite A P'] [Module.Projective A P'] (w : P →ₗ[A] P'), Function.Bijective (w.baseChange (A ⧸ 𝔞)) → Function.Bijective w := by
  intro A _ 𝔞 h𝔞 P _ _ _ P' _ _ _ _ w hw
  have surj : Function.Surjective w := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top h𝔞 ?_
    intro y _
    obtain ⟨z, hz⟩ := hw.2 ((1 : A ⧸ 𝔞) ⊗ₜ[A] y)
    obtain ⟨x, rfl⟩ := exists_eq_one_tmul_quotient 𝔞 z
    rw [LinearMap.baseChange_tmul] at hz
    have hmem : w x - y ∈ 𝔞 • (⊤ : Submodule A P') := by
      rw [← one_tmul_quotient_eq_zero_iff_mem_smul, TensorProduct.tmul_sub, hz, sub_self]
    have : y = w x - (w x - y) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right hmem)
  refine ⟨?_, surj⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property w LinearMap.id surj
  set π : P →ₗ[A] P := LinearMap.id - s ∘ₗ w with hπ
  have hwπ : ∀ p, w (π p) = 0 := fun p => by
    have := LinearMap.congr_fun hs (w p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [hπ, this]
  have hπw : ∀ p, w p = 0 → π p = p := fun p hp => by simp [hπ, hp]
  have hbot : LinearMap.range π = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔞 _ ?_ ?_ h𝔞
    · rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _
    · rintro _ ⟨p, rfl⟩
      have h0 : (1 : A ⧸ 𝔞) ⊗ₜ[A] π p = 0 := by
        apply hw.1
        rw [LinearMap.baseChange_tmul, hwπ, TensorProduct.tmul_zero, map_zero]
      rw [one_tmul_quotient_eq_zero_iff_mem_smul] at h0
      rw [LinearMap.range_eq_map, ← Submodule.map_smul'', ← hπw _ (hwπ p)]
      exact Submodule.mem_map_of_mem h0
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  have : π p ∈ LinearMap.range π := ⟨p, rfl⟩
  rw [hbot, Submodule.mem_bot, hπw p hp] at this
  exact this

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfBijectiveBaseChangeQuotientJacobsonStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_of_bijective_baseChange_quotient_jacobson : ∀ (A : Type) [CommRing A] (𝔞 : Ideal A), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] (P' : Type) [AddCommGroup P'] [Module A P'] [Module.Finite A P'] [Module.Projective A P'] (w : P →ₗ[A] P'), Function.Bijective (w.baseChange (A ⧸ 𝔞)) → Function.Bijective w := by
  first | exact @GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient | exact GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient | (intros; apply GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicComplete
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKReal

theorem constantCoeff_frobS_apply (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (p : (Wq l a)⟦X⟧) :
    constantCoeff (frobS l a p) = sigma l a (constantCoeff p) := by
  simp only [frobS]
  simp only [RingHom.coe_comp, Function.comp_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
  simp

theorem eisPoly_distinguished_complete : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) ∧ IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧ := by
  intro l _ a _ Ep ⟨hmon, hdeg, hdvd, w, hw⟩
  constructor
  · have hφ := (deltaS l a).φ_eq (Ep : (Wq l a)⟦X⟧)
    have h1 := congrArg constantCoeff hφ
    rw [show (deltaS l a).φ (Ep : (Wq l a)⟦X⟧) = frobS l a Ep from rfl, constantCoeff_frobS_apply] at h1
    simp only [Polynomial.constantCoeff_coe, map_add (f := _), map_pow, map_mul, map_natCast, hw] at h1
    set c := constantCoeff ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) with hc
    obtain ⟨k, hk⟩ : ∃ k, l = k + 2 := ⟨l - 2, by have := (Fact.out : l.Prime).two_le; omega⟩
    have h2 : c = sigma l a (w : Wq l a) - (l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l := by
      have hl0 : (l : Wq l a) ≠ 0 := WittVector.p_nonzero l (Fq l a)
      apply mul_left_cancel₀ hl0
      have : ((l : Wq l a) * w) ^ l = (l : Wq l a) * ((l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l) := by
        have e : (l : Wq l a) ^ l = (l : Wq l a) ^ (k + 2) := by rw [← hk]
        rw [mul_pow, e]; ring
      rw [this] at h1
      linear_combination -h1
    rw [isUnit_iff_constantCoeff, ← hc, h2]
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [← WittVector.constantCoeff_apply]
    simp only [map_sub, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow k.succ_ne_zero, zero_mul, sub_zero]
    rw [WittVector.constantCoeff_apply, coeff_sigma, ← WittVector.constantCoeff_apply]
    exact pow_ne_zero _ ((w.isUnit.map (WittVector.constantCoeff (p := l) (R := Fq l a))).ne_zero)
  · set e := Ep.natDegree with he
    haveI : NeZero e := ⟨hdeg.ne'⟩
    have hP : Polynomial.C (l : Wq l a) ∣ Ep - Polynomial.X ^ e := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases lt_trichotomy i e with h | rfl | h
      · rw [if_neg h.ne, sub_zero]; exact hdvd i h
      · have h1 : Ep.coeff e = 1 := hmon.coeff_natDegree
        rw [if_pos rfl, h1, sub_self]; exact dvd_zero _
      · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_zero]; exact dvd_zero _
    obtain ⟨q, hq⟩ := hP
    have hS : (Ep : (Wq l a)⟦X⟧) = X ^ e + (l : (Wq l a)⟦X⟧) * (q : (Wq l a)⟦X⟧) := by
      have := congrArg (fun p : Polynomial (Wq l a) => (p : (Wq l a)⟦X⟧)) hq
      simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
        map_natCast] at this
      have hc : ((l : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = l := map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l a)) l
      rw [hc] at this
      linear_combination this
    have hJ : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)} =
        Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {eis l a e} := by
      apply le_antisymm
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem, hS,
          show (X : (Wq l a)⟦X⟧) ^ e + (l : (Wq l a)⟦X⟧) * q = eis l a e + (l : (Wq l a)⟦X⟧) * (q - 1) by
            rw [eis]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem,
          show eis l a e = (Ep : (Wq l a)⟦X⟧) + (l : (Wq l a)⟦X⟧) * (1 - q) by rw [eis, hS]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    rw [hJ]
    exact complete_eis l a e

end GlobalTheory.BKReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicCompleteStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_distinguished_powerSeries_adicComplete : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) ∧ IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧ := by
  first | exact @GlobalTheory.BKReal.eisPoly_distinguished_complete | exact GlobalTheory.BKReal.eisPoly_distinguished_complete | (intros; apply GlobalTheory.BKReal.eisPoly_distinguished_complete <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableSpanningFinsetMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableSpanningFinsetMatrices
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory

theorem exists_stable_spanning_finset : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (Om l)) (L : FinExt l), Continuous ρ → (∀ g i j, (ρ g).val i j ∈ L.1) → ∃ t : Finset (Matrix (Fin a) (Fin a) (Om l)), (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧ (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧ (∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c y) • y = 1) ∧ ∀ g, ∀ x ∈ t, ∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], (ρ g).val * x = ∑ y ∈ t, zOm l (c y) • y := by
  intro l _ Γ _ _ _ _ a ρ L hρ hL
  classical
  obtain ⟨t₀, ht₀⟩ := zl_span_image_finite l Γ a ρ hρ
  let e : Matrix (Fin a) (Fin a) L.1 →ₗ[ℚ_[l]] Matrix (Fin a) (Fin a) (Om l) :=
    LinearMap.mapMatrix L.1.val.toLinearMap
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let bM := Module.finBasis ℚ_[l] (Matrix (Fin a) (Fin a) L.1)
  let B : Finset (Matrix (Fin a) (Fin a) (Om l)) := insert 1 (Finset.univ.image (fun k => e (bM k)))
  let t₁ : Finset Γ := insert 1 t₀
  let t : Finset (Matrix (Fin a) (Fin a) (Om l)) := (t₁ ×ˢ B).image (fun p => (ρ p.1).val * p.2)
  have hBL : ∀ b ∈ B, ∀ i j, b i j ∈ L.1 := by
    intro b hb i j
    rcases Finset.mem_insert.mp hb with rfl | hb
    · by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hb
      exact (bM k i j).2
  have hmemt : ∀ h ∈ t₁, ∀ b ∈ B, (ρ h).val * b ∈ t := fun h hh b hb =>
    Finset.mem_image.mpr ⟨(h, b), Finset.mem_product.mpr ⟨hh, hb⟩, rfl⟩
  have hBt : ∀ b ∈ B, b ∈ t := fun b hb => by
    have := hmemt 1 (Finset.mem_insert_self _ _) b hb
    simpa using this
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · intro x hx i j
    obtain ⟨⟨h, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    have hb := (Finset.mem_product.mp hp).2
    simp only [Matrix.mul_apply]
    exact L.1.sum_mem fun k _ => L.1.mul_mem (hL h i k) (hBL b hb k j)
  · intro x hx
    have hxe : x = e (fun i j => ⟨x i j, hx i j⟩) := by ext i j; rfl
    have hsp : (fun i j => (⟨x i j, hx i j⟩ : L.1)) ∈ Submodule.span ℚ_[l] (Set.range bM) := by
      rw [bM.span_eq]; trivial
    have h2 : e (fun i j => ⟨x i j, hx i j⟩) ∈ Submodule.span ℚ_[l] (e '' Set.range bM) := by
      rw [Submodule.span_image]; exact Submodule.mem_map_of_mem hsp
    rw [hxe]
    refine Submodule.span_mono ?_ h2
    rintro y ⟨z, ⟨k, rfl⟩, rfl⟩
    exact hBt _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  · refine ⟨fun y => if y = 1 then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (1 : Matrix (Fin a) (Fin a) (Om l))]
    · simp
    · intro y _ hy; simp [hy]
    · intro h1; exact absurd (hBt 1 (Finset.mem_insert_self _ _)) h1
  · intro g x hx
    obtain ⟨⟨h, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    have hb := (Finset.mem_product.mp hp).2
    obtain ⟨f', hf'sup, hf'⟩ := ht₀ (Finsupp.single (g * h) 1)
    have hgh : ((ρ (g * h) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
        f'.sum fun k c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
          ((ρ k : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
      rw [← hf', Finsupp.sum_single_index (by simp)]
      simp
    refine ⟨fun y => ∑ k ∈ f'.support with (ρ k).val * b = y, f' k, ?_⟩
    have hmaps : ∀ k ∈ f'.support, (ρ k).val * b ∈ t := fun k hk =>
      hmemt k (Finset.mem_insert_of_mem (hf'sup hk)) b hb
    calc (ρ g).val * ((ρ h).val * b) = (ρ (g * h)).val * b := by rw [map_mul, Units.val_mul, Matrix.mul_assoc]
      _ = ∑ k ∈ f'.support, zOm l (f' k) • ((ρ k).val * b) := by
          rw [hgh, Finsupp.sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.smul_mul]; rfl
      _ = ∑ y ∈ t, ∑ k ∈ f'.support with (ρ k).val * b = y, zOm l (f' k) • ((ρ k).val * b) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ y ∈ t, zOm l (∑ k ∈ f'.support with (ρ k).val * b = y, f' k) • y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.sum_smul]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [(Finset.mem_filter.mp hk).2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableSpanningFinsetMatricesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_spanning_finset_matrices : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (Om l)) (L : FinExt l), Continuous ρ → (∀ g i j, (ρ g).val i j ∈ L.1) → ∃ t : Finset (Matrix (Fin a) (Fin a) (Om l)), (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧ (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧ (∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c y) • y = 1) ∧ ∀ g, ∀ x ∈ t, ∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], (ρ g).val * x = ∑ y ∈ t, zOm l (c y) • y := by
  first | exact @GlobalTheory.exists_stable_spanning_finset | exact GlobalTheory.exists_stable_spanning_finset | (intros; apply GlobalTheory.exists_stable_spanning_finset; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastEqOneOfMod
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ScalarFrob

section HidaSetting

open IsLocalRing GlobalTheory.TwistDet GlobalTheory.PrimeToInertia

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem natCast_eq_one_of_mod {q : ℕ} (hq : q % X.l i = 1) : (q : ResidueField (X.O0 i)) = 1 := by
  have hl : ((X.l i : ℕ) : ResidueField (X.O0 i)) = 0 := by
    rw [← map_natCast (residue (X.O0 i)), (residue_eq_zero_iff _).2 (l_mem i)]
  rw [← Nat.mod_add_div q (X.l i), hq]
  push_cast
  rw [hl]
  simp

theorem frob_scalar_place (bkP : BKPh X) (h : GalHyp bkP i s) {P : PlE D.host} {z : GE N} {L : Subgroup (GE N)}
    (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : Small i s L z) (hA : ∀ v, Over P v → v ∉ X.S0 i ∧ normV v % X.l i = 1)
    (hS : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L)
    {v : PlE D.host} (hv : Over P v) {σ : GE N}
    (hσ : IsFrob (N.plOm.1 v) (normV v) σ) : ∃ c : ResidueField (X.O0 i), c ≠ 0 ∧ c ≠ 1 ∧ resT i s σ = c • 1 := by
  obtain ⟨e, he, -, hu, -⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have key : ∀ τ : GE N, IsFrob (N.plOm.1 P) (normV P) τ → resT i s τ = residue (X.O0 i) e • 1 := by
    intro τ hτ
    obtain ⟨g, hg⟩ := hS τ hτ
    have e1 : resT i s (g * τ * g⁻¹ * z⁻¹ * z) = residue (X.O0 i) e • 1 := by
      rw [map_mul, resT_apply, (hL.2.2.2.2 _ hg).1, one_mul, resT_apply, he]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have e2 := conj_scalar _ e1 g⁻¹
    rwa [show g⁻¹ * (g * τ * g⁻¹ * z⁻¹ * z) * g⁻¹⁻¹ = τ by group] at e2
  have hp := hA v hv
  have hp0 := hA _ (over_refl P)
  rcases hv with rfl | hv
  · exact ⟨_, c0, c1, key σ hσ⟩
  · have ε := eps_frob i hp.1 (natCast_eq_one_of_mod i hp.2) hσ
    obtain ⟨τ, g, hτ, rfl⟩ := exists_frob_of_conj X hv hσ
    have ε0 := eps_frob i hp0.1 (natCast_eq_one_of_mod i hp0.2) hτ
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at ε
    refine ⟨_, inv_ne_zero c0, inv_ne_one.2 c1, conj_scalar _ (scalar_of_dual i s ε c0 ?_) g⟩
    obtain ⟨A, hA⟩ := h.2.2.1
    have e3 : ((((eps0 X i τ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s τ).map (residue (X.O0 i)) =
        residue (X.O0 i) e • 1 := by
      rw [← key τ hτ, resT_apply]
      ext a b
      simp [ε0]
    rw [hA τ _ (cConj_apply X τ), Matrix.map_mul, Matrix.map_mul, e3, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

end HidaSetting


open GlobalTheory.PrimeToInertia in
theorem firstPlace : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstPlace i s := by
  intro h1 h2 h3 D N X bkP i s h P z L hz hL hA hS Λ _ _ _ _ κ hκ hκl B _ _ _ _ hB ρ hρ v hv
  have hp := hA v hv
  have hq := natCast_eq_one_of_mod i hp.2
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
  obtain ⟨c, c0, c1, hc⟩ := frob_scalar_place i s bkP h hz hL hA hS hv hσ
  obtain ⟨c', c1', hc'⟩ : ∃ c' : IsLocalRing.ResidueField (X.O0 i), c' ≠ 1 ∧
      ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) = c' • 1 := by
    rcases hρ with rfl | hρ
    · exact ⟨c, c1, by rw [Tgl_coe, ← resT_apply, hc]⟩
    · exact ⟨c⁻¹, inv_ne_one.2 c1, by rw [hρ, dual_of_scalar i s (eps_frob i hp.1 hq hσ) c0 hc]⟩
  have hcont : Continuous fun g => ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
    rcases hρ with rfl | hρ
    · simp_rw [Tgl_coe]; exact continuous_Tmat i s
    · simp_rw [show ∀ g, _ = _ from hρ]; exact continuous_Tdual i s
  refine primary_case (l := X.l i) h1 h2 h3 (N.plOm.2 v) (fun h => hp.1 (X.twistExcludedPlaces_contains_residueChar i h)) _
    ?_ (fun m => ?_) ⟨σ, hσ.1⟩ hσ (fun m hm => ?_) (fun m hm => ?_)
  · exact (contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ hcont κ hκ hB).comp
      (f := fun p : DecV N v × (Fin D.R.r → B) => ((p.1 : GE N), p.2)) (by fun_prop)
  · obtain ⟨n, hn⟩ := exists_pow_kill hB m
    refine ⟨n, funext fun a => ?_⟩
    have := hn _ (map_mem_pow (Λ := Λ) (Ideal.pow_mem_pow (l_mem i) n)) a
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
    exact this
  · exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm)
  · exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' hq m hm

end GlobalTheory.ScalarFrob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeNotMemSqAndDeltaNotMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeNotMemSqAndDeltaNotMem
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.LSq

def cInt (l : ℕ) (n : ℕ) : ℤ := ((n : ℤ) - (n : ℤ) ^ l) / l

theorem l_mul_cInt (l : ℕ) [hl : Fact l.Prime] (n : ℕ) : (l : ℤ) * cInt l n = (n : ℤ) - (n : ℤ) ^ l := by
  unfold cInt
  apply Int.mul_ediv_cancel'
  have h : (((n : ℤ) - (n : ℤ) ^ l : ℤ) : ZMod l) = 0 := by
    push_cast; rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h

theorem δ_natCast (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (n : ℕ) :
    D.δ (n : A) = ((cInt l n : ℤ) : A) := by
  induction n with
  | zero =>
    have : cInt l 0 = 0 := by
      unfold cInt; simp [zero_pow hl.out.ne_zero]
    simp [this, Delta.δ_zero]
  | succ n ih =>
    have h := D.δ_add (n : A) 1
    rw [D.δ_one, ih] at h
    push_cast
    rw [h]
    have key : cInt l (n + 1) = cInt l n - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k := by
      have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
      apply mul_left_cancel₀ h0
      have e1 := l_mul_cInt l (n + 1)
      have e2 := l_mul_cInt l n
      have h5 : ((n : ℤ) + 1) ^ l = (n : ℤ) ^ l + 1 ^ l + (l : ℤ) *
          ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k * (1 : ℤ) ^ (l - k) := by
        rw [add_pow_prime_eq' hl.out]
        congr 2
        refine Finset.sum_congr rfl fun k _ => by ring
      simp only [one_pow, mul_one] at h5
      push_cast at e1
      rw [mul_sub, e1, e2, h5]; ring
    rw [key, Int.cast_sub, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, one_pow, mul_one, add_zero]

theorem cInt_self (l : ℕ) [hl : Fact l.Prime] : cInt l l = 1 - (l : ℤ) ^ (l - 1) := by
  have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  apply mul_left_cancel₀ h0
  rw [l_mul_cInt, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hl.out.one_le]

theorem δ_l (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) :
    D.δ (l : A) = 1 - (l : A) ^ (l - 1) := by
  rw [δ_natCast, cInt_self]; push_cast; ring

theorem δ_mem_of_mem_sq (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (m : Ideal A)
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.δ x ∈ m := by
  rw [sq] at hx
  have hl0 := hl.out.ne_zero
  suffices x ∈ m ∧ D.δ x ∈ m from this.2
  refine Submodule.mul_induction_on hx (fun a ha b hb => ⟨m.mul_mem_right b ha, ?_⟩) ?_
  · rw [D.δ_mul]
    refine m.add_mem (m.add_mem (m.mul_mem_right _ (m.pow_mem_of_mem ha _ (Nat.pos_of_ne_zero hl0)))
      (m.mul_mem_right _ (m.pow_mem_of_mem hb _ (Nat.pos_of_ne_zero hl0)))) ?_
    exact m.mul_mem_right _ (m.mul_mem_right _ hlm)
  · rintro x y ⟨hx, hδx⟩ ⟨hy, hδy⟩
    refine ⟨m.add_mem hx hy, ?_⟩
    rw [D.δ_add]
    refine m.sub_mem (m.add_mem hδx hδy) (m.sum_mem fun k hk => ?_)
    obtain ⟨hk0, hkl⟩ := Finset.mem_Ioo.1 hk
    exact m.mul_mem_left _ (m.pow_mem_of_mem hy _ (Nat.sub_pos_of_lt hkl))

theorem l_not_mem_sq : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (m : Ideal A),
    m ≠ ⊤ → (l : A) ∈ m → (l : A) ∉ m ^ 2 ∧ D.δ (l : A) ∉ m := by
  intro l hl A _ D m hm hlm
  have hδ : D.δ (l : A) ∉ m := by
    intro h
    rw [δ_l] at h
    have h2 : (l : A) ^ (l - 1) ∈ m :=
      m.pow_mem_of_mem hlm _ (Nat.sub_pos_of_lt hl.out.one_lt)
    exact hm ((Ideal.eq_top_iff_one _).2 (by simpa using m.add_mem h h2))
  exact ⟨fun h => hδ (δ_mem_of_mem_sq l D m hlm h), hδ⟩

end GlobalTheory.BSP.LSq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeNotMemSqAndDeltaNotMemStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (m : Ideal A), m ≠ ⊤ → (l : A) ∈ m → (l : A) ∉ m ^ 2 ∧ D.δ (l : A) ∉ m := by
  first | exact @GlobalTheory.BSP.LSq.l_not_mem_sq | exact GlobalTheory.BSP.LSq.l_not_mem_sq | (intros; apply GlobalTheory.BSP.LSq.l_not_mem_sq <;> assumption)
end
end
