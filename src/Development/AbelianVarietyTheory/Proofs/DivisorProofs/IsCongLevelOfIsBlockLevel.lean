module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsMixMaximalMinorFockVectorsUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfThetaModelCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVolumeOneMeasureDefiniteOpenCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVolumeOneMeasureDefiniteOpenCompact
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteLevelMeasure

theorem exists_isMeasDef_openCompact : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsDefiniteSpace V → IsOpenCompactLevel V K →
  ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Links.IsMeasDef V K μ 𝓕 := by
  intro D V K hV hK
  have hd : ∀ ρ : D.what₂.Tau, (V.sig (tauE D ρ)).1 = 0 ∨ (V.sig (tauE D ρ)).2 = 0 := by
    intro ρ
    rcases hV.2 (tauE D ρ) with h | h <;> rw [h] <;> simp
  choose ν hν hg using fun ρ => GlobalTheory.Mem.DefiniteMeasure.exists_probHaar _ _ (hd ρ)
  obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV.1 K hK.1 hK.2
    (fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m) ν hν (fun ρ => (hg ρ _).2 rfl)
    (fun ρ m h => (hg ρ m).1 h)
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.DefiniteLevelMeasure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVolumeOneMeasureDefiniteOpenCompactStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_volumeOne_measure_definite_openCompact : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsDefiniteSpace V → IsOpenCompactLevel V K →
  ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Links.IsMeasDef V K μ 𝓕 := by
  first | exact @GlobalTheory.DefiniteLevelMeasure.exists_isMeasDef_openCompact | exact GlobalTheory.DefiniteLevelMeasure.exists_isMeasDef_openCompact | (intros; apply GlobalTheory.DefiniteLevelMeasure.exists_isMeasDef_openCompact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelOfStandardCongruenceLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelOfStandardCongruenceLevel
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CongLevelStd

theorem mem_RInt_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : Formalism.L2.DIV.AfE F E) :
    y ∈ Formalism.L2.DIV.RInt F E ↔
      GlobalTheory.LFun.finAdEquiv F E (Algebra.TensorProduct.comm F E (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) y) ∈
        Formalism.UG.intAd E := by
  have hι : ∀ (x : E) (a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      ((GlobalTheory.LFun.finAdEquiv F E).toRingHom.comp
          (Algebra.TensorProduct.comm F E (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)).toRingHom) (x ⊗ₜ[F] a) =
        algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := by
    intro x a
    show GlobalTheory.LFun.toFinAd F E (a ⊗ₜ[F] x) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
  exact ⟨GlobalTheory.AdeleBaseChange.map_mem_int hι, GlobalTheory.AdeleBaseChange.mem_int_of_map hι⟩

variable {D : D7}

theorem swap_mem_iff (e : TensorProduct D.host.F (Af D.host.F) D.host.E) (c : Formalism.MainNotions.StandardLatticesGL3.AE D)
    (h : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E e = GlobalTheory.BotFormula.toFinE D c) :
    Lev.swapAE D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ c ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  rw [show Formalism.L2.Herm.intAf D.host.F D.host.E = Formalism.L2.DIV.RInt D.host.F D.host.E from rfl,
    mem_RInt_iff, show Formalism.MainNotions.StandardLatticesGL3.OhE D = Formalism.L2.DIV.RInt ℚ D.host.E from rfl, mem_RInt_iff]
  have e1 : ∀ e' : TensorProduct D.host.F (Af D.host.F) D.host.E,
      Algebra.TensorProduct.comm D.host.F D.host.E (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)
        (Lev.swapAE D e') = e' := by
    intro e'
    induction e' using TensorProduct.induction_on with
    | zero => rfl
    | tmul a x => rfl
    | add a b ha hb => rw [RingHom.map_add (f := _), map_add (Algebra.TensorProduct.comm D.host.F D.host.E (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)), ha, hb]
  rw [e1, h]
  rfl

theorem cong_transfer (e : TensorProduct D.host.F (Af D.host.F) D.host.E) (c : Formalism.MainNotions.StandardLatticesGL3.AE D)
    (h : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E e = GlobalTheory.BotFormula.toFinE D c) (b N : ℕ) (z : Lev.EAf D)
    (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc : Lev.swapAE D e - (b : Lev.EAf D) = N • z) :
    ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, c - (b : Formalism.MainNotions.StandardLatticesGL3.AE D) = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
  set w := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm z with hw_def
  have hw : Lev.swapAE D w = z := by
    show (Algebra.TensorProduct.comm _ _ _) ((Algebra.TensorProduct.comm _ _ _).symm z) = z
    exact AlgEquiv.apply_symm_apply _ _
  set s := (GlobalTheory.BotFormula.toFinE D).symm (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E w) with hs_def
  have hs : s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D :=
    (swap_mem_iff w s (by rw [hs_def, RingEquiv.apply_symm_apply])).1 (hw ▸ hz)
  refine ⟨s, hs, (GlobalTheory.BotFormula.toFinE D).injective ?_⟩
  have hinj : Function.Injective (Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
  have e2 : e - (b : TensorProduct D.host.F (Af D.host.F) D.host.E) = (N : TensorProduct D.host.F (Af D.host.F) D.host.E) * w := by
    apply hinj
    rw [RingHom.map_sub, map_natCast (Lev.swapAE D) b, hc, RingHom.map_mul, map_natCast (Lev.swapAE D) N, hw,
      nsmul_eq_mul]
  rw [RingEquiv.map_sub, map_natCast (GlobalTheory.BotFormula.toFinE D) b, RingEquiv.map_mul,
    map_natCast (GlobalTheory.BotFormula.toFinE D) N, hs_def, RingEquiv.apply_symm_apply, ← h,
    ← map_natCast (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E) b, ← RingEquiv.map_sub, e2, RingEquiv.map_mul,
    map_natCast (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E) N]

theorem ker_finE (V : HSp D) {k : GA D V} (hk : Lev.finE V k = 1) : k ∈ GinfC V := by
  show finHom V k = 1
  have hinj : Function.Injective (Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
  have h1 : Formalism.UG.bc (Lev.swapAE D) (finHom V k) = 1 := hk
  apply Units.ext
  have h2 := congrArg Units.val h1
  change Matrix.map (finHom V k).val (Lev.swapAE D) = 1 at h2
  refine Matrix.map_injective hinj ?_
  beta_reduce
  rw [h2, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mulVec_mem_iff {R : Type} [CommRing R] {S : Subring R} {r : ℕ} (M : GL (Fin r) R)
    (h1 : ∀ i j, (M : Matrix (Fin r) (Fin r) R) i j ∈ S)
    (h2 : ∀ i j, ((M⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) i j ∈ S) (v : Fin r → R) :
    (∀ i, v i ∈ S) ↔ ∀ i, (Matrix.mulVec (M : Matrix (Fin r) (Fin r) R) v) i ∈ S := by
  have key : ∀ A : Matrix (Fin r) (Fin r) R, (∀ i j, A i j ∈ S) → ∀ w : Fin r → R, (∀ i, w i ∈ S) →
      ∀ i, Matrix.mulVec A w i ∈ S := by
    intro A hA w hw i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hw j)
  refine ⟨key _ h1 v, fun hv => ?_⟩
  have e : v = Matrix.mulVec ((M⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) (Matrix.mulVec (M : Matrix (Fin r) (Fin r) R) v) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [e]
  exact key _ h2 _ hv

theorem entry_mem {D : D7} {r : ℕ} (g : GL (Fin r) (Lev.EAf D)) (w : Matrix (Fin r) (Fin r) (Lev.EAf D)) (m : ℕ)
    (hw : ∀ i j, w i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (e : g.val - 1 = m • w) (i j : Fin r) :
    g.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have e3 : g.val i j - (1 : Matrix (Fin r) (Fin r) (Lev.EAf D)) i j = m • w i j := by
    have := congrFun (congrFun e i) j
    simpa only [Matrix.sub_apply, Matrix.smul_apply] using this
  rw [eq_add_of_sub_eq e3]
  refine add_mem (nsmul_mem (hw i j) m) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem entry_cong {D : D7} {r : ℕ} (g : GL (Fin r) (Lev.EAf D)) (w : Matrix (Fin r) (Fin r) (Lev.EAf D)) (m : ℕ)
    (e : g.val - 1 = m • w) (i j : Fin r) :
    g.val i j - (((if i = j then 1 else 0 : ℕ)) : Lev.EAf D) = m • w i j := by
  have := congrFun (congrFun e i) j
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] at this
  rw [← this]
  split_ifs <;> simp


set_option maxHeartbeats 4000000 in
theorem exists_level : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n)), V.gram = 1 →
  (∀ x, IsFinPt V (ι x) x) → Function.Injective ι → ι.range = GfC V → J ≤ intG D n → IsCongLevel J →
  ∃ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsOpenCompactLevel V K ∧ ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J := by
  intro D V n ι J _hg hfin hinj hrange hJ hcongJ
  obtain ⟨m, hm, hcong⟩ := hcongJ
  obtain ⟨-, e0, -⟩ := hfin 1
  subst e0
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hent : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (i j : Fin V.rank), GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((finHom V (ι x)).1 i j) =
      GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) := by
    intro x i j
    obtain ⟨-, e, h⟩ := hfin x
    simpa using h i j
  have hint : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (i j : Fin V.rank), (Lev.finE V (ι x)).val i j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      ((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D :=
    fun x i j => swap_mem_iff _ _ (hent x i j)
  have hGf : ∀ x, ι x ∈ GfC V := fun x => hrange ▸ ⟨x, rfl⟩

  have hfinj : ∀ x y, Lev.finE V (ι x) = Lev.finE V (ι y) → x = y := by
    intro x y h
    have h1 : Lev.finE V ((ι y)⁻¹ * ι x) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := (GlobalTheory.UnitarySplit.real_finite_split D V).2.2.1 _ (ker_finE V h1)
      (mul_mem (inv_mem (hGf y)) (hGf x))
    exact hinj (inv_mul_eq_one.1 h2).symm
  have hstd : Submodule.IsFullLattice D.host.E (Formalism.L2.Col.stdLat D.host.E V.rank) := by
    letI := Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := V.rank)
    constructor
    apply eq_top_iff.mpr
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin V.rank → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (by simpa using Formalism.L2.Col.single_mem_stdLat (E := D.host.E) i 1))
  obtain ⟨hK₀o, hK₀c⟩ := GlobalTheory.FunObj.congLev_open_compact V (Λ := Formalism.L2.Col.stdLat D.host.E V.rank)
    hstd (𝔪 := ⊤) top_ne_bot
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = GlobalTheory.ChiGrid.congLev D.sp.cm V.gram (Formalism.L2.Col.stdLat D.host.E V.rank) ⊤ := ⟨_, rfl⟩
  rw [← hK₀] at hK₀o hK₀c
  obtain ⟨f, hf⟩ : ∃ f : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* GL (Fin V.rank) (Lev.EAf D), f = (Lev.finE V).comp ι := ⟨_, rfl⟩
  have hfx : ∀ x, f x = Lev.finE V (ι x) := fun x => by rw [hf]; rfl

  have hmax : ∀ x ∈ intG D V.rank, f x ∈ K₀ := by
    intro x hx
    have hle : intG D V.rank ≤ K₀.comap f := by
      rw [GlobalTheory.NormSum.intG, Subgroup.closure_le]
      intro k hk
      have h1 : ∀ i j, (f k).val i j ∈
          Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j => by rw [hfx]; exact (hint k i j).2 (hk i j).1
      have h2 : ∀ i j, ((f k)⁻¹).val i j ∈
          Formalism.L2.Herm.intAf D.host.F D.host.E := by
        intro i j
        rw [← map_inv, hfx]
        exact (hint k⁻¹ i j).2 (by simpa using (hk i j).2)
      show f k ∈ K₀
      rw [hK₀, GlobalTheory.ChiGrid.congLev_top, Subgroup.mem_inf]
      refine ⟨hfx k ▸ GlobalTheory.LevSplit.finE_mem_UA V (ι k), fun v => ?_⟩
      change v ∈ Formalism.UG.latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E)
          (Formalism.L2.Col.stdLat D.host.E V.rank) ↔
        Matrix.mulVec (f k).val v ∈
          Formalism.UG.latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E V.rank)
      rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std]
      exact mulVec_mem_iff (f k) h1 h2 v
    exact hle hx

  have hopen : IsOpen (((K₀ ⊓ J.map f).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [Subgroup.comap_inf, Subgroup.coe_inf]
    refine hK₀o.inter (Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_)
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
    have hc : Continuous (finHom V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
    have hmN : m ≠ 0 := hm.ne'
    have hev1 : ∀ᶠ κ in nhds (1 : GA D V), ∃ z : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D),
        (∀ i j, z i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ (Lev.finE V κ).val - 1 = m • z := by
      have h := GlobalTheory.FunObj.eventually_cong_mat (F := D.host.F) (E := D.host.E) (n := V.rank) (X := GA D V) (x₀ := 1)
        (1 : GL (Fin V.rank) (Lev.EAf D)) hmN hc (finHom V).map_one
      refine h.mono fun κ hκ => ?_
      obtain ⟨z, hz, hz'⟩ := hκ
      refine ⟨z, hz, ?_⟩
      rw [inv_one, one_mul, mul_one] at hz'
      exact hz'
    have hev2 : ∀ᶠ κ in nhds (1 : GA D V), ∃ z : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D),
        (∀ i j, z i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ (Lev.finE V κ⁻¹).val - 1 = m • z := by
      have hc2 : Continuous fun κ : GA D V => finHom V κ⁻¹ := hc.comp continuous_inv
      have h := GlobalTheory.FunObj.eventually_cong_mat (F := D.host.F) (E := D.host.E) (n := V.rank) (X := GA D V) (x₀ := 1)
        (1 : GL (Fin V.rank) (Lev.EAf D)) hmN hc2 (by rw [inv_one]; exact (finHom V).map_one)
      refine h.mono fun κ hκ => ?_
      obtain ⟨z, hz, hz'⟩ := hκ
      refine ⟨z, hz, ?_⟩
      rw [inv_one, one_mul, mul_one] at hz'
      exact hz'
    filter_upwards [hev1, hev2] with κ ⟨z, hz, hz'⟩ ⟨z2, hz2, hz2'⟩
    obtain ⟨a, ha, k, hk, hκ⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 κ
    obtain ⟨x, hx⟩ : k ∈ ι.range := hrange ▸ hk
    have hfa : Lev.finE V a = 1 := by
      show Formalism.UG.bc (Lev.swapAE D) (finHom V a) = 1
      rw [show finHom V a = 1 from ha, map_one]
    have e1 : Lev.finE V κ = Lev.finE V (ι x) := by rw [hκ, map_mul, hfa, one_mul, hx]
    have e2 : Lev.finE V κ⁻¹ = Lev.finE V (ι x⁻¹) :=
      (map_inv (Lev.finE V) κ).trans ((congrArg (·⁻¹) e1).trans ((map_inv (Lev.finE V) (ι x)).symm.trans
        (congrArg (Lev.finE V) (map_inv ι x).symm)))
    have hI : ∀ (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (g : GL (Fin V.rank) (Lev.EAf D)) (w : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)),
        g = Lev.finE V (ι y) → (∀ i j, w i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → g.val - 1 = m • w →
          ∀ i j, (y : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)).val i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
      intro y g w hg hw e i j
      subst hg
      exact (hint y i j).1 (entry_mem _ w m hw e i j)
    have hxJ : x ∈ J := by
      refine hcong x (Subgroup.subset_closure (fun i j => ⟨hI x _ z e1 hz hz' i j, ?_⟩)) fun i j => ?_
      · simpa using hI x⁻¹ _ z2 e2 hz2 hz2' i j
      · have hC : ∀ (g : GL (Fin V.rank) (Lev.EAf D)), g = Lev.finE V (ι x) → g.val - 1 = m • z →
            Lev.swapAE D ((finHom V (ι x)).val i j) - (((if i = j then 1 else 0 : ℕ)) : Lev.EAf D) = m • z i j := by
          intro g hg e
          subst hg
          exact entry_cong _ z m e i j
        obtain ⟨s, hs, es⟩ := cong_transfer ((finHom V (ι x)).val i j) _ (hent x i j) (if i = j then 1 else 0) m (z i j)
          (hz i j) (hC _ e1 hz')
        refine ⟨s, hs, ?_⟩
        rw [Matrix.sub_apply, Matrix.one_apply, ← es]
        split_ifs <;> simp
    have h3 : f x ∈ J.map f := Subgroup.mem_map_of_mem f hxJ
    have h4 : Lev.finE V κ = f x := e1.trans (hfx x).symm
    exact Subgroup.mem_comap.2 (Eq.subst (motive := fun g => g ∈ J.map f) h4.symm h3)
  refine ⟨K₀ ⊓ J.map f, ⟨hopen, ?_⟩, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hcl : IsClosed ((Lev.levA V (K₀ ⊓ J.map f) : Subgroup (GA D V)) : Set (GA D V)) := by
      have e : ((Lev.levA V (K₀ ⊓ J.map f) : Subgroup (GA D V)) : Set (GA D V)) =
          (GfC V : Set (GA D V)) ∩ (((K₀ ⊓ J.map f).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
      rw [e]
      exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter (Subgroup.isClosed_of_isOpen _ hopen)
    refine hK₀c.of_isClosed_subset hcl fun k hk => ?_
    obtain ⟨h1, h2⟩ := Lev.mem_levA.1 hk
    exact Lev.mem_levA.2 ⟨h1, h2.1⟩
  · obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 h).2
    rw [hfx] at hyx
    rwa [← hfinj y x hyx]
  · rw [← hfx]
    exact ⟨hmax x (hJ h), Subgroup.mem_map_of_mem f h⟩

end GlobalTheory.CongLevelStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactLevelOfStandardCongruenceLevelStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n)), V.gram = 1 →
  (∀ x, IsFinPt V (ι x) x) → Function.Injective ι → ι.range = GfC V → J ≤ intG D n → IsCongLevel J →
  ∃ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsOpenCompactLevel V K ∧ ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J := by
  first | exact @GlobalTheory.CongLevelStd.exists_level | exact GlobalTheory.CongLevelStd.exists_level | (intros; apply GlobalTheory.CongLevelStd.exists_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormScaleCurveIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormScaleCurveIdeal
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem unram (D : D7) : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) :=
  Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := (GlobalTheory.Mem.host_cmData D.R D.host).cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

theorem cc_eq_conj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [IsCMField.complexEmbedding_complexConj]
  exact (Formalism.HC.HostAx.conjE_apply _ _ _).symm

end GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio

open scoped Pointwise nonZeroDivisors

theorem map_mul_bar (D : D7) (hU : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
      (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc).map
        ((Formalism.L2.Pj.hostOf D hU).bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 D.host.E)} := by
  rw [← Formalism.MainNotions.UnusedSlot33.normK_holds D cc hc, Ideal.pointwise_smul_def]
  congr 2
  refine RingHom.ext fun x => RingOfIntegers.ext ?_
  show ((Formalism.L2.Pj.barE D x : 𝓞 D.host.E) : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
  rw [Formalism.L2.Pj.barE_eq_conj]
  exact (Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul D.host.conj x).symm

theorem absNorm_ne_zero {K : Type*} [Field K] [NumberField K] {I : Ideal (𝓞 K)} (h : I ≠ ⊥) :
    (Ideal.absNorm I : ℕ) ≠ 0 := fun h0 => h (Ideal.absNorm_eq_zero_iff.1 h0)

theorem map_ne_bot (D : D7) (hU : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ := by
  intro h0
  have h := map_mul_bar D hU cc hc
  rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h
  exact absNorm_ne_zero hc (by exact_mod_cast h)

theorem exists_mul_conj (D : D7) (cc c0 : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) (h0 : c0 ≠ ⊥) :
    ∃ r : D.host.E, r * D.host.conj r * ((Ideal.absNorm c0 : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) := by
  have hU := unram D
  set H := Formalism.L2.Pj.hostOf D hU
  set F := maximalRealSubfield D.host.E
  have hn0 : ((Ideal.absNorm c0 : ℕ) : F) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
  have hn : ((Ideal.absNorm cc : ℕ) : F) ≠ 0 := by exact_mod_cast absNorm_ne_zero hc
  set x : F := ((Ideal.absNorm cc : ℕ) : F) / ((Ideal.absNorm c0 : ℕ) : F) with hxdef
  have hx : x ≠ 0 := div_ne_zero hn hn0
  have hid : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x : D.host.E)) *
      ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0 *
        (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
        (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [map_mul_bar D hU c0 h0, map_mul_bar D hU cc hc, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    have hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
    rw [hxdef]
    push_cast
    field_simp
  have hloc := GlobalTheory.local_norm_of_ideal_norm D.host.E H x hx
    ⟨_, _, map_ne_bot D hU c0 h0, map_ne_bot D hU cc hc, hid⟩
  have hreal : ∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ (-(H.d : F)) * b ^ 2 := by
    intro σ
    have hpos : 0 ≤ σ x := by
      rw [hxdef, map_div₀, map_natCast, map_natCast]; positivity
    exact ⟨Real.sqrt (σ x), 0, by rw [Real.sq_sqrt hpos]; ring⟩
  have hd : (-(H.d : F)) ≠ 0 := by
    have : (H.d : F) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
    exact neg_ne_zero.2 this
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt F (-(H.d : F)) x hd hx hreal hloc
  refine ⟨(a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD, ?_⟩
  have ha : D.host.conj (a : D.host.E) = a := by
    rw [← cc_eq_conj]; exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 a.2
  have hb : D.host.conj (b : D.host.E) = b := by
    rw [← cc_eq_conj]; exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 b.2
  have hs : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := Formalism.MainNotions.UnusedSlot33.PolarisationData.conj_b D
  have hs2 := D.host.sqrtMinusD_sq
  have hxE : (x : D.host.E) = (a : D.host.E) ^ 2 + (D.host.d : D.host.E) * (b : D.host.E) ^ 2 := by
    have := congrArg (fun t : F => (t : D.host.E)) hab
    push_cast at this
    rw [this]
    have hHd : ((H.d : ℕ) : D.host.E) = (D.host.d : D.host.E) := rfl
    rw [hHd]; ring
  have hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
  have hxE' : (x : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) / ((Ideal.absNorm c0 : ℕ) : D.host.E) := by
    rw [hxdef]
    push_cast
    try rfl
  rw [map_add (f := _), map_mul, ha, hb, hs]
  have key : ((a : D.host.E) + b * D.host.sqrtMinusD) * (a + b * -D.host.sqrtMinusD) = x := by
    rw [hxE]; linear_combination (-(b : D.host.E) ^ 2) * hs2
  rw [key, hxE']
  field_simp

end GlobalTheory.NormRatio

theorem GlobalTheory.NormRatio.exists_scale : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → ∃ r : D.host.E, IsScale D cc r :=
  fun D cc hcc => GlobalTheory.NormRatio.exists_mul_conj D cc D.host.ccK hcc.1 D.host.ccK_ne_bot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormScaleCurveIdealStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normScale_curveIdeal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → ∃ r : D.host.E, IsScale D cc r := by
  first | exact @GlobalTheory.NormRatio.exists_scale | exact GlobalTheory.NormRatio.exists_scale | (intros; apply GlobalTheory.NormRatio.exists_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemL2OfContinuousAutomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemL2OfContinuousAutomorphic
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteSqInt

theorem memL2_of_continuous_definite : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → Links.IsMeasDef V K μ 𝓕 →
    ∀ u : GA D V → ℂ, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) → GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) μ u := by
  intro D V K μ 𝓕 hV _ hμ u hu hinv
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.2.2
  have := hμ.1.1
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D V
    (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite V hV.1 hV.2)
  have hcov' : ∀ g : GA D V, ∃ γ ∈ GQ V, γ * g ∈ C := fun g => by
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  refine (GlobalTheory.AutomorphicL2Unitary.memL2_iff_fundamental_domain hμ.2).2 ⟨hinv, (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2 ?_⟩
  simpa only [← _root_.norm_pow] using (GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ V) C hC hcov' μ
    inferInstance 𝓕 hμ.2 (fun g => u g ^ 2) (hu.pow 2) fun γ hγ g => by rw [hinv γ hγ]).norm

end GlobalTheory.DefiniteSqInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemL2OfContinuousAutomorphicStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memL2_of_continuous_automorphic : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → Links.IsMeasDef V K μ 𝓕 →
  ∀ u : GA D V → ℂ, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) → GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) μ u := by
  first | exact @GlobalTheory.DefiniteSqInt.memL2_of_continuous_definite | exact GlobalTheory.DefiniteSqInt.memL2_of_continuous_definite | (intros; apply GlobalTheory.DefiniteSqInt.memL2_of_continuous_definite <;> assumption)
end
end

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

theorem finsum_const_mul {α : Type*} (c : ℂ) (f : α → ℂ) : ∑ᶠ a, c * f a = c * ∑ᶠ a, f a := (mul_finsum f c).symm

theorem ofReal_finsum {α : Type*} (f : α → ℝ) : ((∑ᶠ a, f a : ℝ) : ℂ) = ∑ᶠ a, (f a : ℂ) := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum _ hs, finsum_eq_sum_of_support_subset (s := hs.toFinset) _ (by
      intro a ha; simpa using ha)]
    push_cast; rfl
  · have hs' : ¬ (Function.support fun a => (f a : ℂ)).Finite := by
      have : (Function.support fun a => (f a : ℂ)) = Function.support f := by ext a; simp
      rwa [this]
    rw [finsum_of_infinite_support hs, finsum_of_infinite_support hs', Complex.ofReal_zero]


open Matrix in
theorem sum_norm_sq_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    ∑ i, ‖∑ j, U i j * v j‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have key : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
      (Matrix.mem_unitaryGroup_iff').1 hU, Matrix.one_mulVec]
  apply Complex.ofReal_injective
  push_cast
  have e : ∀ w : ι → ℂ, ∑ i, ((‖w i‖ : ℂ)) ^ 2 = star w ⬝ᵥ w := fun w => by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
  have e2 := e (U *ᵥ v)
  simp only [Matrix.mulVec, dotProduct] at e2
  rw [e2, e v]
  simpa [Matrix.mulVec, dotProduct] using key

end GlobalTheory.NormExact

section
noncomputable section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Compact
open Formalism.MainNotions.StandardLattice Matrix
open scoped TensorProduct ComplexOrder MatrixOrder

private theorem negDef_of_signature_aux {n q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G 0 q) : (-G).PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Formalism.UG.Jpq 0 q = -1 := by
    ext (i | i) (j | j)
    · exact i.elim0
    · exact i.elim0
    · exact j.elim0
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
  have h2 : (star P.1 * (-G).reindex e e * P.1).PosDef := by
    have e1 : (-G).reindex e e = -(G.reindex e e) := by ext i j; simp
    have : star P.1 * (-G).reindex e e * P.1 = 1 := by
      have hP' : star P.1 * G.reindex e e * P.1 = Formalism.UG.Jpq 0 q := hP
      rw [e1, Matrix.mul_neg, Matrix.neg_mul, hP', h1, neg_neg]
    rw [this]; exact Matrix.PosDef.one
  have h3 := ((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective
  simpa using h3

private theorem exists_bound_definite_aux {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) :
    ∃ R : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → ∀ i j, ‖g i j‖ ≤ R := by
  rcases hG with hG | hG
  · exact GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
  · obtain ⟨R, hR⟩ := GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
    refine ⟨R, fun g hg => hR g ?_⟩
    rw [Matrix.mul_neg, Matrix.neg_mul, hg]

private theorem definite_gramAt_aux {D : D7} (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.what₂.Tau) :
    (gramAt D V τ).PosDef ∨ (-gramAt D V τ).PosDef := by
  have h1 := hs (tauE D τ)
  rcases hd (tauE D τ) with h | h
  · left; rw [h] at h1; exact GlobalTheory.DefiniteQuotient.posDef_of_signature h1
  · right; rw [h] at h1; exact negDef_of_signature_aux h1

private theorem exists_compact_def_aux {D : D7} (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) := by
    refine (GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_
    rw [hπ.map_ratIn]
    exact GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D) (GlobalTheory.DefiniteQuotient.gram_hermND V)
      (Formalism.L2.G.gram_totDef D.sp.cm V hs hd)
      (GlobalTheory.Mass.isCompact_stdLevel _ _ (GlobalTheory.DefiniteQuotient.gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)
  choose R hR using fun τ => exists_bound_definite_aux (definite_gramAt_aux V hs hd τ)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V).2 C' hC'
  have hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K := by
    intro k hk
    refine hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_
    · have := ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1
      rwa [hπ k] at this
    · have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
        ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
      have hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
      have e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) =
          ((mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
      have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
      simp only [Matrix.map_mul, e, hJ] at this
      exact ((hR τ _ this i j).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  haveI := hf.1
  refine ⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π),
    (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h
  refine ⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩
  simp only [e]
  group

end Compact

set_option maxHeartbeats 4000000 in
private theorem integral_definiteUnitaryQuotient_eq_classSum_aux : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → Function.Injective ι → ι.range = GfC V →
  (∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n) →
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → Links.IsMeasDef V K μ 𝓕 →
  ∀ Φ : GA D V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun V K Φ →
    Finite (Cls D n J) ∧ Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ) (GlobalTheory.AutomorphicL2Unitary.autMeasure V μ) ∧
    ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V μ =
      ∑ᶠ x : Cls D n J, ((gam D J x.out : ℂ))⁻¹ * Φ (ι x.out) := by
  intro D V n ι J K μ 𝓕 hV hinj hran hrat hK hJ hμ Φ hΦ
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.1
  haveI : μ.IsHaarMeasure := hμ.1.1
  have hF : IsFundamentalDomain (GQ V) 𝓕 μ := hμ.2
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) Φ := hΦ.left
  let Ψ : Formalism.MainNotions.StandardLatticesGL3.GA D n →* Bridge.Gf V := (finHom V).rangeRestrict.comp ι
  have hΨi : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ι x ∈ GinfC V := congrArg Subtype.val hx
    have h2 : ι x ∈ GfC V := by rw [← hran]; exact ⟨x, rfl⟩
    exact hinj ((GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V h2 h1).trans (map_one ι).symm)
  have hΨs : Function.Surjective Ψ := by
    intro g
    obtain ⟨α, hα, e⟩ := GlobalTheory.Mem.FinPartLift.exists_gfC_finHom_eq V g
    rw [← hran] at hα
    obtain ⟨x, rfl⟩ := hα
    exact ⟨x, Subtype.ext e⟩
  have hratΨ : ∀ x, x ∈ ratG D n ↔ ∃ γ : GQ V, Bridge.ratF V γ = Ψ x := by
    intro x
    rw [← hrat x]
    constructor
    · rintro ⟨γ, hγ, h⟩; exact ⟨⟨γ, hγ⟩, Subtype.ext h⟩
    · rintro ⟨γ, h⟩; exact ⟨γ, γ.2, congrArg Subtype.val h⟩
  have hJΨ : ∀ x, x ∈ J ↔ Ψ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K := fun x =>
    (hJ x).symm.trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.mem_levelFin (ι x)).symm
  have hΨdef : ∀ x, Ψ x = (finHom V).rangeRestrict (ι x) := fun _ => rfl
  clear_value Ψ
  obtain ⟨e, he⟩ : ∃ e : Formalism.MainNotions.StandardLatticesGL3.GA D n ≃* Bridge.Gf V, ∀ x, e x = Ψ x :=
    ⟨MulEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩, fun _ => rfl⟩
  have hre : ∀ y, Ψ (e.symm y) = y := fun y => (he _).symm.trans (e.apply_symm_apply y)
  obtain ⟨C, hC, hCe⟩ := exists_compact_def_aux V hV.1 hV.2
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover_of_compact (GQ V) (finHom V).rangeRestrict
    (finHom V).rangeRestrict_surjective (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) hK.1 hC hCe
  have hsurj : Function.Surjective fun a : Fin m => (DoubleCoset.mk (ratG D n) J (e.symm (c a)) : Cls D n J) := by
    intro q
    obtain ⟨a, γ, k, hk⟩ := hc (Ψ q.out)
    refine ⟨a, ?_⟩
    show DoubleCoset.mk (ratG D n) J (e.symm (c a)) = q
    conv_rhs => rw [← DoubleCoset.out_eq' q]
    rw [DoubleCoset.eq]
    refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
      (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
    apply hΨi
    simp only [map_mul, hre]
    exact hk
  haveI hfin : Finite (Cls D n J) := Finite.of_surjective _ hsurj
  haveI : Fintype (Cls D n J) := Fintype.ofFinite _
  have hreps : Bridge.IsReps (Bridge.ratF V) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) (fun q : Cls D n J => Ψ q.out) := by
    intro g
    refine (hΨs g).elim fun x hx => ?_
    rw [← hx]
    refine ⟨DoubleCoset.mk (ratG D n) J x, ?_, ?_⟩
    · obtain ⟨h, hh, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (ratG D n) J x
      obtain ⟨γ, hγ⟩ := (hratΨ h⁻¹).1 (inv_mem hh)
      refine ⟨γ, ⟨Ψ k⁻¹, (hJΨ _).1 (inv_mem hk)⟩, ?_⟩
      show Ψ x = Bridge.ratF V γ * Ψ (DoubleCoset.mk (ratG D n) J x).out * Ψ k⁻¹
      rw [hγ, hout, ← map_mul Ψ, ← map_mul Ψ]
      congr 1
      group
    · rintro q ⟨γ, k, hq⟩
      rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
      refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
        (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
      apply hΨi
      simp only [map_mul, hre]
      exact hq
  obtain ⟨-, hIO, hsum⟩ := GlobalTheory.DefiniteClassSum.classSumIntegral D V hV K hK μ 𝓕 hμ (Cls D n J)
    (fun q => Ψ q.out) hreps (fun q => ι q.out) (fun q => (hΨdef _).symm) Φ hΦ
  have hcard : ∀ x, Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.classGroupAt V K (Ψ x)) = gam D J x := by
    intro x
    unfold gam
    refine Nat.card_eq_of_bijective (fun γ => ⟨e.symm (Bridge.ratF V γ.1), (hratΨ _).2 ⟨γ.1, (hre _).symm⟩,
      (hJΨ _).2 ?_⟩) ⟨?_, ?_⟩
    · simp only [map_mul, map_inv, hre]
      exact (Bridge.mem_stab _).1 γ.2
    · intro a b hab
      have h1 := congrArg (fun s : {γ : Formalism.MainNotions.StandardLatticesGL3.GA D n // γ ∈ ratG D n ∧ x⁻¹ * γ * x ∈ J} => Ψ s.1) hab
      simp only [hre] at h1
      exact Subtype.ext (GlobalTheory.FormInner.ratF_injective V h1)
    · rintro ⟨y, hy1, hy2⟩
      refine ((hratΨ y).1 hy1).elim fun γ hγ => ?_
      refine ⟨⟨γ, (Bridge.mem_stab _).2 ?_⟩, ?_⟩
      · rw [hγ, ← map_inv Ψ, ← map_mul Ψ, ← map_mul Ψ]
        exact (hJΨ _).1 hy2
      · apply Subtype.ext
        apply hΨi
        exact (hre _).trans hγ
  refine ⟨hfin, ?_, ?_⟩
  · have h1 : MemLp (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ)) 1 (μ.restrict 𝓕) := by
      rw [hL.lift_descend]; exact memLp_one_iff_integrable.2 hIO
    exact memLp_one_iff_integrable.1 ((GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hF).2 h1)
  · show ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ = _
    rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hF]
    simp only [hL.descend_mk]
    rw [hsum, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hcard]

end
end

namespace GlobalTheory.NormExact

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}

def IsDictWt (P : Pair D cc δ t0 Q) (X : Data P) : Prop :=
  IsDict P X ∧ ∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))

theorem om_apply_mul (X : Data P) (g g' : GA D X.A) (h h' : GA D X.B) (f : WO X.A X.B → ℂ) :
    X.om (g * g', h * h') f = X.om (g, h) (X.om (g', h') f) := by
  have : ((g * g', h * h') : GA D X.A × GA D X.B) = (g, h) * (g', h') := rfl
  rw [this, map_mul]; rfl

theorem ker_rat (hX : IsDictWt P X) {γ : GA D X.A} (hγ : γ ∈ GQ X.A) {γ' : GA D X.B} (hγ' : γ' ∈ GQ X.B)
    (g : GA D X.A) (h : GA D X.B) (T : Tup D P.a P.d P.n) :
    thetaKO X.om (γ * g) (γ' * h) (X.fock T) = thetaKO X.om g h (X.fock T) := by
  unfold thetaKO
  rw [om_apply_mul]
  exact hX.1.2.weil.om_aut γ hγ γ' hγ' _ (hX.1.2.weil.om_pres _ _ (GlobalTheory.T.fock_vector_isThetaFunction_definite_pair P X hX.1 T))

theorem classFun_A (hX : IsDictWt P X) (h : GA D X.B) (T : Tup D P.a P.d P.n) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun X.A X.KA (fun g => thetaKO X.om g h (X.fock T) * (1 : GA D X.A → ℂ) g) := by
  refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun k hk g => ?_⟩
  · simp only [Pi.one_apply, mul_one]
    have := ker_rat hX hγ (one_mem (GQ X.B)) g h T
    rwa [one_mul] at this
  · simp only [Pi.one_apply, mul_one]
    unfold thetaKO
    rw [show h = h * 1 from (mul_one h).symm, om_apply_mul, GlobalTheory.T.weilRep_real_fixes_fock_maximal_minors P X hX.1 hX.2 k hk T, mul_one]
  · simp only [Pi.one_apply, mul_one]
    obtain ⟨hk1, hk2⟩ := hk
    rw [← hX.1.1.rangeA] at hk1
    obtain ⟨k', rfl⟩ := hk1
    have hk' : k' ∈ intG D P.a := (hX.1.1.levA_iff k').1 hk2
    unfold thetaKO
    rw [show h = h * 1 from (mul_one h).symm, om_apply_mul, hX.1.2.fixA k' hk' T, mul_one]

theorem lift_classSum (hX : IsDictWt P X) (h : GA D X.B) (T : Tup D P.a P.d P.n) :
    Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ X.A) (fun g => thetaKO X.om g h (X.fock T) * (1 : GA D X.A → ℂ) g))
      (GlobalTheory.AutomorphicL2Unitary.autMeasure X.A X.m) ∧
    X.lift T h = ∑ᶠ x : Cls D P.a (intG D P.a), ((gam D (intG D P.a) x.out : ℂ))⁻¹ *
      thetaKO X.om (X.ιA x.out) h (X.fock T) := by
  obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measA
  have := integral_definiteUnitaryQuotient_eq_classSum_aux X.A P.a X.ιA (intG D P.a) X.KA X.m 𝓕 hX.1.1.defA hX.1.1.injA hX.1.1.rangeA hX.1.1.ratA hX.1.1.levA
    hX.1.1.levA_iff h𝓕 _ (classFun_A hX h T)
  refine ⟨this.2.1, ?_⟩
  unfold Data.lift GlobalTheory.Core.Rk.IP.up
  rw [this.2.2]
  simp

theorem finite_cls_A (hX : IsDictWt P X) (T : Tup D P.a P.d P.n) : Finite (Cls D P.a (intG D P.a)) := by
  obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measA
  exact (integral_definiteUnitaryQuotient_eq_classSum_aux X.A P.a X.ιA (intG D P.a) X.KA X.m 𝓕 hX.1.1.defA hX.1.1.injA hX.1.1.rangeA hX.1.1.ratA hX.1.1.levA
    hX.1.1.levA_iff h𝓕 _ (classFun_A hX 1 T)).1

theorem continuous_lift (hX : IsDictWt P X) (T : Tup D P.a P.d P.n) : Continuous (X.lift T) := by
  haveI := finite_cls_A hX T
  haveI := Fintype.ofFinite (Cls D P.a (intG D P.a))
  have e : X.lift T = fun h => ∑ x : Cls D P.a (intG D P.a), ((gam D (intG D P.a) x.out : ℂ))⁻¹ *
      thetaKO X.om (X.ιA x.out) h (X.fock T) := by
    funext h
    rw [(lift_classSum hX h T).2, finsum_eq_sum_of_fintype]
  rw [e]
  refine continuous_finsetSum _ fun x _ => continuous_const.mul ?_
  exact (hX.1.2.weil.om_cont _ (GlobalTheory.T.fock_vector_isThetaFunction_definite_pair P X hX.1 T) 0).comp (Continuous.prodMk continuous_const continuous_id)

theorem lift_eq (hX : IsDictWt P X) (h : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (T : Tup D P.a P.d P.n) :
    X.lift T (X.ιB h) = X.c₁ * P.coord h T := by
  rw [(lift_classSum hX (X.ιB h) T).2, Pair.coord]
  simp_rw [hX.1.2.ker, ← finsum_const_mul X.c₁]
  congr 1; funext x; ring

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}

theorem lift_mul_apply (X : Data P) (T : Tup D P.a P.d P.n) (h k : GA D X.B) :
    X.lift T (h * k) = GlobalTheory.Core.Rk.IP.up X.om X.m (X.om (1, k) (X.fock T)) 1 h := by
  unfold Data.lift GlobalTheory.Core.Rk.IP.up
  congr 1; funext q
  simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO]
  rw [show Quotient.out q = Quotient.out q * 1 from (mul_one _).symm, om_apply_mul, mul_one]

theorem norm_lift_mul_level (hX : IsDictWt P X) {k : GA D X.B} (hk : k ∈ Lev.levA X.B X.KB) (h : GA D X.B)
    (T : Tup D P.a P.d P.n) : ‖X.lift T (h * k)‖ = ‖X.lift T h‖ := by
  obtain ⟨hk1, hk2⟩ := hk
  rw [← hX.1.1.rangeB] at hk1
  obtain ⟨j, rfl⟩ := hk1
  obtain ⟨c, hc, hcT⟩ := hX.1.2.eigB j ((hX.1.1.levB_iff j).1 hk2)
  rw [lift_mul_apply, hcT T]
  have : GlobalTheory.Core.Rk.IP.up X.om X.m (c • X.fock T) 1 h = c * X.lift T h := by
    unfold Data.lift GlobalTheory.Core.Rk.IP.up
    rw [← integral_const_mul]
    congr 1; funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [this, norm_mul, hc, one_mul]

theorem sum_lift_mul_real (hX : IsDictWt P X) {k : GA D X.B} (hk : k ∈ GinfC X.B) (h : GA D X.B) :
    ∑ T, ‖X.lift T (h * k)‖ ^ 2 = ∑ T, ‖X.lift T h‖ ^ 2 := by
  obtain ⟨U, hU, hUT⟩ := GlobalTheory.T.realPoints_mix_maximalMinorFockVectors_unitary P X hX.1 k hk
  have e : ∀ T, X.lift T (h * k) = ∑ T', U T T' * X.lift T' h := by
    intro T
    rw [lift_mul_apply, hUT T]
    unfold Data.lift GlobalTheory.Core.Rk.IP.up
    have hi : ∀ T', Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ X.A)
        (fun g => thetaKO X.om g h (X.fock T') * (1 : GA D X.A → ℂ) g)) (GlobalTheory.AutomorphicL2Unitary.autMeasure X.A X.m) :=
      fun T' => (lift_classSum hX h T').1
    rw [show (∑ T', U T T' * ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ X.A)
          (fun g => thetaKO X.om g h (X.fock T') * (1 : GA D X.A → ℂ) g) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure X.A X.m) =
        ∑ T', ∫ q, U T T' * GlobalTheory.AutomorphicL2Unitary.descend (GQ X.A)
          (fun g => thetaKO X.om g h (X.fock T') * (1 : GA D X.A → ℂ) g) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure X.A X.m from
        Finset.sum_congr rfl (fun T' _ => (integral_const_mul _ _).symm)]
    rw [← integral_finsetSum _ (fun T' _ => (hi T').const_mul (U T T'))]
    congr 1; funext q
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.one_apply, mul_one]
  simp_rw [e]
  exact sum_norm_sq_unitary U hU _

theorem lift_rat (hX : IsDictWt P X) {γ : GA D X.B} (hγ : γ ∈ GQ X.B) (h : GA D X.B) (T : Tup D P.a P.d P.n) :
    X.lift T (γ * h) = X.lift T h := by
  unfold Data.lift GlobalTheory.Core.Rk.IP.up
  congr 1; funext q
  simp only [GlobalTheory.AutomorphicL2Unitary.descend]
  have := ker_rat hX (one_mem (GQ X.A)) hγ (Quotient.out q) h T
  rw [one_mul] at this
  rw [this]

theorem classFun_B (hX : IsDictWt P X) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun X.B X.KB (fun h => ((∑ T, ‖X.lift T h‖ ^ 2 : ℝ) : ℂ)) := by
  refine ⟨fun γ hγ h => ?_, fun k hk h => ?_, fun k hk h => ?_⟩
  · simp only [lift_rat hX hγ]
  · rw [sum_lift_mul_real hX hk]
  · simp only [norm_lift_mul_level hX hk]

theorem norm_mul_eq (hX : IsDictWt P X) :
    (P.norm : ℂ) * ((‖X.c₁‖ ^ 2 : ℝ) : ℂ) =
      ∑ T, GlobalTheory.Cusp.petersson X.B X.mH (X.lift T) (X.lift T) := by
  obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measB
  have hc := integral_definiteUnitaryQuotient_eq_classSum_aux X.B P.d X.ιB P.J X.KB X.mH 𝓕 hX.1.1.defB hX.1.1.injB hX.1.1.rangeB hX.1.1.ratB hX.1.1.levB
    hX.1.1.levB_iff h𝓕 _ (classFun_B hX)
  have hint : ∀ T, Integrable (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ X.B) (X.lift T) q *
      (starRingEnd ℂ) (GlobalTheory.AutomorphicL2Unitary.descend (GQ X.B) (X.lift T) q)) (GlobalTheory.AutomorphicL2Unitary.autMeasure X.B X.mH) := by
    intro T
    obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measB
    have hm := (GlobalTheory.T.memL2_of_continuous_automorphic X.B X.KB X.mH 𝓕 hX.1.1.defB hX.1.1.levB h𝓕 (X.lift T) (continuous_lift hX T)
      (fun γ hγ h => lift_rat hX hγ h T)).2
    have h2 := hm.integrable_norm_pow (p := 2) (by norm_num)
    have h3 : Integrable (fun q => ((‖GlobalTheory.AutomorphicL2Unitary.descend (GQ X.B) (X.lift T) q‖ ^ 2 : ℝ) : ℂ))
        (GlobalTheory.AutomorphicL2Unitary.autMeasure X.B X.mH) := by
      have := h2.ofReal (𝕜 := ℂ)
      simpa using this
    refine h3.congr (Filter.Eventually.of_forall fun q => ?_)
    simp [Complex.mul_conj']
  have e1 : ∑ T, GlobalTheory.Cusp.petersson X.B X.mH (X.lift T) (X.lift T) =
      ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ X.B) (fun h => ((∑ T, ‖X.lift T h‖ ^ 2 : ℝ) : ℂ)) q
        ∂GlobalTheory.AutomorphicL2Unitary.autMeasure X.B X.mH := by
    simp only [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet]
    rw [← integral_finsetSum _ (fun T _ => hint T)]
    congr 1; funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, Complex.mul_conj']
    push_cast; rfl
  have hs : ∀ y, ∑ T, ‖X.lift T (X.ιB y)‖ ^ 2 = ‖X.c₁‖ ^ 2 * P.sq y := by
    intro y
    simp only [lift_eq hX, norm_mul, mul_pow, Pair.sq, Finset.mul_sum]
  rw [e1, hc.2.2, Pair.norm, ofReal_finsum, mul_comm, ← finsum_const_mul]
  congr 1; funext x
  rw [hs]
  push_cast; ring

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P} {r : D.host.E}

theorem test_TT (P : Pair D cc δ t0 Q) : P.F ∈ TT D (tor0 D cc δ) P.a P.d :=
  GlobalTheory.NormSum.RepInv.test_mem (GlobalTheory.InducedType.induced_type D).1 P.crv P P.level_pos

theorem IsExact.reads_om (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) (x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D P.d)
    {G : VC D P.a P.d → ℂ} (hG : G ∈ TT D (tor0 D cc δ) P.a P.d) {f : WO X.A X.B → ℂ}
    (hf : Reads X.ψ X.θ X.rkA X.rkB cc δ r G f) :
    Reads X.ψ X.θ X.rkA X.rkB cc δ r (P.W.Om x y G) (X.om (X.ιA x, X.ιB y) f) := by
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup P.e0
    (GlobalTheory.NormSum.VacMove.vac_TT (GlobalTheory.InducedType.induced_type D).1 P.crv P.vac.1)
  have h1 := GlobalTheory.T.weil_datum_finite_part_moves_vacuum_as_theta_model X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup P.e0 P.W X.χA X.χB X.om h.weil hI t0 P.pt0 P.even_mul
    P.vac h.chA h.chB x y _ _ (h.std.ptA x) (h.std.ptB y) f₀ hf₀
  have h2 := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup P.e0 P.W X.χA X.χB X.om h.weil P.vac.1 x y _ _
    (h.std.ptA x) (h.std.ptB y) 1 f₀ hf₀ (by rwa [one_smul]) G hG f hf
  rwa [one_smul] at h2

theorem IsExact.om_fock (h : IsExact P X r) (x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) (T : Tup D P.a P.d P.n) :
    X.om (X.ιA x, X.ιB y) (X.fock T) =
      pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (X.om (X.ιA x, X.ιB y) X.vac)
        (MvPolynomial.rename X.var (minorPol D T)) :=
  GlobalTheory.OrientedHeis.om_fin_pureTensorO X.ψ X.A X.B X.χA X.χB X.om h.weil X.θ h.inf _ (h.std.ptA x).1 _ (h.std.ptB y).1
    _ _ _ _ _ _ h.read.1

theorem IsExact.norm_const (h : IsExact P X r) : ‖X.c₁‖ ^ 2 * normConst D cc δ P.a P.n = 1 := by
  have hA := area_pos P.crv
  have hp := Real.pi_pos
  rw [h.const, norm_prod, ← Finset.prod_pow, normConst, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [norm_pow, ← pow_mul, mul_comm _ 2, pow_mul, norm_period_sq P.crv.1.1 h.scale, ← mul_pow]
  have : area (lamOf D cc δ) / Real.pi * (Real.pi / area (lamOf D cc δ)) = 1 := by field_simp
  rw [this, one_pow]

theorem normConst_pos (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (a : ℕ) (n : D.what₂.Tau → ℕ) : 0 < normConst D cc δ a n :=
  Finset.prod_pos fun _ _ => pow_pos (div_pos Real.pi_pos (area_pos hc)) _

theorem IsExact.isDictWt (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) : IsDictWt P X := by
  have hF := test_TT P
  have hb : ∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2)) := fun τ => by
    have h1 := GlobalTheory.T.hasInfinityExponent_of_finitePartPower P.W.chV' (-P.W.ep') X.χB h.weil.hecT h.chB τ
    have h2 : ((2 * (P.n τ : ℤ) : ℤ) : ℚ) = ((P.W.ep' * P.W.chV'.n τ - (P.d : ℤ) : ℤ) : ℚ) := by rw [P.wt τ]
    push_cast at h1 h2
    convert h1 using 1
    linarith
  refine ⟨⟨h.std.frame, h.inf, h.weil, h.read.1,
    GlobalTheory.T.isFockVacuum_of_readsGaussianEntire X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup _ _ hF.1 h.read, fun h0 => ?_, fun x y T => ?_,
    fun k hk T => ?_, fun j hj => ?_, hb⟩, hb⟩
  · have := h.norm_const
    rw [h0] at this
    simp at this
  · rw [thetaKO, h.om_fock, h.const]
    exact GlobalTheory.T.fockVector_minorProduct_origin_eq_periods_jet X.ψ X.θ X.A X.B X.rkA X.rkB cc δ r h.setup _ _ (P.W.maps x y _ hF).1 (h.reads_om hI x y hF h.read) P.n T
  · have h1 := h.reads_om hI k 1 hF h.read
    rw [P.fix k hk] at h1
    have h2 := h.om_fock k 1 T
    rw [h1.unique h.read, map_one] at h2
    exact h2
  · obtain ⟨c, hc, hcF⟩ := P.eig j hj
    refine ⟨c, hc, fun T => ?_⟩
    have h1 := h.reads_om hI 1 j hF h.read
    rw [hcF] at h1
    have h2 := h.om_fock 1 j T
    rw [h1.unique (h.read.smul c), map_one, GlobalTheory.FiniteFock.pureTensorO_smul] at h2
    exact h2

theorem IsExact.upConv (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))}
    {μ₀ : Measure (GA D X.B)} (hm : IsMaxLevel X.toFrame K₀ μ₀) (T : Tup D P.a P.d P.n) :
    GlobalTheory.Core.Rk.IP.UpConv X.om X.m μ₀ (X.fock T) 1 := by
  have hX := h.isDictWt hI
  obtain ⟨𝓕, h𝓕⟩ := hm.meas
  exact ⟨fun y => (lift_classSum hX y T).1, GlobalTheory.T.memL2_of_continuous_automorphic X.B K₀ μ₀ 𝓕 hX.1.1.defB hm.lev h𝓕 (X.lift T) (continuous_lift hX T)
    fun γ hγ y => lift_rat hX hγ y T⟩

theorem IsExact.norm_eq (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))}
    {μ₀ : Measure (GA D X.B)} (hm : IsMaxLevel X.toFrame K₀ μ₀) :
    (P.norm : ℂ) = (normConst D cc δ P.a P.n : ℂ) * (P.J.relIndex (intG D P.d) : ℂ) *
      ∑ T, GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) := by
  have hX := h.isDictWt hI
  obtain ⟨𝓕, h𝓕⟩ := hX.1.1.measB
  obtain ⟨𝓕₀, h𝓕₀⟩ := hm.meas
  have e := GlobalTheory.T.levelMeasure_eq_relIndex_smul X.B P.d X.ιB P.J (intG D P.d) X.KB K₀ X.mH μ₀ hX.1.1.rangeB P.J_le P.idx_ne hX.1.1.levB hm.lev
    hX.1.1.levB_iff hm.mem_iff h𝓕.1 h𝓕₀.1
  have e2 : ∀ T, GlobalTheory.Cusp.petersson X.B X.mH (X.lift T) (X.lift T) =
      (P.J.relIndex (intG D P.d) : ℂ) * GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) := fun T => by
    simp only [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet]
    rw [e, GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul, integral_smul_measure]
    simp
  have e3 := norm_mul_eq hX
  have e4 : ((‖X.c₁‖ ^ 2 * normConst D cc δ P.a P.n : ℝ) : ℂ) = 1 := by rw [h.norm_const]; rfl
  simp only [e2, ← Finset.mul_sum] at e3
  push_cast at e3 e4
  linear_combination (normConst D cc δ P.a P.n : ℂ) * e3 - (P.norm : ℂ) * e4

theorem exists_stdFrame (P : Pair D cc δ t0 Q) (hJ : IsCongLevel P.J) :
    ∃ (Y : Frame P) (K₀ : Subgroup (GL (Fin Y.B.rank) (Lev.EAf D))) (μ₀ : Measure (GA D Y.B)),
      IsStdFrame P Y ∧ IsMaxLevel Y K₀ μ₀ := by
  obtain ⟨A, rA, gA, dA⟩ := GlobalTheory.T.exists_standardPositiveDefinite_hermitianSpace_rank D P.a
  obtain ⟨B, rB, gB, dB⟩ := GlobalTheory.T.exists_standardPositiveDefinite_hermitianSpace_rank D P.d
  obtain ⟨ιA, pA, iA, sA, qA⟩ := GlobalTheory.T.exists_finiteAdelicEmbedding_standardUnitaryGroup A P.a gA rA
  obtain ⟨ιB, pB, iB, sB, qB⟩ := GlobalTheory.T.exists_finiteAdelicEmbedding_standardUnitaryGroup B P.d gB rB
  obtain ⟨KA, lA, mA⟩ := GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel A P.a ιA _ gA pA iA sA le_rfl (isCongLevel_intG _)
  obtain ⟨KB, lB, mB⟩ := GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel B P.d ιB _ gB pB iB sB P.J_le hJ
  obtain ⟨K₀, l₀, m₀⟩ := GlobalTheory.T.exists_openCompactLevel_of_standardCongruenceLevel B P.d ιB _ gB pB iB sB le_rfl (isCongLevel_intG _)
  obtain ⟨μA, 𝓕A, hA⟩ := GlobalTheory.T.exists_volumeOne_measure_definite_openCompact A KA dA lA
  obtain ⟨μB, 𝓕B, hB⟩ := GlobalTheory.T.exists_volumeOne_measure_definite_openCompact B KB dB lB
  obtain ⟨μ₀, 𝓕₀, h₀⟩ := GlobalTheory.T.exists_volumeOne_measure_definite_openCompact B K₀ dB l₀
  exact ⟨⟨A, B, rA, rB, ιA, ιB, KA, KB, μA, μB⟩, K₀, μ₀,
    ⟨⟨gA, gB, dA, dB, iA, iB, sA, sB, qA, qB, lA, lB, mA, mB, hA.1.1, hB.1.1, ⟨_, hA⟩, ⟨_, hB⟩⟩, pA, pB⟩, l₀, m₀, ⟨_, h₀⟩⟩

theorem exists_isExact (P : Pair D cc δ t0 Q) (hJ : IsCongLevel P.J) :
    ∃ (X : Data P) (r : D.host.E) (K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))) (μ₀ : Measure (GA D X.B)),
      IsExact P X r ∧ IsMaxLevel X.toFrame K₀ μ₀ := by
  obtain ⟨Y, K₀, μ₀, hY, hm⟩ := exists_stdFrame P hJ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_normScale_curveIdeal D cc P.crv.1
  obtain ⟨χA, a1, a2, a3⟩ := GlobalTheory.T.exists_heckeCharacter_of_thetaModelCharacter P.W.chV P.W.ep P.W.ep_pm.1
  obtain ⟨χB, b1, b2, b3⟩ := GlobalTheory.T.exists_heckeCharacter_of_thetaModelCharacter P.W.chV' (-P.W.ep') (by rcases P.W.ep_pm.2 with h | h <;> simp [h])
  obtain ⟨om, hom⟩ := GlobalTheory.Unf.Inhab.exists_weil hψ Y.A Y.B a1 b1 (Y.rkA.symm ▸ a2) (Y.rkB.symm ▸ b2)
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction ψ θ Y.A Y.B Y.rkA Y.rkB cc δ r ⟨hψ, hθ, hY.frame.gramA, hY.frame.gramB, P.crv, hr⟩ P.F (test_TT P)
  exact ⟨⟨Y, ψ, θ, χA, χB, om, f, ∏ τ, period D δ r τ ^ (P.a * P.n τ)⟩, r, K₀, μ₀, ⟨hY, hθ, hom, a3, b3, hr, hf, rfl⟩, hm⟩

theorem isCongLevel_of_isBlockLevel {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a : ℕ}
    (h : GlobalTheory.FunObj.SqNum.IsBlockLevel P 𝔪 a) : IsCongLevel P.J := by
  refine ⟨Ideal.absNorm 𝔪, Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪), fun k hk hc => (h k).2 ⟨hk, fun i j hj hi => ?_⟩⟩
  obtain ⟨s, hs, e⟩ := hc i j
  have hij : i ≠ j := fun e' => by subst e'; omega
  rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at e
  refine AddSubgroup.subset_closure ⟨(Ideal.absNorm 𝔪 : 𝓞 D.host.E), Ideal.absNorm_mem _, s, hs, ?_⟩
  rw [e]
  simp

theorem exact_dictionary (P : Pair D cc δ t0 Q) (hI : GlobalTheory.NormSum.Inp D) (hJ : IsCongLevel P.J) :
    0 < normConst D cc δ P.a P.n ∧
    (∃ (X : Data P) (r : D.host.E) (K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))) (μ₀ : Measure (GA D X.B)),
      IsExact P X r ∧ IsMaxLevel X.toFrame K₀ μ₀) ∧
    ∀ (X : Data P) (r : D.host.E) (K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))) (μ₀ : Measure (GA D X.B)),
      IsExact P X r → IsMaxLevel X.toFrame K₀ μ₀ →
      IsDictWt P X ∧ (∀ T, GlobalTheory.Core.Rk.IP.UpConv X.om X.m μ₀ (X.fock T) 1) ∧
      (∀ h T, X.lift T (X.ιB h) = X.c₁ * P.coord h T) ∧ ‖X.c₁‖ ^ 2 * normConst D cc δ P.a P.n = 1 ∧
      (P.norm : ℂ) = (normConst D cc δ P.a P.n : ℂ) * (P.J.relIndex (intG D P.d) : ℂ) *
        ∑ T, GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) :=
  ⟨normConst_pos P.crv _ _, exists_isExact P hJ, fun _ _ _ _ h hm =>
    ⟨h.isDictWt hI, h.upConv hI hm, lift_eq (h.isDictWt hI), h.norm_const, h.norm_eq hI hm⟩⟩

end GlobalTheory.NormExact
