module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLatticeHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FormalGroupLawFirstHalfHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CoefWfPhAt
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhEvenOf

@[expose] public section

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem lamOf_lat_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ :=
  lamOf_lat idealLattice_holds D cc hc δ hδ

theorem delta_ne_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  delta_ne' idealLattice_holds D cc hc δ hδ

theorem sgStar_spec (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Differentiable ℂ (sgStar (lamOf D cc δ)) ∧ deriv (sgStar (lamOf D cc δ)) 0 = 1 ∧
      (∀ z, sgStar (lamOf D cc δ) (-z) = -sgStar (lamOf D cc δ) z) := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat_holds D cc hc δ (delta_ne_holds D cc hc δ hδ)
  have h := sigmaStarEx_holds w₁ w₂ hw
  rw [hL]
  unfold sgStar
  have hs := Classical.epsilon_spec h
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem area_lamOf (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt |(NumberField.discr D.host.K : ℝ)| / 2 := by
  have h := idealLattice_holds D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
    (Formalism.MainNotions.Ext.finrank_K D.host) (Formalism.MainNotions.Ext.no_real_K D.host) cc δ hc hδ
  exact h.2

end Formalism.MainNotions.Ext
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpDict
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

noncomputable def conjK : D.host.K →+* D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  (AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K →+* D.host.K)

theorem conjK_coe (x : D.host.K) : ((conjK D x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K x

noncomputable def tauKp : D.host.K →+* ℂ_[p] :=
  lam.comp ((D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring (fun _ => test_vector_mem_schwartz_bruhat D _))

theorem tauKp_apply (x : D.host.K) : tauKp D lam x = lamC lam (D.host.φ₀ (x : D.host.E)) := by
  unfold tauKp lamC
  first
  | rfl
  | (simp [test_vector_mem_schwartz_bruhat]; done)
  | (rw [dif_pos (test_vector_mem_schwartz_bruhat D _)]; rfl)

end Formalism.MainNotions.Ext
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLetters
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext

theorem embT_injective (D : D7) : Function.Injective (embT D) := by
  intro τ τ' h
  have h1 := (factEmb D.R D.host).1.1 h
  exact D.eTau.injective (Subtype.ext h1)

theorem card_Tau_eq (D : D7) : Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E := by
  have h1 := Module.finrank_mul_finrank ℚ D.host.K D.host.E
  rw [Formalism.MainNotions.Ext.finrank_K D.host, Formalism.MainNotions.StandardLattice.finrank_host D] at h1
  rw [D.what₂.card_Tau]
  omega

theorem trace_sum_over_letters (H : TraceSum) (D : D7) : StandardLatticesGL3.TraceMapNormalisation D :=
  H D.host.E D.host.K D.host.φ₀ D.what₂.Tau (embT D) (embT_injective D) (GL3Theta.induced_cm_type D) (card_Tau_eq D)

end Formalism.MainNotions.Ext
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtPhDualWHolds
section -- merged from Formalism.PeriodIntegrals.FglPtW
noncomputable section

namespace PI.FglPtW

def SerOver {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (F : MvPowerSeries σ K) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ S

def PtOver {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (a : MvPowerSeries σ K) : Prop :=
  SerOver S a ∧ MvPowerSeries.constantCoeff a = 0

def AddGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    SerOver S (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) →
    ∀ (σ : Type) (a b : MvPowerSeries σ K), PtOver S a → PtOver S b →
      PtOver S (PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex)

def MulGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    ∀ c : K, SerOver S (PowerSeries.subst
      (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) →
    ∀ (σ : Type) (a : MvPowerSeries σ K), PtOver S a →
      PtOver S (PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex)

end PI.FglPtW

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.ConstantCoeffPsubst
noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

variable {K : Type*} [CommRing K]

theorem serOver_iff (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    SerOver S f ↔ f ∈ SerS S σ := by
  constructor
  · intro h
    refine ⟨fun n => ⟨MvPowerSeries.coeff n f, h n⟩, ?_⟩
    ext n
    first
    | rfl
    | simp [MvPowerSeries.coeff_map]
  · rintro ⟨g, rfl⟩ n
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n g).2

end PI.FglPtW.Wk

end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglPtW
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.AddGenThm
noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

theorem addGen_thm : PI.FglPtW.AddGen := by
  intro K _ S l ex hex0 hinv hF σ a b ha hb
  have hcc : ∀ {τ : Type} (f : PowerSeries K) (c : MvPowerSeries τ K),
      MvPowerSeries.constantCoeff c = 0 →
      MvPowerSeries.constantCoeff (PowerSeries.subst c f) = PowerSeries.constantCoeff f := by
    intro τ f c hc
    rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hc)]
    rw [finsum_eq_single _ 0]
    · simp
    · intro d hd
      rw [map_pow, hc, zero_pow hd, smul_zero]
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := hcc l ex hex0
    rw [hinv] at h
    rw [← h]
    exact PowerSeries.constantCoeff_X
  have hP0 : ∀ s, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → MvPowerSeries σ K) s) = 0 := by
    intro s
    fin_cases s <;> simp [ha.2, hb.2]
  have hP : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ K) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  have hmix : ∀ (c : MvPowerSeries (Fin 2) K), MvPowerSeries.constantCoeff c = 0 →
      ∀ f : PowerSeries K, MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst c f) =
        PowerSeries.subst (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) c) f := by
    intro c hc f
    exact MvPowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero hc)) hP f
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have hG0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) = 0 := by
    rw [map_add (f := _), hcc l _ hX0, hcc l _ hX1, hl0, add_zero]
  have hG : MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K)
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) =
      PowerSeries.subst a l + PowerSeries.subst b l := by
    rw [MvPowerSeries.subst_add hP, hmix _ hX0, hmix _ hX1, MvPowerSeries.subst_X hP,
      MvPowerSeries.subst_X hP]
    rfl
  have heq : PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex =
      MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) := by
    rw [hmix _ hG0, hG]
  refine ⟨?_, ?_⟩
  · rw [heq, serOver_iff]
    refine mvsubst_mem_SerS S hP0 (fun i => ?_) ((serOver_iff S _).mp hF)
    fin_cases i <;> simp [(serOver_iff S a).mp ha.1, (serOver_iff S b).mp hb.1]
  · rw [hcc ex _ (by rw [map_add (f := _), hcc l a ha.2, hcc l b hb.2, hl0, add_zero])]
    exact hex0

end PI.FglPtW.Wk

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.MulGenThm
noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

theorem mulGen_thm : PI.FglPtW.MulGen := by
  intro K _ S l ex hex hl c hG σ a ha
  obtain ⟨haS, ha0⟩ := ha
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  have hsub : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero hex'

  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h1 := congrArg MvPowerSeries.constantCoeff hl
    rw [PowerSeries.constantCoeff_subst hsub,
      finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])] at h1
    simpa using h1.trans (PowerSeries.constantCoeff_X (R := K))
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit K) = 0 := by simp
  have hXs : PowerSeries.HasSubst (MvPowerSeries.X () : MvPowerSeries Unit K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hX0
  have has : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  have hA0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero hX0 l hl0, mul_zero]
  have hAs := PowerSeries.HasSubst.of_constantCoeff_zero hA0

  have hinner : PowerSeries.subst a (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) =
      MvPowerSeries.C c * PowerSeries.subst a l := by
    rw [← PowerSeries.coe_substAlgHom has, map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_comp_subst_apply hXs has]
    congr 1
    · have h2 := (PowerSeries.substAlgHom has).commutes c
      rw [PowerSeries.coe_substAlgHom] at h2
      first
        | exact h2
        | simp
        | (simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h2
           exact h2)
    · congr 1
      exact PowerSeries.subst_X has
  have key : PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex =
      PowerSeries.subst a (PowerSeries.subst (MvPowerSeries.C c *
        PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) := by
    rw [PowerSeries.subst_comp_subst_apply hAs has, hinner]
  rw [key]
  refine ⟨?_, ?_⟩
  · rw [serOver_iff]
    exact subst_mem_SerS S ha0 ((serOver_iff S a).mp haS) ((serOver_iff S _).mp hG)
  · exact PowerSeries.constantCoeff_subst_eq_zero ha0 _
      (PowerSeries.constantCoeff_subst_eq_zero hA0 ex hex)

end PI.FglPtW.Wk

end
end

theorem formal_group_add_generation : PI.FglPtW.AddGen := PI.FglPtW.Wk.addGen_thm

theorem formal_group_mul_generation : PI.FglPtW.MulGen := PI.FglPtW.Wk.mulGen_thm

end

namespace Formalism.MainNotions.Ext

theorem addPtW_holds : AddPtW :=
  fun p _ g hOk hF σ a b ha hb =>
    formal_group_add_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 hF σ a b ha hb

theorem mulPtW_holds : MulPtW :=
  fun p _ g hOk c hc σ a ha =>
    formal_group_mul_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 c hc σ a ha

end Formalism.MainNotions.Ext
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpInertOf
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

def InertPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (b : K) (d p : ℕ), b ^ 2 = -(d : K) → p.Prime →
    jacobiSym (-(d : ℤ)) p = -1 → (Ideal.span {(p : 𝓞 K)}).IsPrime

theorem okpInert_of (HO : OkpInertG) (HI : InertPrime) (D : D7) : okpInert D := by
  intro p _ lam h2 hin
  have := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  obtain ⟨b, hb, -⟩ := exists_gen_K D.host
  have hb' : b ^ 2 = -(D.host.d : D.host.K) := by rw [hb]; push_cast; rfl
  have hpr := HI D.host.K (finrank_K D.host) b D.host.d p hb' (Fact.out) hin

  let φK : D.host.K →+* Qbar :=
    (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring (fun x => test_vector_mem_schwartz_bruhat D _)
  let c : D.host.K →+* D.host.K := (AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K →+* D.host.K)
  have hc : ∀ x : D.host.K, ((c x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := fun x =>
    AlgEquiv.restrictNormal_commutes D.host.conj D.host.K x
  have hne : ∃ x, c x ≠ x := by
    refine ⟨b, fun h => ?_⟩
    have hbE : ((b : D.host.K) : D.host.E) ^ 2 = -(D.host.d : D.host.E) := by
      have := congrArg (fun z : D.host.K => (z : D.host.E)) hb'
      simpa using this
    have h1 := hc b
    rw [h] at h1

    have h3 := Formalism.BasicNotions.Examples₂.emb_conj D.host D.host.φ₀ (b : D.host.E)
    rw [← h1] at h3
    have h4 : (D.host.φ₀ (b : D.host.E)) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, hbE]; simp
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h3.symm
    rw [hr] at h4
    have h5 : ((r ^ 2 : ℝ) : ℂ) = ((-(D.host.d : ℝ) : ℝ) : ℂ) := by push_cast; exact h4
    have h6 : r ^ 2 = -(D.host.d : ℝ) := by exact_mod_cast h5
    have h7 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
    nlinarith [sq_nonneg r]
  have key := HO D.host.K c p (lam.comp φK) (finrank_K D.host) hne h2 hpr
  rw [← key]
  unfold OKp
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp only [tauK, tauKc, RingHom.comp_apply]
    rw [lamC_mem' lam (test_vector_mem_schwartz_bruhat D _), lamC_mem' lam (test_vector_mem_schwartz_bruhat D _)]
    congr 2
    exact Subtype.ext (congrArg D.host.φ₀ (hc _))
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    simp only [tauK, tauKc, RingHom.comp_apply]
    rw [lamC_mem' lam (test_vector_mem_schwartz_bruhat D _), lamC_mem' lam (test_vector_mem_schwartz_bruhat D _)]
    congr 2
    exact Subtype.ext (congrArg D.host.φ₀ (hc _)).symm

end Formalism.MainNotions.Ext
end
