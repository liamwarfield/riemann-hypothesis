module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEquality
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.KsetSubset

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishing
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishing
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof

open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry nnPlus eeV capelliAPlus capelliExpand)

theorem eeV_eq_om {n : ℕ} (X : GMod n) : eeV X.E = om X := by
  refine LinearMap.ext fun u => funext fun b => ?_
  simp [eeV, om_apply]

theorem exists_ker {M : Type} [AddCommGroup M] [Module ℂ M] [Nontrivial M] (T : Module.End ℂ M) {k : ℕ}
    (h : T ^ k = 0) : ∃ v : M, v ≠ 0 ∧ T v = 0 := by
  obtain ⟨w, hw⟩ := exists_ne (0 : M)
  have hex : ∃ j : ℕ, (T ^ j) w = 0 := ⟨k, by simp [h]⟩
  classical
  have hj := Nat.find_spec hex
  have hmin := fun i => Nat.find_min hex (m := i)
  set j := Nat.find hex with hjdef
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0] at hj
    exact absurd (by simpa using hj) hw
  · refine ⟨(T ^ (j - 1)) w, hmin _ (by omega), ?_⟩
    rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hpos]
    exact hj

theorem eq_zero_of_nilp {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) {c : ℂ} {k : ℕ}
    (hc : c ≠ 0) (h : (T - c • (1 : Module.End ℂ M)) ^ k = 0) {v : M} (hv : T v = 0) : v = 0 := by
  have key : ∀ j : ℕ, ((T - c • (1 : Module.End ℂ M)) ^ j) v = (-c) ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Module.End.mul_apply]
      have : (T - c • (1 : Module.End ℂ M)) v = (-c) • v := by simp [hv]
      rw [this, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have := key k
  rw [h] at this
  have h2 : (-c) ^ k • v = 0 := by simpa using this.symm
  exact (smul_eq_zero.mp h2).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr hc))

theorem exists_nnPlus_ne {m : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : GlRel E) (w : ℂ) {v : M} (hv0 : v ≠ 0)
    (hinj : capelliC E (w - 1) v = 0 → v = 0) :
    ∃ y : Fin (m + 1) → ℂ, nnPlus E y w v ≠ 0 := by
  by_contra hall
  push_neg at hall
  have hmin : ∀ d c : Fin (m + 1), cminor E d.succAbove c.succAbove (w - 1) v = 0 := by
    intro d c
    have h := congrFun (hall (Pi.single c 1)) d
    simp only [nnPlus, Pi.zero_apply] at h
    rw [Finset.sum_eq_single c (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
      (fun hc => absurd (Finset.mem_univ c) hc)] at h
    simpa [pow_ne_zero] using h
  have hexp := (capelliExpand (𝒰 := Module.End ℂ M) m E (w - 1) hE).2 0 0
  have happ := LinearMap.congr_fun hexp v
  simp only [if_true, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, hmin, map_zero,
    smul_zero, Finset.sum_const_zero] at happ
  exact hv0 (hinj happ.symm)

theorem nonVan : NonVan := by
  intro n X χ s hX hnt hfree
  have hQ := GlobalTheory.CompanionTheory.RgExhHecke.qdetEq
  obtain ⟨k, hk⟩ := hX
  haveI := hnt
  cases n with
  | zero => exact s.elim0
  | succ m =>
    set w : ℂ := (((m + 1 : ℕ) : ℂ) - 1) / 2 - χ s with hw

    have h1 := hk (-χ s)
    have hcap0 : Formalism.QuantumDeterminants.capP χ (-χ s) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [hcap0, zero_smul, sub_zero] at h1
    obtain ⟨v, hv0, hv⟩ := exists_ker _ h1
    have hCw : capelliC X.E w v = 0 := by
      rw [← hQ]
      rw [show w = -χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2 by rw [hw]; ring]
      exact hv

    have h2 := hk (-χ s - 1)
    have hc : Formalism.QuantumDeterminants.capP χ (-χ s - 1) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun t _ h => hfree t ?_
      linear_combination h
    have hinj : capelliC X.E (w - 1) v = 0 → v = 0 := by
      intro h
      rw [← hQ] at h
      rw [show w - 1 = -χ s - 1 + (((m + 1 : ℕ) : ℂ) - 1) / 2 by rw [hw]; ring] at h
      exact eq_zero_of_nilp _ hc h2 h
    obtain ⟨y, hy⟩ := exists_nnPlus_ne X.E X.gl w hv0 hinj
    have hev := capelliAPlus X.V m X.E y w v X.gl hCw
    rw [eeV_eq_om] at hev
    intro hbot
    apply hy
    have hmem : nnPlus X.E y w v ∈ stepSub X (χ s) := by
      unfold stepSub
      refine Module.End.mem_maxGenEigenspace _ _ _ |>.mpr ⟨1, ?_⟩
      rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hev]
      rw [hw, ← sub_smul]
      have : -((((m + 1 : ℕ) : ℂ) - 1) / 2 - χ s) - (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2) = 0 := by ring
      rw [this, zero_smul]
    rw [hbot] at hmem
    simpa using hmem

end GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeNonVanishing : CompanionTheory.RgExh.Hk.NonVan := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | exact GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.NonVanProof.nonVan <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactFiniteAdelesAwayPBoundedDenominators
open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KModExists

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (IsKFin IsKTypeOf IsKStableOn)
open CompanionTheory.D.DSIC

theorem kHighest_iff {n : ℕ} (ε : Fin n → Bool) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : V →ₗ[ℂ] W) (hι : Function.Injective ι) (E' : Fin n → Fin n → Module.End ℂ V)
    (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b v, ι (E' a b v) = E a b (ι v)) (μ : Fin n → ℝ) (v : V) :
    KHighest ε E' μ v ↔ KHighest ε E μ (ι v) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← h, h1 a, map_smul]
    · rw [← h, h2 a b hab he, map_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => hι ?_, fun a b hab he => hι ?_⟩
    · rw [h, h1 a, map_smul]
    · rw [h, h2 a b hab he, map_zero]

theorem glRel_of_inj {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : V →ₗ[ℂ] W) (hι : Function.Injective ι) (E' : Fin n → Fin n → Module.End ℂ V)
    (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b v, ι (E' a b v) = E a b (ι v)) (hE : GlRel E) :
    GlRel E' := by
  intro a b c d
  ext v
  apply hι
  have := LinearMap.congr_fun (hE a b c d) (ι v)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, h]
  rw [this]
  split_ifs <;> simp [h]

theorem kModExists (h1 : SmMod) (h2 : KFinSm) (h3 : KFinStab) (h4 : StabLink) (h5 : HWofType) (h6 : TypeOfHW) :
    CompanionTheory.D.LK.KModExists := by
  intro n ε H _ _ _ σ hσ hirr
  obtain ⟨S, E, hS⟩ := h1 n ε H σ hσ
  obtain ⟨V₀, hV, hst⟩ := h3 n ε H σ S E hσ hS
  have hsm : ∀ v, IsKFin ε σ v → v ∈ S := fun v hv => (hS.mem v).2 (h2 n ε H σ hσ hirr v hv)
  set D : Submodule ℂ H := V₀.map S.subtype with hD
  have hmem : ∀ v, v ∈ D ↔ IsKFin ε σ v := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hV x).1 hx
    · intro hv
      exact ⟨⟨v, hsm v hv⟩, (hV _).2 hv, rfl⟩
  have hDS : D ≤ S := fun v hv => hsm v ((hmem v).1 hv)
  let ι : D →ₗ[ℂ] S := Submodule.inclusion hDS
  have hι : Function.Injective ι := Submodule.inclusion_injective hDS
  have hin : ∀ a b (v : D), (S.subtype ∘ₗ E a b ∘ₗ ι) v ∈ D := fun a b v =>
    ⟨E a b (ι v), hst a b _ ((hV _).2 ((hmem _).1 v.2)), rfl⟩
  let E' : Fin n → Fin n → Module.End ℂ D := fun a b => LinearMap.codRestrict D (S.subtype ∘ₗ E a b ∘ₗ ι) (hin a b)
  have hE' : ∀ a b v, ι (E' a b v) = E a b (ι v) := fun a b v => Subtype.ext rfl
  have hT : ∀ T : Submodule ℂ H, FiniteDimensional ℂ T → IsKStableOn ε σ T → T ≤ D :=
    fun T hf hs v hv => (hmem v).2 ⟨T, hf, hv, hs⟩
  refine ⟨D, E', hmem, fun X hX v => hS.real X hX (ι v), glRel_of_inj ι hι E' E hE' hS.gl,
    fun a b x y => hS.unit a b (ι x) (ι y), ?_, ?_, ?_⟩
  · intro x
    obtain ⟨T, hf, hx, hs⟩ := (hmem _).1 x.2
    have hTD := hT T hf hs
    have hTS : T ≤ S := hTD.trans hDS
    have f1 : FiniteDimensional ℂ (T.comap S.subtype) :=
      (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
    have f2 : FiniteDimensional ℂ (T.comap D.subtype) :=
      (Submodule.comapSubtypeEquivOfLe hTD).symm.finiteDimensional
    have hk : KStab ε E (T.comap S.subtype) := by
      rw [h4 n ε H σ S E hσ hS _ f1, Submodule.map_comap_subtype, inf_eq_right.2 hTS]
      exact hs
    exact ⟨T.comap D.subtype, f2, fun a b hab v hv => hk a b hab (ι v) hv, hx⟩
  · intro μ T hty
    have hTD := hT T hty.1 hty.2.1
    obtain ⟨v, hv0, hvT, hv⟩ := h5 n ε H σ S E hσ hS μ T hty (hTD.trans hDS)
    refine ⟨⟨v, hTD hvT⟩, fun h => hv0 (Subtype.ext (congrArg (fun z : D => (z : H)) h)), hvT, ?_⟩
    exact (kHighest_iff ε ι hι E' E hE' μ _).2 hv
  · intro μ x hx0 hx
    exact h6 n ε H σ S E hσ hS μ (ι x) (fun h => hx0 (hι (h.trans (map_zero ι).symm))) ((hmem _).1 x.2)
      ((kHighest_iff ε ι hι E' E hE' μ _).1 hx)

end GlobalTheory.CompanionTheory.KModExists
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEqualityStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.QuantumDeterminantEquality : CompanionTheory.RgExh.Hk.QdetEq := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | exact GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.qdetEq <;> assumption)
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemUJsetOfMemKset
open Matrix
open PI.UpqRep (UJset Kset IsKFin IsKStableOn)

namespace GlobalTheory.CompanionTheory.KFinStab

theorem kFinStab : CompanionTheory.D.DSIC.KFinStab :=
  _root_.UpperTheory.Reformulated.B.Gc1.kFinStab

end GlobalTheory.CompanionTheory.KFinStab
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrthCycCycStable
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.LowKType

open CompanionTheory.D.LK CompanionTheory.D.DSIC Formalism.REAL

theorem orthCyc_cyc_stable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (a b : Fin n) {x : V} (hx : x ∈ Cyc E v) :
    E a b x ∈ Cyc E v := by
  obtain ⟨t, rfl⟩ := hx
  refine ⟨FreeAlgebra.ι ℂ (a, b) * t, ?_⟩
  simp [ev]

theorem orthCyc : CompanionTheory.D.LK.OrthCyc := by
  intro n ε V _ _ E μ v u _ hU hL h1 hu hvu m hm
  obtain ⟨S, hS, hSst, hmS⟩ := hL m
  set W : Submodule ℂ V := S ⊓ Cyc E v with hW
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (inf_le_left : W ≤ S)
  have hWst : ∀ a b, ε a = ε b → ∀ x ∈ W, E a b x ∈ W := fun a b hab x hx =>
    ⟨hSst a b hab x hx.1, orthCyc_cyc_stable E v a b hx.2⟩
  have hOst : ∀ a b, ε a = ε b → ∀ x ∈ Wᗮ, E a b x ∈ Wᗮ := by
    intro a b hab x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro w hw
    rw [← hU b a hab.symm]
    exact hx _ (hWst b a hab.symm w hw)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.exists_add_mem_mem_orthogonal (K := W) u
  have key : ∀ a b, ε a = ε b → ∀ c : ℂ, E a b u = c • u → E a b p = c • p := by
    intro a b hab c hc
    have h : E a b p - c • p ∈ W ⊓ Wᗮ := by
      refine ⟨W.sub_mem (hWst a b hab p hp) (W.smul_mem c hp), ?_⟩
      have : E a b p - c • p = c • q - E a b q := by
        rw [hpq, map_add (f := _), smul_add] at hc
        rw [sub_eq_sub_iff_add_eq_add, hc, add_comm]
      rw [this]
      exact Wᗮ.sub_mem (Wᗮ.smul_mem c hq) (hOst a b hab q hq)
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  have hpH : KHighest ε E μ p := by
    refine ⟨fun a => key a a rfl _ (hu.1 a), fun a b hab hε => ?_⟩
    have := key a b hε 0 (by rw [zero_smul]; exact hu.2 a b hab hε)
    simpa using this
  obtain ⟨c, hc⟩ := h1 p hp.2 hpH
  have hq' := (Submodule.mem_orthogonal W q).1 hq
  have hpu : ⟪p, u⟫_ℂ = 0 := by rw [hc, inner_smul_left, hvu, mul_zero]
  have hp0 : p = 0 := by
    rw [hpq, inner_add_right, hq' p hp, add_zero] at hpu
    exact inner_self_eq_zero.1 hpu
  rw [hpq, hp0, zero_add]
  exact hq' m ⟨hmS, hm⟩

end GlobalTheory.CompanionTheory.LowKType
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsAdFam
open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LKInvLift

open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC (KStab)
open CompanionTheory.D.LK

variable {n : ℕ}

def AdFam {ι : Type} [Fintype ι] (w : ι → FreeAlgebra ℂ (Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ c d i j, star (M c d j i) = M d c i j) ∧
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
    ∀ c d i, E c d * ev E (w i) - ev E (w i) * E c d = ∑ j, M c d j i • ev E (w j)

theorem exists_adFam (a : FreeAlgebra ℂ (Fin n × Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → FreeAlgebra ℂ (Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ)
      (t : ι → ℂ), AdFam w M ∧ a = ∑ i, t i • w i := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ => r, ⟨?_, ?_⟩, ?_⟩
    · intro c d i j; simp
    · intro V _ _ E _ c d i; simp
    · simp [Algebra.algebraMap_eq_smul_one]
  | grade1 x =>
    refine ⟨Fin n × Fin n, inferInstance, fun p => FreeAlgebra.ι ℂ p,
      fun c d => Matrix.of fun j i => (if d = i.1 ∧ j = (c, i.2) then 1 else 0) - (if i.2 = c ∧ j = (i.1, d) then 1 else 0),
      Pi.single x 1, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_sub, Prod.mk.injEq, apply_ite star, star_one, star_zero]
      congr 1
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2.symm, h1.symm, h3.symm⟩
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h3, h2.symm, h1⟩
    · rintro V _ _ E hE c d ⟨a, b⟩
      have h := hE c d a b
      simp only [ev, FreeAlgebra.lift_ι_apply, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [h]
      congr 1
      · by_cases h1 : d = a <;> simp [h1]
      · by_cases h1 : b = c <;> simp [h1]
    · simp [Pi.single_apply]
  | mul a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι × ι', inferInstance, fun p => w p.1 * w' p.2,
      fun c d => Matrix.of fun j i => (if j.2 = i.2 then M c d j.1 i.1 else 0) + (if j.1 = i.1 then M' c d j.2 i.2 else 0),
      fun p => t p.1 * t' p.2, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_add, apply_ite star, star_zero, h1, h1', eq_comm]
    · rintro V _ _ E hE c d ⟨i, i'⟩
      have e1 := h2 V E hE c d i
      have e2 := h2' V E hE c d i'
      have : E c d * ev E (w i * w' i') - ev E (w i * w' i') * E c d =
          (E c d * ev E (w i) - ev E (w i) * E c d) * ev E (w' i') +
            ev E (w i) * (E c d * ev E (w' i') - ev E (w' i') * E c d) := by
        rw [map_mul]; noncomm_ring
      simp only []
      rw [this, e1, e2]
      simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, Fintype.sum_prod_type, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm]
      congr 1
      rw [Finset.sum_comm]
      simp
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [smul_mul_smul_comm]
  | add a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', fun c d => Matrix.fromBlocks (M c d) 0 0 (M' c d),
      Sum.elim t t', ⟨?_, ?_⟩, ?_⟩
    · rintro c d (i | i) (j | j) <;> simp [← h1 d c, ← h1' d c]
    · rintro V _ _ E hE c d (i | i)
      · simp [Fintype.sum_sum_type, h2 V E hE]
      · simp [Fintype.sum_sum_type, h2' V E hE]
    · simp [Fintype.sum_sum_type]

theorem AdFam.comm {ι : Type} [Fintype ι] {w : ι → FreeAlgebra ℂ (Fin n × Fin n)}
    {M : Fin n → Fin n → Matrix ι ι ℂ} (h : AdFam w M) {V : Type} [AddCommGroup V] [Module ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (c d : Fin n) (t : ι → ℂ) :
    E c d * ev E (∑ i, t i • w i) - ev E (∑ i, t i • w i) * E c d = ev E (∑ j, (M c d *ᵥ t) j • w j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub, h.2 V E hE, Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul,
    smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem invLift : InvLift := by
  classical
  intro n ε V _ _ E L a hE hL ha
  obtain ⟨ι, _, w, M, t, hM, rfl⟩ := exists_adFam a
  let N : Submodule ℂ (EuclideanSpace ℂ ι) :=
    { carrier := {x | ∀ s ∈ L, ev E (∑ i, x i • w i) s = 0}
      add_mem' := by
        intro x y hx hy s hs
        have := hx s hs
        have := hy s hs
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _), LinearMap.add_apply, *, add_zero]
      zero_mem' := by intro s hs; simp
      smul_mem' := by
        intro r x hx s hs
        have := hx s hs
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, LinearMap.smul_apply, this,
          smul_zero] }
  have hN : ∀ x, x ∈ N ↔ ∀ s ∈ L, ev E (∑ i, x i • w i) s = 0 := fun x => Iff.rfl
  let D : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ ι) := fun c d => Matrix.toEuclideanLin (M c d)
  have hD : ∀ c d x, (D c d x).ofLp = M c d *ᵥ x.ofLp := fun c d x => rfl
  have hadj : ∀ c d x y, ⟪x, D c d y⟫_ℂ = ⟪D d c x, y⟫_ℂ := by
    intro c d x y
    have : M d c = (M c d)ᴴ := by ext i j; simp [Matrix.conjTranspose_apply, ← hM.1 c d]
    simp only [D]
    rw [this, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hDN : ∀ c d, ε c = ε d → ∀ x ∈ N, D c d x ∈ N := by
    intro c d hcd x hx
    rw [hN] at hx ⊢
    intro s hs
    rw [hD, ← hM.comm hE]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hx s hs, hx _ (hL c d hcd s hs), map_zero, sub_zero]
  have ht : ∀ c d, ε c = ε d → D c d (WithLp.toLp 2 t) ∈ N := by
    intro c d hcd
    rw [hN]
    intro s hs
    rw [hD, ← hM.comm hE]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, ha c d hcd s hs, sub_self]
  obtain ⟨k, hk, t', ht', e⟩ := N.exists_add_mem_mem_orthogonal (WithLp.toLp 2 t)
  have h0 : ∀ c d, ε c = ε d → D c d t' = 0 := by
    intro c d hcd
    have h1 : D c d t' ∈ N := by
      have := N.sub_mem (ht c d hcd) (hDN c d hcd k hk)
      rwa [e, map_add, add_sub_cancel_left] at this
    rw [← inner_self_eq_zero (𝕜 := ℂ), hadj]
    exact (Submodule.mem_orthogonal _ _).1 ht' _ (hDN d c hcd.symm _ h1)
  refine ⟨∑ i, t' i • w i, ?_, ?_⟩
  · intro V' _ _ E' hE' c d hcd
    have := hM.comm hE' c d t'.ofLp
    rw [← hD, h0 c d hcd] at this
    have h2 : ev E' (∑ j, (0 : EuclideanSpace ℂ ι).ofLp j • w j) = 0 := by simp
    rw [h2] at this
    exact sub_eq_zero.1 this
  · intro s hs
    have e' : ∀ i, t i = k i + t' i := fun i => congrArg (fun x : EuclideanSpace ℂ ι => x i) e
    have := (hN k).1 hk s hs
    simp only [e', add_smul, Finset.sum_add_distrib, map_add (f := _), LinearMap.add_apply, this, zero_add]

end GlobalTheory.CompanionTheory.LKInvLift
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeRankOne
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeRankOne
open Finset Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli CompanionTheory.RgExh

namespace GlobalTheory.CompanionTheory.RgExhHecke

variable {n : ℕ}

theorem capEntry_tensE_apply (X : GMod n) (x : ℂ) (a b : Fin n) (f : Fin n → X.V) (d : Fin n) :
    capEntry (tensE X) x a b f d = capEntry X.E x a b (f d) + if d = a then f b else 0 := by
  unfold capEntry
  by_cases h : a = b
  · simp [h, tensE_apply, Module.algebraMap_end_apply]; abel
  · simp [h, tensE_apply]

theorem capEntry_apply_shift {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (x : ℂ) (a b : Fin n) (v : V) :
    capEntry E x a b v = capEntry E (x - 1) a b v + if b = a then v else 0 := by
  unfold capEntry
  by_cases h : a = b
  · subst h
    simp [Module.algebraMap_end_apply, sub_smul, add_assoc]
  · simp [h, Ne.symm h]

theorem sum_pair_swap {M : Type*} [AddCommMonoid M] {q : ℕ} (Φ : Fin (q + 2) → Fin (q + 1) → M) :
    ∑ i, ∑ k, Φ i k = ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), Φ (i.succAbove k) (k.predAbove i) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let τ : Equiv.Perm (Fin (q + 2) × Fin (q + 1)) :=
    Function.Involutive.toPerm (fun p => (p.1.succAbove p.2, p.2.predAbove p.1)) (by
      rintro ⟨i, k⟩
      simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove])
  exact (Equiv.sum_comp τ (fun p => Φ p.1 p.2)).symm

theorem sign_pair_swap {q : ℕ} (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (-1 : ℂ) ^ (i.succAbove k : ℕ) * (-1) ^ (k.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (k : ℕ)) := by
  have h : (i.succAbove k : ℕ) + (k.predAbove i : ℕ) + 1 = (i : ℕ) + (k : ℕ) ∨
      (i.succAbove k : ℕ) + (k.predAbove i : ℕ) = (i : ℕ) + (k : ℕ) + 1 := by
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val, Fin.val_pred,
      Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
    split_ifs <;> omega
  rw [← pow_add, ← pow_add]
  rcases h with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

theorem cminor_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (R C : Fin 0 → Fin n) (x : ℂ) : cminor E R C x = 1 := by
  simp [cminor]

section Key

variable {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {q : ℕ}
  (R C : Fin (q + 2) → Fin n) (x : ℂ) (f : Fin n → V) (d : Fin n)

def dbl (i : Fin (q + 2)) (k : Fin (q + 1)) (l : Fin (q + 1)) : V :=
  cminor E ((R ∘ i.succAbove) ∘ k.succAbove) ((C ∘ Fin.succ) ∘ l.succAbove) (x - 1 - 1) (f (C l.succ))

theorem dbl_swap (i : Fin (q + 2)) (k l : Fin (q + 1)) :
    dbl E R C x f (i.succAbove k) (k.predAbove i) l = dbl E R C x f i k l := by
  unfold dbl
  have : (R ∘ (i.succAbove k).succAbove) ∘ (k.predAbove i).succAbove = (R ∘ i.succAbove) ∘ k.succAbove := by
    funext t
    simp only [Function.comp, Fin.succAbove_succAbove_succAbove_predAbove]
  rw [this]

theorem minor_expand (i : Fin (q + 2)) (l : Fin (q + 1)) :
    cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) =
      ∑ k : Fin (q + 1), ((-1 : ℂ) ^ (k : ℕ)) •
        capEntry E (x - 1) (R (i.succAbove k)) (C 0) (dbl E R C x f i k l) := by
  rw [cminor_succ_col]
  have h0 : (C ∘ l.succ.succAbove) 0 = C 0 := by simp
  have h1 : (C ∘ l.succ.succAbove) ∘ Fin.succ = (C ∘ Fin.succ) ∘ l.succAbove := by
    funext t
    simp [Function.comp, Fin.succ_succAbove_succ]
  rw [h0, h1]
  simp [dbl, LinearMap.sum_apply, Module.End.mul_apply]

theorem key_identity :
    (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • capEntry E x (R i) (C 0)
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0)) +
      (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if C 0 = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0)) =
    ∑ i : Fin (q + 2), ∑ l : Fin (q + 1), if d = R i then
      ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
        cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0 := by
  have h1 : (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • capEntry E x (R i) (C 0)
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0)) =
      ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ∑ l : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ)) •
        capEntry E x (R i) (C 0) (if d = R (i.succAbove k) then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.smul_sum, Function.comp]
  have h2 : (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if C 0 = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0)) =
      ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ∑ l : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ)) •
        (if d = R i then (if C 0 = R (i.succAbove k) then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : d = R i <;> simp [h, Finset.smul_sum]
  have h3 : (∑ i : Fin (q + 2), ∑ l : Fin (q + 1), if d = R i then
      ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
        cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0) =
      ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = R i then
        ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) • ((-1 : ℂ) ^ (k : ℕ)) •
          capEntry E (x - 1) (R (i.succAbove k)) (C 0) (dbl E R C x f i k l) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : d = R i
    · simp only [h, if_true, minor_expand, Finset.smul_sum]
    · simp [h]
  rw [h1, h2, h3, sum_pair_swap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fin.succAbove_succAbove_predAbove, dbl_swap]
  have hs : (-1 : ℂ) ^ (i.succAbove k : ℕ) * (-1) ^ (((k.predAbove i : Fin (q + 1)) : ℕ) + (l : ℕ)) =
      -((-1) ^ (i : ℕ) * (-1) ^ ((k : ℕ) + (l : ℕ))) := by
    rw [pow_add, ← mul_assoc, sign_pair_swap, pow_add]; ring
  by_cases hd : d = R i
  · simp only [hd, if_true, map_smul, smul_smul, hs]
    rw [capEntry_apply_shift E x (R (i.succAbove k)) (C 0)]
    by_cases hc : C 0 = R (i.succAbove k)
    · simp only [hc, if_true, smul_add, Fin.val_succ, pow_add, pow_one]
      module
    · simp only [hc, if_false, add_zero, smul_zero, Fin.val_succ, pow_add, pow_one]
      module
  · simp [hd]

end Key

theorem cminor_tensE_apply (X : GMod n) (q : ℕ) : ∀ (R C : Fin (q + 1) → Fin n) (x : ℂ)
    (f : Fin n → X.V) (d : Fin n),
    cminor (tensE X) R C x f d = cminor X.E R C x (f d) +
      ∑ i : Fin (q + 1), ∑ j : Fin (q + 1), if d = R i then
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          cminor X.E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) (f (C j)) else 0 := by
  induction q with
  | zero =>
    intro R C x f d
    rw [cminor_succ_col, cminor_succ_col X.E]
    simp [cminor_zero, capEntry_tensE_apply, Module.End.mul_apply, LinearMap.sum_apply]
  | succ q ih =>
    intro R C x f d
    have hL : cminor (tensE X) R C x f d =
        ∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) •
          (capEntry X.E x (R i) (C 0) (cminor (tensE X) (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1) f d) +
            if d = R i then cminor (tensE X) (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1) f (C 0) else 0) := by
      rw [cminor_succ_col]
      simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
        Module.End.mul_apply, capEntry_tensE_apply]
    have hR := key_identity X.E R C x f d
    have hsplit : ∀ i : Fin (q + 2), (∑ j : Fin (q + 2), if d = R i then
          ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
            cminor X.E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) (f (C j)) else 0) =
        ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
          cminor X.E (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1) (f (C 0)) else 0) +
        ∑ l : Fin (q + 1), if d = R i then
          ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
            cminor X.E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0 := by
      intro i
      rw [Fin.sum_univ_succ]
      by_cases h : d = R i
      · simp [h, Fin.succAbove_zero]
      · simp [h]
    rw [hL]
    simp only [hsplit, Finset.sum_add_distrib]
    rw [← hR, cminor_succ_col X.E R C x]
    have hit : ∀ (p : Prop) [Decidable p] (a b : X.V),
        (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) := by
      intro p _ a b
      split_ifs <;> simp
    simp only [ih, hit, map_add (f := _), smul_add, Finset.sum_add_distrib, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.mul_apply]
    simp only [dbl, Function.comp_apply]
    abel

abbrev minorOp {m : ℕ} (X : GMod (m + 1)) (y : ℂ) : Module.End ℂ (Fin (m + 1) → X.V) :=
  Hk.minorOp X y

theorem minorOp_apply {m : ℕ} (X : GMod (m + 1)) (y : ℂ) (f : Fin (m + 1) → X.V) (a : Fin (m + 1)) :
    minorOp X y f a = ∑ c : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (c : ℕ))) • cminor X.E a.succAbove c.succAbove y (f c) :=
  rfl

theorem rankOneTens : ∀ (m : ℕ) (X : GMod (m + 1)) (u : ℂ),
    qdet (tensE X) u = (qdet X.E u).compLeft (Fin (m + 1)) + minorOp X (u - 1) := by
  intro m X u
  rw [qdet_eq_capelliC, qdet_eq_capelliC]
  refine LinearMap.ext fun f => funext fun d => ?_
  rw [capelliC, capelliC, cminor_tensE_apply X m id id u f d]
  simp only [LinearMap.add_apply, Pi.add_apply, minorOp_apply, LinearMap.compLeft_apply,
    Function.comp_apply, id_eq, Function.id_comp]
  simp

theorem rankOne : Hk.RankOne := rankOneTens

end GlobalTheory.CompanionTheory.RgExhHecke
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeRankOneStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeRankOne : CompanionTheory.RgExh.Hk.RankOne := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.rankOne | exact GlobalTheory.CompanionTheory.RgExhHecke.rankOne | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.rankOne <;> assumption)
end
end
