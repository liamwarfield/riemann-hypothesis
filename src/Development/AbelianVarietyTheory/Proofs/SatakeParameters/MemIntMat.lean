module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinTypInvariantFormOfIsotIn
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletedLatticeBasisAtPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmEmbeddingsEqOneOfInert

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
noncomputable section

namespace GlobalTheory.Hk3.HoweDuality

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def intMat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) L) where
  carrier := {u | ∀ i j, u i j ∈ Formalism.UG.intL L}
  zero_mem' := fun _ _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i j => (Formalism.UG.intL L).add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => (Formalism.UG.intL L).neg_mem (ha i j)

def intVec (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a : ℕ) : AddSubgroup (Fin a → L) where
  carrier := {u | ∀ i, u i ∈ Formalism.UG.intL L}
  zero_mem' := fun _ => (Formalism.UG.intL L).zero_mem
  add_mem' := fun ha hb i => (Formalism.UG.intL L).add_mem (ha i) (hb i)
  neg_mem' := fun ha i => (Formalism.UG.intL L).neg_mem (ha i)

theorem mem_intMat {a b : ℕ} (u : Matrix (Fin a) (Fin b) L) : u ∈ intMat L a b ↔ ∀ i j, u i j ∈ Formalism.UG.intL L := Iff.rfl

theorem mem_intVec {a : ℕ} (u : Fin a → L) : u ∈ intVec L a ↔ ∀ i, u i ∈ Formalism.UG.intL L := Iff.rfl

def latIdx {a b : ℕ} (x : Matrix (Fin a) (Fin b) L) : ℕ :=
  Nat.card (Set.range fun u : intVec L b => (QuotientAddGroup.mk (Matrix.mulVec x (u : Fin b → L)) : (Fin a → L) ⧸ intVec L a))

end GlobalTheory.Hk3.HoweDuality

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOneOfCompact
noncomputable section

namespace GlobalTheory.XiOver

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

section Coeff

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem norm_iota_le_one (b : N.O i) : ‖iotaOQ N A i b‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.CoeffEmbedding.exists_norm_le N A i
  by_contra h
  rw [not_le] at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have := hC (b ^ n)
  rw [map_pow, norm_pow] at this
  linarith

theorem norm_iota_lt_one {c : N.O i} (hc : c ∈ IsLocalRing.maximalIdeal (N.O i)) :
    ‖iotaOQ N A i c‖ < 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.CoeffEmbedding.exists_pow_le_span N A i
  have h1 : c ^ e ∈ Ideal.span {((N.l i : ℕ) : N.O i)} := he (Ideal.pow_mem_pow hc e)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 h1
  have hl : ‖iotaOQ N A i ((N.l i : ℕ) : N.O i)‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[N.l i] (Qbar (N.l i))), norm_algebraMap']
    exact Padic.norm_p_lt_one
  by_contra h
  rw [not_lt] at h
  have h2 := one_le_pow₀ h (n := e)
  rw [← norm_pow, ← map_pow, hb, map_mul, norm_mul] at h2
  exact absurd ((mul_le_of_le_one_right (norm_nonneg _) (norm_iota_le_one N A i b)).trans_lt hl) (not_lt.2 h2)

theorem isUnit_of_norm {c : N.O i} (hc : ‖iotaOQ N A i c‖ = 1) : IsUnit c := by
  by_contra hu
  have := norm_iota_lt_one N A i (c := c) ((IsLocalRing.mem_maximalIdeal c).2 hu)
  linarith

theorem norm_iota_unit {c : N.O i} (hc : IsUnit c) : ‖iotaOQ N A i c‖ = 1 := by
  obtain ⟨u, rfl⟩ := hc
  have h1 := norm_iota_le_one N A i (u : N.O i)
  have h2 := norm_iota_le_one N A i ((u⁻¹ : (N.O i)ˣ) : N.O i)
  have h3 : ‖iotaOQ N A i (u : N.O i)‖ * ‖iotaOQ N A i ((u⁻¹ : (N.O i)ˣ) : N.O i)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  nlinarith [norm_nonneg (iotaOQ N A i (u : N.O i)), norm_nonneg (iotaOQ N A i ((u⁻¹ : (N.O i)ˣ) : N.O i))]

theorem iota_inj : Function.Injective (iotaOQ N A i) :=
  (A.iotaQ i).injective.comp (IsFractionRing.injective (N.O i) (FractionRing (N.O i)))

theorem iota_smul (z : ℤ_[N.l i]) (y : N.O i) :
    iotaOQ N A i (z • y) = algebraMap ℚ_[N.l i] (Qbar (N.l i)) (z : ℚ_[N.l i]) * iotaOQ N A i y := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  exact A.iotaQ_alg i z

theorem isClosed_range_iota : IsClosed (Set.range (iotaOQ N A i)) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[N.l i]) (M := N.O i)
  let f : (s → ℤ_[N.l i]) → Qbar (N.l i) := fun c =>
    ∑ y : s, algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c y : ℚ_[N.l i]) * iotaOQ N A i y
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun y _ => ?_
    exact ((continuous_algebraMap ℚ_[N.l i] (Qbar (N.l i))).comp
      ((continuous_subtype_val : Continuous fun x : ℤ_[N.l i] => (x : ℚ_[N.l i])).comp
        (continuous_apply y))).mul continuous_const
  have hr : Set.range (iotaOQ N A i) = Set.range f := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      have hb : b ∈ Submodule.span ℤ_[N.l i] (s : Set (N.O i)) := hs ▸ Submodule.mem_top
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hb
      refine ⟨fun y => c y, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [f, iota_smul]
      exact Finset.sum_coe_sort s (fun y => algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c y : ℚ_[N.l i]) * iotaOQ N A i y)
    · rintro ⟨c, rfl⟩
      refine ⟨∑ y : s, c y • (y : N.O i), ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [f, iota_smul]
  rw [hr]
  exact (isCompact_range hf).isClosed

theorem mem_range_of_norm {x : FractionRing (N.O i)} (hx : ‖A.iotaQ i x‖ = 1) :
    A.iotaQ i x ∈ Set.range (iotaOQ N A i) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rcases ValuationRing.isInteger_or_isInteger (N.O i) x with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨c, by rw [← hc]; rfl⟩
  · have h1 : ‖iotaOQ N A i c‖ = 1 := by
      show ‖A.iotaQ i (algebraMap _ _ c)‖ = 1
      rw [hc, map_inv₀, norm_inv, hx, inv_one]
    obtain ⟨u, rfl⟩ := isUnit_of_norm N A i h1
    refine ⟨((u⁻¹ : (N.O i)ˣ) : N.O i), ?_⟩
    show A.iotaQ i (algebraMap _ _ _) = _
    congr 1
    have h2 : algebraMap (N.O i) (FractionRing (N.O i)) (u : N.O i) * algebraMap (N.O i) (FractionRing (N.O i)) ((u⁻¹ : (N.O i)ˣ) : N.O i) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hc] at h2
    field_simp at h2
    exact h2

theorem norm_eq_one_of_compact {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k]
    (d : Γ →* k) (hd : Continuous d) (g : Γ) : ‖d g‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_norm.comp hd)).bddAbove
  have hle : ∀ g, ‖d g‖ ≤ 1 := by
    intro g
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have : ‖d (g ^ n)‖ ≤ C := hC ⟨g ^ n, rfl⟩
    rw [map_pow, norm_pow] at this
    linarith
  have h1 : ‖d g‖ * ‖d g⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one]
  have := hle g; have := hle g⁻¹; have := norm_nonneg (d g); have := norm_nonneg (d g⁻¹)
  nlinarith

theorem mem_pow_of_norm_lt (k : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ y : N.O i, ‖iotaOQ N A i y‖ < δ →
    y ∈ IsLocalRing.maximalIdeal (N.O i) ^ k := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  have hp0 : iotaOQ N A i p ≠ 0 := by
    intro h
    have : p = 0 := iota_inj N A i (by simpa using h)
    exact hp.ne_zero this
  refine ⟨‖iotaOQ N A i p‖ ^ k, pow_pos (norm_pos_iff.2 hp0) k, fun y hy => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · exact zero_mem _
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hp
  rw [map_mul, norm_mul, norm_iota_unit N A i u.isUnit, one_mul, map_pow, norm_pow] at hy
  have hlt : ‖iotaOQ N A i p‖ < 1 := norm_iota_lt_one N A i (by
    rw [hp.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self p)
  have hkn : k ≤ n := by
    by_contra h
    rw [not_le] at h
    exact absurd hy (not_lt.2 (pow_le_pow_of_le_one (norm_nonneg _) hlt.le h.le))
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact (pow_dvd_pow p hkn).mul_left _

theorem exists_integral_char (d : G H.E N.Om →* Qbar (N.l i)) (hd : Continuous d) (S : Set (G H.E N.Om))
    (hS : closure S = Set.univ) (hv : ∀ σ ∈ S, d σ ∈ Set.range (A.iotaQ i)) :
    ∃ ξ : G H.E N.Om →* (N.O i)ˣ, Continuous (fun g => ((ξ g : (N.O i)ˣ) : N.O i)) ∧
      ∀ g, iotaOQ N A i ((ξ g : (N.O i)ˣ) : N.O i) = d g := by
  have : IsGalois H.E N.Om := {}
  have hn := norm_eq_one_of_compact d hd
  have hinj := iota_inj N A i
  have hall : ∀ g, d g ∈ Set.range (iotaOQ N A i) := by
    have hsub : closure S ⊆ d ⁻¹' Set.range (iotaOQ N A i) :=
      closure_minimal (fun σ hσ => by
        obtain ⟨x, hx⟩ := hv σ hσ
        have := mem_range_of_norm N A i (x := x) (by rw [hx]; exact hn σ)
        rw [hx] at this
        exact this) ((isClosed_range_iota N A i).preimage hd)
    intro g
    exact hsub (hS ▸ Set.mem_univ g)
  choose u hu using hall
  let ξ0 : G H.E N.Om →* N.O i :=
    { toFun := u
      map_one' := hinj (by rw [hu, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hu, map_mul, map_mul, hu, hu]) }
  refine ⟨ξ0.toHomUnits, ?_, fun g => ?_⟩
  · have hval : (fun g => ((ξ0.toHomUnits g : (N.O i)ˣ) : N.O i)) = u := funext fun g => rfl
    rw [hval, continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
      (N.O_adic i).hasBasis_nhds_zero.tendsto_right_iff]
    intro k _
    obtain ⟨δ, hδ, hk⟩ := mem_pow_of_norm_lt N A i k
    have hcd : ∀ᶠ x in nhds g, ‖d x - d g‖ < δ := by
      have := (hd.tendsto g)
      exact (Metric.tendsto_nhds.1 this δ hδ).mono fun x hx => by simpa [dist_eq_norm] using hx
    filter_upwards [hcd] with x hx
    apply hk
    rw [map_sub, hu, hu]
    exact hx
  · exact hu g

end Coeff

section Main

open Formalism.L2.Host

theorem inf_int (D : D7) (hA : Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut) (τ : D.host.E →+* ℂ) (z : ℂ)
    (hz : z ∈ D.naut.infG D.naut.etaTinv τ) : ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
  obtain ⟨v, hv⟩ := D.R.t_odd
  have hs : ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = -(v : ℂ) - 1 / 2 := by
    rw [hv]
    push_cast
    ring
  obtain ⟨h1, h3⟩ := hA.2.1 τ
  rw [h3] at hz
  rcases h1 with h1 | h1
  · rw [h1] at hz
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz
    subst hz
    exact ⟨-(v : ℤ) - 1, by rw [hs]; push_cast; ring⟩
  · rw [h1] at hz
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz
    subst hz
    exact ⟨-(v : ℤ), by rw [hs]; push_cast; ring⟩

theorem frob_value (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch)
    (T : NCharTied D C nch Tp) (V : ValLL0 D C) (w : PlE D.host) :
    ∃ x : D.what₂.LL, D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) =
      {D.what₂.embLL x} := by
  obtain ⟨v, hv⟩ := D.R.t_odd
  have hu := (D.naut.etaTinv_def w).1
  have hU := (T.unr_iff _ w).1 hu
  have hf := T.frob _ w hU
  rw [T.etaTinv] at hf hU
  have hE : C.eta.UnrAt w := by simpa using hU.inv
  obtain ⟨y, hy⟩ := V.eta w hE
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
    have := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hn : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hy' : D.what₂.embLL (y : D.what₂.LL) =
      ((C.eta.val w : ℂˣ) : ℂ) * ((normV w : ℕ) : ℂ) ^ (-(((1 / 2 : ℝ)) : ℂ)) := by
    have e : D.what₂.embLL (y : D.what₂.LL) = C.eta.valTw (1 / 2) w := hy
    rw [e, HChar.valTw, hn]
  refine ⟨(y : D.what₂.LL) * (((normV w : ℕ) : D.what₂.LL)⁻¹) ^ v, ?_⟩
  rw [D.naut.frobEig_tw _ _ hu, hf, Multiset.map_singleton, HChar.val_inv, inv_inv]
  congr 1
  rw [map_mul, map_pow, map_inv₀, map_natCast, hy', mul_assoc]
  congr 1
  have e1 : (((-(D.R.t : ℝ) / 2 : ℝ)) : ℂ) = -(((1 / 2 : ℝ)) : ℂ) + -(v : ℂ) := by
    rw [hv]
    push_cast
    ring
  rw [e1, Complex.cpow_add _ _ hq, Complex.cpow_neg _ (v : ℂ), Complex.cpow_natCast, inv_pow]

end Main

end GlobalTheory.XiOver
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSelfEqOneIffOfLinearOrderedCommGroupWithZero
noncomputable section

open Formalism.UG Matrix

namespace GlobalTheory.Hk3.Inh

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_two {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (hq : Odd q) : Valued.v (2 : L) = 1 := by
  obtain ⟨-, -, -, -, -, h2, hc⟩ := h
  let O := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hc' : Nat.card (IsLocalRing.ResidueField O) = q ^ 2 := hc
  haveI : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by rw [hc']; positivity)
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField O)
  have h0 : ((q ^ 2 : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← hc', Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
  have hle : Valued.v (2 : L) ≤ 1 := (2 : O).2
  by_contra hne
  have hlt : Valued.v (2 : L) < 1 := lt_of_le_of_ne hle hne
  have hm : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [Valuation.mem_maximalIdeal_iff]; exact hlt
  have h2' : (2 : IsLocalRing.ResidueField O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (2 : O)).2 hm
    rwa [map_ofNat] at this
  obtain ⟨k, hk⟩ : Odd (q ^ 2) := hq.pow
  rw [hk] at h0
  push_cast at h0
  rw [h2'] at h0
  simp at h0




section Main

variable {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {ψ : AddChar L ℂ}







end Main

section Laurent

end Laurent

end GlobalTheory.Hk3.Inh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationEqOfHeckeAgreementTwistLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationEqOfHeckeAgreementTwistLaws
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.LocSepTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpChar_zero_unr (w : PlE H) (χ : A.LP w) (hd : A.lpDim χ = 1) (hu : A.unr χ) :
    A.lpChar (A.lpZero w) χ = A.lpZero w := by
  have hu0 := A.lpZero_unr w
  have hc := A.unr_char _ _ hd hu0 hu
  have hcard := A.frobEig_card _ hc
  rw [A.lpDim_char _ _ hd, A.lpDim_zero] at hcard
  calc A.lpChar (A.lpZero w) χ = A.lpUnr w (A.frobEig (A.lpChar (A.lpZero w) χ)) := A.unr_eq_lpUnr _ hc
    _ = A.lpUnr w (A.frobEig (A.lpZero w)) := by rw [Multiset.card_eq_zero.mp hcard, A.frobEig_zero]
    _ = A.lpZero w := (A.unr_eq_lpUnr _ hu0).symm

theorem spehLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  have hsum : ∀ a b : A.LP w, A.lpChar (A.lpSum a b) (A.locG χ w) =
      A.lpSum (A.lpChar a (A.locG χ w)) (A.lpChar b (A.locG χ w)) := fun a b => (hC w a b _ _ 0 hχ hχ).1
  have htw : ∀ (a : A.LP w) (s : ℝ), A.lpChar (A.lpTw a s) (A.locG χ w) = A.lpTw (A.lpChar a (A.locG χ w)) s :=
    fun a s => (hC w a a _ _ s hχ hχ).2.1
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact hz.symm
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, hsum, htw, A.locG_tw]

theorem isoLoc_twist_of_laws (hC : GlobalTheory.RowTie.CharLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H)
    (hz : A.lpChar (A.lpZero w) (A.locG χ w) = A.lpZero w) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  induction S with
  | nil => exact hz.symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, spehLoc_twist_of_laws N A hC p χ w hz, (hC w _ _ _ _ 0 hχ hχ).1]

theorem isoLoc_append_one (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil =>
    change A.lpSum (spehLoc N A q w) (A.lpZero w) = A.lpSum (A.lpZero w) (spehLoc N A q w)
    exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

theorem heckePol_coeff (i : N.Loc) (x : N.X i) (w : PlE H) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ R.nV) :
    (heckePol N i x w).coeff (R.nV - k) =
      (-1 : N.O i) ^ k * ((normV w : ℕ) : N.O i) ^ (k * (k - 1) / 2) * ((N.hT i w k : N.X i → N.O i) x) := by
  unfold heckePol
  exact GlobalTheory.PtLocalEig.coeff_monic_poly_sum R.nV k hk1 hk2
    (fun k' => (-1 : N.O i) ^ k' * ((normV w : ℕ) : N.O i) ^ (k' * (k' - 1) / 2) * ((N.hT i w k' : N.X i → N.O i) x))

theorem main : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → GlobalTheory.RowTie.CharLaws D.nd D.naut →
    (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v →
      D.naut.locW i σ v = D.naut.locW i' σ v) →
    (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') →
    KillingConditions.LocalisationUniqueness D := by
  intro D M HT hC hW hmu
  unfold KillingConditions.LocalisationUniqueness
  intro i i' _ hj hw σ _ hA hA'
  by_contra hne
  obtain ⟨φ, hφ⟩ := HT.sameO i i' hj hw
  obtain ⟨Sig, hSig, x, hx⟩ := hA
  obtain ⟨Sig', hSig', x', hx'⟩ := hA'
  obtain ⟨v, k, hv, hv', hk1, hk2, hunit⟩ := HT.sep i i' φ hφ hj hw hne x x'
  obtain ⟨p, hp1, hp2⟩ := hx v hv
  obtain ⟨p', hp1', hp2'⟩ := hx' v hv'
  have hinj' : Function.Injective (iotaO D.nd D.naut i') := by
    unfold iotaO
    simp only [RingHom.coe_comp]
    exact (D.naut.iotaQC i').injective.comp ((D.naut.iotaQ i').injective.comp
      (IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))))
  have hmuP : muPart D.nd D.naut i = muPart D.nd D.naut i' := by
    unfold muPart; rw [hmu i i' hj hw]
  have hz := lpChar_zero_unr D.nd D.naut v (D.naut.locG D.naut.etaTinv v) (D.naut.locG_dim _ v)
    (D.naut.etaTinv_def v).1
  have hpar : isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) v =
      isoLoc D.nd D.naut (twistIso D.nd D.naut (Sig' ++ [muPart D.nd D.naut i']) D.naut.etaTinv) v := by
    rw [isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz, isoLoc_twist_of_laws D.nd D.naut hC _ _ v hz,
      isoLoc_append_one, isoLoc_append_one, hSig.2.2 v hv.1, hSig'.2.2 v hv'.1, hW i i' σ v hv.1, hmuP]
  have hpp : p.map (φ : D.nd.O i →+* D.nd.O i') = p' := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i') hinj'
    rw [Polynomial.map_map, hp1', ← hpar, ← hp1]
    congr 1
    exact RingHom.ext fun z => (hφ z).symm
  set n := D.R.nV - k
  have e1 : IsLocalRing.residue (D.nd.O i) (p.coeff n) =
      IsLocalRing.residue (D.nd.O i) ((heckePol D.nd i x v).coeff n) := by
    have := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P n) hp2
    simpa only [Polynomial.coeff_map] using this
  have e2 : IsLocalRing.residue (D.nd.O i') (p'.coeff n) =
      IsLocalRing.residue (D.nd.O i') ((heckePol D.nd i' x' v).coeff n) := by
    have := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P n) hp2'
    simpa only [Polynomial.coeff_map] using this
  have e3 := GlobalTheory.PtLocalEig.residue_map_equiv φ e1
  have hcp : φ (p.coeff n) = p'.coeff n := by
    rw [← hpp, Polynomial.coeff_map]; rfl
  have hφc : φ ((-1 : D.nd.O i) ^ k * ((normV v : ℕ) : D.nd.O i) ^ (k * (k - 1) / 2) *
      ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x)) = (-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
      φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) := by
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [hcp, e2, heckePol_coeff D.nd i x v k hk1 hk2, heckePol_coeff D.nd i' x' v k hk1 hk2, hφc] at e3
  have hq := GlobalTheory.PtLocalEig.normV_unit D i' v hv'.2.1
  have hc : IsUnit ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2)) :=
    ((isUnit_one.neg).pow k).mul (hq.pow _)
  have hdiff : IsLocalRing.residue (D.nd.O i')
      ((-1 : D.nd.O i') ^ k * ((normV v : ℕ) : D.nd.O i') ^ (k * (k - 1) / 2) *
        (φ ((D.nd.hT i v k : D.nd.X i → D.nd.O i) x) - (D.nd.hT i' v k : D.nd.X i' → D.nd.O i') x')) = 0 := by
    rw [mul_sub, map_sub, e3, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hdiff
  exact hdiff (hc.mul hunit)

end GlobalTheory.LocSepTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizationEqOfHeckeAgreementTwistLawsStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_eq_of_heckeAgreement_twistLaws : ∀ (D : D7) (M : Formalism.L2.MtFam D), Formalism.L2.HeckeTied D M → GlobalTheory.RowTie.CharLaws D.nd D.naut → (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v → D.naut.locW i σ v = D.naut.locW i' σ v) → (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') → KillingConditions.LocalisationUniqueness D := by
  first | exact @GlobalTheory.LocSepTie.main | exact GlobalTheory.LocSepTie.main | (intros; apply GlobalTheory.LocSepTie.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDivisors

section Algebra

variable {R : Type} [CommRing R] {n : ℕ} {ε : R} {A B C : Matrix (Fin n) (Fin n) R}

theorem conj_diag_inv (h1 : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R))
    (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d d' : Fin n → R) (hd : ∀ i, d i * d' i = 1) :
    ε • ((B * Matrix.diagonal d * C) * (B * Matrix.diagonal d' * C)) = ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have h3 : Matrix.diagonal d * Matrix.diagonal d' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hd)
  calc ε • ((B * Matrix.diagonal d * C) * (B * Matrix.diagonal d' * C))
      = B * Matrix.diagonal d * (ε • (C * B)) * Matrix.diagonal d' * C := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = ε • (B * (Matrix.diagonal d * Matrix.diagonal d') * C) := by
        rw [h2]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by rw [h3, Matrix.mul_one, h1]

theorem conj_diag_mulVec (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d : Fin n → R)
    (hA : ε • A = ε • (B * Matrix.diagonal d * C)) {y z : Fin n → R}
    (h : (fun a => ε * y a) = fun a => ε * B.mulVec z a) :
    (fun a => ε * A.mulVec y a) = fun a => ε * B.mulVec (fun i => d i * z i) a := by
  have h' : ε • y = ε • B.mulVec z := h
  have h3 : (fun i => d i * z i) = (Matrix.diagonal d).mulVec z := funext fun i => (Matrix.mulVec_diagonal d z i).symm
  show ε • A.mulVec y = ε • B.mulVec (fun i => d i * z i)
  rw [← Matrix.smul_mulVec, hA, Matrix.smul_mulVec, ← Matrix.mulVec_smul, h', Matrix.mulVec_smul, h3,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, Matrix.mul_assoc _ C,
    ← Matrix.mul_smul, h2, Matrix.mul_smul, Matrix.mul_one]

theorem conj_diag_scale (hε : ε * ε = ε) (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d d' : Fin n → R)
    (x : R) (hd : ∀ i, d i * d' i = x) (hA : ε • A = ε • (B * Matrix.diagonal d * C)) {y z : Fin n → R}
    (h : (fun a => ε * y a) = fun a => ε * B.mulVec z a) :
    (fun a => ε * (x * y a)) = fun a => ε * A.mulVec (fun a => ε * B.mulVec (fun i => d' i * z i) a) a := by
  rw [conj_diag_mulVec h2 d hA (z := fun i => d' i * z i) (funext fun a => by rw [← mul_assoc, hε])]
  have h1 : (fun i => d i * (d' i * z i)) = x • z := funext fun i => by
    rw [← mul_assoc, hd, Pi.smul_apply, smul_eq_mul]
  rw [h1, Matrix.mulVec_smul]
  funext a
  rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, congrFun h a, mul_left_comm]

theorem det_congr (hε : ε * ε = ε) (h : ε • A = ε • B) : ε * A.det = ε * B.det := by
  have h1 : ε * ε ^ Fintype.card (Fin n) = ε := by
    rw [← pow_succ']; exact IsIdempotentElem.pow_succ_eq _ hε
  have h2 := congrArg (fun M => ε * Matrix.det M) h
  simpa only [Matrix.det_smul, ← mul_assoc, h1] using h2

theorem conj_diag_det (hε : ε * ε = ε) (h1 : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d : Fin n → R)
    (hA : ε • A = ε • (B * Matrix.diagonal d * C)) : ε * A.det = ε * ∏ i, d i := by
  have h2 := det_congr hε h1
  rw [Matrix.det_mul, Matrix.det_one] at h2
  rw [det_congr hε hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  linear_combination (∏ i, d i) * h2

end Algebra

theorem getD_label (n k i : ℕ) :
    (List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i 0 = if i < k then 1 else 0 := by
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using h)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem dualLab_label (n k : ℕ) : dualLab (List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0) = splitLab n k := by
  simp [dualLab, splitLab]

theorem prod_label {R : Type} [CommRing R] (x : R) {n k : ℕ} (h : k ≤ n) :
    (∏ i : Fin n, if i.1 < k then x else 1) = x ^ k := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Fin.card_filter_val_lt, min_eq_right h]

theorem int_mul_mem (D : D7) (u : 𝓞 D.host.E) {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    finPart D (incA D (u : D.host.E)) * y ∈ intAE D := by
  refine AddSubgroup.closure_induction (p := fun y _ => finPart D (incA D (u : D.host.E)) * y ∈ intAE D) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨b, hb, u * v, ?_⟩
    show ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x _ h; rw [mul_neg]; exact neg_mem h

theorem one_mem_int (D : D7) : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩


set_option maxHeartbeats 1000000 in
theorem exists_model {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (he : IsIdemAt e P) (h0 : (ϖ : D.host.E) ≠ 0) (hk : k ≤ V.rank) :
    ∃ α : GA D V, IsHeckeElt V e (ϖ : D.host.E) k α ∧
      DivAt V e (ϖ : D.host.E) (List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0) α := by
  obtain ⟨B, hB1, hB2⟩ := GlobalTheory.T.exists_completedLattice_basis_at_prime V P e he
  have hε : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he.1.1]
  obtain ⟨C, hC1, hC2⟩ := (GlobalTheory.T.completedLattice_integrality V).2.2 (finPart D e) B hε fun y hy => (hB2 y hy).imp fun _ h => h.2
  obtain ⟨d, hd⟩ : ∃ d : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
    ∀ i, d i = if i.1 < k then finPart D (incA D (ϖ : D.host.E)) else 1 := ⟨_, fun _ => rfl⟩
  have hdc : ∀ i : Fin V.rank, finPart D (incA D ((ϖ : D.host.E) ^
      ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0))) = d i := fun i => by
    rw [getD_label, hd]
    split_ifs
    · rw [zpow_one]
    · rw [zpow_zero, RingHom.map_one, RingHom.map_one]
  obtain ⟨α, hs, hα⟩ := GlobalTheory.T.exists_adelic_unitary_split_place_component V e he.1 (B * Matrix.diagonal d * C) _
    (conj_diag_inv hC1 hC2 d (fun i => if i.1 < k then finPart D (incA D (ϖ : D.host.E)⁻¹) else 1) fun i => by
      rw [hd]
      split_ifs
      · rw [← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ h0, RingHom.map_one, RingHom.map_one]
      · exact mul_one _)
  have idem : ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (fun a => finPart D e * (finPart D e * y a)) = fun a => finPart D e * y a := fun y =>
    funext fun a => by rw [← mul_assoc, hε]
  refine ⟨α, ⟨((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e (e + cA D e) (Or.inl ⟨he, rfl⟩)).2.2.1 α hs, hs, fun y hy => ?_,
    fun y hy => ?_, 1, 1, ?_, ?_, ?_, ?_⟩, ?_, B, hB1, hB2, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    rw [conj_diag_mulVec hC2 d hα h]
    refine hB1 _ fun i => ?_
    rw [hd]
    split_ifs
    · exact int_mul_mem D ϖ (hz i)
    · rw [one_mul]; exact hz i
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    refine ⟨_, hB1 (fun i => (if i.1 < k then 1 else finPart D (incA D (ϖ : D.host.E))) * z i) fun i => ?_, ?_⟩
    · beta_reduce
      split_ifs
      · rw [one_mul]; exact hz i
      · exact int_mul_mem D ϖ (hz i)
    · refine conj_diag_scale hε hC2 d _ _ (fun i => ?_) hα h
      rw [hd]
      split_ifs
      · exact mul_one _
      · exact one_mul _
  · rw [RingHom.map_one]; exact one_mem_int D
  · rw [RingHom.map_one]; exact one_mem_int D
  · rw [mul_one, mul_one]
  · refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he.1, zero_mul]
    · have h1 := conj_diag_det hε hC1 d hα
      rw [funext hd, prod_label _ hk] at h1
      rw [mul_one, (finPart D).map_mul, (finPart D).map_mul, (finPart D).map_pow, (finPart D).map_det]
      exact h1
  · rw [List.length_append, List.length_replicate, List.length_replicate]; omega
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    refine ⟨z, hz, ?_⟩
    simp only [hdc]
    exact conj_diag_mulVec hC2 d hα h
  · refine ⟨_, hB1 z hz, ?_⟩
    simp only [hdc]
    exact conj_diag_mulVec hC2 d hα (idem _)

theorem divAt_inv_of_isHeckeElt : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → k ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) k α → DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ := by
  intro D V P e ϖ k α he h1 h2 hk hα
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
  obtain ⟨α₀, hH, hD⟩ := exists_model V P e ϖ k he h0 hk
  obtain ⟨a, ha, b, hb, rfl⟩ := (((GlobalTheory.T.involution_spherical_hecke_anti V P e he).2.2 ϖ h1 h2).2 k α₀ hH).2 ϖ α h1 h2 hα
  rw [← dualLab_label]
  exact (GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e _ _ _ he.1.1 h0 ((GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e _ _ _ he.1.1 h0 hD).2 a ha.1 b hb.1)).1

end GlobalTheory.SplitDivisors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_divisors_inv_hecke_element_split_place : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → k ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) k α → DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ := by
  first | exact @GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt | exact GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt | (intros; apply GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNeAlt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.InertialTypes

theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E p) : w ∉ placesOver E q := by
  intro hw'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b hw')

end GlobalTheory.InertialTypes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DepthZeroJacquetInjectiveOfAdmissible
namespace GlobalTheory

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

theorem depthZeroJacquetInjective_of_admissible :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.MoyPrasadJacquetIso →
      GlobalTheory.Published.DepthZeroJacquetInjective := by
  intro hBZ hMP k _ _ _ _ n s d e π v hv h0
  have hadm := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hb := hMP k n s d e π.V π.π hadm
  have h00 : (0 : π.V) ∈ fixed π.π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) := by
    first
      | exact Submodule.zero_mem _
      | exact fun _ => map_zero _
      | simp [fixed]
  exact hb.injOn hv h00 (by simpa using h0)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.KS

theorem isProjOver_pow : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsProjOver s → ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB →
    Out.RelAmple A L → ∀ k : ℕ, IsProjOver ((GlobalTheory.KS.pow A k).hom ≫ s) := by
  intro R _ _ X s hs A _ _ hA L hL hamp k
  obtain ⟨hsp, H, hH⟩ := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs
  have p := Out.powIsPowGrp A k
  have hrel : Out.RelAmple (Out.powObj A k) (Out.boxLB L p.pr) :=
    GlobalTheory.relAmple_boxLB X (Out.powObj A k) A k p L hL hamp
  obtain ⟨-, N, hN⟩ := GlobalTheory.RelAmpleQProj.isProper_and_exists_isAmpleLB (Out.powObj A k)
    (LB.isLB_linComb hL _ _) hrel hH
  let e : GlobalTheory.KS.pow A k ≅ Out.powObj A k :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Out.powIsLimit A k)
  have hpA : IsProper A.hom := hA.proper
  have : IsProper (GlobalTheory.KS.pow A k).hom := GlobalTheory.KS.Leray.isProper_pow_hom A hpA k
  have : IsIso e.hom.left := ((Over.forget X).mapIso e).isIso_hom
  have := hsp
  exact (hN.pull_of_isAffineHom e.hom.left).isProjOver _

end GlobalTheory.KS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsPowValEqZpow
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

namespace GlobalTheory.TotDisjUnlinked

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_val_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
  have hq' : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [val_absPow, LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (by exact_mod_cast (zpow_pos hq _).ne'),
    Complex.cpow_def_of_ne_zero hq', ← Complex.ofReal_log (zpow_pos hq _).le, Real.log_zpow,
    ← Complex.exp_int_mul, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem absPow_eq_unrChar (s : ℂ) :
    absPow k s = unrChar k (Units.mk0 ((resCard k : ℂ) ^ (-s))
      (by
        have hq : (0 : ℝ) < resCard k := by exact_mod_cast zero_lt_one.trans (SplitWeil.one_lt_resCard k)
        exact Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hq.ne')))) := by
  ext x
  rw [absPow_val_eq_zpow, unrChar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end GlobalTheory.TotDisjUnlinked

theorem GlobalTheory.TotDisjUnlinked.main :
    GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.UnlinkedProductIrreducible := by
  intro H k _ _ _ _ r t s s' π₁ π₂ d d' σ σ' h₁ h₂ hu
  refine H k r t s s' π₁ π₂ d d' σ σ' h₁ h₂ fun a b h j _ => ?_
  rw [GlobalTheory.TotDisjUnlinked.absPow_eq_unrChar]
  exact hu a b h _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiAlgUnitInert
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem ringHom_mem_qbar {A : Type} [Field A] [NumberField A] (f : A →+* ℂ) (x : A) : f x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).map f.toRatAlgHom

theorem lamC_eq_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam s = lam ⟨s, hs⟩ := by
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hs]

theorem chi_alg_unit_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (χ : TaylorLogMetric.IdE D → ℂ),
    TaylorLogMetric.IsChi D χ → p ≠ 2 → GL3Theta.InertK D p → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
      χ 𝔞 ∈ TaylorLogMetric.Qbar ∧ χ 𝔞 ≠ 0 ∧ ‖TaylorLogMetric.lamC lam (χ 𝔞)‖ = 1 := by
  intro D p _ lam χ hχ hp2 hin 𝔞 ha
  letI := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  set P : ℂ := ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z with hPdef
  have hpow : χ 𝔞 ^ k = P⁻¹ := by
    have h := hχ.2 ⟨z, hzu⟩
    simp only at h
    rw [← hspan, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.chi_pow D χ hχ ha k hk] at h
    rw [h, hPdef, Finset.prod_inv_distrib]
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun τ _ => (map_ne_zero _).mpr hz0
  have hP : P ∈ TaylorLogMetric.Qbar := prod_mem fun τ _ => ringHom_mem_qbar _ z
  have hk0 : k ≠ 0 := by omega
  have halg : χ 𝔞 ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff] at hP ⊢
    have h2 : IsAlgebraic ℚ (χ 𝔞 ^ k) := by rw [hpow]; exact hP.inv
    exact IsAlgebraic.of_pow (Nat.pos_of_ne_zero hk0) h2
  have hne : χ 𝔞 ≠ 0 := by
    intro h0
    rw [h0, zero_pow hk0] at hpow
    exact hP0 (inv_eq_zero.mp hpow.symm)
  refine ⟨halg, hne, ?_⟩
  have hnu := GlobalTheory.T.norm_prod_cmEmbeddings_eq_one_of_inert D p lam hp2 hin z hz
  rw [← hPdef, lamC_eq_of_mem lam hP] at hnu
  have hsub : (⟨χ 𝔞, halg⟩ : TaylorLogMetric.Qbar) ^ k = (⟨P, hP⟩ : TaylorLogMetric.Qbar)⁻¹ := by
    apply Subtype.ext
    simp [hpow]
  have e1 : ‖lam ⟨χ 𝔞, halg⟩‖ ^ k = 1 := by
    rw [← norm_pow, ← map_pow, hsub, map_inv₀, norm_inv, hnu, inv_one]
  rw [lamC_eq_of_mem lam halg]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk0).mp e1

end GlobalTheory.TwV.Xc

end
end
