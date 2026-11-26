module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PairingOmegaPrimeZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolKap

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.LeadingMinorIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ideal

variable {D : D7}

abbrev dI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

theorem star_F (c : D.host.F) : star (algebraMap D.host.F D.host.E c) = algebraMap D.host.F D.host.E c :=
  (NumberField.IsCMField.complexConj D.host.E).commutes c

theorem star_int (o : 𝓞 D.host.E) : ∃ o' : 𝓞 D.host.E, (o' : D.host.E) = star (o : D.host.E) := by
  exact ⟨⟨star (o : D.host.E), o.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩

theorem star_mem_pow (n : ℕ) (y : 𝓞 D.host.E) (hy : y ∈ dI D ^ n) :
    ∃ y' ∈ dI D ^ n, (y' : D.host.E) = star (y : D.host.E) := by
  rw [← Ideal.map_pow] at hy ⊢
  have hy' : y ∈ Submodule.span (𝓞 D.host.E)
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) '' ((differentIdeal ℤ (𝓞 D.host.F) ^ n : Ideal (𝓞 D.host.F)) : Set (𝓞 D.host.F))) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c, Ideal.mem_map_of_mem _ hc, ?_⟩
    have e : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (c : D.host.F) := rfl
    rw [e, star_F]
  | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' + y', Ideal.add_mem _ hx' hy', ?_⟩
    rw [show ((x' + y' : 𝓞 D.host.E) : D.host.E) = (x' : D.host.E) + (y' : D.host.E) from rfl,
      show ((x + y : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) + (y : D.host.E) from rfl, ex, ey, star_add]
  | smul a x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨a', ea⟩ := star_int a
    refine ⟨a' * x', Ideal.mul_mem_left _ _ hx', ?_⟩
    rw [smul_eq_mul, show ((a' * x' : 𝓞 D.host.E) : D.host.E) = (a' : D.host.E) * (x' : D.host.E) from rfl,
      show ((a * x : 𝓞 D.host.E) : D.host.E) = (a : D.host.E) * (x : D.host.E) from rfl, ea, ex, star_mul, mul_comm]

theorem dI_ne_bot (n : ℕ) : dI D ^ n ≠ ⊥ := by
  have h : dI D ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
  rw [← Ideal.zero_eq_bot] at h ⊢
  exact pow_ne_zero n h

theorem mem_inv_coe {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) (x : D.host.E) :
    x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ ↔
      ∀ y ∈ J, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (y : D.host.E) := by
  have hJ' : (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  rw [FractionalIdeal.mem_inv_iff hJ']
  constructor
  · intro h y hy
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hy))
    exact ⟨o, ho⟩
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    obtain ⟨o, ho⟩ := h y hy
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨o, ho⟩

theorem star_mem_inv (n : ℕ) {x : D.host.E}
    (hx : x ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹) :
    star x ∈ (((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  rw [mem_inv_coe (dI_ne_bot n)] at hx ⊢
  intro y hy
  obtain ⟨y', hy', ey⟩ := star_mem_pow n y hy
  obtain ⟨o, ho⟩ := hx y' hy'
  obtain ⟨o', eo⟩ := star_int o
  refine ⟨o', ?_⟩
  rw [eo, ho, ey, star_mul, star_star, mul_comm]

end Ideal

section Entry

variable {D : D7}

theorem hT_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) (m n : ℕ)
    (v v' : (VS D).V)
    (hv : ∀ x ∈ ((dI D ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹,
      x • v ∈ Λ)
    (hv' : ∀ y ∈ ((dI D ^ n : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹,
      y • v' ∈ Λ) :
    ∃ o ∈ dI D ^ (m + n), (o : D.host.E) = (VS D).hT v v' := by
  set Z := (VS D).hT v v' with hZ
  let FI := FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E
  set A : FI := ((dI D ^ m : Ideal (𝓞 D.host.E)) : FI)⁻¹
  set B : FI := ((dI D ^ n : Ideal (𝓞 D.host.E)) : FI)⁻¹
  have hJ : ((dI D ^ (m + n) : Ideal (𝓞 D.host.E)) : FI) = (A * B)⁻¹ := by
    rw [mul_inv, inv_inv, inv_inv, ← FractionalIdeal.coeIdeal_mul, ← pow_add]
  have hAB0 : A * B ≠ 0 := by
    refine mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_) <;>
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero] <;> exact dI_ne_bot _
  have hmem : Z ∈ (A * B)⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hAB0]
    intro w hw
    refine FractionalIdeal.mul_induction_on hw ?_ ?_
    · intro a ha b hb
      have ha' : star a ∈ A := star_mem_inv m ha
      obtain ⟨c, hc⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun (hv _ ha') (hv' _ hb)
      refine (FractionalIdeal.mem_one_iff _).2 ⟨c, ?_⟩
      show (c : D.host.E) = _
      rw [hc, LinearMap.map_smulₛₗ₂, LinearMap.map_smulₛₗ, RingHom.id_apply, starRingEnd_apply, star_star,
        smul_eq_mul, smul_eq_mul, hZ]
      ring
    · intro x y hx hy
      rw [mul_add]
      exact Submodule.add_mem _ hx hy
  rw [← hJ] at hmem
  obtain ⟨o, ho, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
  exact ⟨o, ho, e⟩

theorem two_sum_sub (r : ℕ) : ∀ q : ℕ, q ≤ r + 1 → 2 * ∑ i : Fin q, (r - (i : ℕ)) = q * (2 * r + 1 - q)
  | 0, _ => by simp
  | q + 1, hq => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [mul_add, two_sum_sub r q (by omega)]
    have e1 : 2 * r + 1 - q = q + 2 * (r - q) + 1 := by omega
    have e2 : 2 * r + 1 - (q + 1) = q + 2 * (r - q) := by omega
    rw [e1, e2]
    ring

end Entry

section Norm

variable {D : D7}

theorem discr_sq : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 :=
  D.host.der.discr_sq

theorem absNorm_dI : ((Ideal.absNorm (dI D) : ℕ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2 := by
  have h := Formalism.MainNotions.BridgeLemma.szf_normDD D discr_sq
  unfold Formalism.MainNotions.BridgeLemma.SzfNormDD Formalism.MainNotions.S.ddE at h
  rw [FractionalIdeal.coeIdeal_absNorm] at h
  exact_mod_cast h

theorem rd_pos : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _

theorem prod_sq_ge (n : ℕ) (o : 𝓞 D.host.E) (ho : o ∈ dI D ^ n) (h0 : (o : D.host.E) ≠ 0) :
    (D.host.rdE ^ D.R.f) ^ (2 * n) ≤ ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h1 := InfinitePlace.prod_eq_abs_norm (o : D.host.E)
  have h2 : ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ w.mult =
      ∏ w : InfinitePlace D.host.E, w (o : D.host.E) ^ 2 :=
    Finset.prod_congr rfl fun w _ => by rw [(IsTotallyComplex.isComplex w).mult_eq_two]
  rw [← h2, h1, ← Algebra.coe_norm_int]
  have ho0 : o ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hspan : Ideal.span {o} ≤ dI D ^ n := (Ideal.span_singleton_le_iff_mem _).2 ho
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hspan
  rw [Ideal.absNorm_span_singleton, map_pow] at hdvd
  have hne : (Algebra.norm ℤ o).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]; exact Algebra.norm_ne_zero_iff.2 ho0
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
  have hle' : ((Ideal.absNorm (dI D) ^ n : ℕ) : ℝ) ≤ ((Algebra.norm ℤ o).natAbs : ℝ) := by exact_mod_cast hle
  rw [Nat.cast_pow, absNorm_dI, ← pow_mul] at hle'
  have e : (((Algebra.norm ℤ o).natAbs : ℕ) : ℝ) = ((|((Algebra.norm ℤ o : ℤ) : ℚ)| : ℚ) : ℝ) := by
    simp [Nat.cast_natAbs, Rat.cast_abs]
  rw [← e]
  exact hle'

end Norm

end Formalism.L2.SG.NGCut.LeadingMinorIntegrality
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ q, Agree δ M q) (p : PlF D)

include δ M hA


omit M hA in
abbrev cc : (D.s.atP p).Ep :=
  algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)

theorem cc_unit : IsUnit (cc δ p) := LocFacts.isUnit_localConstant p ⟨δ, M, hA⟩

theorem frFac_mul (a : Fin (D.R.rS + 1)) : frFac δ p a * cc δ p ^ (D.R.rS - a.val) = 1 := by
  unfold frFac
  exact Ring.inverse_mul_cancel _ ((cc_unit δ M hA p).pow _)

theorem inv_frFac (a : Fin (D.R.rS + 1)) : Ring.inverse (frFac δ p a) = cc δ p ^ (D.R.rS - a.val) := by
  unfold frFac
  exact Ring.inverse_inverse ((cc_unit δ M hA p).pow _)

theorem cj_cc : (D.s.atP p).cj (cc δ p) = cc δ p := by
  have hE : (D.s.atP p).ιE (uP p : D.host.E) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((uP p : ℚ) : (D.s.atP p).Fp) := by
    rw [← map_ratCast (algebraMap D.host.F D.host.E), (D.s.atP p).compat, map_ratCast]
  simp only [cc, map_mul, hE, AlgEquiv.commutes]

theorem cj_frFac (a : Fin (D.R.rS + 1)) : (D.s.atP p).cj (frFac δ p a) = frFac δ p a := by
  have h := frFac_mul δ M hA p a
  have h' : (D.s.atP p).cj (frFac δ p a) * cc δ p ^ (D.R.rS - a.val) = 1 := by
    rw [← cj_cc δ M hA p, ← map_pow, ← map_mul, h, map_one]
  calc (D.s.atP p).cj (frFac δ p a)
      = (D.s.atP p).cj (frFac δ p a) * (cc δ p ^ (D.R.rS - a.val) * frFac δ p a) := by
        rw [mul_comm (cc δ p ^ _), h, mul_one]
    _ = frFac δ p a := by rw [← mul_assoc, h', one_mul]

theorem locMem_iff {k : ℕ} (hk : k ≤ D.R.rS) (x : D.host.E) :
    LocMem D p (ddPow D k) x ↔ cc δ p ^ k * (D.s.atP p).ιE x ∈ (D.s.atP p).O := by
  have hD := locDiffC_holds D ⟨δ, M, hA⟩ p ⟨D.R.rS - k, by omega⟩
  have e1 : (-((D.R.rS : ℤ) - ((D.R.rS - k : ℕ) : ℤ))) = -(k : ℤ) := by
    rw [Nat.cast_sub hk]; ring
  dsimp only at hD
  rw [e1] at hD
  have hg := frFac_mul δ M hA p ⟨D.R.rS - k, by omega⟩
  simp only [Nat.sub_sub_self hk] at hg
  have hO : (M p).L.O = (D.s.atP p).O := (hA p).2.2.2.1
  unfold LocMem ddPow
  rw [← SetLike.mem_coe, ← LocFacts.lf_span_coe_of_eq hO, hD, LocFacts.lf_span_coe_of_eq hO, SetLike.mem_coe,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨o, ho⟩
    rw [← ho, Subring.smul_def, smul_eq_mul, mul_left_comm, mul_comm (cc δ p ^ k), hg, mul_one]
    exact o.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    rw [Subring.smul_def, smul_eq_mul]
    show cc δ p ^ k * (D.s.atP p).ιE x * frFac δ p ⟨D.R.rS - k, by omega⟩ = (D.s.atP p).ιE x
    rw [mul_comm (cc δ p ^ k), mul_assoc, mul_comm (cc δ p ^ k), hg, mul_one]

theorem locMem_sub (I : FI D) {x y : D.host.E} (hx : LocMem D p I x) (hy : LocMem D p I y) :
    LocMem D p I (x - y) := by
  unfold LocMem at *
  rw [map_sub]
  exact sub_mem hx hy

theorem locMem_conj {k : ℕ} (hk : k ≤ D.R.rS) {y : D.host.E} (h : LocMem D p (ddPow D k) y) :
    LocMem D p (ddPow D k) (D.conjF y) := by
  rw [locMem_iff δ M hA p hk] at *
  rw [← (D.s.atP p).cj_ιE, ← cj_cc δ M hA p, ← map_pow, ← map_mul]
  exact LocFacts.lf_cj_mem p _ h

theorem untyped (hs : (M p).split = none) :
    Loc.resChar p ≠ D.host.g 0 ∧ Loc.resChar p ≠ D.host.g 1 := by
  have h6 := (hA p).2.2.2.2.2
  have hsD : (D.s.atP p).split = none := by
    cases hD : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [hs, hD] at h6; exact h6.elim
  have := (D.s_split p).not.1 (by rw [hsD]; simp)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this
  exact this

theorem unitAt_untyped (hs : (M p).split = none) : (uP p : ℚ) = 1 / (gS D : ℚ) := by
  obtain ⟨h0, h1⟩ := untyped δ M hA p hs
  unfold uP gpart
  rw [if_neg h0, if_neg h1]
  simp

theorem gS_mul_uP (hs : (M p).split = none) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * (D.s.atP p).ιE (uP p : D.host.E) = 1 := by
  rw [← map_mul, unitAt_untyped δ M hA p hs]
  have hg : (gS D : ℚ) ≠ 0 := by
    unfold Lat.gS; push_cast
    exact mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)
  have : ((gS D : ℕ) : D.host.E) * (((1 / (gS D : ℚ)) : ℚ) : D.host.E) = 1 := by
    rw [show ((gS D : ℕ) : D.host.E) = (((gS D : ℚ)) : D.host.E) by push_cast; rfl, ← Rat.cast_mul,
      mul_one_div_cancel hg, Rat.cast_one]
  rw [this, map_one]

omit δ M hA in
theorem gS_mem_qq : ((gS D : ℕ) : 𝓞 D.host.E) ∈ qq D :=
  Ideal.mem_span_singleton_self _

theorem locMem_qd_of (hs : (M p).split = none) (k : ℕ) {x : D.host.E} (h : LocMem D p (ddPow D k) x) :
    LocMem D p (qdPow D k) x := by
  unfold LocMem at *
  set ι := (D.s.atP p).ιE
  have key : ∀ y ∈ Submodule.span (D.s.atP p).O (ι '' (ddPow D k : Set D.host.E)),
      ι ((gS D : ℕ) : D.host.E) * y ∈ Submodule.span (D.s.atP p).O (ι '' (qdPow D k : Set D.host.E)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      rw [← map_mul]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      unfold qdPow
      have hq : ((gS D : ℕ) : D.host.E) ∈ (qq D : FI D) := by
        rw [FractionalIdeal.mem_coeIdeal]
        exact ⟨_, gS_mem_qq, map_natCast _ _⟩
      exact FractionalIdeal.mul_mem_mul hq hz
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul o y _ hy =>
      rw [Subring.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subring.smul_def]
      exact Submodule.smul_mem _ o hy
  have hu : ι (uP p : D.host.E) ∈ (D.s.atP p).O := LocFacts.unitPart_mem₂ p
  have e : ι x = ι (uP p : D.host.E) * (ι ((gS D : ℕ) : D.host.E) * ι x) := by
    rw [← mul_assoc, mul_comm (ι (uP p : D.host.E)), gS_mul_uP δ M hA p hs, one_mul]
  rw [e, show ι (uP p : D.host.E) * (ι ((gS D : ℕ) : D.host.E) * ι x) =
    (⟨_, hu⟩ : (D.s.atP p).O) • (ι ((gS D : ℕ) : D.host.E) * ι x) by rw [Subring.smul_def, smul_eq_mul]]
  exact Submodule.smul_mem _ _ (key _ h)

theorem lL_low (a : MatR D) (i j : Fin (D.R.rS + 1)) (hji : j < i) :
    StabShape.lL (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) a i j =
      cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j) := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  simp only [StabShape.lL, Matrix.of_apply, hcj, RingHom.coe_coe]
  rw [cj_frFac δ M hA p i, cj_frFac δ M hA p j, inv_frFac δ M hA p j]
  have hi := frFac_mul δ M hA p i
  have hji' : j.val < i.val := hji
  have hi' : i.val < D.R.rS + 1 := i.isLt
  have e : D.R.rS - j.val = (D.R.rS - i.val) + (i.val - j.val) := by omega
  rw [e, pow_add]
  linear_combination (cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j)) * hi

theorem ρL_up (b : MatR D) (i j : Fin (D.R.rS + 1)) (hij : i < j) :
    StabShape.ρL (D.s.atP p).ιE (frFac δ p) b i j = cc δ p ^ (j.val - i.val) * (D.s.atP p).ιE (bt D b i j) := by
  simp only [StabShape.ρL, Matrix.of_apply, bt]
  rw [inv_frFac δ M hA p i]
  have hj := frFac_mul δ M hA p j
  have hij' : i.val < j.val := hij
  have hj' : j.val < D.R.rS + 1 := j.isLt
  have e : D.R.rS - i.val = (D.R.rS - j.val) + (j.val - i.val) := by omega
  rw [show cc δ p ^ (D.R.rS - i.val) = cc δ p ^ (D.R.rS - j.val) * cc δ p ^ (j.val - i.val) by rw [← pow_add, ← e]]
  linear_combination (cc δ p ^ (j.val - i.val) *
    (D.s.atP p).ιE ((-1) ^ (D.R.rS - i.val) * b i j * (-1) ^ (D.R.rS - j.val))) * hj

theorem R_none (hs : (M p).split = none) : (M p).R = (D.s.atP p).O := by
  unfold Loc.Model.R
  rw [hs]
  exact (hA p).2.2.2.1

theorem intLow_iff_L (hs : (M p).split = none) {a b : MatR D} (ha : IsLoUni a) (hb : IsUpUni b) :
    Formalism.MainNotions.S.TieN.IntLow (M p) (StabShape.lOf δ M p a b) ↔
      ∀ i j : Fin (D.R.rS + 1), j < i → cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (a i j) ∈ (D.s.atP p).O := by
  have hR := R_none δ M hA p hs
  have hl : StabShape.lOf δ M p a b =
      StabShape.lL (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) a := by
    simp only [StabShape.lOf, hs]
  constructor
  · intro h i j hji
    have := h.2.2 i j
    rw [hR, hl, lL_low δ M hA p a i j hji] at this
    exact this
  · intro h
    refine ⟨StabShape.lOf_diag δ M (hA p) a b ha hb, fun i j hij => ?_, fun i j => ?_⟩
    · rw [hl]; simp [StabShape.lL, (ha i j).1 hij]
    · rw [hR]
      rcases lt_trichotomy j i with hji | rfl | hij
      · rw [hl, lL_low δ M hA p a i j hji]; exact h i j hji
      · rw [StabShape.lOf_diag δ M (hA p) a b ha hb]; exact Subring.one_mem _
      · rw [hl]; simp [StabShape.lL, (ha i j).1 hij]

theorem intUp_iff_L (hs : (M p).split = none) {a b : MatR D} (ha : IsLoUni a) (hb : IsUpUni b) :
    Formalism.MainNotions.S.TieN.IntUp (M p) (StabShape.ρOf δ M p a b) ↔
      ∀ i j : Fin (D.R.rS + 1), j < i → cc δ p ^ (i.val - j.val) * (D.s.atP p).ιE (bt D b j i) ∈ (D.s.atP p).O := by
  have hR := R_none δ M hA p hs
  have hr : StabShape.ρOf δ M p a b = StabShape.ρL (D.s.atP p).ιE (frFac δ p) b := by
    simp only [StabShape.ρOf, hs]
  constructor
  · intro h i j hji
    have := h.2.2 j i
    rw [hR, hr, ρL_up δ M hA p b j i hji] at this
    exact this
  · intro h
    refine ⟨StabShape.ρOf_diag δ M (hA p) a b ha hb, fun i j hji => ?_, fun i j => ?_⟩
    · rw [hr]; simp [StabShape.ρL, (hb i j).1 hji]
    · rw [hR]
      rcases lt_trichotomy i j with hij | rfl | hji
      · rw [hr, ρL_up δ M hA p b i j hij]; exact h j i hij
      · rw [StabShape.ρOf_diag δ M (hA p) a b ha hb]; exact Subring.one_mem _
      · rw [hr]; simp [StabShape.ρL, (hb i j).1 hji]


omit δ M hA p in
theorem locShapeL : LocShapeL D := by
  intro δ M p hA hs a b ha hb
  rw [intLow_iff_L δ M hA p hs ha hb, intUp_iff_L δ M hA p hs ha hb]
  constructor
  · rintro ⟨h1, h2⟩ i j hji
    have hk : i.val - j.val ≤ D.R.rS := by have := i.isLt; omega
    have m1 := (locMem_iff δ M hA p hk (a i j)).2 (h1 i j hji)
    have m2 := (locMem_iff δ M hA p hk (bt D b j i)).2 (h2 i j hji)
    exact ⟨m1, m2, locMem_qd_of δ M hA p hs _ (locMem_sub δ M hA p _ m1 (locMem_conj δ M hA p hk m2))⟩
  · intro h
    exact ⟨fun i j hji => (locMem_iff δ M hA p (by have := i.isLt; omega) _).1 (h i j hji).1,
      fun i j hji => (locMem_iff δ M hA p (by have := i.isLt; omega) _).1 (h i j hji).2.1⟩

end Formalism.L2.SG.Pf.StabIntSh
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCOfOcc
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def OccT (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u') : Prop :=
  t ∈ (Y.tO u u').ngSet ∧ (Y.tO u u').vec t ≠ 0 ∧ clsOf Y u u' t = c ∧ ptPN t = γ

def yT (t : TauC Y u u') : (VS D).V := yv (X.Fu u) t.frame.fl

def yT' (t : TauC Y u u') : (VS D).V := t.lin.symm (yv t.frame.fl (X.Fu u))

def coefA (t0 t : TauC Y u u') : D.host.E :=
  brS (VS D) (yT Y u u' t) (yT Y u u' t0) / brS (VS D) (yT Y u u' t0) (yT Y u u' t0)

def coefA' (t0 t : TauC Y u u') : D.host.E :=
  brS (VS D) (yT' Y u u' t) (yT' Y u u' t0) / brS (VS D) (yT' Y u u' t0) (yT' Y u u' t0)

theorem occ_iff (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν ↔ ∃ t, OccT Y u u' c γ t ∧ nmlOf Y u u' t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    exact ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨t, h1, h2, h3, h4, h5⟩

end Defs

section Rel

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def RelC (t0 t : TauC Y u u') : Prop :=
  (Y.tO u u').rowOf t = (Y.tO u u').rowOf t0 ∧ (Y.tO u u').s0 t0 t = 1

end Rel

def NmlLine : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 t : TauC Y u u', Gt t0 ≠ 0 → Gt t ≠ 0 → ptPN t0 = γ → ptPN t = γ → RelC Y u u' t0 t →
          coefA Y u u' t0 t * star (coefA Y u u' t0 t) = 1 ∧ coefA' Y u u' t0 t * star (coefA' Y u u' t0 t) = 1

def NmlInt : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 : TauC Y u u', Gt t0 ≠ 0 → ptPN t0 = γ →
        ∃ J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E, J ≠ 0 ∧ J' ≠ 0 ∧
          (∀ t : TauC Y u u', Gt t ≠ 0 → ptPN t = γ → RelC Y u u' t0 t →
            coefA Y u u' t0 t ∈ J ∧ coefA' Y u u' t0 t ∈ J') ∧
          (1 : ℝ) ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * NormalInvariants.PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2 ∧
          (1 : ℝ) ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u' : ℕ) : ℝ) ^ (2 * D.R.f) * NormalInvariants.PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2

def NmlSep : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 t1 t2 : TauC Y u u', Gt t0 ≠ 0 → Gt t1 ≠ 0 → Gt t2 ≠ 0 →
          ptPN t0 = γ → ptPN t1 = γ → ptPN t2 = γ → RelC Y u u' t0 t1 → RelC Y u u' t0 t2 →
          coefA Y u u' t0 t1 = coefA Y u u' t0 t2 → coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2 →
          nmlOf Y u u' t1 = nmlOf Y u u' t2

theorem relC_of_occ {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (hTie : ConcTie X Y)
    {c : Set (TauC Y u u')} {γ : PN.Pts D.host.E D.R.rS} {t0 t : TauC Y u u'}
    (h0 : OccT Y u u' c γ t0) (h : OccT Y u u' c γ t) : RelC Y u u' t0 t := by
  have hrefl := (CorankRelation.corankOne_equivalence_holds D X Y u u' hTie).1 t h.1
  have ht : t ∈ clsOf Y u u' t := ⟨h.1, rfl, hrefl⟩
  rw [h.2.2.1, ← h0.2.2.1] at ht
  exact ⟨ht.2.1, ht.2.2⟩

theorem nmlInv_of (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : NormalInvariants.NmlInv := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u u' hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occ_iff Y u u' νL νB ng c γ ν0).1 hν0
  have hTie : ConcTie X Y := hctx.2.2
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u' hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u' := fun ν =>
    if h : ∃ t, OccT Y u u' c γ t ∧ nmlOf Y u u' t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν →
      OccT Y u u' c γ (pick ν) ∧ nmlOf Y u u' (pick ν) = ν := by
    intro ν hν
    have h := (occ_iff Y u u' νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u' t0 (pick ν), coefA' Y u u' t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (relC_of_occ hTie ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u' hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (relC_of_occ hTie ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u' hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (relC_of_occ hTie ht0 hp1) (relC_of_occ hTie ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobMoveOf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerConj
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def locL (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) * A.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a))
  | some g => glue g.e (Matrix.diagonal (cf Zd p) * A.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))
      (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p))

def locR (p : PlF D) (A B : PairVal.MatR D) : MatP D p :=
  match (Zd.M p).split with
  | none => Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) * B.map (D.s.atP p).ιE *
      Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))
  | some g => glue g.e (Matrix.diagonal (cfi Zd p) * B.map ((p1 g.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))
      (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 g.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p))

theorem tr_lem {K : Type*} [CommRing K] {n : ℕ} (S L X B : Matrix (Fin n) (Fin n) K) (hS : S * S = 1)
    (hSt : S.transpose = S) :
    (L * (X * S) * B * S).transpose * S = (S * B.transpose * S) * (X.transpose * S) * (S * L.transpose * S) := by
  simp only [Matrix.transpose_mul, hSt, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc S S, hS, Matrix.one_mul]

theorem corner_conj {K : Type*} [CommRing K] {r : ℕ} {L U Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hL : IsLo L)
    (hU : IsUp U) (c : K) : L * (Y - c • Ecorner r) * U = L * Y * U - c • Ecorner r := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU]

theorem locMove (u u' : D.what₂.Word) (p : PlF D) {Z₁ Z₂ A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B)
    (h : Z₂ * Sg D.host.E D.R.rS = A * (Z₁ * Sg D.host.E D.R.rS) * B) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p =
      locL Zd p A B * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A B := by
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  · set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)
    set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)
    have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
    rw [zzp_sgn_ord Zd u u' p hM Z₂, zzp_sgn_ord Zd u u' p hM Z₁, h, Matrix.map_mul, Matrix.map_mul,
      regroup fr fri hfr]
    simp only [locL, locR, hM]
    rfl
  · obtain ⟨hge, hgq⟩ := hAg
    have hcc : ∀ a, cf Zd p a * cfi Zd p a = 1 := cf_cfi Zd p
    have hcc' : ∀ a, cfi Zd p a * cf Zd p a = 1 := cfi_cf Zd p
    have hL1 : IsLo (Matrix.diagonal (cf Zd p) * A.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p)) :=
      isLo_conj (isLo_map _ hA) _ _ hcc
    have hU1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) :=
      isUp_conj (isUp_map _ hB) _ _ hcc'
    have hL2a : IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hU2a : IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
        Sg (D.s.atP p).Fp D.R.rS) :=
      (isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hA)) _ _ (fun a => sgn_sq' D.R.rS a) :
        IsUp (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    have hL2 := isLo_conj hL2a (cf Zd p) (cfi Zd p) hcc
    have hU2 := isUp_conj hU2a (cfi Zd p) (cf Zd p) hcc'
    have hZ2 : Z₂ = A * (Z₁ * Sg D.host.E D.R.rS) * B * Sg D.host.E D.R.rS := by
      rw [← h, Matrix.mul_assoc, sg_sq, Matrix.mul_one]
    simp only [locL, locR, hM, hge]
    apply mat_eq sg.e
    · have l1 := zz1' Zd p sg hR g hM hge hgq u u' Z₂
      have r1 := zz1' Zd p sg hR g hM hge hgq u u' Z₁
      have key1 : (A * (Z₁ * Sg D.host.E D.R.rS) * B).map ((p1 sg.e).comp (D.s.atP p).ιE) =
          A.map ((p1 sg.e).comp (D.s.atP p).ιE) * (Z₁ * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) *
            B.map ((p1 sg.e).comp (D.s.atP p).ιE) := by simp only [Matrix.map_mul]
      rw [h, key1, fact1 (cf Zd p) (cfi Zd p) hcc'] at l1
      refine l1.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, r1, corner_conj hL1 hU1]
    · have e2 : (Z₂.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS =
          (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            ((Z₁.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
            (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
        rw [hZ2, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
        exact tr_lem _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _)
      have l2 := zz2' Zd p sg hR g hM hge hgq u u' Z₂
      have r2 := zz2' Zd p sg hR g hM hge hgq u u' Z₁
      rw [e2, fact1 (cf Zd p) (cfi Zd p) hcc'] at l2
      refine l2.trans ?_
      conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, r2, corner_conj hL2 hU2]

end Formalism.L2.SG.Pf.TupGlob
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def StabApprox (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z₁ A₀ B₀ : PairVal.MatR D), AtMat w Z₁ → IsLo A₀ → IsUp B₀ →
    (∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) →
    ∃ X Y : PairVal.MatR D, IsLo X ∧ IsUp Y ∧
      X * (Z₁ * Sg D.host.E D.R.rS) * Y = Z₁ * Sg D.host.E D.R.rS ∧
      ∀ p, TieN.IntLow (Zd.M p) (locL Zd p (A₀ * X) (Y * B₀)) ∧ TieN.IntUp (Zd.M p) (locR Zd p (A₀ * X) (Y * B₀))

def Dict : Prop :=
  ∀ A B : PairVal.MatR D, IsLo A → IsUp B →
    (∀ p, TieN.IntLow (Zd.M p) (locL Zd p A B) ∧ TieN.IntUp (Zd.M p) (locR Zd p A B)) →
    IntFr A.conjTranspose ∧ IntFr (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS) ∧
      TieG A.conjTranspose (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS)

variable {Zd}

theorem isUpUni_of {K : Type*} [CommRing K] {n : ℕ} {U : Matrix (Fin n) (Fin n) K} (h : IsUp U) : IsUpUni U :=
  fun i j => ⟨fun hji => h.2 j i hji, by rintro rfl; exact h.1 i⟩

theorem isUp_conjT {n : ℕ} {A : Matrix (Fin n) (Fin n) D.host.E} (h : IsLo A) : IsUp A.conjTranspose :=
  ⟨fun a => by simp [Matrix.conjTranspose_apply, h.1 a],
    fun a b hab => by simp [Matrix.conjTranspose_apply, h.2 a b hab]⟩

theorem globMove_of (u u' : D.what₂.Word) (hS : StabApprox Zd u u') (hD : Dict Zd) : GlobMove D Zd.M Zd.δ u u' := by
  intro w Z₁ Z₂ _ hZ₁ hZ₂ htup
  have hZ₁' := hZ₁
  obtain ⟨L1, U1, hL1, hU1, e1⟩ := hZ₁
  obtain ⟨L2, U2, hL2, hU2, e2⟩ := hZ₂
  rw [Formalism.L2.SG.Pf.AtPt.zhatOM_eq] at e1 e2
  have lo : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsLoUni L → Formalism.DoubleCosetMeasures.IsLowUni L :=
    fun L h => ⟨fun i j hij => (h i j).1 hij, fun a => (h a a).2 rfl⟩
  have up : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni U → Formalism.DoubleCosetMeasures.IsUpUni U :=
    fun U h => ⟨fun i j hji => (h i j).1 hji, fun a => (h a a).2 rfl⟩
  have lo' : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L → IsLo L :=
    fun L h => ⟨h.2, fun a b hab => h.1 hab⟩
  have up' : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U → IsUp U :=
    fun U h => ⟨h.2, fun a b hab => h.1 hab⟩
  have detL : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L →
      IsUnit L.det := fun L h => by
    rw [Matrix.det_of_lowerTriangular L h.1]
    simp [h.2]
  have detU : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U →
      IsUnit U.det := fun U h => by
    rw [Matrix.det_of_upperTriangular h.1]
    simp [h.2]
  have hA₀lo : IsLo (L2 * L1⁻¹) :=
    isLo_mul (lo' _ (lo _ hL2)) (lo' _ (Formalism.DoubleCosetMeasures.isLowUni_inv (hx := lo _ hL1)))
  have hB₀up : IsUp (U1⁻¹ * U2) :=
    isUp_mul (up' _ (Formalism.DoubleCosetMeasures.isUpUni_inv (hx := up _ hU1))) (up' _ (up _ hU2))
  have hmove : Z₂ * Sg D.host.E D.R.rS = (L2 * L1⁻¹) * (Z₁ * Sg D.host.E D.R.rS) * (U1⁻¹ * U2) := by
    rw [e2, e1]
    have i1 : L1⁻¹ * L1 = 1 := Matrix.nonsing_inv_mul L1 (detL _ (lo _ hL1))
    have i2 : U1 * U1⁻¹ = 1 := Matrix.mul_nonsing_inv U1 (detU _ (up _ hU1))
    calc L2 * ptMat w * U2 = L2 * (L1⁻¹ * L1) * ptMat w * ((U1 * U1⁻¹) * U2) := by
          rw [i1, i2, Matrix.mul_one, Matrix.one_mul]
      _ = L2 * L1⁻¹ * (L1 * ptMat w * U1) * (U1⁻¹ * U2) := by simp only [Matrix.mul_assoc]
  have hstab : ∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) *
          locR Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ := by
    intro p
    have hmem := mem_kkOrb_self (M := Zd.M) p (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p)
    have ht := htup p
    unfold tupZ at ht
    rw [← ht] at hmem
    obtain ⟨l, ρ, hl, hρ, heq⟩ := hmem
    refine ⟨l, ρ, hl, hρ, ?_⟩
    rw [← locMove (Zd := Zd) u u' p hA₀lo hB₀up hmove]
    exact heq
  obtain ⟨X, Y, hX, hY, hXY, hint⟩ := hS w Z₁ (L2 * L1⁻¹) (U1⁻¹ * U2) hZ₁' hA₀lo hB₀up hstab
  obtain ⟨hIA, hIB, hT⟩ := hD (L2 * L1⁻¹ * X) (Y * (U1⁻¹ * U2)) (isLo_mul hA₀lo hX) (isUp_mul hY hB₀up) hint
  have hSg : Sg D.host.E D.R.rS =
      Matrix.diagonal (fun b : Fin (D.R.rS + 1) => (-1 : D.host.E) ^ (D.R.rS - b.val)) := by
    have h1 := (Formalism.L2.SG.Pf.AtPt.zhatOM_eq (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).symm.trans
      (Formalism.L2.SG.Pf.zhatOM_eq_pv 1)
    simpa using h1
  have hsq : ∀ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - b.val) * (-1 : D.host.E) ^ (D.R.rS - b.val) = 1 := by
    intro b
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hSS : Sg D.host.E D.R.rS * Sg D.host.E D.R.rS = 1 := by
    rw [hSg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact hsq b
  refine ⟨(L2 * L1⁻¹ * X).conjTranspose, Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS,
    isUpUni_of (isUp_conjT (isLo_mul hA₀lo hX)), isUpUni_of ?_, hIA, hIB, hT, ?_⟩
  · rw [hSg]
    exact isUp_conj (isUp_mul hY hB₀up) _ _ hsq
  · rw [Matrix.conjTranspose_conjTranspose]
    have h3 : Z₂ * Sg D.host.E D.R.rS =
        L2 * L1⁻¹ * X * (Z₁ * Sg D.host.E D.R.rS) * (Y * (U1⁻¹ * U2)) := by
      rw [hmove]
      conv_lhs => rw [← hXY]
      simp only [Matrix.mul_assoc]
    calc Z₂ = Z₂ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      _ = L2 * L1⁻¹ * X * Z₁ * (Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS) := by
          rw [h3]
          simp only [Matrix.mul_assoc]

end Formalism.L2.SG.Pf.TupGlob
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataTies
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol MeasureTheory

theorem typFacts_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u u' : D.what₂.Word) : TypFacts X u u' := by
  apply typFacts_of (h1 := gSplitX_holds X) (h3 := Formalism.L2.SG.LocVolKap.kapX X hb u u')
  exact tCongX X u u'

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Gam1TieCHolds
noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.MassDataConc MeasureTheory
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem Gam1TieC_holds (Y : Formalism.L2.SG.Full.Full X) :
    LevelOneLatticeAgreement X hb hK FdN FdN' u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq := by
  unfold LevelOneLatticeAgreement
  show Formalism.L2.SG.TermOp.Gam1 Y.TR = _
  rw [Formalism.L2.SG.Pf.gamma_one_typed_places_holds X Y.TR]
  rfl

end Formalism.L2.SG.IntegralApproximation
end
end
