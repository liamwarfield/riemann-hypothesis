module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixExistsFixedFrobeniusSolution

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBasicOfEquiv
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem acris_basic : ∀ (l : ℕ) [Fact l.Prime], (∀ x : Formalism.Per.Acris l, ((l : ℕ) : Formalism.Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : Formalism.Per.Acris l)}) (Formalism.Per.Acris l) ∧ (∀ (k : ℕ) (x : Formalism.Per.Acris l), ∃ d : ↥(Formalism.Per.Acris0 l), x - algebraMap ↥(Formalism.Per.Acris0 l) (Formalism.Per.Acris l) d ∈ Ideal.span {((l : ℕ) : Formalism.Per.Acris l) ^ k}) ∧ ∀ (k : ℕ) (d : ↥(Formalism.Per.Acris0 l)), algebraMap ↥(Formalism.Per.Acris0 l) (Formalism.Per.Acris l) d ∈ Ideal.span {((l : ℕ) : Formalism.Per.Acris l) ^ k} ↔ d ∈ Ideal.span {((l : ℕ) : ↥(Formalism.Per.Acris0 l)) ^ k} := by
  intro l _
  obtain ⟨hc, ht, hd, hv⟩ := GlobalTheory.MemLoc.acris_basic l
  refine ⟨ht, hc, fun k x => ?_, fun k d => ?_⟩
  · obtain ⟨s, z, hz⟩ := hd x k
    exact ⟨s, Ideal.mem_span_singleton.2 ⟨z, by rw [hz, add_sub_cancel_left]⟩⟩
  · rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    exact hv d k

end GlobalTheory.Per
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusProperties
attribute [local irreducible] Formalism.Per.σC Formalism.Per.σO Formalism.Per.φA Formalism.Per.zA Formalism.Per.AinfP Formalism.Per.zP Formalism.Per.toC Formalism.Per.θP Formalism.Per.kerP Formalism.Per.ev Formalism.Per.FilP Formalism.Per.θD Formalism.Per.pD Formalism.Per.zD Formalism.Per.FilD Formalism.Per.Acris0 Formalism.Per.Acris Formalism.Per.Bcris Formalism.Per.aB Formalism.Per.a0B Formalism.Per.zB Formalism.Per.φB Formalism.Per.σF Formalism.Per.σA Formalism.Per.extP Formalism.Per.σDp Formalism.Per.σD Formalism.Per.σB Formalism.Per.IsLog

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisFrobE

open scoped Nat

theorem pow_mul_factorial_dvd (l : ℕ) (hl : 0 < l) : ∀ n : ℕ, l ^ n * n ! ∣ (l * n)!
  | 0 => by simp
  | n + 1 => by
    have ih := pow_mul_factorial_dvd l hl n
    have e : l * (n + 1) = (l * n + (l - 1)) + 1 := by rw [Nat.mul_succ]; omega
    have h2 : (l * n)! ∣ (l * n + (l - 1))! := Nat.factorial_dvd_factorial (by omega)
    have e2 : l ^ (n + 1) * (n + 1)! = (l * n + (l - 1) + 1) * (l ^ n * n !) := by
      rw [← e, Nat.factorial_succ, pow_succ]; ring
    rw [e2, e, Nat.factorial_succ]
    exact Nat.mul_dvd_mul_left _ (ih.trans h2)

theorem pow_succ_dvd_factorial (l : ℕ) (hl : 0 < l) : l ^ (l + 1) ∣ (l * l)! := by
  refine dvd_trans ?_ (pow_mul_factorial_dvd l hl l)
  rw [pow_succ]
  exact Nat.mul_dvd_mul_left _ (Nat.dvd_factorial hl le_rfl)

variable (l : ℕ) [Fact l.Prime]

theorem isUnit_natCast_ainfP (n : ℕ) (hn : n ≠ 0) : IsUnit (n : Formalism.Per.AinfP l) :=
  GlobalTheory.AcrisDiscExt.isUnit_natCast_of (l := l) ((algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)).comp (Formalism.Per.zA l))
    (by
      have := IsLocalization.Away.algebraMap_isUnit (S := Formalism.Per.AinfP l) (l : Formalism.Per.Ainf l)
      simpa using this) n hn

end GlobalTheory.AcrisFrobE

namespace GlobalTheory.AcrisFrobE
open scoped Nat
variable (l : ℕ) [Fact l.Prime]

theorem coe_natCast0 (k : ℕ) : ((k : Formalism.Per.Acris0 l) : Formalism.Per.AinfP l) = k :=
  map_natCast (Formalism.Per.Acris0 l).val k

theorem exists_dpow (x : Formalism.Per.Ainf l) (hx : Formalism.Per.θ l x = 0) (n : ℕ) :
    ∃ d : Formalism.Per.Acris0 l, ((n ! : ℕ) : Formalism.Per.AinfP l) * (d : Formalism.Per.AinfP l) =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n := by
  obtain ⟨u, hu⟩ := isUnit_natCast_ainfP l (n !) (Nat.factorial_ne_zero n)
  have key : ((n ! : ℕ) : Formalism.Per.AinfP l) *
      (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n * ((u⁻¹ : (Formalism.Per.AinfP l)ˣ) : Formalism.Per.AinfP l)) =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n := by
    rw [← hu, mul_comm, mul_assoc, Units.inv_mul, mul_one]
  exact ⟨⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l x n _ hx key⟩, key⟩

theorem exists_div_l (x : Formalism.Per.Ainf l) (hx : Formalism.Per.θ l x = 0) :
    ∃ y w : Formalism.Per.Acris0 l, (l : Formalism.Per.Acris0 l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) x ^ l ∧
      y ^ l = (l : Formalism.Per.Acris0 l) * w := by
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  set X := algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x with hX
  obtain ⟨g, hg⟩ := exists_dpow l x hx l
  obtain ⟨d, hd⟩ := exists_dpow l x hx (l * l)
  obtain ⟨m, hm⟩ := pow_succ_dvd_factorial l hl0
  have e : l * (l - 1)! = l ! := Nat.mul_factorial_pred hl0.ne'
  refine ⟨(((l - 1)! : ℕ) : Formalism.Per.Acris0 l) * g, (m : Formalism.Per.Acris0 l) * d, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, coe_natCast0,
      coe_natCast0, ← hX, ← hg, ← mul_assoc, ← Nat.cast_mul, e]
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_mul, coe_natCast0,
      coe_natCast0, coe_natCast0]
    refine ((isUnit_natCast_ainfP l (l ^ l) (pow_ne_zero _ hl0.ne')).mul_right_inj).1 ?_
    have h1 : ((l ^ l : ℕ) : Formalism.Per.AinfP l) * ((((l - 1)! : ℕ) : Formalism.Per.AinfP l) * (g : Formalism.Per.AinfP l)) ^ l =
        X ^ (l * l) := by
      rw [pow_mul, ← hg, ← e, Nat.cast_mul, Nat.cast_pow, ← mul_pow]; ring
    rw [h1, ← hd, hm]
    push_cast; ring

end GlobalTheory.AcrisFrobE

namespace GlobalTheory.AcrisFrobE

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∃ v : (Per.Acris l)ˣ, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a bk.E) = (l : Per.Acris l) * v) ∧ (∀ a : Ainf l, phiA l ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (WittVector.frobenius a)) ∧ ∀ (g : GQ l) (a : Ainf l), sigA g ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (Per.σA g a) := by
  intro l _ K bk
  obtain ⟨htor, hcomp, -, -⟩ := GlobalTheory.Per.acris_basic l
  haveI := hcomp
  refine ⟨htor, hcomp, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := bk.isUnit_δ
    have hφ : frobS l bk.a bk.E = bk.E ^ l + (l : bk.S) * (u : bk.S) := by
      rw [hu]; exact (deltaS l bk.a).φ_eq bk.E
    have hx : Formalism.Per.θ l (bk.ev bk.E) = 0 := by
      have h : bk.ev bk.E ∈ RingHom.ker (Formalism.Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact h
    obtain ⟨y, w, hy, hw⟩ := exists_div_l l _ hx
    set j := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) with hj
    set a := algebraMap (Ainf l) (Formalism.Per.Acris l) with ha_def
    have ha : ∀ t, a t = j (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) t) :=
      fun t => GlobalTheory.RingIface.tower l t
    set A : Formalism.Per.Acris l := a (bk.ev (u : bk.S)) with hA
    have hAu : IsUnit A := (u.isUnit.map bk.ev).map a
    obtain ⟨U, hU⟩ := hAu
    set Y := j y with hY
    set z := ((U⁻¹ : (Formalism.Per.Acris l)ˣ) : Formalism.Per.Acris l) * Y with hz_def
    have hz : z ^ l ∈ Ideal.span {(l : Formalism.Per.Acris l)} := by
      rw [hz_def, mul_pow, show Y ^ l = (l : Formalism.Per.Acris l) * j w by rw [hY, ← map_pow, hw, map_mul, map_natCast]]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    have hJ : (-z) ^ l ∈ (⊥ : Ideal (Formalism.Per.Acris l)).jacobson := by
      refine IsAdicComplete.le_jacobson_bot (Ideal.span {(l : Formalism.Per.Acris l)}) ?_
      rw [neg_pow]; exact Ideal.mul_mem_left _ _ hz
    have h1 : IsUnit (1 - (-z) ^ l) := by
      have := Ideal.mem_jacobson_bot.1 hJ (-1)
      rwa [mul_neg_one, neg_add_eq_sub] at this
    have h2 : IsUnit (1 + z) := by
      rw [← mul_neg_geom_sum, sub_neg_eq_add] at h1
      exact isUnit_of_mul_isUnit_left h1
    obtain ⟨V, hV⟩ := h2
    refine ⟨U * V, ?_⟩
    have hUU : (U : Formalism.Per.Acris l) * ((U⁻¹ : (Formalism.Per.Acris l)ˣ) : Formalism.Per.Acris l) = 1 := U.mul_inv
    have hxl : a (bk.ev bk.E) ^ l = (l : Formalism.Per.Acris l) * Y := by
      rw [ha, ← map_pow, ← hy, map_mul, map_natCast]
    rw [RingHom.comp_apply, hφ, map_add (f := _), map_mul, map_pow, map_natCast, map_add (f := _), map_pow, map_mul, map_natCast, hxl,
      Units.val_mul, hV, hU, hz_def]
    rw [← hA]
    rw [hU] at hUU
    linear_combination (-(l : Formalism.Per.Acris l) * Y) * hUU
  · intro a
    rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
    congr 1
    ext n
    rw [GlobalTheory.RingIface.phiA_coeff l a n, WittVector.coeff_frobenius_charP]
  · intro g a
    rw [(GlobalTheory.CrisMaps.sigA_extends g).alg]

end GlobalTheory.AcrisFrobE
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_torsionFree_complete_frobenius_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∃ v : (Per.Acris l)ˣ, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a bk.E) = (l : Per.Acris l) * v) ∧ (∀ a : Ainf l, phiA l ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (WittVector.frobenius a)) ∧ ∀ (g : GQ l) (a : Ainf l), sigA g ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (Per.σA g a) := by
  first | exact @GlobalTheory.AcrisFrobE.main | exact GlobalTheory.AcrisFrobE.main | (intros; apply GlobalTheory.AcrisFrobE.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnivCharWithUnivChar
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwistDet

namespace GlobalTheory.UnivChar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

section Chosen

def IsUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop :=
  ∀ i Q M, Y.delU i Q M = GalChar.delU D.host X.cc (X.l i) Q M

def withUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun i Q M => GalChar.delU D.host X.cc (X.l i) Q M
    delU_unr := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).1
    delU_l := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.1
    delU_anti := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.1
    delU_open := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.1
    delU_res := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.1
    delU_conj := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.1 }

end Chosen

section Family


variable (X) in
abbrev Fam (i : X.Tw) (M : ℕ) : Type := PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))

variable {i : X.Tw} {M : ℕ} (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (d : Fam X i M)



variable {H S d}

end Family

section Record

variable {H : X.Tw → ℕ → Subgroup (GE N)} {S : X.Tw → ℕ → Finset (PlE D.host)} {d : ∀ i M, Fam X i M}

end Record

theorem delUTie_of_isUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : K1 X → IsUnivChar Y → DelUTie Y :=
  fun hK hY => GalChar.delUTie_of_exists Y hY hK

end GlobalTheory.UnivChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisenstein
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisenstein
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isUnit_toDisc_frobS_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    IsUnit (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) := by
  intro l hl K bk
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hl0 : (0 : ℝ) < l := by linarith
  have hE : ‖toDisc l (X : bk.S) bk.ρ₀ bk.E‖ ≤ (l : ℝ)⁻¹ := (GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk bk.S (RingHom.id _)).2.2.2
  obtain ⟨v, hv⟩ := bk.isUnit_δ
  have hφ : frobS l bk.a bk.E = bk.E ^ l + (l : bk.S) * (v : bk.S) := by
    rw [hv]; exact (deltaS l bk.a).φ_eq bk.E
  set t := toDisc l (X : bk.S) bk.ρ₀ with ht
  set i : Disc l (X : bk.S) bk.ρ₀ := ofPre l (X : bk.S) bk.ρ₀ (IsLocalization.Away.invSelf (l : bk.S)) with hi
  have hLi : (l : Disc l (X : bk.S) bk.ρ₀) * i = 1 := by
    rw [hi, ← map_natCast (ofPre l (X : bk.S) bk.ρ₀), ← map_mul,
      ← map_natCast (algebraMap bk.S (PreDisc l (X : bk.S) bk.ρ₀)), IsLocalization.Away.mul_invSelf, map_one]
  have hni : ‖i‖ ≤ l := by
    rw [hi, norm_ofPre]
    exact gauge_le l _ _ hl0 (Submodule.subset_span ⟨0, 0, 1, by simp, by simp⟩)
  have hw : t v * t ↑v⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  set z := i * t ↑v⁻¹ * t bk.E ^ l with hz
  have hnz : ‖z‖ < 1 := by
    have h1 : ‖t bk.E ^ l‖ ≤ (l : ℝ)⁻¹ ^ l :=
      (norm_pow_le' _ hl.out.pos).trans (pow_le_pow_left₀ (norm_nonneg _) hE l)
    have h2 : (l : ℝ)⁻¹ ^ l ≤ (l : ℝ)⁻¹ ^ 2 :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by linarith)) (by exact_mod_cast hl.out.two_le)
    calc ‖z‖ ≤ ‖i‖ * ‖t ↑v⁻¹‖ * ‖t bk.E ^ l‖ := by
            rw [hz]; exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (l : ℝ) * 1 * (l : ℝ)⁻¹ ^ 2 := by
            gcongr
            · exact norm_toDisc_le _
            · exact h1.trans h2
      _ = (l : ℝ)⁻¹ := by field_simp
      _ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have key : t (frobS l bk.a bk.E) = (l : Disc l (X : bk.S) bk.ρ₀) * t v * (1 - (-z)) := by
    rw [hφ, map_add (f := _), map_mul, map_pow, map_natCast, hz]
    linear_combination (-(t bk.E ^ l) * (t v * t ↑v⁻¹)) * hLi + (-(t bk.E ^ l)) * hw
  rw [key]
  exact ((isUnit_l_disc l (X : bk.S) bk.ρ₀).mul ((Units.isUnit v).map t)).mul
    ⟨Units.oneSub (-z) (by rwa [norm_neg]), rfl⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitClosedDiscFrobeniusEisensteinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsUnit (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) := by
  first | exact @GlobalTheory.BSP.isUnit_toDisc_frobS_E | exact GlobalTheory.BSP.isUnit_toDisc_frobS_E | (intros; apply GlobalTheory.BSP.isUnit_toDisc_frobS_E <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

variable {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}

def tup {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) : Fin m → Matrix (Fin a) (Fin a) (Om l) :=
  fun k => ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))

def latL {m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ) :
    Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
  Submodule.span ℤ_[l] (⋃ k, (fun x => Pi.single k ((l : Om l) ^ M • x)) '' (t k : Set (Matrix (Fin a) (Fin a) (Om l))))

def latT {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ) :
    Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
  Submodule.span ℤ_[l] (Set.range (tup ρs)) ⊔ latL t M

def Carries (r : Γ →* GL (Fin a) (Om l)) {d d' m : ℕ} (b : Fin d → Matrix (Fin a) (Fin a) (Om l))
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ)
    (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)) (P : Matrix (Fin d) (Fin d') ℤ_[l]) (N : ℕ) : Prop :=
  ∀ (z : Fin d' → ℤ_[l]) (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ latL t M →
    ∑ s, zOm l (z s) • bb s = (F.sum fun g c => zOm l c • tup ρs g) + y →
    ∃ w : Fin d → ℤ_[l], ∑ i, zOm l ((P *ᵥ z) i) • b i =
      (F.sum fun g c => zOm l c • ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) +
        (l : Om l) ^ N • ∑ i, zOm l (w i) • b i

theorem zOm_smul {α : Type} [AddCommGroup α] [Module (Om l) α] [Module ℤ_[l] α] [IsScalarTower ℤ_[l] (Om l) α]
    (c : ℤ_[l]) (x : α) : zOm l c • x = c • x := by
  rw [← algebraMap_smul (Om l) c x]
  congr 1

theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l))]
  exact (PadicAlgCl.norm_extends l (l : ℚ_[l])).trans Padic.norm_p

theorem norm_zOm_le (c : ℤ_[l]) : ‖zOm l c‖ ≤ 1 := by
  simp only [zOm, RingHom.comp_apply]
  exact (PadicAlgCl.norm_extends l _).trans_le (PadicInt.norm_le_one c)

theorem tup_mem_latT {m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (M : ℕ) (g : Γ) : tup ρs g ∈ latT ρs t M :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨g, rfl⟩)

theorem traceL : ∀ (l : ℕ) [Fact l.Prime] (a d : ℕ) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)), ∃ K : ℕ, ∀ w : Fin d → ℤ_[l], ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ (l : ℝ) ^ K := by
  intro l _ a d b
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (∑ i, ‖(b i).trace‖) (show (1 : ℝ) < l by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine ⟨K, fun w => ?_⟩
  rw [Matrix.trace_sum]
  refine (norm_sum_le _ _).trans (le_trans ?_ hK.le)
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_zOm_le _)

end GlobalTheory.TraceConjugationCover

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixOfStabilizerTrivial
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass
open scoped Pointwise

noncomputable section

namespace GlobalTheory.TypeDegOne

theorem fix_of_stabilizer_trivial {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    (c : E →+* PadicAlgCl l) (P : Ideal (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ P ↔ ‖c (x : E)‖ < 1)
    (hP : ∀ σ : E ≃ₐ[ℚ] E, σ • P = P → σ = 1) (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : E) :
    τ (c x) = c x := by
  letI : Algebra E (PadicAlgCl l) := c.toAlgebra
  haveI : IsScalarTower ℚ E (PadicAlgCl l) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let φ : E →ₐ[ℚ] PadicAlgCl l := ((τ : PadicAlgCl l →+* PadicAlgCl l).comp c).toRatAlgHom
  let σ : E ≃ₐ[ℚ] E := φ.restrictNormal' E
  have hσ : ∀ y, c (σ y) = τ (c y) := fun y => φ.restrictNormal_commutes E y
  have h1 : σ⁻¹ • P = P := by
    ext y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, hc, hc]
    have e : ((σ • y : 𝓞 E) : E) = σ (y : E) := rfl
    have hn : ‖τ (c y)‖ = ‖c y‖ := (spectralNorm_eq_of_equiv τ _).symm
    rw [e, hσ, hn]
  have h2 : σ = 1 := inv_eq_one.1 (hP _ h1)
  rw [← hσ, h2]
  rfl

theorem eq_bot_of_subset_closure {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (S : Set (PadicAlgCl l)) (hK : (K : Set (PadicAlgCl l)) ⊆ closure S)
    (hS : ∀ (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ y ∈ S, τ y = y) : K = ⊥ := by
  haveI : IsGalois ℚ_[l] (PadicAlgCl l) := IsAlgClosure.isGalois _ _
  refine eq_bot_iff.2 fun y hy => (InfiniteGalois.mem_bot_iff_fixed y).2 fun τ => ?_
  have hc : Continuous τ :=
    (AddMonoidHomClass.isometry_of_norm τ fun x => (spectralNorm_eq_of_equiv τ x).symm).continuous
  exact closure_minimal (fun y hy => hS τ y hy) (isClosed_eq hc continuous_id) (hK hy)

theorem mem_place_iff (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : 𝓞 D.host.E) :
    x ∈ w.asIdeal ↔ ‖(D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (x : D.host.E))‖ < 1 := by
  rw [← D.nd.plOm.2 w x]
  set y := algebraMap D.host.E D.nd.Om (x : D.host.E)
  by_cases hy : y = 0
  · simp [hy]
  have hj : 0 < ‖(D.nbr i w hw).j y‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 hy)
  have h := D.nbr_ind i w hw y⁻¹
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hj,
    inv_le_one₀ (zero_lt_iff.2 ((_root_.map_ne_zero _).2 hy))] at h
  rw [← not_le, ← not_le, h]

theorem degree_one : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → (placesOver D.host.E (D.nd.l i)).ncard = 2 * D.R.f ∧ ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 := by
  intro D i k hk
  have hs : (placesOver D.host.E (D.nd.l i)).ncard = finrank ℚ D.host.E := by
    rw [hk]; exact D.nd.g_split k
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  refine ⟨?_, fun w hw => ?_⟩
  · have h1 : finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
    have h5 : D.R.f = 2 * D.R.ord := rfl
    rw [hs, h1, h5]; ring
  · have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.nd.l i) Fact.out hs w hw).2.2
    have hb : (D.nbr i w hw).Kw.1 = ⊥ := by
      refine eq_bot_of_subset_closure _ _ (D.nbr i w hw).j_dense ?_
      rintro τ _ ⟨x, rfl⟩
      exact fix_of_stabilizer_trivial ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) w.asIdeal
        (mem_place_iff D i w hw) hP τ x
    exact IntermediateField.finrank_eq_one_iff.2 hb

end GlobalTheory.TypeDegOne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatDescentElementsPushout
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatDescentElementsPushout
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem ff_descent_elem_pushout : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), f.FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → Function.Injective f ∧ ∀ b, p b = q b → b ∈ f.range := by
  intro A B D _ _ _ f p q hf hpo
  refine ⟨hf.injective, fun b hb => ?_⟩
  letI : Algebra A B := f.toAlgebra
  haveI : Module.FaithfullyFlat A B := hf

  have hw : CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom f)
        (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := B))) =
      CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom f)
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom) := by
    ext a
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) (A := B) (B := B) a
  have e := congrArg (fun x => (hpo.desc _ _ hw).hom x) hb
  have e1 := congrArg (fun g => g.hom b) (hpo.inl_desc _ _ hw)
  have e2 := congrArg (fun g => g.hom b) (hpo.inr_desc _ _ hw)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e e1 e2

  have key : b ∈ (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := B)).eqLocus
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom :=
    e1.symm.trans (e.trans e2)
  have hmem := (Algebra.IsEffective.of_faithfullyFlat A B).eqLocus_includeLeft_includeRight ▸
    SetLike.mem_coe.mpr key
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatDescentElementsPushoutStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faithfullyFlat_descent_elements_pushout : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), f.FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → Function.Injective f ∧ ∀ b, p b = q b → b ∈ f.range := by
  first | exact @GlobalTheory.BSP.ff_descent_elem_pushout | exact GlobalTheory.BSP.ff_descent_elem_pushout | (intros; apply GlobalTheory.BSP.ff_descent_elem_pushout <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescent
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem eq_zero_of_mem_adI_pow {l : ℕ} {R : Type} [CommRing R] (B : Obj l R) (x : B.A)
    (hx : ∀ n : ℕ, x ∈ adI B ^ n) : x = 0 := by
  refine B.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact hx n

theorem cover_injective_and_descent : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C),
    Cover h → Function.Injective h.f ∧ ∀ (D : Obj l R) (p q : Hom C D), IsPO h h p q →
      ∀ c, p.f c = q.f c → c ∈ h.f.range := by
  intro l _ R _ B C h hc

  have hinj : ∀ m : ℕ, Function.Injective (qmap h m) := fun m =>
    RingHom.FaithfullyFlat.injective (hc.ff m)

  have hlev : ∀ (m : ℕ) (b : B.A), h.f b ∈ adI C ^ m → b ∈ adI B ^ m := fun m b hb => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hinj m
    rw [qmap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  refine ⟨fun x y hxy => ?_, fun D p q hpo c hpq => ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow B _ fun n => hlev n _ ?_
    rw [map_sub, hxy, sub_self]; exact Ideal.zero_mem _
  ·
    have happ : ∀ m : ℕ, ∃ b : B.A, h.f b - c ∈ adI C ^ m := fun m => by
      have hd := (GlobalTheory.T.faithfullyFlat_descent_elements_pushout _ _ _ (qmap h m) (qmap p m) (qmap q m) (hc.ff m) (hpo.po m)).2
        (Ideal.Quotient.mk _ c) (by rw [qmap_mk, qmap_mk, hpq])
      obtain ⟨b', hb'⟩ := hd
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      refine ⟨b, ?_⟩
      rw [qmap_mk, Ideal.Quotient.eq] at hb'
      exact hb'
    choose b hb using happ
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (adI B ^ m • ⊤ : Submodule B.A B.A)] := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      refine hlev m _ ?_
      have e : h.f (b m - b n) = (h.f (b m) - c) - (h.f (b n) - c) := by rw [map_sub]; ring
      rw [e]
      exact Ideal.sub_mem _ (hb m) (Ideal.pow_le_pow_right hmn (hb n))
    obtain ⟨L, hL⟩ := B.complete.toIsPrecomplete.prec' b hcauchy
    refine ⟨L, ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow C _ fun n => ?_
    have h1 : b n - L ∈ adI B ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    have h2 : h.f (b n - L) ∈ adI C ^ n := adI_pow_le h n h1
    have e : h.f L - c = (h.f (b n) - c) - h.f (b n - L) := by rw [map_sub]; ring
    rw [e]
    exact Ideal.sub_mem _ (hb n) h2

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescentStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_cover_injective_and_descent : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h → Function.Injective h.f ∧ ∀ (D : Obj l R) (p q : Hom C D), IsPO h h p q → ∀ c, p.f c = q.f c → c ∈ h.f.range := by
  first | exact @GlobalTheory.BSP.cover_injective_and_descent | exact GlobalTheory.BSP.cover_injective_and_descent | (intros; apply GlobalTheory.BSP.cover_injective_and_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZero
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.ThetaPer

theorem thetaD_aDp_pow_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (n : ℕ), ((Per.θD l).comp (aDp l)) (τ ^ n) ≠ 0 := by
  intro l _ K bk τ hτ n
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hinj : Function.Injective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro x y h
    rw [WittVector.frobenius_eq_map_frobenius] at h
    exact WittVector.map_injective _ (frobeniusEquiv (OCb l) l).injective h
  have hpi : WittVector.frobenius (GlobalTheory.MemLoc.TiedUnif.piOne ε) = WittVector.teichmuller l ε - 1 := by
    rw [GlobalTheory.MemLoc.TiedUnif.piOne, map_sub, map_one, WittVector.frobenius_eq_map_frobenius]
    change WittVector.map (frobenius (OCb l) l) (WittVector.teichmuller l ((frobeniusEquiv (OCb l) l).symm ε)) - 1 = _
    rw [WittVector.map_teichmuller, frobenius_apply_frobeniusEquiv_symm]
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    intro y
    obtain ⟨x, hx⟩ := WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective y
    exact ⟨x, by rw [WittVector.frobenius_eq_map_frobenius]; exact hx⟩
  obtain ⟨η₀, hη₀⟩ := hsurj (η : Ainf l)
  obtain ⟨η₁, hη₁⟩ := hsurj ((η⁻¹ : (Ainf l)ˣ) : Ainf l)
  have hu : η₀ * η₁ = 1 := hinj (by rw [map_mul, map_one, hη₀, hη₁, Units.mul_inv])
  have hτe : τ = η₀ * GlobalTheory.MemLoc.TiedUnif.piOne ε := hinj (by rw [hφ, map_mul, hη₀, hpi])
  set f := (Per.θD l).comp (aDp l)
  have hf0 : f η₀ ≠ 0 := by
    intro h
    have := congrArg f hu
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hf1 : f (GlobalTheory.MemLoc.TiedUnif.piOne ε) ≠ 0 := GlobalTheory.MemLoc.TiedUnif.theta_piOne hε
  rw [map_pow, hτe, map_mul]
  exact pow_ne_zero _ (mul_ne_zero hf0 hf1)

end GlobalTheory.ThetaPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZeroStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_ainf_period_pow_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (n : ℕ), ((Per.θD l).comp (aDp l)) (τ ^ n) ≠ 0 := by
  first | exact @GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero | exact GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero | (intros; apply GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpMultiplicityRestrictFiniteExt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpMultiplicityRestrictFiniteExt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.JumpRestrict

open GlobalTheory.DRFil

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_inclusion (P : LocPrime l) {K K' : FinExt l} (h : K.1 ≤ K'.1) (c : ↥K.1) :
    algebraMap ↥K'.1 P.R.BdR (IntermediateField.inclusion h c) = algebraMap ↥K.1 P.R.BdR c := rfl

theorem idem_restrict_mul (P : LocPrime l) {K K' LL : FinExt l} (h : K.1 ≤ K'.1)
    (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) :
    haveI := K.2; haveI := K'.2
    idem (K := ↥K.1) P.R.BdR (τ.comp (IntermediateField.inclusion h)) * idem (K := ↥K'.1) P.R.BdR τ =
      idem (K := ↥K'.1) P.R.BdR τ := by
  haveI := K.2; haveI := K'.2
  obtain ⟨n, a, c, hrep, h1⟩ := idem_repr (K := ↥K.1) P.R.BdR (τ.comp (IntermediateField.inclusion h))
  have e := exists_smul_idem (K := ↥K'.1) (F := P.R.BdR) τ n a (fun i => IntermediateField.inclusion h (c i))
  simp only [algebraMap_inclusion] at e
  rw [hrep, mul_comm, e]
  simp only [AlgHom.comp_apply] at h1
  rw [h1, one_smul]

theorem multV_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ a = multV (P.PD K) ρ (τ.comp (IntermediateField.inclusion h)) a := by
  intro l _ P AI T K K' LL h V _ _ _ _ _ ρ hdr τ a
  haveI := K.2; haveI := K'.2; haveI := LL.2
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  obtain ⟨m, d, k, hA⟩ := exists_adapted (P.PD K) (isField_dR T) ρ (filSpans T K LL ρ hdr)
    (τ.comp (IntermediateField.inclusion h))
  have hI := idem_restrict_mul P h τ
  have hA' : Adapted (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ
      (fun i => sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ) (d i)) k := by
    refine ⟨fun i => ?_, fun r hr i => ?_, fun n y hy => ?_⟩
    · have hm := hA.mem i
      refine ⟨sm_idem_mem_DdRE (P.PD K') _ τ
        (GlobalTheory.Per.TiedRestrict.ddR_le h ρ (Submodule.mem_inf.1 (Submodule.mem_inf.1 hm).1).1), ?_⟩
      refine sm_idem_mem_FilV (P.PD K') τ ?_
      rw [GlobalTheory.JumpDescent.FilV_eq P K K']
      exact (Submodule.mem_inf.1 hm).2
    · have := hA.indep (fun i => r i * idem P.R.BdR τ) (by
        simpa only [sm_mul] using hr) i
      rw [mul_left_comm, hI] at this
      rw [mul_comm]; exact this
    · rw [GlobalTheory.JumpDescent.FilV_eq P K K'] at hy
      obtain ⟨r, hr, hy'⟩ := hA.span n y hy
      refine ⟨r, fun i => ?_, ?_⟩
      · rw [GlobalTheory.JumpDescent.FilV_eq P K K']; exact hr i
      · have e : sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ) y = sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ)
            (sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR (τ.comp (IntermediateField.inclusion h))) y) := by
          rw [← sm_mul, mul_comm, hI]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [e, hy', map_sum]
        exact Finset.sum_congr rfl fun i _ => sm_comm _ _ _
  rw [hA.multV_eq, hA'.multV_eq]

end GlobalTheory.JumpRestrict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeJumpMultiplicityRestrictFiniteExtStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeJumpMultiplicity_restrict_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ a = multV (P.PD K) ρ (τ.comp (IntermediateField.inclusion h)) a := by
  first | exact @GlobalTheory.JumpRestrict.multV_restrict | exact GlobalTheory.JumpRestrict.multV_restrict | (intros; apply GlobalTheory.JumpRestrict.multV_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitLeOfFamily
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.EtaFromCut

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths IsDiscreteValuationRing

section General

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [Fintype X]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)

theorem congMod_le_of_family (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Finset X)
    (E : Set (Module.End O M)) (a : X → O)
    (hc : ∀ α ∈ E, ∀ f : T, α * act f = act f * α)
    (h1 : ∀ x ∈ S, ∃ α ∈ E, ∀ u ∈ Vx T (actK T act).toRingHom x,
      α.baseChange (FractionRing O) u = a x • u)
    (h0 : ∀ α ∈ E, ∀ x, x ∉ S → ∀ u ∈ Vx T (actK T act).toRingHom x,
      α.baseChange (FractionRing O) u = 0) :
    Module.length O (CongMod T (actK T act).toRingHom (latIn O M) (S : Set X)) ≤
      ∑ x ∈ S, (finrank (FractionRing O) (Vx T (actK T act).toRingHom x) : ℕ∞) * addVal O (a x) := by
  have hspan := eigSpan T act hsep
  have hcK : ∀ α ∈ E, ∀ f : T, α.baseChange (FractionRing O) * (actK T act).toRingHom f =
      (actK T act).toRingHom f * α.baseChange (FractionRing O) := by
    intro α hα f
    show α.baseChange (FractionRing O) * (act f).baseChange (FractionRing O) =
      (act f).baseChange (FractionRing O) * α.baseChange (FractionRing O)
    rw [← LinearMap.baseChange_mul, hc α hα f, LinearMap.baseChange_mul]
  refine congMod_le hspan (latIn O M) fg_latIn S ((fun α => α.baseChange (FractionRing O)) '' E)
    (fun x => addVal O (a x)) ?_ ?_ ?_ ?_
  · rintro _ ⟨α, hα, rfl⟩ f
    exact hcK α hα f
  · rintro _ ⟨α, hα, rfl⟩ v hv
    exact baseChange_latIn α v hv
  · rintro _ ⟨α, hα, rfl⟩ v _
    have hle : (⨆ x, Vx T (actK T act).toRingHom x) ≤
        (Formalism.NG.VS T (actK T act).toRingHom (S : Set X)).comap (α.baseChange (FractionRing O)) := by
      refine iSup_le fun x u hu => ?_
      rw [Submodule.mem_comap]
      by_cases hx : x ∈ S
      · refine le_iSup₂ (f := fun y (_ : y ∈ (S : Set X)) => Vx T (actK T act).toRingHom y) x hx ?_
        refine mem_Vx.mpr fun f => ?_
        rw [← Module.End.mul_apply, ← hcK α hα f, Module.End.mul_apply, mem_Vx.mp hu f,
          LinearMap.map_smul_of_tower]
      · rw [h0 α hα x hx u hu]
        exact zero_mem _
    rw [hspan] at hle
    exact hle (Submodule.mem_top (x := v))
  · intro x hx
    obtain ⟨α, hα, h⟩ := h1 x hx
    exact ⟨_, ⟨α, hα, rfl⟩, a x, h, le_rfl⟩

theorem lenUnit_le_of_family (l : ℕ) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Finset X)
    (E : Set (Module.End O M)) (a : X → O) (ha : ∀ x ∈ S, a x ≠ 0)
    (hc : ∀ α ∈ E, ∀ f : T, α * act f = act f * α)
    (h1 : ∀ x ∈ S, ∃ α ∈ E, ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = a x • u)
    (h0 : ∀ α ∈ E, ∀ x, x ∉ S → ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = 0) :
    lenUnit (O := O) l
        (↥((latIn O M ⊔ (⨆ x ∈ (S : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
            (⨆ x ∈ (S : Set X), heckeEig T act x).restrictScalars O) ⧸
          (latIn O M ⊓ (⨆ x ∈ (S : Set X), heckeEig T act x).restrictScalars O).comap
            ((latIn O M ⊔ (⨆ x ∈ (S : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
              (⨆ x ∈ (S : Set X), heckeEig T act x).restrictScalars O).subtype) ≤
      ∑ π ∈ S, (heckeMult T act π : ℚ) * lenUnit (O := O) l (O ⧸ Ideal.span {a π}) := by
  have hE : heckeEig T act = Vx T (actK T act).toRingHom := funext (heckeEig_eq T act)
  rw [hE] at h1 h0
  have hlen := (len_le T act hsep (latIn O M) S).trans
    (congMod_le_of_family T act hsep S E a hc h1 h0)
  simp only [heckeMult, lenUnit, IdempotentNormalFormsLenFacts.length_quot_span]
  rw [hE]
  have hsum : ∑ x ∈ S, (Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) : ℕ∞) *
        addVal O (a x) =
      ((∑ x ∈ S, Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) *
        (addVal O (a x)).toNat : ℕ) : ℕ∞) := by
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [ENat.natCast_toNat (fun h => ha x hx (addVal_eq_top_iff.mp h))]
  rw [hsum] at hlen
  have hnat := ENat.toNat_le_of_le_natCast hlen
  simp only [← mul_div_assoc, ← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast hnat

end General

theorem etaBound_of_fam : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ), CongruenceFamilyEndomorphisms CT i k ρ eta → EtaBound CT i k ρ eta := by
  rintro D CT i k ρ eta ⟨E, a, c, hE, hg⟩
  refine ⟨c, ?_, fun π hπ => (hg π hπ).2.2.2⟩
  rw [etaLoc_eq]
  refine (lenUnit_le_of_family (D.nd.T i) (D.nd.act i) (D.nd.l i) (D.nd.T_sep i) (D.nd.Zgood i) E a
    (fun π hπ => (hg π hπ).1) (fun α hα => (hE α hα).1) (fun π hπ => (hg π hπ).2.1)
    (fun α hα => (hE α hα).2)).trans ?_
  exact Finset.sum_le_sum fun π hπ =>
    mul_le_mul_of_nonneg_left (hg π hπ).2.2.1 (Nat.cast_nonneg _)

theorem etaBound_of_cut : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ), CongruenceLocalDecomposition CT i k ρ eta → EtaBound CT i k ρ eta :=
  fun D CT i k ρ eta h => etaBound_of_fam D CT i k ρ eta (GlobalTheory.CutFam.fam_of_cut D CT i k ρ eta h)

end GlobalTheory.EtaFromCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingleton
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem invertible_eq_zero_of_smul_eq_zero {A : Type} [CommRing A] {M : Type} [AddCommGroup M]
    [Module A M] [Module.Invertible A M] (a : A) (h : ∀ m : M, a • m = 0) : a = 0 := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := A) (M := M)).2 1
  have hz : ∀ s : Module.Dual A M ⊗[A] M, a • s = 0 := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => exact smul_zero a
    | tmul f m => rw [← TensorProduct.tmul_smul, h m, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  have : a = contractLeft A M (a • t) := by rw [map_smul, ht, smul_eq_mul, mul_one]
  rw [this, hz t, map_zero]

theorem mem_nonZeroDivisors_of_invertible_span_singleton : ∀ (A : Type) [CommRing A] (d : A),
    Module.Invertible A ↥(Ideal.span {d}) → d ∈ nonZeroDivisors A := by
  intro A _ d hinv
  rw [mem_nonZeroDivisors_iff_right]
  intro a had
  apply invertible_eq_zero_of_smul_eq_zero (M := ↥(Ideal.span {d})) a
  rintro ⟨m, hm⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hm
  ext
  simp only [Submodule.coe_smul, smul_eq_mul, ZeroMemClass.coe_zero]
  calc a * (c * d) = c * (a * d) := by ring
    _ = 0 := by rw [had, mul_zero]

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlacesOkOfModEqOne
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem placesOk_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), q0.Prime → (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p ≡ 1 [MOD H.QS * H.q * H.d]) → (∀ k, q0 ≠ H.g k) → q0 ≠ H.pde → q0 ≠ H.pde' → OverP H q0 w0 → PlacesOk H q0 w0 ∧ 5 ≤ q0 := by
  intro R H q0 w0 hq hmod hg hp hp' hw
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := by
    intro p h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    exacts [H.g_prime 0, H.g_prime 1, H.pde_prime, H.pde'_prime, hq]
  have h4 : (4 : ℕ) ∣ H.QS * H.q * H.d := (by norm_num : 4 ∣ 16).trans H.sixteen_dvd_condN
  have h5 : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], 5 ≤ p := by
    intro p h
    have h1 : p % 4 = 1 % 4 := (hmod p h).of_dvd h4
    have h2 := (hprime p h).two_le
    omega
  refine ⟨⟨hw, ?_, fun p h => ?_⟩, h5 q0 (by simp)⟩
  · have a1 := H.g_ne
    have a2 := H.pde_ne
    have a3 := H.pde_ne_g 0
    have a4 := H.pde_ne_g 1
    have a5 := hg 0
    have a6 := hg 1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
      and_true]
    omega
  · have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p (hprime p h) (hmod p h)
    have := h5 p h
    refine ⟨hprime p h, by omega, ?_, fun P hP => (GlobalTheory.Mem.Chr.splitsC_main R H p (hprime p h) hs P hP).1⟩
    exact GlobalTheory.SplitEmbSep.not_dvd_discr_of_split (hprime p h) _
      ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver (hprime p h)).symm.trans hs)

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBounds
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.FontaineAdm

theorem fontaine_bounds : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm8 D := by
  intro D l _ K LL T
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.dcris_finite_le_of_tied (D.locT l) K LL T.V T.ρ
  refine ⟨⟨h1, h2⟩, fun τ => ?_⟩
  obtain ⟨hd, -⟩ := GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ
  exact ⟨(hd τ).1, (hd τ).2.1⟩

end GlobalTheory.Per.FontaineAdm
end
