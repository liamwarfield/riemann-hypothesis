module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsSubDivMemSP

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarSteps
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def starFrame (γ : TermDef.Term D u u' F0 what₂) : Fin (D.R.rS + 1) → (VS D).V :=
  frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹

def starZh (f f' : Fin (D.R.rS + 1) → (VS D).V) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  fun a b => brS (VS D) (f' b) (f a)

def starOm (f f' : Fin (D.R.rS + 1) → (VS D).V) : (VS D).V :=
  ∑ b, (starZh f f').adjugate b (Fin.last D.R.rS) • f' b

def starCompat (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS *
      leadMinorE (starZh (frame (lf D F0)) (frame F'₂)) (D.R.rS + 1) =
    leadMinorE (starZh (frame (lf D F0)) (frame F'₂)) D.R.rS *
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) (D.R.rS + 1) ∧
  leadMinorE (starZh (frame (lf D F0)) (frame F'₂)) (D.R.rS + 1) • starOm (frame (lf D F0)) (starFrame γ) -
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) (D.R.rS + 1) • starOm (frame (lf D F0)) (frame F'₂) ∈
    Xsp (lf D F0)

variable (u u' F0 what₂)

def StarGenLoc : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    ∀ p, (locH Zd p).IsGeneric (tLoc Zd p γ)

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwd
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdCut

def liftF {T' : D.host.E} (F' : LFlag (D.sp.Y 0) D.R.rS T') : LFlag (D.sp.Y 0) D.R.rS T' := ⟨F'.fl, F'.fl.z⟩

theorem isom_of_N0F {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
  hn.1

theorem mapL_lf {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) :
    mapL n (isom_of_N0F hn) (lf D F0) = lf D F0 := by
  apply mapL_eq_self
  · intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simpa [frame, FlagG.fvec, lf] using hn.2.2.2.2
    · simpa [frame, FlagG.fvec, lf] using hn.2.2.2.1 i
  · exact hn.2.2.2.2

theorem zhatL_mapL_N0F {T' : D.host.E} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') : ZhatL (lf D F0) (mapL n (isom_of_N0F hn) F') = ZhatL (lf D F0) F' := by
  conv_lhs => rw [← mapL_lf hn]
  exact zhat_mapL n (isom_of_N0F hn) (lf D F0) F'

theorem mem_EZ_of {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Formalism.HermitianLatticesTheory.gmap n Λ₂ = Λ)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : PairVal.MatR D)
    (hT : IsTerm Λ₂ (gS D) (lf D F0) F'₂) (hA : AdmWit Λ₂ (gS D) (lf D F0) F'₂ 1)
    (hG : IsGeneric Λ₂ (gS D) (lf D F0) F'₂) (hO : FrameOK D Λ₂ F'₂) (hZ : ZhatL (lf D F0) F'₂ = Z) :
    mapL n (isom_of_N0F hn) F'₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z := by
  have hβ := isom_of_N0F hn
  have hF := mapL_lf hn
  subst hΛ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hF]
    refine ⟨(IsLift_mapL n hβ Λ₂ F'₂).2 hT.1, (IsAdmissible_mapL n hβ _ Λ₂ _ F'₂).2 hT.2.1, ?_⟩
    exact (gval_mapL n hβ (lf D F0) F'₂).symm ▸ hT.2.2
  · rw [← hF]
    exact (AdmWit_mapL n hβ _ Λ₂ _ F'₂ 1).2 hA
  · rw [← hF]
    exact (generic_isomorphism_holds (S := VS D) (r := D.R.rS) (gS D) _ _ n hβ Λ₂ (lf D F0) F'₂).2 hG
  · have h := (positive_definite_isomorphism D u' n hβ Λ₂ (lf D F0) F'₂).2 ⟨hT.1, hT.2.1, hO⟩
    exact h.2.2
  · exact (zhatL_mapL_N0F hn F'₂).trans hZ

theorem gmap_eq_of_image {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} {Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h : (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (Λ : Set (VS D).V)) : Formalism.HermitianLatticesTheory.gmap n Λ₂ = Λ := by
  apply SetLike.coe_injective
  rw [coe_gmap]
  exact h

end BwdCut

open BwdCut

variable (u u' F0 what₂)

def BwdN : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∃ n ∈ unipotentFrameFixers F0,
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

def BwdPair : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ unipotentFrameFixers F0),
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V) →
        ∃ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' ∧
          Rep γ'.lam (lf D F0) (PD D γ'.lam (lf D F0) u') γ'.cls (mapL n (isom_of_N0F hn) (liftF F'₂))

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalDenominators
noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel Polynomial

namespace Formalism.L2.SG.Pf.LocalDenominators

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem val_iF_le (a b : F) :
    valuation A.Fp (A.ιF a) ≤ valuation A.Fp (A.ιF b) ↔ p.valuation F a ≤ p.valuation F b := by
  first
  | exact ((Valuation.Compatible.vle_iff_le (v := valuation A.Fp) _ _).symm).trans (A.val a b)
  | exact ((Valuation.Compatible.vle_iff_le _ _).symm).trans (A.val a b)

theorem iF_mem_iff (a : F) : A.ιF a ∈ 𝒪[A.Fp] ↔ p.valuation F a ≤ 1 := by
  have h := val_iF_le A a 1
  rw [map_one, map_one, map_one] at h
  rw [Valuation.mem_integer_iff]
  first
  | exact h
  | simpa using h

theorem val_int_le (t : 𝓞 F) : p.valuation F (t : F) ≤ 1 := p.valuation_le_one t

theorem val_unit {t : 𝓞 F} (ht : t ∉ p.asIdeal) : p.valuation F (t : F) = 1 := by
  refine le_antisymm (val_int_le t) (not_lt.mp fun h => ht ?_)
  first
  | exact (p.valuation_lt_one_iff_mem t).mp h
  | exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) p t).mp h

theorem iF_unit {t : 𝓞 F} (ht : t ∉ p.asIdeal) : valuation A.Fp (A.ιF (t : F)) = 1 := by
  have h1 := (val_iF_le A (t : F) 1).mpr (by rw [map_one, val_unit ht])
  have h2 := (val_iF_le A 1 (t : F)).mpr (by rw [map_one, val_unit ht])
  rw [map_one, map_one] at h1 h2
  exact le_antisymm h1 h2

theorem exists_den {a : F} (ha : p.valuation F a ≤ 1) :
    ∃ t : 𝓞 F, t ∉ p.asIdeal ∧ ∃ y : 𝓞 F, (y : F) = (t : F) * a := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hs0' : ((s : 𝓞 F) : F) ≠ 0 := by exact_mod_cast hs0
  rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap] at ha
  have hpos : 0 < p.intValuation s := by
    rw [zero_lt_iff]
    exact (intValuation_ne_zero p s hs0)
  have hrs : p.intValuation r ≤ p.intValuation s := by
    rwa [div_le_one₀ hpos] at ha
  have hr : r ∈ p.asIdeal ^ Formalism.HermitianLattices.Ext.L3.vF p.asIdeal s := by
    rw [← intValuation_le_pow_iff_mem]
    exact hrs.trans ((intValuation_le_pow_iff_mem p s _).2
      (Formalism.HermitianLattices.Ext.L3.localValuationFiltration.mem_pow_vF p.isMaximal hs0))
  obtain ⟨t, ht, hmul⟩ := Formalism.L2.SG.Pf.G2.exists_mul_mem_span p.isMaximal hs0
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hmul r hr)
  refine ⟨t, ht, y, ?_⟩
  have h := congrArg (algebraMap (𝓞 F) F) hy
  simp only [map_mul] at h
  field_simp
  rw [mul_comm] at h
  simpa [mul_comm] using h

theorem iE_int {y : E} (hy : IsIntegral ℤ y) : A.ιE y ∈ A.O := by
  refine (A.O_def _).mpr ?_
  first
  | exact (map_isIntegral_int A.ιE hy).tower_top
  | exact IsIntegral.tower_top (map_isIntegral_int A.ιE hy)

theorem iE_alg (a : F) : A.ιE (algebraMap F E a) = algebraMap A.Fp A.Ep (A.ιF a) := A.compat a

theorem alg_mem_O {z : A.Fp} (hz : z ∈ 𝒪[A.Fp]) : algebraMap A.Fp A.Ep z ∈ A.O := by
  refine (A.O_def _).mpr ?_
  exact isIntegral_algebraMap (x := (⟨z, hz⟩ : 𝒪[A.Fp]))

instance : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)

theorem mem_of_alg_mem_O {z : A.Fp} (hz : algebraMap A.Fp A.Ep z ∈ A.O) : z ∈ 𝒪[A.Fp] := by
  have h1 := (A.O_def _).mp hz
  have h2 : IsIntegral 𝒪[A.Fp] z :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[A.Fp] A.Fp A.Ep)
      (algebraMap A.Fp A.Ep).injective).mp h1
  first
  | exact (Valuation.integer.integers _).mem_of_integral h2
  | simpa using (Valuation.integer.integers _).mem_of_integral h2

variable (hσ : ∀ e, sig (sig e) = e) (hfix : ∀ y : E, sig y = y → y ∈ (algebraMap F E).range)
include hσ hfix

theorem iE_sig_mem {x : E} (hx : A.ιE x ∈ A.O) : A.ιE (sig x) ∈ A.O := by
  rw [← A.cj_ιE]
  exact (A.O_def _).mpr
    (((A.O_def _).mp hx).map ((A.cj : A.Ep →ₐ[A.Fp] A.Ep).restrictScalars 𝒪[A.Fp]))

theorem iE_mem_O_iff (x : E) :
    A.ιE x ∈ A.O ↔ ∃ s : 𝓞 F, s ∉ p.asIdeal ∧ IsIntegral ℤ (algebraMap F E (s : F) * x) := by
  constructor
  · intro hx

    obtain ⟨t, ht⟩ := hfix (x + sig x) (by rw [map_add (f := _), hσ, add_comm])
    obtain ⟨n, hn⟩ := hfix (x * sig x) (by rw [map_mul, hσ, mul_comm])
    have hxs := iE_sig_mem A hσ hfix hx
    have htO : A.ιF t ∈ 𝒪[A.Fp] := by
      apply mem_of_alg_mem_O A
      rw [← iE_alg, ht, map_add (f := _)]; exact A.O.add_mem hx hxs
    have hnO : A.ιF n ∈ 𝒪[A.Fp] := by
      apply mem_of_alg_mem_O A
      rw [← iE_alg, hn, map_mul]; exact A.O.mul_mem hx hxs
    obtain ⟨s₁, hs₁, y₁, hy₁⟩ := exists_den ((iF_mem_iff A t).1 htO)
    obtain ⟨s₂, hs₂, y₂, hy₂⟩ := exists_den ((iF_mem_iff A n).1 hnO)
    refine ⟨s₁ * s₂, fun h => (p.isPrime.mem_or_mem h).elim hs₁ hs₂, ?_⟩
    set c : E := algebraMap F E ((s₁ * s₂ : 𝓞 F) : F) with hc
    have hkey : (c * x) ^ 2 - algebraMap F E ((s₂ * y₁ : 𝓞 F) : F) * (c * x) +
        algebraMap F E ((s₁ * s₁ * s₂ * y₂ : 𝓞 F) : F) = 0 := by
      have hy₁' : algebraMap (𝓞 F) F y₁ = algebraMap (𝓞 F) F s₁ * t := hy₁
      have hy₂' : algebraMap (𝓞 F) F y₂ = algebraMap (𝓞 F) F s₂ * n := hy₂
      have e1 : algebraMap F E ((s₂ * y₁ : 𝓞 F) : F) = c * (x + sig x) := by
        rw [hc, ← ht, ← map_mul]; congr 1
        show algebraMap (𝓞 F) F (s₂ * y₁) = algebraMap (𝓞 F) F (s₁ * s₂) * t
        rw [map_mul, map_mul, hy₁']; ring
      have e2 : algebraMap F E ((s₁ * s₁ * s₂ * y₂ : 𝓞 F) : F) = c * c * (x * sig x) := by
        rw [hc, ← hn, ← map_mul, ← map_mul]; congr 1
        show algebraMap (𝓞 F) F (s₁ * s₁ * s₂ * y₂) = algebraMap (𝓞 F) F (s₁ * s₂) * algebraMap (𝓞 F) F (s₁ * s₂) * n
        rw [map_mul, map_mul, map_mul, map_mul, hy₂']; ring
      rw [e1, e2]; ring
    have hint : IsIntegral (𝓞 F) (c * x) := by
      refine ⟨X ^ 2 - C (s₂ * y₁) * X + C (s₁ * s₁ * s₂ * y₂), ?_, ?_⟩
      · monicity!
      · rw [← hkey]
        simp [eval₂_sub, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_pow]
        rfl
    exact isIntegral_trans (R := ℤ) _ hint
  · rintro ⟨s, hs, hint⟩
    have h1 := iE_int A hint
    rw [map_mul, iE_alg] at h1
    have hinv : (A.ιF (s : F))⁻¹ ∈ 𝒪[A.Fp] := by
      rw [Valuation.mem_integer_iff, map_inv₀, iF_unit A hs, inv_one]
    have hne : A.ιF (s : F) ≠ 0 := by
      intro h0; have := iF_unit A hs; rw [h0, map_zero] at this; exact zero_ne_one this
    have e : A.ιE x = algebraMap A.Fp A.Ep (A.ιF (s : F))⁻¹ * (algebraMap A.Fp A.Ep (A.ιF (s : F)) * A.ιE x) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
    rw [e]
    exact A.O.mul_mem (alg_mem_O A hinv) h1

end Formalism.L2.SG.Pf.LocalDenominators
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmPart
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace OmP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def OmV {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (v : S.V) : Prop :=
  v ∈ Submodule.span E (Set.range F'.fvec) ∧ ∀ a, S.hT (F.fvec a) v = if a = Fin.last r then 1 else 0

theorem fvec_cs {T : E} (F : FlagG S r T) (i : Fin r) : F.fvec i.castSucc = F.e i := by
  simp [FlagG.fvec]

theorem fvec_last {T : E} (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem hT_comb {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E) (a : Fin (r + 1)) :
    S.hT (F.fvec a) (∑ b, c b • F'.fvec b) = (Zhat F F' *ᵥ c) a := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

theorem eq_zero_of_orth {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0)
    {d : S.V} (hd : d ∈ Submodule.span E (Set.range F'.fvec)) (h : ∀ a, S.hT (F.fvec a) d = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hd
  have hc : Zhat F F' *ᵥ c = 0 := funext fun a => by rw [← hT_comb]; exact h a
  rw [Matrix.eq_zero_of_mulVec_eq_zero hdet hc]
  simp

theorem exists_om {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) :
    ∃ v, OmV F F' v := by
  set c : Fin (r + 1) → E := (Zhat F F')⁻¹ *ᵥ Pi.single (Fin.last r) 1 with hc
  refine ⟨∑ b, c b • F'.fvec b, (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩, fun a => ?_⟩
  rw [hT_comb, hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  by_cases ha : a = Fin.last r
  · subst ha; simp
  · simp [ha]

theorem om_unique {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) {v w : S.V}
    (hv : OmV F F' v) (hw : OmV F F' w) : v = w := by
  have := eq_zero_of_orth F F' hdet (Submodule.sub_mem _ hv.1 hw.1) fun a => by
    rw [map_sub, hv.2, hw.2, sub_self]
  exact sub_eq_zero.1 this

theorem comb_eq {T T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hdet : (Zhat F F').det ≠ 0) {Ω : S.V}
    (hΩ : OmV F F' Ω) (c : Fin (r + 1) → E) (hc : ∀ i : Fin r, S.hT (F.e i) (∑ b, c b • F'.fvec b) = 0) :
    ∑ b, c b • F'.fvec b = S.hT F.z (∑ b, c b • F'.fvec b) • Ω := by
  set v := ∑ b, c b • F'.fvec b with hv
  have hvs : v ∈ Submodule.span E (Set.range F'.fvec) := (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩
  have := eq_zero_of_orth F F' hdet (Submodule.sub_mem _ hvs (Submodule.smul_mem _ (S.hT F.z v) hΩ.1))
    fun a => by
      rw [map_sub, map_smul, hΩ.2, smul_eq_mul]
      refine Fin.lastCases ?_ (fun i => ?_) a
      · rw [fvec_last]; simp
      · rw [fvec_cs, hc i]; simp [Fin.castSucc_ne_last]
  exact sub_eq_zero.1 this

end OmP

open OmP

section Cls

variable {D : Formalism.BasicNotions.D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem omCls_of_om {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS T')
    (hZ : ZhatL (lf D F0) F'₂ = ZhatL (lf D F0) F') (hdet : (ZhatL (lf D F0) F'₂).det ≠ 0) {Ω₂ Ω' : (VS D).V}
    (h₂ : OmV F0 F'₂.fl Ω₂) (h' : OmV F0 F'.fl Ω') (hX : Ω' - Ω₂ ∈ Xsp (lf D F0)) : OmCls F0 F'₂ F' := by
  intro c hc
  have hZ' : Zhat F0 F'₂.fl = Zhat F0 F'.fl := hZ
  have hdet₂ : (Zhat F0 F'₂.fl).det ≠ 0 := hdet
  have hdet' : (Zhat F0 F'.fl).det ≠ 0 := by rw [← hZ']; exact hdet
  have hc₂ : ∀ i, (VS D).hT (F0.e i) (∑ b, c b • F'₂.fl.fvec b) = 0 := hc
  have hc' : ∀ i, (VS D).hT (F0.e i) (∑ b, c b • F'.fl.fvec b) = 0 := by
    intro i
    rw [← fvec_cs, hT_comb, ← hZ', ← hT_comb, fvec_cs]
    exact hc₂ i
  have hμ : (VS D).hT F0.z (∑ b, c b • F'.fl.fvec b) = (VS D).hT F0.z (∑ b, c b • F'₂.fl.fvec b) := by
    rw [← fvec_last, hT_comb, hT_comb, hZ']
  have e₂ := comb_eq F0 F'₂.fl hdet₂ h₂ c hc₂
  have e' := comb_eq F0 F'.fl hdet' h' c hc'
  have hs : ∑ b, c b • (frame F' b - frame F'₂ b) =
      ∑ b, c b • F'.fl.fvec b - ∑ b, c b • F'₂.fl.fvec b := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => smul_sub _ _ _
  rw [hs, e', e₂, hμ, ← smul_sub]
  exact Submodule.smul_mem _ _ hX

end Cls

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def OmDet : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → ∀ F', IsPartner γ Z F' →
        (ZhatL (lf D F0) (repF γ)).det ≠ 0 ∧ Matrix.det Z ≠ 0

def OmLoc : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' → (ZhatL (lf D F0) (repF γ)).det ≠ 0 → Matrix.det Z ≠ 0 → ∀ Ω₂ Ωγ : (VS D).V, OmV F0 F'₂.fl Ω₂ → OmV F0 (repF γ).fl Ωγ →
        Ω₂ - Ωγ ∈ Xsp (lf D F0)

def OmRep : Prop :=
  IsRowReps D F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    (ZhatL (lf D F0) (repF γ)).det ≠ 0 → Matrix.det Z ≠ 0 →
    ∀ F', IsPartner γ Z F' → ∀ Ω' Ωγ : (VS D).V, OmV F0 F'.fl Ω' → OmV F0 (repF γ).fl Ωγ →
      Ω' - Ωγ ∈ Xsp (lf D F0)

variable {u u' F0 what₂}

theorem omPart_of (h0 : OmDet Zd u u' F0 what₂) (h1 : OmLoc Zd u u' F0 what₂) (h2 : OmRep u u' F0 what₂) :
    OmPart Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'₂ φ φ' hS F' hP
  obtain ⟨hdγ, hdZ⟩ := h0 hrows γ Z hC F'₂ φ φ' hS F' hP
  have hZ₂ : ZhatL (lf D F0) F'₂ = Z := hS.1
  have hZ' : ZhatL (lf D F0) F' = Z := hP.1.2.2.2.2
  have hd₂ : (ZhatL (lf D F0) F'₂).det ≠ 0 := by rw [hZ₂]; exact hdZ
  have hd' : (ZhatL (lf D F0) F').det ≠ 0 := by rw [hZ']; exact hdZ
  obtain ⟨Ωγ, hγ⟩ := exists_om F0 (repF γ).fl hdγ
  obtain ⟨Ω₂, h₂⟩ := exists_om F0 F'₂.fl hd₂
  obtain ⟨Ω', h'⟩ := exists_om F0 F'.fl hd'
  have e1 := h1 hrows γ Z hC F'₂ φ φ' hS hdγ hdZ Ω₂ Ωγ h₂ hγ
  have e2 := h2 hrows γ Z hC hdγ hdZ F' hP Ω' Ωγ h' hγ
  refine omCls_of_om F0 F'₂ F' (hZ₂.trans hZ'.symm) hd₂ h₂ h' ?_
  have : Ω' - Ω₂ = (Ω' - Ωγ) - (Ω₂ - Ωγ) := by abel
  rw [this]
  exact Submodule.sub_mem _ e2 e1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
