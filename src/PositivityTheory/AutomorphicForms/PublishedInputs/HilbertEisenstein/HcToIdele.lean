module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchInt
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.UnitaryTransvectionZeroSecondMemClosure

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HcToIdele
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection


open Classical in
def finK (c : HeightOneSpectrum (𝓞 F) → ℕ) (yf : (Af F)ˣ) (ξ : F) (b : (Af F)ˣ) : ℂ :=
  if (∀ w, Valued.v (pLoc F w ((b : Af F) * (yf : Af F))) ≤ WithZero.exp (-(c w : ℤ))) ∧
      (∀ w, Valued.v (pLoc F w (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ)) ≤
        WithZero.exp ((c w : ℤ) + dd w))
  then ((finiteAdelicChar F (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ) : Circle) : ℂ) else 0

def ωF (ω : HChar F) (b : (Af F)ˣ) : ℂ := ((ω.1 (ofFinite b) : ℂˣ) : ℂ)

def qc (ω : HChar F) : QuasiCharacter F where
  toMonoidHom := QuotientGroup.lift _ ω.1 (by
    rintro _ ⟨a, rfl⟩
    exact ω.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ω.2.1

theorem norm_qc (ω : HChar F) (h : IsOfFinOrder ω) (c : GroundTheory.Global.IdeleClassGroup F) :
    ‖((qc ω c : ℂˣ) : ℂ)‖ = 1 := by
  induction c using QuotientGroup.induction_on with
  | H x => exact L2.norm_omega_eq_one h x

def hc (ω : HChar F) (h : IsOfFinOrder ω) : HeckeCharacter F := QuasiCharacter.toUnitary (qc ω) (norm_qc ω h)

theorem hc_toIdele (ω : HChar F) (h : IsOfFinOrder ω) (x : IdeleGroup F) :
    (((hc ω h).toIdele x : Circle) : ℂ) = ((ω.1 x : ℂˣ) : ℂ) := rfl

def xiF (ξ : Fˣ) : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom ξ

def ordAt (b : (Af F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : ℤ := ord (pLoc F v (b : Af F))


open Classical in
def locF (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (yf : (Af F)ˣ) (ξ : F) (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) : ℂ :=
  (if Valued.v ((a : v.adicCompletion F) * pLoc F v (yf : Af F)) ≤ WithZero.exp (-(c v : ℤ)) ∧
      Valued.v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * algebraMap F (v.adicCompletion F) ξ) ≤
        WithZero.exp ((c v : ℤ) + dd v)
    then (localAdelicChar F v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) ξ) : ℂ) else 0) * ((ω.loc v a : ℂˣ) : ℂ)⁻¹

def cst (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if c v = 0 then ((ω.val v : ℂˣ) : ℂ) ^ (-dd v) else
    ∫ x in ordShell (v.adicCompletion F) (-((c v : ℤ) + dd v)), ((ω.loc v x : ℂˣ) : ℂ) *
      (localAdelicChar F v (x : v.adicCompletion F) : ℂ) ∂multHaar (v.adicCompletion F)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4 GroundTheory.Automorphic.GodementSection

def InvSubst : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (f : (v.adicCompletion F)ˣ → ℂ) (t : (v.adicCompletion F)ˣ),
    (Integrable f (multHaar (v.adicCompletion F)) ↔
      Integrable (fun x => f (t * x⁻¹)) (multHaar (v.adicCompletion F))) ∧
    ∫ a, f a ∂multHaar (v.adicCompletion F) = ∫ x, f (t * x⁻¹) ∂multHaar (v.adicCompletion F)

def LocInt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (yf : (Af F)ˣ) (ξ : Fˣ) (v : HeightOneSpectrum (𝓞 F)),
    Integrable (locF ω c yf (ξ : F) v) (multHaar (v.adicCompletion F)) ∧
    ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F) =
      ((ω.loc v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ξ) : ℂˣ) : ℂ)⁻¹ *
        if ordAt (xiF ξ * yf) v + dd v < 0 then 0 else
          cst ω c v * ∑ j ∈ Finset.range ((ordAt (xiF ξ * yf) v + dd v).toNat + 1), chiW ω c v ^ j

def OmegaProd : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (b : (Af F)ˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w ∉ S, c w = 0 ∧ IsIntegralUnitAt b w) →
    ωF ω b = ∏ v ∈ S, ((ω.loc v (finUnitAt v b) : ℂˣ) : ℂ)

def FinSplit : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (yf : (Af F)ˣ) (ξ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w ∉ S, c w = 0 ∧ dd w = 0 ∧ IsIntegralUnitAt yf w ∧ IsIntegralUnitAt (xiF ξ) w) →
    (∀ v, Integrable (locF ω c yf (ξ : F) v) (multHaar (v.adicCompletion F))) →
    Integrable (fun b => finK c yf (ξ : F) b * (ωF ω b)⁻¹) (finiteIdeleMeasure F) ∧
      ∫ b, finK c yf (ξ : F) b * (ωF ω b)⁻¹ ∂finiteIdeleMeasure F =
        ∏ v ∈ S, ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F)

def OmegaPos : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ ξ : Fˣ, (∀ v, 0 < reAt v (ξ : F)) → ωF ω (xiF ξ) = 1

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.QuasiCharConductorLoc
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalShellIntegral

section Abstract

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem shell_vanish (χ : Kˣ →* ℂˣ) (ψ : AddChar K Circle) {n j k : ℤ} (hψ : IsTrivialOn ψ n) {v : Kˣ}
    (hv0 : ord (v : K) = 0) (hv1 : χ v ≠ 1) (hvj : (v : K) - 1 ∈ valBall K j) (hjk : n ≤ j + k) :
    ∫ u in ordShell K k, ((χ u : ℂˣ) : ℂ) * (ψ (u : K) : ℂ) ∂multHaar K = 0 := by
  refine setIntegral_ordShell_eq_zero _ hv0 (a := ((χ v : ℂˣ) : ℂ)) (fun h => hv1 (Units.val_eq_one.mp h)) k
    fun u hu => ?_
  have hmem : ((v : K) - 1) * (u : K) ∈ valBall K n := by
    have h := mul_mem_valBall hvj ((mem_valBall_iff_le_ord u.ne_zero).mpr (le_of_eq (mem_ordShell.mp hu).symm))
    exact valBall_antitone hjk h
  have hψ' : (ψ ((v * u : Kˣ) : K) : ℂ) = (ψ (u : K) : ℂ) := by
    rw [show ((v * u : Kˣ) : K) = (u : K) + ((v : K) - 1) * (u : K) by push_cast; ring,
      AddChar.map_add_eq_mul, hψ _ hmem, mul_one]
  rw [hψ', map_mul, Units.val_mul]
  ring

theorem shell_ne_zero (χ : Kˣ →* ℂˣ) (ψ : AddChar K Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hχ : Continuous χ) (hr : ¬ IsUnramifiedChar χ) :
    ∫ u in ordShell K (addCharConductor ψ - quasiCharConductor χ), ((χ u : ℂˣ) : ℂ) * (ψ (u : K) : ℂ)
      ∂multHaar K ≠ 0 := by
  have hχ' : Continuous (χ⁻¹ : Kˣ →* ℂˣ) := continuous_quasiChar_inv hχ
  have hr' : ¬ IsUnramifiedChar χ⁻¹ := by rwa [isUnramifiedChar_inv_iff]
  obtain ⟨a, ha, k, hk⟩ := exists_localEpsilon_eq_monomial (χ := χ⁻¹) (ψ := ψ) hψ hψ1 hχ'
  have h0 := hk 0
  rw [localEpsilon_of_not_isUnramified_eq hr', quasiCharConductor_inv, inv_inv] at h0
  set m : ℤ := addCharConductor ψ - quasiCharConductor χ
  have hadd : ∫ x in (valBall K m : Set K) \ valBall K (m + 1), quasiCharExt χ x * (ψ x : ℂ) ∂haarIntegers K ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h0
    simp only [neg_zero, Complex.cpow_zero, one_zpow, mul_one] at h0
    exact ha h0.symm
  have hsh := setIntegral_ordShell_eq_haarIntegers (fun x => quasiCharExt χ x * (ψ x : ℂ)) m
  simp only [quasiCharExt_units] at hsh
  rw [hsh]
  refine mul_ne_zero ?_ hadd
  have h1 : (multHaarConst K).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨multHaarConst_ne_zero, multHaarConst_ne_top⟩
  have h2 : (residueCard K : ℝ) ^ m ≠ 0 := zpow_ne_zero _ residueCard_pos_real.ne'
  exact_mod_cast mul_ne_zero h1 h2

end Abstract

section Bridge

variable {F : Type} [Field F] [NumberField F]

theorem dd_eq (w : HeightOneSpectrum (𝓞 F)) : dd w = differentExp w := by
  unfold dd differentExp ordI
  rw [FractionalIdeal.count_coe]
  exact _root_.differentIdeal_ne_bot

theorem continuous_loc (ω : HChar F) (w : HeightOneSpectrum (𝓞 F)) : Continuous (ω.loc w) :=
  ω.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele w)

theorem mem_U_iff (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (x : (w.adicCompletion F)ˣ) :
    x ∈ unitFiltrationUnits (w.adicCompletion F) n ↔
      IsUnitAt w x ∧ Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have h0 : x ∈ unitFiltrationUnits (w.adicCompletion F) 0 ↔ IsUnitAt w x := by
    rw [mem_unitFiltrationUnits_zero_iff_ord, IsUnitAt, valued_eq_one_iff_ord x.ne_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [h0]
    refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
    have hx : (x : w.adicCompletion F) ∈ valBall (w.adicCompletion F) 0 := by
      rw [mem_valBall_iff_le_ord x.ne_zero]
      exact le_of_eq ((valued_eq_one_iff_ord x.ne_zero).mp h).symm
    have h1 : (1 : w.adicCompletion F) ∈ valBall (w.adicCompletion F) 0 := by
      rw [mem_valBall_iff_le_ord one_ne_zero]
      have := (valued_eq_one_iff_ord (one_ne_zero (α := w.adicCompletion F))).mp (map_one _)
      omega
    have := (mem_valBall_iff_valued).mp (sub_mem hx h1)
    simpa using this
  · rw [mem_unitFiltrationUnits_iff_valBall hn, mem_valBall_iff_valued]
    constructor
    · intro h
      refine ⟨?_, h⟩
      have hU := unitFiltrationUnits_antitone (Nat.zero_le n) ((mem_unitFiltrationUnits_iff_valBall hn).mpr
        ((mem_valBall_iff_valued).mpr h))
      exact h0.mp hU
    · exact fun h => h.2

theorem quasiCharConductor_loc {ω : HChar F} {c : ℕ} {w : HeightOneSpectrum (𝓞 F)} (h : IsCondAt w ω c) :
    quasiCharConductor (ω.loc w) = c := by
  have hset : {n : ℕ | unitFiltrationUnits (w.adicCompletion F) n ≤ (ω.loc w).ker} =
      {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
        Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hle x hx hv
      exact MonoidHom.mem_ker.mp (hle ((mem_U_iff w n x).mpr ⟨hx, hv⟩))
    · intro hP x hx
      obtain ⟨h1, h2⟩ := (mem_U_iff w n x).mp hx
      exact MonoidHom.mem_ker.mpr (hP x h1 h2)
  unfold quasiCharConductor
  rw [hset]
  exact h.csInf_eq

end Bridge

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalShellIntegral

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open LocalShellIntegral

theorem local_ramified_holds : LocRam := by
  intro F _ _ _ ω c H w hcw
  set χ := ω.loc w
  set ψ := localAdelicChar F w
  have hcond : quasiCharConductor χ = c w := quasiCharConductor_loc (H.cond w)
  have hn : addCharConductor ψ = -dd w := by rw [addCharConductor_localAdelicChar, dd_eq]
  have hχ : Continuous χ := continuous_loc ω w
  have hr : ¬ IsUnramifiedChar χ := by
    rw [← quasiCharConductor_eq_zero_iff, hcond]
    all_goals first | exact hcw | exact hχ
  refine ⟨fun k hk => ?_, ?_⟩
  · set j : ℕ := (-dd w - k).toNat with hj
    have hjc : j < c w := by
      have : (j : ℤ) < c w := by
        rcases le_or_gt (-dd w - k) 0 with h | h
        · rw [hj, Int.toNat_of_nonpos h]; exact_mod_cast Nat.pos_of_ne_zero hcw
        · rw [hj, Int.toNat_of_nonneg h.le]; omega
      exact_mod_cast this
    have hnot : j ∉ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
        Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} :=
      fun hm => absurd ((H.cond w).2 hm) (not_le.mpr hjc)
    simp only [Set.mem_ofPred_eq, not_forall] at hnot
    obtain ⟨x, hx1, hx2, hx3⟩ := hnot
    have hψt : IsTrivialOn ψ (-dd w) := (isTrivialOn_localAdelicChar_iff w _).2 (by rw [dd_eq])
    refine shell_vanish χ ψ (n := -dd w) (j := j) hψt ((valued_eq_one_iff_ord x.ne_zero).mp hx1) hx3
      ((mem_valBall_iff_valued).mpr hx2) ?_
    have : (-dd w - k) ≤ (j : ℤ) := by rw [hj]; exact Int.self_le_toNat _
    omega
  · have h := shell_ne_zero χ ψ (continuous_localAdelicChar w) (localAdelicChar_ne_one w) hχ hr
    rw [hn, hcond] at h
    have e : -((c w : ℤ) + dd w) = -dd w - (c w : ℤ) := by ring
    rw [e]
    exact h

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.AestronglyMeasurableColumnWeight
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem isClosed_valuation_le (w : HeightOneSpectrum (𝓞 F)) (γ : WithZero (Multiplicative ℤ)) :
    IsClosed {x : w.adicCompletion F | Valued.v x ≤ γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : γ < Valued.v x := lt_of_not_ge hx
  filter_upwards [Valued.locally_const (lt_of_le_of_lt zero_le hx').ne'] with y hy
  intro hy'
  have e : Valued.v y = Valued.v x := hy
  exact absurd (e ▸ hy') (not_le.mpr hx')

theorem continuous_pLoc (w : HeightOneSpectrum (𝓞 F)) : Continuous (pLoc F w) :=
  RestrictedProduct.continuous_eval w

theorem continuous_pFin : Continuous (pFin F) := continuous_snd

theorem continuous_pInf : Continuous (UpperTheory.V.TR.pInf F) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem isClosed_row (c : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsClosed {y : Fin 2 → Ad F | ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F (y 1)) - 1) ≤ WithZero.exp (-(c w : ℤ))} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun w => IsClosed.inter ?_ ?_
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 0)))
  · exact (isClosed_valuation_le w _).preimage
      (((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 1))).sub continuous_const)

theorem isClosed_col (c : HeightOneSpectrum (𝓞 F) → ℕ) :
    IsClosed {y : Fin 2 → Ad F | ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
      Valued.v (pLoc F w (pFin F (y 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isClosed_iInter fun w => IsClosed.inter ?_ ?_
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 0)))
  · exact (isClosed_valuation_le w _).preimage
      ((continuous_pLoc w).comp (continuous_pFin.comp (continuous_apply 1)))

theorem coe_scalar (a : Ideles F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      Matrix.diagonal fun _ => (a : Ad F) := rfl

theorem continuous_av : Continuous (av (F := F)) :=
  ((continuous_moduleSection (w0 F)).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

theorem continuous_rowv (g : GA F 2) (ξ : Fin 2 → F) : Continuous fun a : Ideles F => rowv g a ξ := by
  unfold rowv Mrow
  simp only [Units.val_mul, coe_scalar]
  exact continuous_const.matrix_vecMul
    ((continuous_pi fun _ => Units.continuous_val).matrix_diagonal.matrix_mul continuous_const)

theorem continuous_colv (g : GA F 2) (ξ : Fin 2 → F) : Continuous fun a : Ideles F => colv g a ξ := by
  unfold colv Mcol
  simp only [Units.val_mul, coe_scalar]
  exact (continuous_const.matrix_mul
    (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal).matrix_mulVec continuous_const

theorem continuous_vInf : Continuous (vInf (F := F)) :=
  continuous_pi fun i => continuous_pInf.comp (continuous_apply i)

theorem measurable_finRow (c : HeightOneSpectrum (𝓞 F) → ℕ) {f : Pp F → Fin 2 → Ad F} (hf : Continuous f) :
    Measurable fun p => finRow c (f p) := by
  unfold finRow
  exact Measurable.ite ((isClosed_row c).preimage hf).measurableSet measurable_const measurable_const

theorem measurable_finCol (c : HeightOneSpectrum (𝓞 F) → ℕ) {f : Pp F → Fin 2 → Ad F} (hf : Continuous f) :
    Measurable fun p => finCol c (f p) := by
  unfold finCol
  refine Measurable.ite ((isClosed_col c).preimage hf).measurableSet ?_ measurable_const
  exact (continuous_subtype_val.comp (continuous_finiteAdelicChar.comp
    (continuous_pFin.comp ((continuous_apply 1).comp hf)))).measurable

theorem measurable_chi (χ : HChar F) : Measurable fun p : Pp F => ((χ.1 (av p) : ℂˣ) : ℂ)⁻¹ :=
  ((Units.continuous_val.comp (χ.2.1.comp continuous_av)).measurable).inv

theorem measurable_first_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) :
    Measurable (kap1 χ c g) := by
  refine measurable_from_prod_countable_left fun ξ => ?_
  exact ((measurable_finRow c ((continuous_rowv g ξ.1).comp continuous_av)).mul (measurable_chi χ)).mul
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).measurable

theorem measurable_second_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) :
    Measurable (kap2 χ c g) := by
  refine measurable_from_prod_countable_left fun ξ => ?_
  exact ((measurable_finCol c ((continuous_colv g ξ.1).comp continuous_av)).mul (measurable_chi χ)).mul
    (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).measurable.inv

theorem measurable_row_weight (g : GA F 2) : Measurable (w1 (F := F) g) :=
  measurable_from_prod_countable_left fun ξ =>
    (continuous_vInf.comp ((continuous_rowv g ξ.1).comp continuous_av)).measurable

theorem measurable_column_weight (g : GA F 2) : Measurable (w2 (F := F) g) :=
  measurable_from_prod_countable_left fun ξ =>
    (continuous_vInf.comp ((continuous_colv g ξ.1).comp continuous_av)).measurable

theorem aestronglyMeasurable_first_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (S : Set {r : ℝ // 0 < r}) :
    AEStronglyMeasurable (kap1 χ c g) (μS F S) := (measurable_first_kernel χ c g).aestronglyMeasurable

theorem aestronglyMeasurable_second_kernel (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (S : Set {r : ℝ // 0 < r}) :
    AEStronglyMeasurable (kap2 χ c g) (μS F S) := (measurable_second_kernel χ c g).aestronglyMeasurable

theorem aestronglyMeasurable_row_weight (g : GA F 2) (S : Set {r : ℝ // 0 < r}) : AEStronglyMeasurable (w1 g) (μS F S) :=
  (measurable_row_weight g).aestronglyMeasurable

theorem aestronglyMeasurable_column_weight (g : GA F 2) (S : Set {r : ℝ // 0 < r}) : AEStronglyMeasurable (w2 g) (μS F S) :=
  (measurable_column_weight g).aestronglyMeasurable

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PFinInfGLMulVec
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem Phi_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    Phi c v = archS F (vInf v) * finRow c v := by
  rw [archS_apply]; rfl

theorem PhiH_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    PhiH c v = archS F (vInf v) * finCol c v := by
  rw [archS_apply]; rfl

theorem finRow_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {v v' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (v i) = pFin F (v' i)) : finRow c v = finRow c v' := by
  unfold finRow; rw [h 0, h 1]

theorem finCol_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {v v' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (v i) = pFin F (v' i)) : finCol c v = finCol c v' := by
  unfold finCol; rw [h 0, h 1]

theorem map_pFin_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) = 1 :=
  congrArg Units.val (UpperTheory.V.TR.pFin_infGL y)

theorem map_pInf_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) =
      (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :=
  congrArg Units.val (UpperTheory.V.TR.pInf_infGL y)

theorem pFin_vecMul_infGL (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i : Fin 2) :
    pFin F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) i) = pFin F (v i) := by
  rw [RingHom.map_vecMul, map_pFin_infGL, Matrix.vecMul_one]; rfl

theorem vInf_vecMul_infGL (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    vInf (v ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      vInf v ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) := by
  funext i
  simp only [vInf]
  rw [RingHom.map_vecMul, map_pInf_infGL]; rfl

theorem pFin_infGL_mulVec (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i : Fin 2) :
    pFin F ((((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v) i) = pFin F (v i) := by
  rw [RingHom.map_mulVec, map_pFin_infGL, Matrix.one_mulVec]; rfl

theorem vInf_infGL_mulVec (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    vInf (((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v) =
      (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) *ᵥ vInf v := by
  funext i
  simp only [vInf]
  rw [RingHom.map_mulVec, map_pInf_infGL]; rfl

theorem row_term (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    Phi c (rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F))) =
      archS F (B1 (vInf (rowv g a ξ)) (UpperTheory.V.TR.toL y.val)) * finRow c (rowv g a ξ) := by
  have hv : rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) =
      rowv g a ξ ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) := by
    simp only [rowv, Mrow, Units.val_mul, Matrix.vecMul_vecMul, mul_assoc]
  rw [hv, Phi_eq, finRow_congr (pFin_vecMul_infGL _ _), vInf_vecMul_infGL, left_bilinear_apply]
  rfl

theorem col_term (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) =
      archS F (B2 (vInf (colv g a ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) * finCol c (colv g a ξ) := by
  have hinv : (Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ =
      UpperTheory.V.TR.infGL F 2 y⁻¹ * Mcol g a := by
    simp only [Mcol, mul_inv_rev, map_inv, mul_assoc]
  have hv : (((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ =
      ((UpperTheory.V.TR.infGL F 2 y⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ colv g a ξ := by
    rw [hinv, Units.val_mul, ← Matrix.mulVec_mulVec]; rfl
  rw [hv, PhiH_eq, finCol_congr (pFin_infGL_mulVec _ _), vInf_infGL_mulVec, right_bilinear_apply]
  rfl

theorem eisInt_row (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) t u =
      (∑' ξ : Xi F, kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val))) *
        ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
  have h : ∀ ξ : Xi F, kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val)) =
      Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) *
        (((χ.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)) := by
    intro ξ
    rw [row_term]
    simp only [kap1, w1, av]
    ring
  have e : (∑' ξ : Xi F, Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F)) * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)))) =
      thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y)) := rfl
  rw [tsum_congr h, tsum_mul_right, e]
  simp only [eisInt]
  ring

theorem eisInt_col (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) {C : ℂ}
    (hC : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) t u =
      C * ((absD (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : ℝ) * ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
        ∑' ξ : Xi F, kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) := by
  have h : ∀ ξ : Xi F, kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) =
      PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1) *
        (((χ.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)⁻¹) := by
    intro ξ
    rw [col_term]
    simp only [kap2, w2, av]
    ring
  have e : (∑' ξ : Xi F, PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F)) * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)) =
      thetaT (PhiH c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y)) := rfl
  rw [tsum_congr h, tsum_mul_right, e]
  simp only [eisInt]
  rw [hC, absD_scalar_mul]
  have ht : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr t.2.ne'
  push_cast
  field_simp

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end
