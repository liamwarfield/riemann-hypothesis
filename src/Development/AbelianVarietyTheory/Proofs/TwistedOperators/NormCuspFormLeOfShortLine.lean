module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallFundamentalSetRealUnipotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInte
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LipschitzBoundRealUnipotentAction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalCongruenceMemLatticeCongruenceLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalCongruenceMemLatticeCongruenceLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CongLevelInst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_hatL_iff (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) :
    x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ x ∈ Formalism.MainNotions.S.lamAf (F := F) Λ := by
  show x ∈ Submodule.span _ _ ↔ x ∈ Submodule.span _ _
  rw [Set.image_eq_range]
  rfl

theorem natCast_smul_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (g : ℕ)
    (z : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    ((g : E ⊗[F] Formalism.MainNotions.S.Af F)) • z ∈ Formalism.L2.Herm.hatL (F := F) (Ideal.span {((g : ℕ) : 𝓞 E)} • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨((g : ℕ) : 𝓞 E) • l, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl, ?_⟩
    funext i
    have h1 : ((g : ℕ) : 𝓞 E) • l i = (g : E) * l i := by
      rw [Algebra.smul_def]; simp
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1, map_mul, map_natCast]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hy

theorem mem_congLev (hc : Formalism.BasicNotions.CMData F E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (g : ℕ)
    (k : GL (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) (hU : k ∈ Formalism.UG.UPts hc.sig J (Formalism.MainNotions.S.Af F))
    (hs : k ∈ Formalism.UG.stabGL (Formalism.MainNotions.S.lamAf (F := F) Λ))
    (hd : ∀ y ∈ Formalism.MainNotions.S.lamAf (F := F) Λ, ∃ z ∈ Formalism.MainNotions.S.lamAf (F := F) Λ,
      ((k : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) - 1) *ᵥ y = (g : E ⊗[F] Formalism.MainNotions.S.Af F) • z) :
    k ∈ congLev hc J Λ (Ideal.span {((g : ℕ) : 𝓞 E)}) := by
  refine ⟨hU, ?_, ?_⟩
  · intro x
    rw [mem_hatL_iff, mem_hatL_iff]
    exact hs x
  · intro x hx
    obtain ⟨z, hz, e⟩ := hd x ((mem_hatL_iff Λ x).1 hx)
    have e2 : (k : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.S.Af F)) *ᵥ x - x = (g : E ⊗[F] Formalism.MainNotions.S.Af F) • z := by
      rw [← e, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [e2]
    exact natCast_smul_mem_hatL Λ g z ((mem_hatL_iff Λ z).2 hz)

end GlobalTheory.CongLevelInst

namespace GlobalTheory.CongLevelInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem kg_mem_levA : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (g : ℕ), 1 ≤ g → ∀ k ∈ (Formalism.IndefR.Eqv.UI.instV fr).Kg g, Formalism.IndefR.Eqv.UI.brg fr (1, k) ∈ Formalism.IndefR.Lev.levA V (congLev D.sp.cm V.gram fr.Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})) := by
  intro D V fr g _ k hk
  rw [Formalism.IndefR.Eqv.brg_mem_levA]
  exact ⟨rfl, mem_congLev D.sp.cm V.gram fr.Λ g k.1 k.2 hk.1 hk.2⟩

end GlobalTheory.CongLevelInst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalCongruenceMemLatticeCongruenceLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_mem_latticeCongruenceLevel : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (g : ℕ), 1 ≤ g → ∀ k ∈ (Formalism.IndefR.Eqv.UI.instV fr).Kg g, Formalism.IndefR.Eqv.UI.brg fr (1, k) ∈ Formalism.IndefR.Lev.levA V (congLev D.sp.cm V.gram fr.Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})) := by
  first | exact @GlobalTheory.CongLevelInst.kg_mem_levA | exact GlobalTheory.CongLevelInst.kg_mem_levA | (intros; apply GlobalTheory.CongLevelInst.kg_mem_levA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicPointRationalLatticeUnitaryModelIsoEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicPointRationalLatticeUnitaryModelIsoEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDict
open Formalism.IndefR.Eqv.UI

theorem mem_hatL_iff (D : D7) (V : HSp D) (fr : Frames D V)
    (w : Fin V.rank → D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) :
    w ∈ Formalism.L2.Herm.hatL (F := D.host.F) fr.Λ ↔ w ∈ (instV fr).Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

theorem finE_brg (D : D7) (V : HSp D) (fr : Frames D V) (x : (instV fr).GA) :
    (Lev.finE V (brg fr x)).1 = (instV fr).fmat x.2 := by
  have hring : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E,
      Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) =
        Formalism.L2.SG.AdBridge.tauF (instV fr) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ((Lev.swapAE D).congr_arg (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    | tmul a b => exact (Formalism.L2.SG.AdBridge.tauF_tmul (instV fr) a b).symm
    | add a b ha hb =>
      have e1 := _root_.map_add (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) a b
      rw [e1, RingHom.map_add (f := _), ha, hb]
      exact (RingHom.map_add _ _ _).symm
  rw [((brg_isBridge fr) x).2]
  ext i j
  simp only [Lev.finE, finHom, matHom, Formalism.UG.bc, Formalism.L2.SG.AdBridge.hmat, Formalism.L2.SG.AdBridge.ofHAFin,
    MonoidHom.comp_apply, Units.coe_map, Matrix.map_apply]
  exact hring _

theorem latAt_brg : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  intro D V fr x
  unfold GlobalTheory.SepPer.latAt GlobalTheory.Count.lamX
  congr 1
  ext y
  rw [← map_inv (brg fr) x, finE_brg D V fr x⁻¹]
  exact mem_hatL_iff D V fr _

end GlobalTheory.LatDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicPointRationalLatticeUnitaryModelIsoEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPointRationalLattice_unitaryModelIso_eq : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  first | exact @GlobalTheory.LatDict.latAt_brg | exact GlobalTheory.LatDict.latAt_brg | (intros; apply GlobalTheory.LatDict.latAt_brg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInstanceFramesOfDiagonalFrameSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInstanceFramesOfDiagonalFrameSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem frames_of_diagonalising_frame : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  intro D V A Λ h
  obtain ⟨hlat, hdual⟩ := h
  have hspan : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    obtain ⟨s, hs⟩ := hlat.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hdual _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  have hf : ∀ v, IsUnit (A.fr ((Formalism.L2.Host.tauPl D).symm v)) := fun v => A.fr_unit _
  refine ⟨{ ε := fun v => A.ε ((Formalism.L2.Host.tauPl D).symm v)
            P := fun v => (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹
            unit := fun v => (Matrix.isUnit_nonsing_inv_iff).2 (hf v)
            spec := ?_
            Λ := Λ
            Λ_fg := hlat.fg
            Λ_span := hspan
            Λ_dual := ?_ }, rfl, fun τ => ?_⟩
  · intro v
    set τ := (Formalism.L2.Host.tauPl D).symm v
    have hg : V.gram.map (Formalism.IndefR.Eqv.UI.phiV D v) = (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
      rw [A.fr_gram τ]; rfl
    have hd : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hf v)
    have hdH : IsUnit ((A.fr τ)ᴴ).det := by
      rw [Matrix.det_conjTranspose]; exact hd.star
    rw [hg, Matrix.conjTranspose_nonsing_inv]
    calc ((A.fr τ)ᴴ)⁻¹ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ) * (A.fr τ)⁻¹
        = (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (A.ε τ) := by
          rw [Matrix.nonsing_inv_mul _ hdH, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · intro x
    rw [hdual x]
    refine forall₂_congr fun y _ => ?_
    unfold Formalism.UG.hform
    simp only [RingHom.mem_range, starRingEnd_apply]
  · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInstanceFramesOfDiagonalFrameSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_instanceFrames_of_diagonalFrame_selfDual : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  first | exact @GlobalTheory.frames_of_diagonalising_frame | exact GlobalTheory.frames_of_diagonalising_frame | (intros; apply GlobalTheory.frames_of_diagonalising_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallS
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HformSpanEqZero
noncomputable section

namespace GlobalTheory.HermitianFormLinearity

open NumberField

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem hform_add_left (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (x + x') y =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (y + y') =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (c • x) y =
      starRingEnd E c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (c • y) =
      c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_zero_left (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem hform_zero_right (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x 0 = 0 := by
  simp [Formalism.UG.hform]

theorem hform_span_eq_zero (J : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (hS : ∀ y ∈ S, ∀ z ∈ S, Formalism.UG.hform (starRingEnd E) J y z = 0) :
    ∀ x ∈ Submodule.span E S, ∀ y ∈ Submodule.span E S,
      Formalism.UG.hform (starRingEnd E) J x y = 0 := by
  have h1 : ∀ x ∈ S, ∀ y ∈ Submodule.span E S, Formalism.UG.hform (starRingEnd E) J x y = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hS x hx z hz
    | zero => exact hform_zero_right J x
    | add a b _ _ ha hb => rw [hform_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [hform_smul_right, ha, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem z hz => exact h1 z hz y hy
  | zero => exact hform_zero_left J y
  | add a b _ _ ha hb => rw [hform_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [hform_smul_left, ha, mul_zero]

theorem main : ∀ (I : Formalism.MainNotions.S.AutInst)
    (R : Submodule (NumberField.RingOfIntegers (Formalism.MainNotions.S.AutInst.E I))
      (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I)),
    R ≠ ⊥ →
    (∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd (Formalism.MainNotions.S.AutInst.E I)) (Formalism.MainNotions.S.AutInst.J I) y z
      = (0 : Formalism.MainNotions.S.AutInst.E I)) →
    Formalism.MainNotions.S.AutInst.IsIsot I (Submodule.span (Formalism.MainNotions.S.AutInst.E I)
      (↑R : Set (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I))) := by
  intro I R hR hiso
  refine ⟨?_, hform_span_eq_zero I.J _ hiso⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  intro h
  apply hr0
  have : r ∈ Submodule.span I.E (↑R : Set (Fin I.n → I.E)) := Submodule.subset_span hr
  rw [h] at this
  exact (Submodule.mem_bot _).1 this

end GlobalTheory.HermitianFormLinearity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallS
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

noncomputable section

namespace GlobalTheory.DeepPoint


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem kg_one (I : AutInst) (m : ℕ) : (1 : I.Gf) ∈ I.Kg m :=
  ⟨K_one I, fun y _ => ⟨0, zero_mem _, by rw [fmat_one, sub_self, Matrix.zero_mulVec, smul_zero]⟩⟩


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem kg_mul (I : AutInst) (m : ℕ) {x y : I.Gf} (hx : x ∈ I.Kg m) (hy : y ∈ I.Kg m) : x * y ∈ I.Kg m := by
  refine ⟨K_mul I hx.1 hy.1, fun v hv => ?_⟩
  obtain ⟨z, hz, hyz⟩ := hy.2 v hv
  obtain ⟨z', hz', hxz⟩ := hx.2 v hv
  refine ⟨I.fmat x *ᵥ z + z', add_mem (K_mv I hx.1 hz) hz', ?_⟩
  have e : (I.fmat (x * y) - 1) *ᵥ v = I.fmat x *ᵥ ((I.fmat y - 1) *ᵥ v) + (I.fmat x - 1) *ᵥ v := by
    rw [fmat_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      Matrix.one_mulVec]
    abel
  rw [e, hyz, hxz, Matrix.mulVec_smul, smul_add]


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem kg_inv (I : AutInst) (m : ℕ) {k : I.Gf} (hk : k ∈ I.Kg m) : k⁻¹ ∈ I.Kg m := by
  refine ⟨K_inv I hk.1, fun y hy => ?_⟩
  obtain ⟨z, hz, hkz⟩ := hk.2 y hy
  refine ⟨-(I.fmat k⁻¹ *ᵥ z), neg_mem (K_mv I (K_inv I hk.1) hz), ?_⟩
  have h1 : I.fmat k⁻¹ * I.fmat k = 1 := fmat_inv_mul I k
  have e : (I.fmat k⁻¹ - 1) *ᵥ y = -(I.fmat k⁻¹ *ᵥ ((I.fmat k - 1) *ᵥ y)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, h1, mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [e, hkz, Matrix.mulVec_smul, smul_neg]

theorem isIsot_span (I : AutInst) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (h0 : R ≠ ⊥)
    (hiso : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) :
    I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
  first
  | exact @_root_.GlobalTheory.HermitianFormLinearity.main
  | exact _root_.GlobalTheory.HermitianFormLinearity.main
  | (apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.HermitianFormLinearity.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HermitianFormLinearity.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HermitianFormLinearity.main ..)

theorem exists_step (I : AutInst) (x : I.GA) (q : ℕ) (hn : 1 ≤ I.n)
    (hrk : ∀ v, rkR (I.ε v) ≤ q) (hl : least I x < 1 / 2) :
    ∃ (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi : ℝ),
      IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R ∧ R ≠ ⊥ ∧ R ≤ stepLt I x (1 / 2) ∧
      R ≤ lamX I x ∧ 0 < hi ∧ largestSize (bas I) (frm I x) R ≤ hi ∧
      (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) ∧
      hi ≤ (2 * least I x) ^ ((1 : ℝ) / q) * lo ∧ hi ^ 2 ≤ (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hspec⟩ := GlobalTheory.PointFlag.flag_spec I x
  have hpiece := (hspec a S τ hF).1
  have ha0 := ((hspec a S τ hF).2 hn).1
  have hτ0 := ((hspec a S τ hF).2 hn).2
  obtain ⟨hS0, hSmono, hSlast, hτmono, hτ, -⟩ := hF
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact absurd (ha0.1 h) (not_le.2 hl)
    · exact h
  have hrkS : ∀ i : Fin (a + 1), (i : ℕ) ≤ rkK (S i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have := (hpiece i).2.1
      simp only [Fin.coe_castSucc] at ih
      simp only [Fin.val_succ]
      omega
  have haq : a ≤ q := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
    have h1 := hrkS (Fin.last a)
    rw [hSlast] at h1
    have h2 := (GlobalTheory.FlagIso.flag_isotropic I x).2.1 v
    simp only [Fin.val_last] at h1
    exact h1.trans (h2.trans (hrk v))
  set τ' : ℕ → ℝ := fun i => if h : i < a then τ ⟨i, h⟩ else 1 / 2 with hτ'
  have hτ'pos : ∀ i ≤ a, 0 < τ' i := by
    intro i _
    simp only [hτ']
    split_ifs with h
    · exact (hτ ⟨i, h⟩).1
    · norm_num
  have hτ'lt : ∀ i < a, τ' i < τ' (i + 1) := by
    intro i hi
    simp only [hτ', dif_pos hi]
    split_ifs with h
    · exact hτmono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
    · exact (hτ ⟨i, hi⟩).2.1
  have hτ'a : τ' a = 1 / 2 := by simp [hτ']
  have hτ'0 : τ' 0 = least I x := by
    simp only [hτ', dif_pos (show 0 < a by omega)]
    exact hτ0 (by omega)
  obtain ⟨b, hb, hratio, hsq⟩ := GlobalTheory.exists_consecutive_ratio_le_rpow a q τ' ha haq hτ'pos hτ'lt hτ'a
  rw [hτ'0] at hratio hsq
  set i : Fin a := ⟨b, hb⟩ with hi_def
  have hib : τ' b = τ i := by simp [hτ', hb, i]
  refine ⟨S i.succ, τ' (b + 1), τ i, ?_, ?_, ?_, ?_, (hτ i).1, ?_, ?_, ?_, ?_⟩
  · rw [(hτ i).2.2.1]; exact (GlobalTheory.CountSteps.steps I x _ (hτ i).1).1
  · intro h
    have := hSmono (Fin.succ_pos i)
    rw [hS0, h] at this
    exact lt_irrefl _ this
  · rw [← hSlast]; exact hSmono.monotone (Fin.le_last _)
  · rw [(hτ i).2.2.1]; exact sSup_le fun N hN => hN.1
  · exact (hpiece i).2.2.1.le
  · intro N hN hNL
    by_cases hb1 : b + 1 < a
    · have eS : S i.succ = S (Fin.castSucc (⟨b + 1, hb1⟩ : Fin a)) := congrArg S (Fin.ext (by simp [i]))
      have e : τ' (b + 1) = τ ⟨b + 1, hb1⟩ := by simp [hτ', hb1]
      rw [e, eS]
      rw [eS] at hN
      exact (hpiece ⟨b + 1, hb1⟩).2.2.2.1 N hN hNL
    · have hba : b + 1 = a := by omega
      have e : τ' (b + 1) = 1 / 2 := by rw [hba, hτ'a]
      have eS : S i.succ = stepLt I x (1 / 2) := by
        rw [← hSlast]; exact congrArg S (Fin.ext (by simp [i, hba]))
      rw [e, eS]
      rw [eS] at hN
      exact (GlobalTheory.CountSteps.steps I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hN hNL
  · rw [← hib]
    have hpos := hτ'pos (b + 1) (by omega)
    rwa [div_le_iff₀ hpos] at hratio
  · rw [← hib]; exact hsq

theorem deep_point : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n →
    (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset,
      ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ),
        (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧
        (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧
        Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤
          (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  intro I x g q hg _ hn hrk hl
  obtain ⟨R, lo, hi, hsat, hR0, hRS, hRL, hhi, hlarge, hlo, hhl, hh2⟩ := exists_step I x q hn hrk hl
  have hisoR : ∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 :=
    fun y hy z hz => (GlobalTheory.FlagIso.flag_isotropic I x).1 y (hRS hy) z (hRS hz)
  have hperp : R ≤ perpIn I x R := fun y hy =>
    Submodule.subset_span ⟨hRL hy, fun s hs => hisoR s hs y hy⟩
  have hWiso : I.IsIsot (Submodule.span I.E (R : Set (Fin I.n → I.E))) := isIsot_span I R hR0 hisoR
  refine ⟨_, hWiso, fun m hm => ?_⟩
  obtain ⟨⟨N, hN⟩, -, hsplit, hdense, -⟩ := GlobalTheory.UnipApprox.strong_approximation I _ hWiso
  have hU : {c : I.Gf | x.2⁻¹ * c * x.2 ∈ I.Kg g} ∈ nhds (1 : I.Gf) := by
    have ho : IsOpen (I.Kg g) := I.topf_open g hg
    have hc : Continuous fun c : I.Gf => x.2⁻¹ * c * x.2 :=
      (continuous_const.mul continuous_id).mul continuous_const
    refine (ho.preimage hc).mem_nhds ?_
    show x.2⁻¹ * 1 * x.2 ∈ I.Kg g
    rw [mul_one, inv_mul_cancel]
    exact kg_one I g
  obtain ⟨γ, ⟨hγF, hγN⟩, hγU⟩ := hdense _ hU m hm
  have hm'N : γ⁻¹ * m ∈ I.NA (Submodule.span I.E (R : Set (Fin I.n → I.E))) := by
    rw [← hN] at hγN hm ⊢
    exact N.mul_mem (N.inv_mem hγN) hm
  have hν := (hsplit _ hm'N).1
  obtain ⟨γ', ⟨hγ'F, -⟩, hγ'K, A, Z, hAZ, heq, hbd, -⟩ :=
    GlobalTheory.SmallFund.small_fundamental_set I x g R lo hi _ hg hsat hR0 hperp hhi hlarge hlo hhl hh2 _ hν
  have hk : (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2) ∈ I.Kg g :=
    kg_mul I g (kg_inv I g hγ'K) hγU
  refine ⟨γ * γ', Formalism.MainNotions.LeviCoordinates.rrg_mul_mem I hγF hγ'F, _, hk,
    (γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1, A, Z, hAZ, fun v => ?_, ?_, hbd⟩
  · have e : uMat (((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1) v) =
        uMat ((γ'.1 v * x.1 v)⁻¹) * (uMat ((γ⁻¹ * m).1 v) * uMat (x.1 v)) := by
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [mul_assoc]
      rfl
    rw [e, heq v]
    have e2 : uMat (γ'.1 v) * uMat (x.1 v) = uMat (γ'.1 v * x.1 v) := rfl
    have e3 : uMat ((γ'.1 v * x.1 v)⁻¹) * uMat (γ'.1 v * x.1 v) = 1 := by
      show uMat ((γ'.1 v * x.1 v)⁻¹ * (γ'.1 v * x.1 v)) = 1
      rw [inv_mul_cancel]
      rfl
    rw [e2, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat ((γ'.1 v * x.1 v)⁻¹)), e3, Matrix.one_mul]
  · have h2 : γ' * x * ((γ'.1 * x.1)⁻¹ * (γ⁻¹ * m).1 * x.1,
        (x⁻¹ * γ' * x).2⁻¹ * (x.2⁻¹ * (γ⁻¹ * m).2 * x.2)) = (γ⁻¹ * m) * x := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_mul]
        group
      · simp only [Prod.snd_mul, Prod.snd_inv]
        group
    calc m * x = γ * ((γ⁻¹ * m) * x) := by group
      _ = γ * γ' * x * _ := by rw [← h2]; simp only [mul_assoc]

end GlobalTheory.DeepPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallSStatement
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size : ∀ (I : AutInst) (x : I.GA) (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ I.n → (∀ v, rkR (I.ε v) ≤ q) → least I x < 1 / 2 → ∃ W, I.IsIsot W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset, ∃ k ∈ I.Kg g, ∃ (u : I.Ginf) (A Z : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ), (∀ v, inG (I.ε v) (A v) ∧ inG (I.ε v) (Z v)) ∧ (∀ v, uMat (u v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v)) ∧ m * x = γ * x * (u, k) ∧ Real.sqrt (∑ v, hs (A v)) + Real.sqrt (∑ v, hs (Z v)) ≤ (I.n : ℝ) ^ 2 * Real.sqrt I.f * g * I.rd * (2 * least I x) ^ ((1 : ℝ) / q) / 4 := by
  first | exact @GlobalTheory.DeepPoint.deep_point | exact GlobalTheory.DeepPoint.deep_point | (intros; apply GlobalTheory.DeepPoint.deep_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeastSizePowMulSqrtAbsNormLeProdNorms
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeastSizePowMulSqrtAbsNormLeProdNorms
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN

noncomputable section

namespace GlobalTheory.LineBound

theorem relIndex_span_singleton {K : Type} [Field K] [NumberField K] (𝔪 𝔟 : Ideal (𝓞 K)) (a : 𝓞 K)
    (ha : a ≠ 0) (h : Ideal.span {a} = 𝔪 * 𝔟) :
    (Ideal.span {a}).toAddSubgroup.relIndex 𝔟.toAddSubgroup = Ideal.absNorm 𝔪 := by
  have hle : Ideal.span {a} ≤ 𝔟 := by rw [h, mul_comm]; exact Ideal.mul_le_left
  have h1 := AddSubgroup.relIndex_mul_index
    (show (Ideal.span {a}).toAddSubgroup ≤ 𝔟.toAddSubgroup from hle)
  have h2 : (Ideal.span {a}).toAddSubgroup.index = Ideal.absNorm 𝔪 * Ideal.absNorm 𝔟 := by
    rw [← map_mul, ← h, Ideal.absNorm_apply]; rfl
  have h3 : 𝔟.toAddSubgroup.index = Ideal.absNorm 𝔟 := by rw [Ideal.absNorm_apply]; rfl
  have hb : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at h
    exact ha h
  have hb0 : Ideal.absNorm 𝔟 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [h2, h3] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hb0) h1

theorem ht_nonneg {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : 0 ≤ ht b X L := by
  unfold ht
  have hc : 0 ≤ Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) L) := by
    unfold Formalism.F.covol
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact le_rfl
  exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _)) hc

theorem size_nonneg {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : 0 ≤ size b X L :=
  Real.rpow_nonneg (ht_nonneg b X L) _

end GlobalTheory.LineBound

namespace GlobalTheory.LineBound

theorem least_pow_mul_sqrt_absNorm_le_prod : ∀ (I : AutInst) (x : I.GA) (𝔪 : Ideal (𝓞 I.E)), 𝔪 ≠ ⊥ →
    ∀ w ∈ 𝔪 • lamX I x, w ≠ 0 → least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪) ≤
      ∏ v, Real.sqrt (∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2) := by
  intro I x 𝔪 h𝔪 w hw hw0
  obtain ⟨hTC, hf, -, hbij, hX0⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  haveI := hTC
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hX0 v).1
  obtain ⟨a, ha𝔪, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  obtain ⟨𝔟, h𝔟⟩ := (Ideal.dvd_span_singleton).2 ha𝔪
  have haE : (a : I.E) ≠ 0 := by exact_mod_cast ha0
  set u : Fin I.n → I.E := (a : I.E)⁻¹ • w with hu
  set ℓ : 𝓞 I.E →ₗ[𝓞 I.E] (Fin I.n → I.E) := LinearMap.toSpanSingleton (𝓞 I.E) _ u with hℓ
  have hℓapp : ∀ c : 𝓞 I.E, ℓ c = (c : I.E) • u := fun c => by
    rw [hℓ, LinearMap.toSpanSingleton_apply]
    exact (algebraMap_smul I.E c u).symm
  have hℓa : ℓ a = w := by rw [hℓapp, hu, smul_smul, mul_inv_cancel₀ haE, one_smul]
  have hu0 : u ≠ 0 := by
    rw [hu]; exact smul_ne_zero (inv_ne_zero haE) hw0
  have hinj : Function.Injective ℓ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hℓapp] at hc
    have : (c : I.E) = 0 := (smul_eq_zero.1 hc).resolve_right hu0
    exact_mod_cast this
  set R : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.map ℓ 𝔟 with hR
  have hab : a ∈ 𝔟 := by
    have : Ideal.span {a} ≤ 𝔟 := by rw [h𝔟, mul_comm]; exact Ideal.mul_le_left
    exact this (Ideal.mem_span_singleton_self a)
  have hwR : w ∈ R := ⟨a, hab, hℓa⟩

  have hRle : R ≤ lamX I x := by
    have key : ∀ y ∈ 𝔪 • lamX I x, ∀ c ∈ 𝔟, ((c : I.E) * (a : I.E)⁻¹) • y ∈ lamX I x := by
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro m hm l hl c hc
        have hmc : m * c ∈ Ideal.span {a} := by rw [h𝔟]; exact Ideal.mul_mem_mul hm hc
        obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hmc
        have hdE : (d : I.E) = (c : I.E) * (a : I.E)⁻¹ * (m : I.E) := by
          have : (d : I.E) * (a : I.E) = (m : I.E) * (c : I.E) := by exact_mod_cast hd
          field_simp
          linear_combination this
        have : ((c : I.E) * (a : I.E)⁻¹) • (m • l) = d • l := by
          rw [← algebraMap_smul I.E m l, smul_smul, ← algebraMap_smul I.E d l]
          congr 1
          exact hdE.symm
        rw [this]
        exact (lamX I x).smul_mem d hl
      · intro y z hy hz c hc
        rw [smul_add]
        exact add_mem (hy c hc) (hz c hc)
    rintro y ⟨c, hc, rfl⟩
    rw [hℓapp, hu, smul_smul]
    exact key w hw c hc
  have hRfg : R.FG := (IsNoetherian.noetherian 𝔟).map ℓ
  have hR0 : R ≠ ⊥ := fun h => hw0 ((Submodule.mem_bot _).1 (h ▸ hwR))
  have hrange : Set.range (fun _ : Fin 1 => w) = {w} := Set.range_const
  have hli : LinearIndependent I.E (fun _ : Fin 1 => w) := LinearIndependent.of_subsingleton 0 hw0
  have hspanw : Submodule.span (𝓞 I.E) {w} = Submodule.map ℓ (Ideal.span {a}) := by
    rw [Ideal.span, Submodule.map_span, Set.image_singleton, hℓa]
  have hwle : Submodule.span (𝓞 I.E) (Set.range fun _ : Fin 1 => w) ≤ R := by
    rw [hrange, Submodule.span_le, Set.singleton_subset_iff]; exact hwR
  have hrk : rkK R = 1 := by
    unfold rkK
    have : Submodule.span I.E (R : Set (Fin I.n → I.E)) = Submodule.span I.E {w} := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro y ⟨c, -, rfl⟩
        rw [hℓapp, hu, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span hwR
    rw [this, finrank_span_singleton hw0]
  have hidx : (Submodule.span (𝓞 I.E) (Set.range fun _ : Fin 1 => w)).toAddSubgroup.relIndex
      R.toAddSubgroup = Ideal.absNorm 𝔪 := by
    rw [hrange, hspanw, hR, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
    exact relIndex_span_singleton 𝔪 𝔟 a ha0 h𝔟
  obtain ⟨hG1, hG2⟩ := htGram I.E (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x) hX 1 (fun _ => w) hli
  have hht := hG2 R hRfg hwle (by rw [hrk])
  rw [hidx, hG1] at hht

  set g : InfinitePlace I.F → ℝ := fun v =>
    ∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2 with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => Finset.sum_nonneg fun i _ => by positivity
  have hdet : ∀ w' : InfinitePlace I.E,
      (gramPl (bas I) (frm I x) w' (fun _ : Fin 1 => w)).det.re = g (w'.comap (algebraMap I.F I.E)) := by
    intro w'
    rw [GlobalTheory.FlagMeas.SizeMove.norm_det_gram, Matrix.det_fin_one, Matrix.of_apply]
    have hU : uMat (x.1 (w'.comap (algebraMap I.F I.E)))⁻¹ = (uMat (x.1 (w'.comap (algebraMap I.F I.E))))⁻¹ := by
      simp [uMat]
    rw [hg]
    simp only [hU, GlobalTheory.FlagMeas.SizeMove.crd]
    set z := (uMat (x.1 (w'.comap (algebraMap I.F I.E))))⁻¹ *ᵥ
      ((I.P (w'.comap (algebraMap I.F I.E)))⁻¹ *ᵥ fun l => I.φ (w'.comap (algebraMap I.F I.E)) (w l))
    have : star z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
  have hprod : ∏ w' : InfinitePlace I.E, (gramPl (bas I) (frm I x) w' (fun _ : Fin 1 => w)).det.re =
      ∏ v, g v := by
    simp only [hdet]
    exact Fintype.prod_bijective _ hbij _ _ (fun _ => rfl)
  rw [hprod] at hht

  have hbdd : BddBelow {t | ∃ S : Submodule (𝓞 I.E) (Fin I.n → I.E), S ≤ lamX I x ∧ S ≠ ⊥ ∧
      size (bas I) (frm I x) S = t} := ⟨0, by rintro t ⟨S, -, -, rfl⟩; exact size_nonneg _ _ _⟩
  have hle : least I x ≤ size (bas I) (frm I x) R := csInf_le hbdd ⟨R, hRle, hR0, rfl⟩
  have h0 : 0 ≤ least I x := le_csInf ⟨_, ⟨R, hRle, hR0, rfl⟩⟩ (by rintro t ⟨S, -, -, rfl⟩; exact size_nonneg _ _ _)
  have hfpos : 0 < nPl I.E := Fintype.card_pos
  have hsz : size (bas I) (frm I x) R ^ (2 * I.f) = ht (bas I) (frm I x) R := by
    unfold size
    rw [hrk, ← Real.rpow_natCast, ← Real.rpow_mul (ht_nonneg _ _ _), ← hf]
    have : (1 : ℝ) / (2 * (nPl I.E : ℝ) * ((1 : ℕ) : ℝ)) * ((2 * nPl I.E : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  have hN0 : (0 : ℝ) ≤ Ideal.absNorm 𝔪 := Nat.cast_nonneg _
  have hsq : (least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪)) ^ 2 ≤
      (∏ v, Real.sqrt (g v)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN0, ← Finset.prod_pow]
    simp only [fun v => Real.sq_sqrt (hg0 v)]
    rw [← hht, ← pow_mul, mul_comm I.f 2, ← hsz]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hle _) hN0
  exact (pow_le_pow_iff_left₀ (by positivity) (Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _)
    two_ne_zero).1 hsq

end GlobalTheory.LineBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeastSizePowMulSqrtAbsNormLeProdNormsStatement
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count Formalism.REAL Formalism.HN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leastSize_pow_mul_sqrt_absNorm_le_prod_norms : ∀ (I : AutInst) (x : I.GA) (𝔪 : Ideal (𝓞 I.E)), 𝔪 ≠ ⊥ → ∀ w ∈ 𝔪 • lamX I x, w ≠ 0 → least I x ^ I.f * Real.sqrt (Ideal.absNorm 𝔪) ≤ ∏ v, Real.sqrt (∑ i, ‖(uMat (x.1 v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun j => I.φ v (w j))) i‖ ^ 2) := by
  first | exact @GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod | exact GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod | (intros; apply GlobalTheory.LineBound.least_pow_mul_sqrt_absNorm_le_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCuspFormLeOfShortLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ShortLineCusp

theorem sum_sqrt_le (ι : Type) [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, Real.sqrt (a i) ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, a i) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => Real.sqrt (a i))
  simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul,
    Real.sq_sqrt (ha _)] at h1
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  simpa [Real.sq_sqrt (ha _)] using h1

theorem sum_sqrt_add_le : ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → ∑ i, (Real.sqrt (a i) + Real.sqrt (b i)) ≤ Real.sqrt (Fintype.card ι) * (Real.sqrt (∑ i, a i) + Real.sqrt (∑ i, b i)) := by
  intro ι _ a b ha hb
  rw [Finset.sum_add_distrib, mul_add]
  exact add_le_add (sum_sqrt_le ι a ha) (sum_sqrt_le ι b hb)

theorem finrank_eq_card_and_rd : ∀ D : D7, Module.finrank ℚ D.host.F = Fintype.card D.what₂.Tau ∧ |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (2 * (Module.finrank ℚ D.host.F : ℝ))) = rdisc D := by
  intro D
  haveI := D.sp.cm.totReal
  refine ⟨?_, ?_⟩
  · rw [Fintype.card_congr (Formalism.L2.Host.tauPl D), ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  · unfold rdisc
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    congr 1
    push_cast
    ring

theorem least_nonneg : ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), 0 ≤ GlobalTheory.Count.least I x := by
  intro I x
  unfold GlobalTheory.Count.least Formalism.HN.leastSize
  apply Real.sInf_nonneg
  rintro t ⟨R, -, -, rfl⟩
  unfold Formalism.HN.size Formalism.HN.ht Formalism.F.covol
  apply Real.rpow_nonneg
  apply mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _))
  split_ifs <;> positivity

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem norm_le_of_not_long : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∀ (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ V.rank → (∀ τ, min (Finset.univ.filter fun a => A.ε τ a = true).card (Finset.univ.filter fun a => A.ε τ a = false).card ≤ q) → ∀ φ : GA D V → ℂ, IsAutFun V φ → IsCuspFun V φ → (∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})), ∀ x, φ (x * k) = φ x) → ∀ c : ℝ, 0 ≤ c → Lip θ A φ c → ∀ (x : GA D V) (s : ℝ), 0 < s → s ≤ 1 / 2 → ¬ Long θ A Λ x s → ‖φ x‖ ≤ c * ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q)) := by
  intro D θ hθ V A Λ hΛ g q hg hq hn hrk φ hφ hcusp hlev c hc hlip x s hs hs2 hlong
  obtain ⟨fr, hfrΛ, hfr⟩ := GlobalTheory.T.exists_instanceFrames_of_diagonalFrame_selfDual D V A Λ hΛ
  subst hfrΛ
  obtain ⟨hfF, hrdE⟩ := finrank_eq_card_and_rd D
  have hfI : (Formalism.IndefR.Eqv.UI.instV fr).f = Fintype.card D.what₂.Tau := hfF
  have hrdI : (Formalism.IndefR.Eqv.UI.instV fr).rd = rdisc D := hrdE
  set x0 := (Formalism.IndefR.Eqv.UI.brg fr).symm x with hx0
  have hbx : Formalism.IndefR.Eqv.UI.brg fr x0 = x := by simp [hx0]
  have hl0 : 0 ≤ GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 := least_nonneg _ x0
  have hlt : GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 < s := by
    by_contra hge
    push_neg at hge
    apply hlong
    intro 𝔪 h𝔪 w hw hw0
    have hL := GlobalTheory.T.adelicPointRationalLattice_unitaryModelIso_eq D V fr x0
    rw [hbx] at hL
    rw [hL] at hw
    have h1 := GlobalTheory.T.leastSize_pow_mul_sqrt_absNorm_le_prod_norms (Formalism.IndefR.Eqv.UI.instV fr) x0 𝔪 h𝔪 w hw hw0
    rw [GlobalTheory.T.rationalVectorNorm_adelicPoint_twoModels_eq D θ hθ V A fr (fun τ => (hfr τ).2) x0 w, hbx, hfI] at h1
    exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hge _) (Real.sqrt_nonneg _)) h1
  have hrkI : ∀ v, GlobalTheory.Count.rkR ((Formalism.IndefR.Eqv.UI.instV fr).ε v) ≤ q := by
    intro (v : InfinitePlace D.host.F)
    have h := (hfr ((Formalism.L2.Host.tauPl D).symm v)).1
    have e : (Formalism.L2.Host.tauPl D) ((Formalism.L2.Host.tauPl D).symm v) = v := Equiv.apply_symm_apply _ _
    rw [e] at h
    show GlobalTheory.Count.rkR (fr.ε v) ≤ q
    rw [h]
    exact hrk _
  obtain ⟨W, hW, hmv⟩ := GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size (Formalism.IndefR.Eqv.UI.instV fr) x0 g q hg hq hn hrkI (hlt.trans_le hs2)
  obtain ⟨hGQ, -, hN⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  obtain ⟨r, C₀, hC₀, hNI⟩ := hN W hW
  apply GlobalTheory.CuspGeo.norm_le_of_unipRad_variation D V φ hφ hcusp r C₀ hC₀ x
  intro m hm
  have hm' : (Formalism.IndefR.Eqv.UI.brg fr).symm m ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W :=
    hNI _ (by simpa using hm)
  obtain ⟨γ, hγ, k, hk, u, Av, Z, hAZ, hu, heq, hbd⟩ := hmv _ hm'
  have hmx : m * x = Formalism.IndefR.Eqv.UI.brg fr γ * (x * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) * Formalism.IndefR.Eqv.UI.brg fr (1, k) := by
    have h2 := congrArg (Formalism.IndefR.Eqv.UI.brg fr) heq
    have h3 : ((u, k) : (Formalism.IndefR.Eqv.UI.instV fr).GA) = (u, 1) * (1, k) := by simp
    rw [h3] at h2
    simp only [map_mul, hbx, ContinuousMulEquiv.apply_symm_apply] at h2
    rw [h2]; group
  rw [hmx, hlev _ (GlobalTheory.T.principalCongruence_mem_latticeCongruenceLevel D V fr g hg k hk), hφ.left _ ((hGQ γ).2 hγ)]
  have h6 := GlobalTheory.T.lipschitz_bound_real_unipotent_action D θ hθ V A fr (fun τ => (hfr τ).2) φ c hc hlip u Av Z hAZ hu x
  have h7 := sum_sqrt_add_le (InfinitePlace D.host.F) (fun v => Formalism.REAL.hs (Av v)) (fun v => Formalism.REAL.hs (Z v))
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hcard : Fintype.card (InfinitePlace D.host.F) = Fintype.card D.what₂.Tau :=
    Fintype.card_congr (Formalism.L2.Host.tauPl D).symm
  rw [hcard] at h7
  rw [hfI, hrdI] at hbd
  have hL : (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) ≤ (2 * s) ^ ((1 : ℝ) / q) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hL0 : 0 ≤ (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) := by positivity
  have hrd0 : 0 ≤ rdisc D := by unfold rdisc; positivity
  have hN : Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau) = Fintype.card D.what₂.Tau :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hP : 0 ≤ (V.rank : ℝ) ^ 2 * (Fintype.card D.what₂.Tau : ℝ) * (g : ℝ) * rdisc D := by positivity
  have hbd' : Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v))) ≤
      (V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q) := by
    calc _ ≤ Real.sqrt (Fintype.card D.what₂.Tau) * ((V.rank : ℝ) ^ 2 * Real.sqrt (Fintype.card D.what₂.Tau) * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4) :=
          mul_le_mul_of_nonneg_left hbd (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau)) * ((V.rank : ℝ) ^ 2 * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q)) / 4 := by ring
      _ = ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D) *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4 := by rw [hN]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hL hP, mul_nonneg hP hL0]
  calc _ ≤ _ := h6
    _ ≤ c * (Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)))) := mul_le_mul_of_nonneg_left h7 hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hbd' hc

end GlobalTheory.ShortLineCusp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCuspFormLeOfShortLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_cuspForm_le_of_shortLine : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∀ (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ V.rank → (∀ τ, min (Finset.univ.filter fun a => A.ε τ a = true).card (Finset.univ.filter fun a => A.ε τ a = false).card ≤ q) → ∀ φ : GA D V → ℂ, IsAutFun V φ → IsCuspFun V φ → (∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})), ∀ x, φ (x * k) = φ x) → ∀ c : ℝ, 0 ≤ c → Lip θ A φ c → ∀ (x : GA D V) (s : ℝ), 0 < s → s ≤ 1 / 2 → ¬ Long θ A Λ x s → ‖φ x‖ ≤ c * ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q)) := by
  first | exact @GlobalTheory.ShortLineCusp.norm_le_of_not_long | exact GlobalTheory.ShortLineCusp.norm_le_of_not_long | (intros; apply GlobalTheory.ShortLineCusp.norm_le_of_not_long <;> assumption)
end
