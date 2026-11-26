module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsIdentityOfEqualFlags
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocRealAtOrd

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnipotentFrameFixers
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem equiv_of_corr {X L S : Type*} (P : X → Prop) (cl : X → S) (G : Set L) (R : X → L → Prop)
    (ha : ∀ x, P x → ∃ y ∈ G, R x y) (hb : ∀ y ∈ G, ∃ x, P x ∧ R x y)
    (hc : ∀ x x' y y', P x → P x' → R x y → R x' y' → (y = y' ↔ cl x = cl x')) :
    Nonempty ({O | ∃ x, P x ∧ O = cl x} ≃ G) := by
  refine ⟨{ toFun := fun O => ⟨(ha _ O.2.choose_spec.1).choose, (ha _ O.2.choose_spec.1).choose_spec.1⟩
            invFun := fun y => ⟨cl (hb y.1 y.2).choose, _, (hb y.1 y.2).choose_spec.1, rfl⟩
            left_inv := ?_
            right_inv := ?_ }⟩
  · rintro ⟨O, hO⟩
    apply Subtype.ext
    have h1 := (ha _ hO.choose_spec.1).choose_spec
    have h2 := (hb _ h1.1).choose_spec
    have h3 := (hc _ _ _ _ hO.choose_spec.1 h2.1 h1.2 h2.2).1 rfl
    show cl (hb _ h1.1).choose = O
    exact (hO.choose_spec.2.trans h3).symm
  · rintro ⟨y, hy⟩
    apply Subtype.ext
    have h2 := (hb y hy).choose_spec
    have hm : ∃ x, P x ∧ cl (hb y hy).choose = cl x := ⟨_, h2.1, rfl⟩
    have h4 := (ha _ hm.choose_spec.1).choose_spec
    show (ha _ hm.choose_spec.1).choose = y
    exact (hc _ _ _ _ hm.choose_spec.1 h2.1 h4.2 h2.2).2 hm.choose_spec.2.symm

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def unipotentFrameFixers {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {n | n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, ∀ x ∈ Xflag (lf D F0) (j + 1), n x - x ∈ Xflag (lf D F0) j) ∧
    (∀ x ∈ orth (VS D) (Xsp (lf D F0)), n x - x ∈ Xsp (lf D F0)) ∧ (∀ a, n (F0.e a) = F0.e a) ∧ n F0.z = F0.z}

def Moves {T' : D.host.E} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') : Prop :=
  (∀ a, n (F'.fl.e a) = F''.fl.e a) ∧ n F'.fl.z = F''.fl.z

def IsPartner (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧
    ∃ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' ∧
      Rep γ'.lam (lf D F0) (PD D γ'.lam (lf D F0) u') γ'.cls F'

def cls (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Set (LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :=
  {F'' | F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z ∧ CntLocal.NilradicalFlagMoved F0 γ.lam F' F''}

theorem frPart_eq (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) :
    frPart γ Z = {O | ∃ F', IsPartner γ Z F' ∧ O = cls γ Z F'} := by
  ext O
  constructor
  · rintro ⟨F', h1, h2, h3⟩
    exact ⟨F', ⟨h1, h2⟩, h3⟩
  · rintro ⟨F', ⟨h1, h2⟩, h3⟩
    exact ⟨F', h1, h2, h3⟩

def RelN (γ : TermDef.Term D u u' F0 what₂) (F'₂ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  ∃ n ∈ unipotentFrameFixers F0, Moves n F'₂ F' ∧ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

def Ctx (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) : Prop :=
  ∃ w : Point D.host.E (D.R.rS + 1), EligAt γ w ∧ ∃ w' : Point D.host.E (D.R.rS + 1),
    Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 ∧ kind w' = kind w ∧ AtMat w' Z

def StarHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  ZhatL (lf D F0) F'₂ = Z ∧
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) ∧
    ∀ p, φ p = LinearEquiv.refl _ _

def Coherent (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)) : Prop :=
  ∃ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ₀ ∧
    {p | locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) ≠ {lattice₂ D Zd.M p Λ₀}}.Finite

variable (u u' F0 what₂)

def StarExists2 : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' ∧ Coherent Zd γ F'₂ φ φ'

def FwdC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ F', IsPartner γ Z F' → ∃ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', RelN γ F'₂ F' Λ₂

def BwdC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∃ F', IsPartner γ Z F' ∧ RelN γ F'₂ F' Λ₂

def UniqC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ F' F'' Λ₂ Λ₃, IsPartner γ Z F' → IsPartner γ Z F'' → RelN γ F'₂ F' Λ₂ → RelN γ F'₂ F'' Λ₃ →
        (Λ₂ = Λ₃ ↔ cls γ Z F' = cls γ Z F'')

variable {u u' F0 what₂}

theorem fStarC_of_route2 (h1 : StarExists2 Zd u u' F0 what₂) (h2 : FwdC Zd u u' F0 what₂) (h3 : BwdC Zd u u' F0 what₂)
    (h4 : UniqC Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ
  have hC : Ctx γ Z := ⟨w, hγ, w', hG', hk, hZ⟩
  obtain ⟨F'₂, φ, φ', hS, hCoh⟩ := h1 γ Z hC
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hCoh
  letI := hΛ₀
  refine ⟨F'₂, φ, φ', hS.1, hS.2.2, hS.2.1, ⟨Λ₀, inferInstance, hfin⟩, ?_⟩
  rw [frPart_eq]
  exact equiv_of_corr (IsPartner γ Z) (cls γ Z) (GlobSet Zd γ F'₂ φ φ') (RelN γ F'₂)
    (h2 γ Z hC F'₂ φ φ' hS) (h3 γ Z hC F'₂ φ φ' hS) (h4 γ Z hC F'₂ φ φ' hS)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPh
noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbCut

open MeasureTheory Formalism.MainNotions.S Formalism.L2.SG.Pf.LocOrbSumPf
open Classical

section Val2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [IsTopologicalRing E]

theorem local_phase_orbit_eq (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1))
    (xy xy' : (Loc.IL (m + 1) → E) × (Loc.IN a → E))
    (l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hq : zAt a xy' = l * zAt a xy * ρ) :
    M.psiR (Loc.simpleLow (Loc.uLow xy'.1) + Loc.simpleUp (Loc.uUp a xy'.2)) = M.psiR (Loc.simpleLow (Loc.uLow xy.1) + Loc.simpleUp (Loc.uUp a xy.2)) := by
  have hψ : ∀ x ∈ M.R, M.psiR x = 1 := fun r hr => by
    simpa using (Formalism.MainNotions.LocalModelPeriodLattices.selfDual_of_core M hOK 1).2 M.R.one_mem r hr
  have hLo : Formalism.DoubleCosetMeasures.IsLowUni (rI a l * rI a (Loc.uLow xy.1)) :=
    Formalism.DoubleCosetMeasures.isLowUni_mul E (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))
  have hUp : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy.2) * rI a ρ) :=
    Formalism.DoubleCosetMeasures.isUpUni_mul E (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))
  have hv : Formalism.DoubleCosetMeasures.IsLowUni (rI a (Loc.uLow xy'.1)) := lowUni_rI a (uLow_lowUni xy'.1)
  have hu : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy'.2)) := upUni_rI a (uUp_upUni a xy'.2)
  have hvPu : rI a (Loc.uLow xy'.1) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * rI a (Loc.uUp a xy'.2) =
      (rI a l * rI a (Loc.uLow xy.1)) * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
        (rI a (Loc.uUp a xy.2) * rI a ρ) := by
    have h := congrArg (rI a) hq
    unfold zAt at h
    simp only [rI_mul, rI_mat] at h
    rw [h]
    simp only [Matrix.mul_assoc]
  have hLd : IsUnit (rI a l * rI a (Loc.uLow xy.1)).det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det E hLo]; exact isUnit_one
  have hUd : IsUnit (rI a (Loc.uUp a xy.2) * rI a ρ).det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det E hUp]; exact isUnit_one
  have hfix : ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * rI a (Loc.uLow xy'.1)) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
      (rI a (Loc.uUp a xy'.2) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) =
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
    calc _ = (rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a (Loc.uLow xy'.1) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          rI a (Loc.uUp a xy'.2)) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a l * rI a (Loc.uLow xy.1))) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          ((rI a (Loc.uUp a xy.2) * rI a ρ) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) := by
          rw [hvPu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hLd, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mul, Matrix.mul_one]
  have h0 := Formalism.DoubleCosetMeasures.Final.phaseWellDef E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 _ _
    (Formalism.DoubleCosetMeasures.isLowUni_mul E (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv) (Formalism.DoubleCosetMeasures.isUpUni_mul E hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)) hfix
  have sa := Formalism.DoubleCosetMeasures.Final.simpleAdd E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum
  rw [(sa _ _).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv, (sa _ _).2 hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)] at h0
  have hLi := (sa (rI a l * rI a (Loc.uLow xy.1))⁻¹ (rI a l * rI a (Loc.uLow xy.1))).1
    (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hLo
  rw [Matrix.nonsing_inv_mul _ hLd, sLow_one] at hLi
  have hUi := (sa (rI a (Loc.uUp a xy.2) * rI a ρ) (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹).2
    hUp (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)
  rw [Matrix.mul_nonsing_inv _ hUd, sUp_one] at hUi
  rw [(sa _ _).1 (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))] at hLi
  rw [(sa _ _).2 (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))] at hUi
  have hph : Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy'.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy'.2)) =
      Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) +
      (Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy.2))) := by
    linear_combination h0 + hLi + hUi
  have h1 : Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) ∈ M.R :=
    add_mem (by rw [sLow_rI]; exact sLow_mem M.R _ hl.2.2) (by rw [sUp_rI]; exact sUp_mem M.R _ hρ.2.2)
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq,
    Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq, ← sLow_rI a (Loc.uLow xy'.1), ← sUp_rI a (Loc.uUp a xy'.2),
    ← sLow_rI a (Loc.uLow xy.1), ← sUp_rI a (Loc.uUp a xy.2), hph, AddChar.map_add_eq_mul, hψ _ h1, one_mul]

end Val2

end Formalism.L2.SG.Pf.LocOrbCut

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf
open Classical ValuativeRel

theorem phase_class_holds {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) : PhCls M δ := by
  intro T T' p w Y Y' hOK hY hO hO' hmem
  obtain ⟨w₀, hw₀, xy0, hxy0⟩ := hO
  obtain ⟨l, ρ, hl, hρ, hY'⟩ := hmem
  have hmat : w₀.mat = modMat δ T T' p w + shM δ T T' p w := modShift_holds δ T T' p w w₀ hw₀
  unfold phL
  rw [hw₀]
  try dsimp only
  by_cases h' : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
      Y' = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2
  · by_cases h : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
        Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2
    · rw [dite_eq_left h', dite_eq_left h]
      congr 1
      have e1 := zAt_eq hmat h.choose
      have e2 := zAt_eq hmat h'.choose
      rw [← h.choose_spec] at e1
      rw [← h'.choose_spec] at e2
      have hq : zAt w₀ h'.choose = l * zAt w₀ h.choose * ρ := by
        rw [e1, e2, hY', mul_add, add_mul,
          mul_shM l ρ (last_of_low l hl.1 hl.2.1) (last_of_up ρ hρ.1 hρ.2.1)]
      haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
      exact LocOrbCut.local_phase_orbit_eq (M p) hOK w₀ h.choose h'.choose l ρ hl hρ hq
    · exact absurd ⟨xy0, hxy0⟩ h
  · obtain ⟨w₁, hw₁, xy, hxy⟩ := hO'
    rw [hw₀] at hw₁
    cases hw₁
    exact absurd ⟨xy, hxy⟩ h'

end Formalism.L2.SG.Pf.Coef
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefVol
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB MeasureTheory
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section VolStep

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolIdxProd : Prop :=
  (∀ p, Agree δ M p) → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → IsRowReps D F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    EligAt γ w → PairVal.NormRep γ w F' L U →
      PairVal.volIdx D u u' F0 what₂ δ M γ w F' L =
        ((PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard : ℝ) *
          ∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w
            (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

end VolStep

section Good

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}


open Formalism.L2.SG.Pf.LocUnramB in
theorem wtL_good (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hA : Agree δ M p)
    (hg : Good δ M w p) {Y : MatP D p} (hYi : IntP M p Y) (hYo : InOrbP δ T T' p w Y) :
    wtL M δ T T' p w Y = 1 := by
  obtain ⟨w₀, hw₀, xy0, hxy0⟩ := hYo
  have hint := orb_int T T' w p hA hg w₀ hw₀
  obtain ⟨h1, h2⟩ := hint xy0.1 xy0.2 (by rw [← hxy0]; exact hYi)
  have hO : kkOrb M p Y = kkOrb M p (modMat δ T T' p w) :=
    kkOrb_eq p (isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow _)) h1
      (isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp _ _)) h2 hxy0
  set H := monoW T T' w p hA hg
  have hOK := hA.1
  have := hOK.haar.sf
  unfold wtL
  rw [hw₀]
  simp only
  have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep) |
      Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y} =
      (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) ×ˢ
        (Set.univ.pi fun _ => ((M p).R : Set (D.s.atP p).Ep)) := by
    ext ⟨x, y⟩
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]
    rw [hO]
    constructor
    · rintro ⟨l, ρ, hl, hρ, he⟩
      have hYint : ∀ i j, (Loc.uLow x * modMat δ T T' p w * Loc.uUp w₀ y) i j ∈ (M p).R := by
        rw [he]; exact int_mul _ (int_mul _ hl.2.2 H.int) hρ.2.2
      obtain ⟨h1, h2⟩ := hint x y hYint
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have := h1 i.1.1 i.1.2
        simp only [Loc.uLow, if_neg (ne_of_gt i.2), dif_pos i.2] at this
        exact this
      · have := h2 i.1.1 i.1.2
        simp only [Loc.uUp, if_neg (ne_of_lt i.2.1), dif_pos i.2] at this
        exact this
    · rintro ⟨hx, hy⟩
      have hL := isLoU_of (Formalism.MainNotions.LocalModelPeriodLattices.isLowUni_uLow x)
      have hN := isUpU_of (Formalism.MainNotions.LocalModelPeriodLattices.isUpUni_uUp w₀ y)
      refine ⟨Loc.uLow x, Loc.uUp w₀ y, ⟨hL.1, hL.2, fun a b => ?_⟩, ⟨hN.1, hN.2, fun a b => ?_⟩, rfl⟩
      · unfold Loc.uLow
        split_ifs
        · exact (M p).R.one_mem
        · exact hx _
        · exact (M p).R.zero_mem
      · unfold Loc.uUp
        split_ifs
        · exact (M p).R.one_mem
        · exact hy _
        · exact (M p).R.zero_mem
  rw [hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  simp [hOK.haar.volR]

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem wtL_finite (hA : ∀ p, Agree δ M p) (hC : LocClsE M δ u u' F0 what₂)
    {γ : TermDef.Term D u u' F0 what₂} {w : Point D.host.E (D.R.rS + 1)} (hγ : EligAt γ w) :
    (Function.mulSupport fun p =>
      (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)).Finite := by
  have hall := LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hall
  refine hall.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq]
  intro hg
  apply hp
  obtain ⟨hyI, hyO⟩ := hC γ w hγ p
  show (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) = 1
  rw [wtL_good _ _ w p (hA p) hg hyI hyO, Complex.ofReal_one]

theorem volProd_of (hA : ∀ p, Agree δ M p)
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hC : LocClsE M δ u u' F0 what₂)
    (hVP : VolIdxProd M δ u u' F0 what₂) : VolProd M δ u u' F0 what₂ := by
  intro γ w hγ
  refine ⟨wtL_finite hA hC hγ, ?_⟩
  have hγ0 := hγ
  have hrel : γ.relevant := PCount.eligRel_holds γ w hγ
  obtain ⟨⟨hgen, -⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat hrel hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by unfold zT; rw [hn]
  have hv : PairVal.vRdef D u u' F0 what₂ δ M γ =
      PairVal.volIdx D u u' F0 what₂ δ M γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1 := by
    unfold PairVal.vRdef; rw [dif_pos ⟨hrel, hgen, hex⟩]
  have hspec := hex.choose_spec
  obtain ⟨hRep, -, hL, hU, e⟩ := hspec
  obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
  have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
    hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
  have hγ' : EligAt γ hex.choose.1 := hw ▸ hγ0
  have key := hVP hA hT hrows γ hex.choose.1 hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 hγ' hex.choose_spec
  have hcast : ((∏ᶠ p, wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℝ) : ℂ) =
      ∏ᶠ p, (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) :=
    Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _
  rw [← hcast, hv, key, ← hw]
  simp only [yT, hz, Complex.ofReal_mul, Complex.ofReal_natCast]
  rfl

end Good

end Formalism.L2.SG.Pf.Coef
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TargetFact
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Helpers

variable {K : Type*} [CommRing K] {n : ℕ}

theorem isUp_sconj {S X : Matrix (Fin n) (Fin n) K} (s d d' : Fin n → K) (hS : S = Matrix.diagonal s)
    (hs : ∀ a, s a * s a = 1) (hd : ∀ a, d a * d' a = 1) (hX : IsUp X) :
    IsUp (S * Matrix.diagonal d * X * Matrix.diagonal d' * S) := by
  have e : S * Matrix.diagonal d * X * Matrix.diagonal d' * S =
      Matrix.diagonal (fun a => s a * d a) * X * Matrix.diagonal (fun a => d' a * s a) := by
    rw [hS, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc _ (Matrix.diagonal d'), Matrix.diagonal_mul_diagonal]
  rw [e]
  exact isUp_conj hX _ _ fun a => by
    calc s a * d a * (d' a * s a) = (d a * d' a) * (s a * s a) := by ring
      _ = 1 := by rw [hd, hs, one_mul]

theorem isLo_sconj {S X : Matrix (Fin n) (Fin n) K} (s d d' : Fin n → K) (hS : S = Matrix.diagonal s)
    (hs : ∀ a, s a * s a = 1) (hd : ∀ a, d a * d' a = 1) (hX : IsLo X) :
    IsLo (S * Matrix.diagonal d * X * Matrix.diagonal d' * S) := by
  have e : S * Matrix.diagonal d * X * Matrix.diagonal d' * S =
      Matrix.diagonal (fun a => s a * d a) * X * Matrix.diagonal (fun a => d' a * s a) := by
    rw [hS, Matrix.diagonal_mul_diagonal, Matrix.mul_assoc _ (Matrix.diagonal d'), Matrix.diagonal_mul_diagonal]
  rw [e]
  exact isLo_conj hX _ _ fun a => by
    calc s a * d a * (d' a * s a) = (d a * d' a) * (s a * s a) := by ring
      _ = 1 := by rw [hd, hs, one_mul]

theorem isLo_one' {K : Type*} [CommRing K] {n : ℕ} : IsLo (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne]⟩

theorem isUp_one' {K : Type*} [CommRing K] {n : ℕ} : IsUp (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply_ne h.ne']⟩

end Helpers

section ClearFp

variable {D : Formalism.BasicNotions.D7}

theorem clear_Fp (p : PlF D) {ι : Type} [Fintype ι] (z : ι → (D.s.atP p).Fp) :
    ∃ c : 𝓞 D.host.F, c ≠ 0 ∧ ∀ k,
      (D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c) * z k ∈ (haveI := (D.s.atP p).lf; 𝒪[(D.s.atP p).Fp]) := by
  haveI := (D.s.atP p).lf
  have h := fun k => clear_F (fun q => D.s.atP q) p (z k)
  choose t ht0 htz using h
  refine ⟨∏ k, t k, Finset.prod_ne_zero_iff.2 fun k _ => ht0 k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), map_mul, map_mul,
    mul_comm ((D.s.atP p).ιF (algebraMap _ _ (t k))), mul_assoc]
  exact Subring.mul_mem _ (iotaF_int_mem (fun q => D.s.atP q) p _) (htz k)

end ClearFp

section TypedFact

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)
  (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
  (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Zd.M p).L) (hM : (Zd.M p).split = some g)
  (hge : g.e = sg.e) (hgq : g.q = sg.q)
include hR hM hge hgq


set_option maxHeartbeats 1000000 in
theorem zz_fact (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {L B : PairVal.MatR D} (hL : IsLo L)
    (hB : IsUp B) :
    CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) * LsDatumB.sgnP p =
      glue sg.e (Matrix.diagonal (cf Zd p) * L.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p))
          (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p)) *
        glue sg.e ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
            (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
              (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS)
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
            (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
              ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS) *
        glue sg.e (Matrix.diagonal (cfi Zd p) * B.map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p))
          (Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose *
            Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) := by
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  set S := Sg (D.s.atP p).Fp D.R.rS with hS
  have hZ : (L * ptMat w * B * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w * B := by
    rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  have hΛ1 : IsLo (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) :=
    isLo_conj (isLo_map φ1 hL) _ _ (cf_cfi Zd p)
  have hV1 : IsUp (Matrix.diagonal (cfi Zd p) * B.map φ1 * Matrix.diagonal (cf Zd p)) :=
    isUp_conj (isUp_map φ1 hB) _ _ (cfi_cf Zd p)
  have hBt : IsLo (S * (B.map φ2).transpose * S) :=
    isLo_conj (isLo_transpose (isUp_map φ2 hB)) _ _ (fun a => sgn_sq' D.R.rS a)
  have hLt : IsUp (S * (L.map φ2).transpose * S) :=
    isUp_conj (isUp_transpose (isLo_map φ2 hL)) _ _ (fun a => sgn_sq' D.R.rS a)
  have hΛ2 : IsLo (Matrix.diagonal (cf Zd p) * (S * (B.map φ2).transpose * S) * Matrix.diagonal (cfi Zd p)) :=
    isLo_conj hBt _ _ (cf_cfi Zd p)
  have hV2 : IsUp (Matrix.diagonal (cfi Zd p) * (S * (L.map φ2).transpose * S) * Matrix.diagonal (cf Zd p)) :=
    isUp_conj hLt _ _ (cfi_cf Zd p)
  refine mat_eq sg.e ?_ ?_
  · have l1 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) *
        LsDatumB.sgnP p).map (p1 sg.e) =
        (Matrix.diagonal (cf Zd p) * L.map φ1 * Matrix.diagonal (cfi Zd p)) *
          ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map φ1 * Matrix.diagonal (cf Zd p))) *
          (Matrix.diagonal (cfi Zd p) * B.map φ1 * Matrix.diagonal (cf Zd p)) -
        (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
      rw [zz1' Zd p sg hR g hM hge hgq, hZ, Matrix.map_mul, Matrix.map_mul, fact1 _ _ (cfi_cf Zd p)]
    rw [l1, Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, glue_map_fst, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hΛ1 hV1]
  · have e2 : ((L * ptMat w * B * Sg D.host.E D.R.rS).map φ2).transpose * S =
        (S * (B.map φ2).transpose * S) * (S * (ptMat w).map φ2 * S) * (S * (L.map φ2).transpose * S) := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
      exact fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])
    have l2 : (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (L * ptMat w * B * Sg D.host.E D.R.rS) *
        LsDatumB.sgnP p).map (p2 sg.e) =
        (Matrix.diagonal (cf Zd p) * (S * (B.map φ2).transpose * S) * Matrix.diagonal (cfi Zd p)) *
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (S * (ptMat w).map φ2 * S) *
            Matrix.diagonal (cf Zd p))) *
          (Matrix.diagonal (cfi Zd p) * (S * (L.map φ2).transpose * S) * Matrix.diagonal (cf Zd p)) -
        ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
      rw [zz2' Zd p sg hR g hM hge hgq, e2, fact1 _ _ (cfi_cf Zd p)]
    rw [l2, Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, glue_map_snd, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hΛ2 hV2]


set_option maxHeartbeats 1000000 in
theorem target_fact (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) :
    ∃ Gl Gu : MatP D p, IsLo Gl ∧ IsUp Gu ∧
      glue sg.e ((sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
            (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
              (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS)
          ((-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
            (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
              ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS) =
        Gl * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * Gu := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0 :=
    fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  obtain ⟨L1, U1, hL1, hU1, h1⟩ := generic_comp (sgF w) (sgF_sgF _) (isLo_one' (K := (D.s.atP p).Fp))
    (isUp_one' (K := (D.s.atP p).Fp))
    (W := (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE))
    (fun a b hb => by simp only [Matrix.map_apply, ptMat_apply', if_neg hb, map_zero])
    (fun a => by
      simp only [Matrix.map_apply, ptMat_apply', if_true]
      exact (map_ne_zero _).2 (pTau_ne' _ a))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (sg.q : (D.s.atP p).Fp)⁻¹ (inv_ne_zero hq)
    (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  obtain ⟨L2, U2, hL2, hU2, h2⟩ := generic_comp (sgF w) (sgF_sgF _) (isLo_one' (K := (D.s.atP p).Fp))
    (isUp_one' (K := (D.s.atP p).Fp))
    (W := Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS)
    (fun a b hb => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb, map_zero,
        mul_zero, zero_mul])
    (fun a => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true]
      exact mul_ne_zero (mul_ne_zero (hs0 _) ((map_ne_zero _).2 (pTau_ne' _ a))) (hs0 _))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (-(sg.q : (D.s.atP p).Fp)⁻¹) (neg_ne_zero.2 (inv_ne_zero hq))
    ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  rw [Matrix.one_mul, Matrix.mul_one] at h1 h2
  refine ⟨glue sg.e L1 L2, glue sg.e U1 U2, isLo_glue sg.e hL1 hL2, isUp_glue sg.e hU1 hU2, mat_eq sg.e ?_ ?_⟩
  · rw [glue_map_fst, h1, Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst, mm1' Zd p sg hR g hM hge hgq]
  · rw [glue_map_snd, h2, Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd, mm2' Zd p sg hR g hM hge hgq]

end TypedFact

end Formalism.L2.SG.Pf.PCountEx
end
end
