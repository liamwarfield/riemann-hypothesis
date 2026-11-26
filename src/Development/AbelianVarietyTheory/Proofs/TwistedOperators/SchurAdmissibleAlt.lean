module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspDiscreteDecompositionOfDecay
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissible
namespace GlobalTheory.SchurAdmissibility

theorem schur_admissible (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N)
    (hirr : Representation.IsIrreducible π) (hadm : GlobalTheory.PRep.IsAdmissible π)
    (φ : N →ₗ[ℂ] N) (hφ : ∀ (g : G) (x : N), φ (π g x) = π g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  by_cases hN : ∀ v : N, v = 0
  · exact ⟨0, LinearMap.ext fun v => by rw [hN (φ v)]; simp⟩
  push Not at hN
  obtain ⟨v, hv⟩ := hN
  let S : Subgroup G :=
    { carrier := {g : G | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hadm.1 v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hLo : IsOpen ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter hSo
  have hLc : IsCompact ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKc.inter_right hSc
  haveI hfd := hadm.2 (K ⊓ S) hLo hLc
  have hmem : ∀ w : N, w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) ↔
      ∀ h : (K ⊓ S : Subgroup G), π (h : G) w = w := by
    intro w
    change (∀ h : (K ⊓ S : Subgroup G), π (h : G) w = _) ↔ _
    simp
  have hvm : v ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (GlobalTheory.PRep.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvm⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hres : ∀ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S), φ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := by
    intro w hw
    rw [hmem] at hw ⊢
    intro h
    rw [← hφ, hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hres)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hw1 : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let U : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top U with h | h
  · exfalso
    have h1 : (w : N) ∈ U.toSubmodule := Module.End.mem_eigenspace_iff.2 hw1
    rw [h] at h1
    exact hw0 h1
  · ext x
    have h1 : x ∈ U.toSubmodule := by
      rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.1 h1

end GlobalTheory.SchurAdmissibility
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.SchurAdm

theorem schur_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), π.IsIrreducible → IsAdmissible π → ∀ φ : N →ₗ[ℂ] N, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id :=
  _root_.GlobalTheory.SchurAdmissibility.schur_admissible

end GlobalTheory.SchurAdm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.SeeConjRead

open Classical

variable {D : D7}

def diagGL {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) : GL (Fin r) κ :=
  Units.map (Matrix.diagonalRingHom (Fin r) κ).toMonoidHom (MulEquiv.piUnits.symm d)

theorem diagGL_val {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) :
    ((diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = Matrix.diagonal fun i => (d i : κ) := rfl

def flagV {M : Type} [Zero M] (ρ k n : ℕ) (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n) : M :=
  if h1 : i.1 < ρ then e ⟨i.1, h1⟩
  else if h2 : i.1 < ρ + k then b ⟨i.1 - ρ, by omega⟩
  else if h4 : i.1 = ρ + k then z
  else if h3 : i.1 < 2 * ρ + k + 1 then f ⟨2 * ρ + k - i.1, by omega⟩
  else 0

def e0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.rS → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.rS → Formalism.L2.SG.HidaSetting.VA I) h) X.e0

def f0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.rS → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.rS → Formalism.L2.SG.HidaSetting.VA I) h) X.f0

def z0T (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h) X.z0

def bwT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.k → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.k → Formalism.L2.SG.HidaSetting.VA I) h) X.bw

def bwdT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Fin D.R.k → Fin (Yc D 0).rank → EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Fin D.R.k → Formalism.L2.SG.HidaSetting.VA I) h) X.bwd

def ewT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) X.ew

def flagAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) :
    Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D :=
  if GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 then
    flagV D.R.rS D.R.k (Yc D 0).rank (e0T X h) (f0T X h) (bwT X h) (z0T X h)
  else flagV D.R.rS D.R.k (Yc D 0).rank (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (z0T X h)

def RedIs {n : ℕ} (β : GL (Fin n) (EAf D)) (PP : Pl D.host.E) (w : Fin n → Fin n → EAf D) : Prop :=
  ∀ i j, ∃ hm : Matrix.mulVec (β⁻¹).val (w j) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E,
    Formalism.L2.DIV.resS D.host.F PP ⟨_, hm⟩ = if i = j then 1 else 0

end GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem diagGL_inv {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) : (diagGL d)⁻¹ = diagGL (fun i => (d i)⁻¹) := by
  unfold diagGL
  rw [← map_inv, ← map_inv]
  rfl

theorem diagGL_conj_apply {κ : Type} [CommRing κ] {r : ℕ} (d : Fin r → κˣ) (u : GL (Fin r) κ) (i j : Fin r) :
    (((diagGL d)⁻¹ * u * diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (((d i)⁻¹ : κˣ) : κ) * (u : Matrix (Fin r) (Fin r) κ) i j * (d j : κ) := by
  rw [diagGL_inv, Units.val_mul, Units.val_mul, diagGL_val, diagGL_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem unipSym_conj_of {κ : Type} [CommRing κ] {r : ℕ} (ρ k : ℕ) (d : Fin r → κˣ) {u : GL (Fin r) κ}
    (hu : u ∈ unipSym κ r ρ k) : (diagGL d)⁻¹ * u * diagGL d ∈ unipSym κ r ρ k := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j a b c => ?_⟩
  · show (((diagGL d)⁻¹ * u * diagGL d : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = 0
    rw [diagGL_conj_apply, h1 hij, mul_zero, zero_mul]
  · rw [diagGL_conj_apply, h2, mul_one, Units.inv_mul]
  · rw [diagGL_conj_apply, h3 i j a b c, mul_zero, zero_mul]

theorem unipSym_conj_iff {κ : Type} [CommRing κ] {r : ℕ} (ρ k : ℕ) (d : Fin r → κˣ) (u : GL (Fin r) κ) :
    u ∈ unipSym κ r ρ k ↔ (diagGL d)⁻¹ * u * diagGL d ∈ unipSym κ r ρ k := by
  refine ⟨unipSym_conj_of ρ k d, fun h => ?_⟩
  have h' := unipSym_conj_of ρ k (fun i => (d i)⁻¹) h
  rw [← diagGL_inv, inv_inv] at h'
  simpa [mul_assoc] using h'

end GlobalTheory.SeeConjRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgree
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TypeHypForms


open GlobalTheory.SmGL in
theorem unipBlock_subset_radicalTwo {k : Type} [Field k] {a b r : ℕ} (h : a + b = r) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock k r a ⊆ (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.radicalTwo k h : Set (GL (Fin r) k)) := by
  intro g hg
  rw [SetLike.mem_coe, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.radicalTwo, mem_unipRad]
  refine ⟨(mem_parab_two k).2 fun j i => ?_, ?_⟩
  · have hj := j.isLt
    have hi := i.isLt
    rw [hg (stdSum h (.inr j)) (stdSum h (.inl i)) (by simp only [stdSum_inl, stdSum_inr]; omega),
      Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp only [stdSum_inl, stdSum_inr] at this
    omega
  · rintro (_ | _) i j
    · have hj := j.isLt
      have hi := i.isLt
      show (g : Matrix (Fin r) (Fin r) k) (stdSum h (.inl i)) (stdSum h (.inl j)) = (1 : Matrix (Fin a) (Fin a) k) i j
      rw [hg _ _ (by simp only [stdSum_inl, stdSum_inr]; omega)]
      simp only [Matrix.one_apply, (stdSum h).injective.eq_iff, Sum.inl.injEq]
    · have hj := j.isLt
      have hi := i.isLt
      show (g : Matrix (Fin r) (Fin r) k) (stdSum h (.inr i)) (stdSum h (.inr j)) = (1 : Matrix (Fin b) (Fin b) k) i j
      rw [hg _ _ (by simp only [stdSum_inl, stdSum_inr]; omega)]
      simp only [Matrix.one_apply, (stdSum h).injective.eq_iff, Sum.inr.injEq]

theorem noRadicalFixed_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (hT : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T := by
  intro a b h ha hb
  obtain ⟨v, hv⟩ := hT.2 a ha (by omega)
  refine ⟨v, (Submodule.eq_bot_iff _).2 fun y hy => hv y fun g hg => ?_⟩
  have := hy ⟨g, unipBlock_subset_radicalTwo h hg⟩
  simpa using this

theorem hypH_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (h : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ := by
  intro a ha har
  obtain ⟨v, hv⟩ := h.2 a ha har
  refine ⟨v, fun y hy => hv y fun g hg => hy g ?_⟩
  intro i j hij
  by_contra hc
  exact hij (hg i j hc)

theorem hypH_and_noRadicalFixed : ∀ (D : D7) (V : HSp D) (T : TypeDataG V), NoFixed T → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T :=
  fun _ _ T h => ⟨hypH_of_noFixed T h, noRadicalFixed_of_noFixed T h⟩

end GlobalTheory.TypeHypForms

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgreeStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeHypothesis_forms_agree : ∀ (D : D7) (V : HSp D) (T : TypeDataG V), NoFixed T → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T := by
  first | exact @GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed | exact GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed | (intros; apply GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularCentralizerNoncompact
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.ArchVanish

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

variable {σ J}

theorem isMulCommutative_cent_projArch_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (w : InfinitePlace F) :
    IsMulCommutative (Orb.cent (projArch σ J w (ratEmb σ J γ))) :=
  Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)


end General

end GlobalTheory.ArchVanish

end

namespace GlobalTheory.ArchVanish


end GlobalTheory.ArchVanish
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwise
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwise
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrAct


open Classical in
noncomputable def partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) : GA D V :=
  ofInf D.sp.cm.sig V.gram (embArchPi D.sp.cm.sig V.gram fun w =>
    if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1)

open Classical in
theorem projArch_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (w : InfinitePlace D.host.F) :
    projArch D.sp.cm.sig V.gram w (partAt V g s) =
      if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1 := by
  rw [partAt, projArch_ofInf, projInfArch_embArchPi]

theorem proj_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    proj D.sp.cm.sig V.gram v (partAt V g s) = 1 := by
  rw [partAt, proj_ofInf]

open Classical in
theorem partAt_insert {D : D7} (V : HSp D) (g : GA D V) {s : Finset D.what₂.Tau} {τ : D.what₂.Tau} (hτ : τ ∉ s) :
    partAt V g (insert τ s) =
      embW V (placeOf D τ) (projArch D.sp.cm.sig V.gram (placeOf D τ) g) * partAt V g s := by
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [map_mul, projArch_partAt, projArch_partAt]
    by_cases hw : w = placeOf D τ
    · subst hw
      have h1 : placeOf D τ ∈ (insert τ s).image (placeOf D) := Finset.mem_image_of_mem _ (Finset.mem_insert_self τ s)
      have h2 : placeOf D τ ∉ s.image (placeOf D) := fun h => by
        obtain ⟨ρ, hρ, e⟩ := Finset.mem_image.1 h
        exact hτ ((placeOf_bijective D).1 e ▸ hρ)
      rw [if_pos h1, if_neg h2, mul_one]
      exact (projArch_embArch_self _ _ _ _).symm
    · rw [projArch_embArch_ne _ _ hw, one_mul]
      congr 1
      simp only [Finset.image_insert, Finset.mem_insert, hw, false_or]
  · rw [map_mul, proj_partAt, proj_partAt, proj_embArch, one_mul]

theorem partAt_univ {D : D7} (V : HSp D) (g : GA D V) [Fintype D.what₂.Tau] :
    partAt V g Finset.univ = (toInf V g : GA D V) := by
  classical
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [projArch_partAt, if_pos]
    · show _ = projArch D.sp.cm.sig V.gram w (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
      rw [projArch_ofInf, projInfArch_projInf]
    · obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
      exact Finset.mem_image_of_mem _ (Finset.mem_univ τ)
  · rw [proj_partAt]
    show _ = proj D.sp.cm.sig V.gram v (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
    rw [proj_ofInf]

end GlobalTheory.TrAct


open GlobalTheory.TrAct in
theorem GlobalTheory.TrAct.toInf_apply_homDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H), ∀ Φ ∈ homDS M ρ U, ∀ (g : GA D V) y, ρ (toInf V g : GA D V) (Φ y) = Φ fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  intro D V S M H _ _ _ ρ U Φ hΦ g y
  classical
  haveI : Finite D.what₂.Tau := Finite.of_injective _ (placeOf_bijective D).1
  haveI : Fintype D.what₂.Tau := Fintype.ofFinite _
  have key : ∀ s : Finset D.what₂.Tau, ρ (partAt V g s) (Φ y) = Φ fun τ =>
      if τ ∈ s then dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) else y τ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : partAt V g ∅ = 1 := by
        rw [partAt]
        have : (fun w => if w ∈ (∅ : Finset D.what₂.Tau).image (placeOf D) then
            projArch D.sp.cm.sig V.gram w g else (1 : GArch D.sp.cm.sig V.gram w)) = 1 := by
          funext w; simp
        rw [this, map_one, map_one]
      simp [this]
    | insert τ s hτ ih =>
      rw [partAt_insert V g hτ, map_mul, ContinuousLinearMap.mul_apply, ih, ← (mem_homPi.1 hΦ).2 τ]
      congr 1
      funext τ'
      by_cases e : τ' = τ
      · subst e
        simp [hτ]
      · rw [Function.update_of_ne e]
        simp [e]
  have := key Finset.univ
  rw [partAt_univ] at this
  simpa using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwiseStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePart_act_discreteSeriesHom_factorwise : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H), ∀ Φ ∈ homDS M ρ U, ∀ (g : GA D V) y, ρ (toInf V g : GA D V) (Φ y) = Φ fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  first | exact @GlobalTheory.TrAct.toInf_apply_homDS | exact GlobalTheory.TrAct.toInf_apply_homDS | (intros; apply GlobalTheory.TrAct.toInf_apply_homDS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionFiniteAdelicPureTensorEqLocalConvolut
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTensorOfIntegrable
open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.SplitWeil NumberField IsDedekindDomain
open GlobalTheory.AutomorphicL2Unitary (conv)

noncomputable section

namespace GlobalTheory.Orb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsFullLattice E L] {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)}
  {μ : Measure (GAd σ J)} {fa fa' : ∀ w, GArch σ J w → ℂ} {ff ff' : ∀ v, GLoc σ J v → ℂ}


omit [NumberField E] [Submodule.IsFullLattice E L] in
theorem unitLoc_mul_translate {v : HeightOneSpectrum (𝓞 F)} {y : GLoc σ J v} (hy : y ∈ stabLoc σ J L v) :
    (fun x => unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y)) = unitLoc σ J L v := by
  funext x
  by_cases hx : x ∈ stabLoc σ J L v
  · simp [unitLoc, hx, mul_mem (inv_mem hx) hy]
  · simp [unitLoc, hx]

theorem conv_unitLoc {v : HeightOneSpectrum (𝓞 F)} (ν : Measure (GLoc σ J v)) :
    conv ν (unitLoc σ J L v) (unitLoc σ J L v) = (ν.real (stabLoc σ J L v) : ℂ) • unitLoc σ J L v := by
  funext y
  by_cases hy : y ∈ stabLoc σ J L v
  · rw [conv, unitLoc_mul_translate hy, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc σ J L v).measurableSet).trans ?_
    rw [Pi.smul_apply, indicator_of_mem hy, Complex.real_smul]
    rfl
  · have : ∀ x, unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y) = 0 := fun x => by
      by_cases hx : x ∈ stabLoc σ J L v
      · simp [unitLoc, hy, Subgroup.mul_mem_cancel_left _ (inv_mem hx)]
      · simp [unitLoc, hx]
    rw [conv]
    simp only [this, integral_zero]
    simp [unitLoc, hy]

theorem IsFinFamily.conv (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff')
    (h1 : ∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) : IsFinFamily σ J L fun v => conv (μf v) (ff v) (ff' v) := by
  refine ⟨fun v => conv_mem_SB (hf.1 v) (hf'.1 v), ?_⟩
  filter_upwards [hf.2, hf'.2, h1] with v e e' e1
  rw [e, e', conv_unitLoc, Measure.real, e1]
  simp

theorem IsFinFamily.mul_translate (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff') (y : GAd σ J) :
    IsFinFamily σ J L fun v x => ff v x * ff' v (x⁻¹ * proj σ J v y) := by
  refine ⟨fun v => ⟨(hf.1 v).1.mul ((hf'.1 v).1.comp_continuous (by fun_prop)), (hf.1 v).2.mul_right⟩, ?_⟩
  filter_upwards [hf.2, hf'.2, eventually_proj_mem_stabLoc σ J L y] with v e e' hy
  rw [e, e', unitLoc_mul_translate hy]

end GlobalTheory.Orb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionFiniteAdelicPureTensorEqLocalConvolut
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
noncomputable section

namespace GlobalTheory.TrConv

variable {D : D7}

theorem finFn_eq_tensorFin (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (y : GfC V) :
    finFn V ff y = tensorFin D.sp.cm.sig V.gram ff ((finPtsEquiv D.sp.cm.sig V.gram).symm y) := by
  unfold finFn tensorFin
  refine finprod_congr fun v => congrArg (ff v) ?_
  have := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm y)
  rw [← this]
  congr 1
  exact (congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply y)).symm

theorem conv_finFn : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ a b, IsFinFamily D.sp.cm.sig V.gram (frameLat V) a → IsFinFamily D.sp.cm.sig V.gram (frameLat V) b → IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fun v => conv (μf v) (a v) (b v)) ∧ finFn V (fun v => conv (μf v) (a v) (b v)) = conv ν (finFn V a) (finFn V b) ∧ finFn V a ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  intro D V μf _ h1 ν hν a b ha hb
  refine ⟨GlobalTheory.Orb.IsFinFamily.conv ha hb h1, funext fun y => ?_, ?_⟩
  · have hfam := GlobalTheory.Orb.IsFinFamily.mul_translate ha hb (y : GA D V)
    have hint : (fun x : GfC V => finFn V a x * finFn V b (x⁻¹ * y)) =
        finFn V (fun v x => a v x * b v (x⁻¹ * proj D.sp.cm.sig V.gram v (y : GA D V))) := by
      funext x
      have e1 := ha.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have e2 := hb.finite_mulSupport ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      rw [finFn_eq_tensorFin, finFn_eq_tensorFin]
      unfold finFn
      unfold tensorFin
      rw [← finprod_mul_distrib e1 e2]
      refine finprod_congr fun v => ?_
      have p1 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm x)
      have p2 := proj_ofFin D.sp.cm.sig V.gram v ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y))
      have q1 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm x) = (x : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply x)
      have q2 : ofFin D.sp.cm.sig V.gram ((finPtsEquiv D.sp.cm.sig V.gram).symm (x⁻¹ * y)) = ((x⁻¹ * y : GfC V) : GA D V) :=
        congrArg Subtype.val ((finPtsEquiv D.sp.cm.sig V.gram).apply_symm_apply _)
      rw [q1] at p1
      rw [q2] at p2
      rw [← p1, ← p2]
      simp [map_mul, map_inv]
    symm
    show ∫ x, finFn V a x * finFn V b (x⁻¹ * y) ∂ν = _
    rw [hint, hν.2 _ hfam]
    rfl
  · have hm := ha.tensorFin_mem
    rw [show finFn V a = tensorFin D.sp.cm.sig V.gram a ∘ (finPtsEquiv D.sp.cm.sig V.gram).symm from
      funext fun y => finFn_eq_tensorFin V a y]
    exact ⟨hm.1.comp_continuous (finPtsEquiv D.sp.cm.sig V.gram).symm.continuous,
      hm.2.comp_homeomorph (finPtsEquiv D.sp.cm.sig V.gram).symm.toHomeomorph⟩

end GlobalTheory.TrConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionFiniteAdelicPureTensorEqLocalConvolutStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_finiteAdelicPureTensor_eq_localConvolutions : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ a b, IsFinFamily D.sp.cm.sig V.gram (frameLat V) a → IsFinFamily D.sp.cm.sig V.gram (frameLat V) b → IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fun v => conv (μf v) (a v) (b v)) ∧ finFn V (fun v => conv (μf v) (a v) (b v)) = conv ν (finFn V a) (finFn V b) ∧ finFn V a ∈ GlobalTheory.SplitWeil.SB (GfC V) := by
  first | exact @GlobalTheory.TrConv.conv_finFn | exact GlobalTheory.TrConv.conv_finFn | (intros; apply GlobalTheory.TrConv.conv_finFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorInnerProductEqFinprodLocalInnerProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorInnerProductEqFinprodLocalInnerProduct
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor.PureScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  rw [wAt_eq_smul, smul_zero]

theorem wAt_neg_wAt_self {m n : ℕ} (q : Place D) (w : Mx D m n) : wAt q (-(wAt q w)) = -(wAt q w) := by
  have hq : idem D q * idem D q = idem D q := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 q
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hq]

theorem wAt_neg_wAt_ne {m n : ℕ} {p q : Place D} (hpq : p ≠ q) (w : Mx D m n) : wAt p (-(wAt q w)) = 0 := by
  have hpq' : idem D p * idem D q = 0 := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q hpq
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hpq', zero_smul, neg_zero]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem ip_base (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) : ipO μ 𝓕 f₀ f₀ = 1 := by
  have hself : ipO μ 𝓕 f₀ f₀ = (nrm2 μ 𝓕 f₀ : ℂ) :=
    (GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f₀ f₀ (base_theta hb) (base_theta hb)).2.2.2.2.1
  rw [hself, restrictedTensorBasePoint_norm_sq hb hμ, Complex.ofReal_one]

theorem finite_mulSupport_ip (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {x₁ x₂ : Place D → WO S T → ℂ} (h₁ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₁)
    (h₂ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₂) :
    (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite := by

  refine (h₁.2.union h₂.2).subset fun p hp => ?_
  rw [Function.mem_mulSupport] at hp
  by_contra hout
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hout
  exact hp (by rw [hout.1, hout.2]; exact ip_base hb hμ)

private theorem heisO_zero_twisted_operators (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext u
  simp [heisO, symplOH, symplO, hO]

theorem pureTensor_innerProduct_eq_finprod_local_of_finset (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (s : Finset (Place D)) :
    ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), (∀ p, p ∉ s → x₁ p = f₀) →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ →
      ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  classical
  have hθ₀ : IsThetaFunO ψ S T f₀ := base_theta hb

  have hsymm : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) :=
    fun f g hf hg => (GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.1
  have hadj : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ w,
      ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g) :=
    fun f g hf hg w => ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.2.2.2.2.2.1 w).2
  induction s using Finset.induction_on with
  | empty =>

    intro x₁ x₂ f₁ f₂ hx h₁ h₂
    have hx₁ : x₁ = fun _ => f₀ := funext fun p => hx p (by simp)
    subst hx₁
    have hf₁ : f₁ = f₀ :=
      (GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique h₁
        (GlobalTheory.T.isPureTensor_base_vector_and_local_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ).1
    subst hf₁
    obtain ⟨hfin, hprod⟩ := h₂.2.2 0
    simp only [wAt_zero, heisO_zero_twisted_operators] at hfin hprod
    rw [hsymm f₂ f₁ h₂.2.1 hθ₀, hprod, map_finprod _ hfin]
    exact finprod_congr fun p => (hsymm (x₂ p) f₁ (h₂.1.1 p).1 hθ₀).symm
  | insert q s hq ih =>
    intro x₁ x₂ f₁ f₂ hx h₁ h₂

    have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update x₁ q f₀) := by
      refine ⟨fun p => ?_, h₁.1.2.subset fun p hp => ?_⟩
      · by_cases hpq : p = q
        · subst hpq
          rw [Function.update_self]
          exact base_isLocal hb p
        · rw [Function.update_of_ne hpq]
          exact h₁.1.1 p
      · by_cases hpq : p = q
        · subst hpq
          simp at hp
        · simpa [Function.update_of_ne hpq] using hp
    have hoff : ∀ p, p ∉ s → Function.update x₁ q f₀ p = f₀ := by
      intro p hp
      by_cases hpq : p = q
      · subst hpq
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hpq]
        exact hx p (by simp [hpq, hp])
    obtain ⟨g₁, hg₁, -⟩ := GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ hres

    obtain ⟨f', hf', hc⟩ := GlobalTheory.T.pureTensor_update_factor_from_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ (Function.update x₁ q f₀) x₁ g₁ q hg₁
      (Function.update_self _ _ _) (fun p hp => (Function.update_of_ne hp _ _).symm) (h₁.1.1 q)
    have hf'₁ : f' = f₁ := (GlobalTheory.T.existsUnique_pureTensor_restrictedFamily D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique hf' h₁
    subst hf'₁
    have hθq : IsThetaFunO ψ S T (x₂ q) := (h₂.1.1 q).1
    have key := hc f₂ (x₂ q) (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x₁ p) (x₂ p)) h₂.2.1 hθq (fun w => by
      rw [hadj g₁ f₂ hg₁.2.1 h₂.2.1]
      have hpw := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₂ f₂ h₂ (-(wAt q w))
      rw [ih _ _ _ _ hoff hg₁ hpw, ← mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ hres hpw.1),
        Function.update_self, wAt_neg_wAt_self, ← hadj f₀ (x₂ q) hθ₀ hθq, mul_comm]
      congr 1
      refine finprod_congr fun p => finprod_congr fun hp => ?_
      rw [Function.update_of_ne hp, wAt_neg_wAt_ne hp, heisO_zero_twisted_operators])
    rw [key, mul_comm]
    exact mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ h₁.1 h₂.1)

end

theorem ip_pure_eq_finprod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite ∧ ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₁ x₂ f₁ f₂ h₁ h₂
  refine ⟨finite_mulSupport_ip hb hμ h₁.1 h₂.1, ?_⟩

  exact pureTensor_innerProduct_eq_finprod_local_of_finset hb hμ h₁.1.2.toFinset x₁ x₂ f₁ f₂
    (fun p hp => by simpa [Set.Finite.mem_toFinset] using hp) h₁ h₂

end GlobalTheory.PlaceTensor.PureScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorInnerProductEqFinprodLocalInnerProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureTensor_innerProduct_eq_finprod_localInnerProducts : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite ∧ ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  first | exact @GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod | exact GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod | (intros; apply GlobalTheory.PlaceTensor.PureScalar.ip_pure_eq_finprod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspTraceClassOfFactorisation
namespace GlobalTheory.Published

theorem cuspTraceClass_of_factorisation : DixmierMalliavinFactorisation → CuspTraceClass :=
  fun h => cuspTraceClass_of_decay GlobalTheory.T.cuspidal_moderateGrowth_rapidDecay h

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitarySelfDualFrameToBaseLatticeFra
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitarySelfDualFrameToBaseLatticeFra
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SelfDualFrameConj

section SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open GlobalTheory.StdFrames GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.IdemSupport Formalism.IndefR.Datum Formalism.L2.NTheta GlobalTheory.NormSum.AdLattice Formalism.L2.Herm

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem exists_gfc (V : HSp D) (γ : GL (Fin V.rank) (Ef D)) (hγ : Unimod (OA D) (gramOf V γ)) :
    ∃ k ∈ Formalism.L2.Theta.GfC V, crdLat V V.L0 = lat ((Formalism.IndefR.Lev.finE V k)⁻¹ * γ) := by
  let L : Submodule (𝓞 D.host.E) V.V :=
    (lat γ).comap ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hL : crdLat V L = lat γ := Submodule.map_comap_eq_of_surjective
    (f := (crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).surjective _
  have hm : ∀ x, x ∈ L ↔ crd V x ∈ lat γ := fun _ => Iff.rfl
  have h1 : Submodule.IsLattice D.host.E L := by
    apply Submodule.IsLattice.of_fg D.host.E
    exact Submodule.fg_of_fg_map_injective
      ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).injective
      (hL ▸ (lat_isLattice γ).fg : (crdLat V L).FG)
  have h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L := by
    ext x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one]
    rw [hm, mem_lat_iff_dual hγ]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := (crd V).surjective y
      have := h y hy
      rw [hT_crd D.sp.cm] at this
      exact this
    · intro h y hy
      rw [hT_crd D.sp.cm]
      exact h _ hy
  obtain ⟨k, hkG, hk⟩ := GlobalTheory.VolumeRatioTypings.exists_conj V L h1 h2
  refine ⟨k, hkG, eq_lat (fun x => ?_) (by
    first | exact isLattice_crdLat V V.standardTuple_isLattice | exact isFullLattice_crdLat V)⟩
  have hk' : ∀ y, y ∈ GlobalTheory.AdLat.hat D.host.F (crdLat V V.L0 : Set (Fin V.rank → D.host.E)) ↔
      finMat D.sp.cm.sig V.gram k *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (lat γ : Set (Fin V.rank → D.host.E)) := by
    rw [← hL, GlobalTheory.LevelChoices.coe_crdLat]
    have := GlobalTheory.LevelChoices.coe_crdLat (GlobalTheory.VolRatioCompare.reLat V L h1 h2)
    rw [← this] at hk
    exact hk
  refine (hatL_of_hat _ _ _ hk' x).trans ((isFrame_lat γ _).trans ?_)
  rw [mulVec_mulVec, _root_.mul_inv_rev, inv_inv, Units.val_mul]
  rfl

end SlopeTestRemainingChoices

end GlobalTheory.SelfDualFrameConj

theorem GlobalTheory.SelfDualFrameConj.frame_conj : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∃ t ∈ GfC V, IsFrame (finE V t * β) (Formalism.L2.Herm.crdLat V V.L0) := by
  intro D V β Λ N h
  obtain ⟨k, hk, hL⟩ := GlobalTheory.SelfDualFrameConj.exists_gfc V β (GlobalTheory.StdFrames.unimod_of_isSD h)
  refine ⟨k⁻¹, inv_mem hk, ?_⟩
  rw [map_inv, hL]
  exact GlobalTheory.StdFrames.isFrame_lat _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteUnitarySelfDualFrameToBaseLatticeFraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteUnitary_selfDualFrame_to_baseLatticeFrame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∃ t ∈ GfC V, IsFrame (finE V t * β) (Formalism.L2.Herm.crdLat V V.L0) := by
  first | exact @GlobalTheory.SelfDualFrameConj.frame_conj | exact GlobalTheory.SelfDualFrameConj.frame_conj | (intros; apply GlobalTheory.SelfDualFrameConj.frame_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsConjPlOfUnderEqOfNe
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

namespace GlobalTheory.UnderConj
open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.SplitOffPlaces

theorem isConjPl_of_under_eq_of_ne : ∀ (D : D7) (PP PP' : Pl D.host.E), (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') →
    PP ≠ PP' → Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro D PP PP' hu hne
  have key : PP' = conjSpec PP := by
    by_contra hc
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem (Q := PP') (P := PP) (P' := conjSpec PP) (Ne.symm hne) hc
    have hfix : star ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) := by
      change star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul, star_star]
    obtain ⟨a, ha⟩ := (D.sp.cm.fixed _).1 hfix
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (B := D.host.E), ha]
      exact (x * Formalism.L2.Col.cO D.host.E x).isIntegral_coe
    have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ = x * Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext ha
    have h1 : (⟨a, hint⟩ : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP'.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    rw [← hu] at h1
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP.asIdeal at h1
    rw [e] at h1
    rcases PP.isPrime.mem_or_mem h1 with h | h
    · exact hx1 h
    · exact hx2 h
  rw [key]
  exact GlobalTheory.LevelPlaces.isConjPl_conjSpec PP

end GlobalTheory.UnderConj
end
