module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem rder_zero (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (0 : GA D V → ℂ) = 0 := by
  funext g
  simp [Rder]

theorem rderC_zero (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (0 : GA D V → ℂ) = 0 := by
  simp [RderC, rder_zero]

theorem gelf_zero (τ : D.what₂.Tau) (k : ℕ) : gelf θ V τ k (0 : GA D V → ℂ) = 0 := by
  unfold gelf
  refine Finset.sum_eq_zero fun idx _ => ?_
  have h : ∀ l : List ((GA D V → ℂ) → GA D V → ℂ), (∀ f ∈ l, f 0 = 0) →
      l.foldr (fun f acc => f acc) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons f l ih =>
      rw [List.foldr_cons, ih (fun f' hf' => hl f' (by simp [hf']))]
      exact hl f (by simp)
  apply h
  intro f hf
  rw [List.mem_ofFn] at hf
  obtain ⟨a, rfl⟩ := hf
  exact rderC_zero θ V τ _

theorem foldr_rder_zero (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, ih]
    exact rder_zero θ V p.1 p.2

theorem isAutFunSm_zero : IsAutFunSm θ V (fun _ => 0) := {
  left _ _ _ := rfl
  level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const
  zfin := by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, fun τ k f hf => ?_⟩
    rw [Submodule.mem_bot] at hf
    subst hf
    rw [gelf_zero]
    exact Submodule.zero_mem _
  growth := by
    refine ⟨0, fun l _ x => ⟨0, fun g _ => ?_⟩⟩
    have h := foldr_rder_zero θ V l
    change ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ)) (x * g)‖ ≤ _
    rw [h]
    simp }

theorem isCuspFun_zero : IsCuspFun V (fun _ => 0) := by
  intro r C _ μ 𝓕 _ _ g
  simp

variable {V} {S : D.what₂.Tau → SPar}

theorem isMultMap_zero (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : IsMultMap θ M J χ 0 := {
  aut v := by
    show IsAutFunSm θ V (fun _ => 0)
    exact isAutFunSm_zero θ V
  cusp v := by
    show IsCuspFun V (fun _ => 0)
    exact isCuspFun_zero V
  lev v k _ g := by simp
  equiv τ g _ v w _ := by
    funext x
    simp [rTr]
  cont τ v x := by
    refine ⟨0, ⟨[], 0, by simp, fun w _ => by simp⟩, fun w => by simp⟩ }


variable (V) in
theorem rder_smul (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  simp only [Rder, Pi.smul_apply, smul_eq_mul]
  first
    | exact deriv_const_mul_field c
    | simp

variable (V) in
theorem foldr_rder_smul (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (c • φ) = c • l.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact rder_smul θ V p.1 p.2 c _


variable (V) in
theorem isAutFunSm_smul {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (c : ℂ) : IsAutFunSm θ V (c • φ) := {
  left γ hγ g := by simp only [Pi.smul_apply, h.left γ hγ g]
  level := by
    obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k hk1 hk2 g => by simp only [Pi.smul_apply, hk k hk1 hk2 g]⟩
  cont := h.cont.const_smul c
  smooth k τs Xs hX g := (h.smooth k τs Xs hX g).const_smul c
  zfin := by
    obtain ⟨W, hW, hφ, hg⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c hφ, hg⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [foldr_rder_smul, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c) }


variable (V) in
theorem isCuspFun_smul {φ : GA D V → ℂ} (h : IsCuspFun V φ) (c : ℂ) : IsCuspFun V (c • φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simp only [Pi.smul_apply]
  rw [MeasureTheory.integral_smul, h r C hC μ 𝓕 hμ h𝓕 g, smul_zero]

theorem isMultMap_smul {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : IsMultMap θ M J χ T) (c : ℂ) : IsMultMap θ M J χ (c • T) := {
  aut v := by
    show IsAutFunSm θ V (c • T v)
    exact isAutFunSm_smul θ V (hT.aut v) c
  cusp v := by
    show IsCuspFun V (c • T v)
    exact isCuspFun_smul V (hT.cusp v) c
  lev v k hk g := by
    simp only [_root_.smul_apply, Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]
    ring
  equiv τ g hg v w hw := by
    rw [_root_.smul_apply, _root_.smul_apply, hT.equiv τ g hg v w hw]
    rfl
  cont τ v x := by
    obtain ⟨ℓ, ⟨L, C, hL, hC⟩, hℓ⟩ := hT.cont τ v x
    refine ⟨c • ℓ, ⟨L, ‖c‖ * C, hL, fun w hw => ?_⟩, fun w => ?_⟩
    · rw [LinearMap.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, _root_.smul_apply, Pi.smul_apply, hℓ w] }

end Formalism.IndefR.Mult

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.WeilFull
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
  Formalism.IndefR.Fock.Sk MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.WeilFull

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SuppV (ε : AF D.host.F) (V : HSp D) (g : GA D V) : Prop :=
  ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = (mt V g - 1) i j

def UnrAtV (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, (1 - algebraMap (AF D.host.F) (AE D) ε) * (x : AE D) = 1 - algebraMap (AF D.host.F) (AE D) ε →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def SphInertAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  S.rank ≠ T.rank → (Even S.rank ∨ Even T.rank) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
      Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (2 : 𝓞 D.host.F) ∉ v.asIdeal →
      (∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) →
      UnrAtV ε χS → UnrAtV ε χT →
    ∀ (g : GA D S) (h : GA D T), SuppV ε S g → SuppV ε T h →
      Lev.finE S g ∈ Formalism.L2.DIV.St βS → Lev.finE T h ∈ Formalism.L2.DIV.St βT →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun w => w = v) f → om (g, h) f = f

def RealAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  LineAtExists D →
  ∀ (θ : InfFam D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ), PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (τ : D.what₂.Tau) (αS αT : ℚ), HasInfExp D χS τ αS → HasInfExp D χT τ αT →
    ∀ (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ →
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f →
          ∀ (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (x : WO S T),
            HasDerivAt (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) (pureTensorO ψ θ S T sS sT BS BT f P) x)
              (pureTensorO ψ θ S T sS sT BS BT f
                (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
                  (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace -
                    (αT : ℂ) * XS.trace) • P) x) 0

structure IsWeilFull (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  datum : IsWeilDatumO ψ S T χS χT om
  inert : SphInertAtO ψ S T χS χT om
  real : RealAtO ψ S T χS χT om

def WeilExistsFull (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilFull ψ S T χS χT om

def InertAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → SphInertAtO ψ S T χS χT om

def RealAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → RealAtO ψ S T χS χT om

theorem weilExistsFull_of (h : AutomorphicFormsHyp.WeilExistsO D) (hi : InertAllO D) (hr : RealAllO D) : WeilExistsFull D := by
  intro ψ S T χS χT hψ hS hT hrS hrT
  obtain ⟨om, hom⟩ := h ψ S T χS χT hψ hS hT hrS hrT
  exact ⟨om, hom, hi ψ S T χS χT om hom, hr ψ S T χS χT om hom⟩

end Formalism.IndefR.WeilFull

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.PeterssonHilbertSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure IsHermPos {N : Type} [AddCommGroup N] [Module ℂ N] (C : Submodule ℂ N) (ip : N → N → ℂ) : Prop where
  fd : FiniteDimensional ℂ C
  add : ∀ x x' y : C, ip ((x : N) + x') y = ip x y + ip x' y
  smul : ∀ (s : ℂ) (x y : C), ip (s • (x : N)) y = starRingEnd ℂ s * ip x y
  herm : ∀ x y : C, starRingEnd ℂ (ip x y) = ip y x
  pos : ∀ x : C, x ≠ 0 → 0 < (ip x x).re

section Gen

variable {N : Type} [AddCommGroup N] [Module ℂ N] {C : Submodule ℂ N} {ip : N → N → ℂ}

theorem isHermPos_scale (h : IsHermPos C ip) {s : ℝ} (hs : 0 < s) :
    IsHermPos C (fun x y => (s : ℂ) * ip x y) := by
  refine ⟨h.fd, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    simp only [h.add x x' y, mul_add]
  · intro a x y
    simp only [h.smul a x y]
    ring
  · intro x y
    simp only [map_mul, Complex.conj_ofReal, h.herm x y]
  · intro x hx
    simp only [Complex.re_ofReal_mul]
    exact mul_pos hs (h.pos x hx)

theorem IsHermPos.map_equiv {N' : Type} [AddCommGroup N'] [Module ℂ N'] (h : IsHermPos C ip) (e : N ≃ₗ[ℂ] N') :
    IsHermPos (C.map (e : N →ₗ[ℂ] N')) (fun x y => ip (e.symm x) (e.symm y)) := by
  have hm : ∀ z : C.map (e : N →ₗ[ℂ] N'), e.symm (z : N') ∈ C := by
    intro z
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp z.2
    rw [← hyz]
    simpa using hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · haveI := h.fd
    infer_instance
  · intro x x' y
    show ip (e.symm ((x : N') + x')) (e.symm y) = ip (e.symm x) (e.symm y) + ip (e.symm x') (e.symm y)
    rw [map_add (f := _)]
    exact h.add ⟨_, hm x⟩ ⟨_, hm x'⟩ ⟨_, hm y⟩
  · intro s x y
    show ip (e.symm (s • (x : N'))) (e.symm y) = starRingEnd ℂ s * ip (e.symm x) (e.symm y)
    rw [map_smul]
    exact h.smul s ⟨_, hm x⟩ ⟨_, hm y⟩
  · intro x y
    exact h.herm ⟨_, hm x⟩ ⟨_, hm y⟩
  · intro x hx
    refine h.pos ⟨_, hm x⟩ ?_
    intro h0
    apply hx
    apply Subtype.ext
    have h1 : e.symm (x : N') = 0 := congrArg Subtype.val h0
    simpa using h1

end Gen

section MultSec

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def PetPos (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ F : GA D V → ℂ, Continuous F → (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → F ≠ 0 →
    IntegrableOn (fun g => ‖F g‖ ^ 2) 𝓕 μ → 0 < ∫ g in 𝓕, ‖F g‖ ^ 2 ∂μ

def SmNonzero (M : DSModel V S) : Prop := ∀ τ, ∃ w : M.sm τ, w ≠ 0

variable (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))

theorem isMultiplicityInner_add_left {T T' T'' : MMap M} {a b : ℂ} (h : IsMultIP M μ 𝓕 T T'' a)
    (h' : IsMultIP M μ 𝓕 T' T'' b) : IsMultIP M μ 𝓕 (T + T') T'' (a + b) := by
  intro v v'
  obtain ⟨i1, e1⟩ := h v v'
  obtain ⟨i2, e2⟩ := h' v v'
  simp only [MultilinearMap.add_apply, Pi.add_apply, star_add, add_mul]
  exact ⟨Integrable.add i1 i2, by rw [integral_add i1 i2, e1, e2]⟩

theorem isMultiplicityInner_smul_left {T T' : MMap M} {a : ℂ} (s : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M μ 𝓕 (s • T) T' (starRingEnd ℂ s * a) := by
  intro v v'
  obtain ⟨i1, e1⟩ := h v v'
  have hf : ∀ g, star ((s • T) v g) * T' v' g = starRingEnd ℂ s * (star (T v g) * T' v' g) := by
    intro g
    rw [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
    rfl
  simp only [hf]
  exact ⟨Integrable.const_mul i1 _, by rw [integral_const_mul, e1, mul_assoc]⟩

theorem isMultiplicityInner_swap {T T' : MMap M} {a : ℂ} (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M μ 𝓕 T' T (starRingEnd ℂ a) := by
  intro v v'
  obtain ⟨i1, e1⟩ := h v' v
  have hf : ∀ g, star (T' v g) * T v' g = starRingEnd ℂ (star (T v' g) * T' v g) := by
    intro g
    show _ = star (star (T v' g) * T' v g)
    rw [star_mul', star_star, mul_comm]
  simp only [hf]
  refine ⟨((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp i1).congr (ae_of_all _ fun g => ?_), ?_⟩
  · simp
  rw [integral_conj, e1, map_mul, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V)) (χ : GA D V → ℂ)

theorem mult_cont_left {T : MMap M} (hT : T ∈ Mult θ M J χ) (v : M.Vec) :
    Continuous (T v) ∧ ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    have hA := (show IsMultMap θ M J χ T from hT).aut v
    exact ⟨hA.cont, hA.left⟩
  | zero =>
    refine ⟨?_, fun _ _ _ => rfl⟩
    simp only [MultilinearMap.zero_apply]
    exact continuous_const
  | add T T' _ _ h1 h2 =>
    refine ⟨?_, fun γ hγ g => ?_⟩
    · rw [MultilinearMap.add_apply]
      exact h1.1.add h2.1
    · simp only [MultilinearMap.add_apply, Pi.add_apply, h1.2 γ hγ g, h2.2 γ hγ g]
  | smul a T _ h1 =>
    refine ⟨?_, fun γ hγ g => ?_⟩
    · rw [MultilinearMap.smul_apply]
      exact h1.1.const_smul a
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, h1.2 γ hγ g]

theorem isHermPos_mult (hθ : IsInfFam θ) (hfin : HCFinite θ M J χ)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1)
    (hS : SchurMult θ M J χ μ 𝓕) (hH : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hP : PetPos V μ 𝓕) (hne : SmNonzero M) : IsHermPos (Mult θ M J χ) (ipM M μ 𝓕) := by
  have hfd : FiniteDimensional ℂ (Mult θ M J χ) := hfin hθ hU

  have huniq : ∀ (T T' : MMap M) (c c' : ℂ), IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 T T' c' → c = c' := by
    intro T T' c c' h h'
    have hne' : ∀ τ, ∃ w : M.sm τ, w ≠ 0 := hne
    choose w hw using hne'
    have hp : (∏ τ, ⟪((w τ : M.sm τ) : M.H τ), ((w τ : M.sm τ) : M.H τ)⟫_ℂ) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro τ _
      rw [inner_self_ne_zero]
      intro h0
      exact hw τ (Subtype.ext h0)
    have e := (h w w).2
    have e' := (h' w w).2
    exact mul_right_cancel₀ hp (e.symm.trans e')
  have hval : ∀ (T T' : MMap M) (c : ℂ), IsMultIP M μ 𝓕 T T' c → ipM M μ 𝓕 T T' = c := by
    intro T T' c h
    have hex : ∃ c, IsMultIP M μ 𝓕 T T' c := ⟨c, h⟩
    unfold ipM
    rw [dite_eq_left hex]
    exact huniq _ _ _ _ hex.choose_spec h
  have hE : ∀ x y : Mult θ M J χ, ∃ c, IsMultIP M μ 𝓕 x y c := fun x y => hS hθ hH hF _ x.2 _ y.2
  refine ⟨hfd, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    obtain ⟨a, ha⟩ := hE x y
    obtain ⟨b, hb⟩ := hE x' y
    rw [hval _ _ _ ha, hval _ _ _ hb]
    exact hval _ _ _ (isMultiplicityInner_add_left M μ 𝓕 ha hb)
  · intro s x y
    obtain ⟨a, ha⟩ := hE x y
    rw [hval _ _ _ ha]
    exact hval _ _ _ (isMultiplicityInner_smul_left M μ 𝓕 s ha)
  · intro x y
    obtain ⟨a, ha⟩ := hE x y
    rw [hval _ _ _ ha, hval _ _ _ (isMultiplicityInner_swap M μ 𝓕 ha)]
  · intro x hx
    obtain ⟨c, hc⟩ := hE x x
    rw [hval _ _ _ hc]
    have hx' : (x : MMap M) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    obtain ⟨v, hv⟩ : ∃ v, (x : MMap M) v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx' (MultilinearMap.ext hcon)
    obtain ⟨hi, he⟩ := hc v v
    have hcl := mult_cont_left M θ J χ x.2 v
    have hI : IntegrableOn (fun g => ‖(x : MMap M) v g‖ ^ 2) 𝓕 μ := by
      refine (Integrable.norm hi).congr (ae_of_all _ fun g => ?_)
      simp only [norm_mul, norm_star, sq]
    have hpos := hP ((x : MMap M) v) hcl.1 hcl.2 hv hI

    have hvne : ∀ τ, ((v τ : M.sm τ) : M.H τ) ≠ 0 := by
      intro τ h0
      apply hv
      exact (x : MMap M).map_coord_zero τ (Subtype.ext h0)
    have hL : ∫ g in 𝓕, star ((x : MMap M) v g) * (x : MMap M) v g ∂μ =
        ((∫ g in 𝓕, ‖(x : MMap M) v g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      refine Eq.trans ?_ (integral_ofReal (𝕜 := ℂ) (μ := μ.restrict 𝓕) (f := fun g => ‖(x : MMap M) v g‖ ^ 2))
      congr 1
      funext g
      rw [RCLike.ofReal_pow]
      exact RCLike.conj_mul _
    have hR : (∏ τ, ⟪((v τ : M.sm τ) : M.H τ), ((v τ : M.sm τ) : M.H τ)⟫_ℂ) =
        ((∏ τ, ‖((v τ : M.sm τ) : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.prod_congr rfl fun τ _ => inner_self_eq_norm_sq_to_K _
    have hRpos : 0 < ∏ τ, ‖((v τ : M.sm τ) : M.H τ)‖ ^ 2 :=
      Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.mpr (hvne τ)) 2
    rw [hL, hR] at he
    have hc' : c = (((∫ g in 𝓕, ‖(x : MMap M) v g‖ ^ 2 ∂μ) / ∏ τ, ‖((v τ : M.sm τ) : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, he, mul_div_assoc, div_self (by exact_mod_cast hRpos.ne'), mul_one]
    rw [hc', Complex.ofReal_re]
    exact div_pos hpos hRpos

def ipMT' (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (x y : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) : ℂ :=
  ipM M μ 𝓕 (PiTensorProduct.lift.symm x) (PiTensorProduct.lift.symm y)

theorem isHermPos_multT (hθ : IsInfFam θ) (hfin : HCFinite θ M J χ)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1)
    (hS : SchurMult θ M J χ μ 𝓕) (hH : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hP : PetPos V μ 𝓕) (hne : SmNonzero M) : IsHermPos (MultT θ M J χ) (ipMT' M μ 𝓕) :=
  (isHermPos_mult M μ 𝓕 θ J χ hθ hfin hU hS hH hF hP hne).map_equiv PiTensorProduct.lift

end MultSec

end Formalism.IndefR.PeterssonHilbertSpace

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsBaseLevel
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {X : CxData A3.fam3.amb3} {s : ℕ}
  {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)}

def indefiniteDataAtBaseLevel (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    IndefRows (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) false) :=
  X.rowsOfR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hR.rowHyp false) hR.liftHyp0 (hR.pos false) hR.proviso0
    hR.types0 hR.h0
    (CxData.cutDims X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hR.wf false) hR.h4pos hR.kForm hR.ewNorm hR.types0
      (hR.what₂ false).1 (hR.ratMu false) (hR.rowHyp false).h3 hR.lifts0.1 hR.ratTh hR.liftHyp0.h3W (hR.partsE false)
      hR.partsW hR.dimParts)

theorem subspaces_stable_in_block (hR : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) : X.zs.Stable ∧ X.zs.InBlock :=
  ⟨hR.stable, hR.inBlock⟩

end Formalism.IndefR.Cx
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.MultGood
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hanti, Q, hQ, rfl⟩, ⟨_, hint⟩, hp, hq⟩ := h
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a),
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a), fun a => by simp [hQ], ?_⟩,
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩, ?_, ?_⟩
  · unfold dualPar
    rw [Finset.image_image]
    ext ⟨x, s⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.rev a, by simpa using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨_, ha⟩
  · obtain ⟨z, hz⟩ := hint (Fin.rev a)
    refine ⟨-z - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)

theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) : StrictAnti fun a : Fin R.r => lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have := lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at this
  have h1 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith

def sgA (R : Ranks) (a : ℕ) : Bool := decide (a < R.k - 1 ∨ Even (a - (R.k - 1)))

theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin R.r => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := hpq ▸ odd_r R
  ext ⟨x, s⟩
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    cases a with
    | inl i => exact ⟨⟨i, by have := i.2; omega⟩, rfl, by simp⟩
    | inr c => exact ⟨⟨p + c, by have := c.2; omega⟩, rfl, by simp⟩
  · rintro ⟨a, rfl, rfl⟩
    by_cases hc : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hc⟩, rfl, by simp [hc]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_, by simp [hc]⟩
      simp only [Sum.elim_inr]
      rw [show p + ((a : ℕ) - p) = a by omega]

end Formalism.IndefR.Mult
end
end
