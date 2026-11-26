module

public import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.DenseWeakVectors
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselDerivatives.ExpSup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame
noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Core

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def IsStable (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : Prop :=
  ∀ h, ∀ f ∈ U, Formalism.L2.NG.rt L n h f ∈ U

def IsSmoothF (f : Formalism.AUTREP.GAf L n → ℂ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong L n N κ → Formalism.L2.NG.rt L n κ f = f

def cyc (f : Formalism.AUTREP.GAf L n → ℂ) : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) :=
  Submodule.span ℂ (Set.range fun h => Formalism.L2.NG.rt L n h f)


variable (L n) in
def CongConj : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (N : ℕ), 0 < N → ∃ N' : ℕ, 0 < N' ∧
    ∀ κ, Formalism.L2.NG.Cong L n N' κ → Formalism.L2.NG.Cong L n N (h⁻¹ * κ * h)

def IsTypeVec (J' : Set (Formalism.AUTREP.GAf L n)) (χ' : Formalism.AUTREP.GAf L n → ℂ) (f : Formalism.AUTREP.GAf L n → ℂ) : Prop :=
  ∀ κ ∈ J', Formalism.L2.NG.rt L n κ f = χ' κ • f

def heckeG {ι : Type} (s : Finset ι) (γ : ι → Formalism.AUTREP.GAf L n) :
    (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf L n → ℂ) :=
  ∑ i ∈ s, Formalism.L2.NG.rt L n (γ i)

def IsCoMax (f : Formalism.AUTREP.GAf L n → ℂ) (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : Prop :=
  U ≤ cyc f ∧ IsStable U ∧ f ∉ U ∧
    ∀ U' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ), U ≤ U' → U' ≤ cyc f → IsStable U' → f ∉ U' → U' = U

def mc (l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ) : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf L n → ℂ) where
  toFun f g := l (Formalism.L2.NG.rt L n g f)
  map_add' f f' := by
    funext g
    simp
  map_smul' a f := by
    funext g
    simp

end Core

section CoreProofs

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem rt_apply (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) (x : Formalism.AUTREP.GAf L n) :
    Formalism.L2.NG.rt L n h f x = f (x * h) := rfl

theorem rt_rt (g h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    Formalism.L2.NG.rt L n g (Formalism.L2.NG.rt L n h f) = Formalism.L2.NG.rt L n (g * h) f := by
  funext x
  rw [rt_apply, rt_apply, rt_apply, mul_assoc]

theorem rt_one (f : Formalism.AUTREP.GAf L n → ℂ) : Formalism.L2.NG.rt L n 1 f = f := by
  funext x
  rw [rt_apply, mul_one]

theorem self_mem_cyc (f : Formalism.AUTREP.GAf L n → ℂ) : f ∈ cyc f := by
  have h := Submodule.subset_span (R := ℂ)
    (Set.mem_range_self (f := fun h : Formalism.AUTREP.GAf L n => Formalism.L2.NG.rt L n h f) (1 : Formalism.AUTREP.GAf L n))
  simp only [rt_one] at h
  exact h

theorem rt_mem_cyc (f : Formalism.AUTREP.GAf L n → ℂ) (h : Formalism.AUTREP.GAf L n) : Formalism.L2.NG.rt L n h f ∈ cyc f := by
  exact Submodule.subset_span ⟨h, rfl⟩

theorem cyc_stable (f : Formalism.AUTREP.GAf L n → ℂ) : IsStable (cyc f) := by
  intro h g hg
  have hle : cyc f ≤ (cyc f).comap (Formalism.L2.NG.rt L n h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    show Formalism.L2.NG.rt L n h (Formalism.L2.NG.rt L n k f) ∈ cyc f
    rw [rt_rt]
    exact rt_mem_cyc f _
  exact hle hg

theorem cyc_le {f : Formalism.AUTREP.GAf L n → ℂ} {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (hU : IsStable U) (hf : f ∈ U) :
    cyc f ≤ U := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact hU k f hf

theorem exists_coMax (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : ∃ U, IsCoMax f U := by
  classical
  let S : Set (Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) := {U | U ≤ cyc f ∧ IsStable U ∧ f ∉ U}
  have h0 : (⊥ : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) ∈ S := by
    refine ⟨bot_le, fun h g hg => ?_, ?_⟩
    · rw [Submodule.mem_bot] at hg ⊢
      rw [hg, map_zero]
    · rw [Submodule.mem_bot]
      exact hf
  obtain ⟨U, -, hU⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir := hc.directedOn
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcS hz).1, fun h g hg => ?_, fun hf' => ?_⟩,
      fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hgz⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hg
      exact (Submodule.mem_sSup_of_directed hne hdir).mpr ⟨z, hz, (hcS hz).2.1 h g hgz⟩
    · obtain ⟨z, hz, hfz⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hf'
      exact (hcS hz).2.2 hfz) ⊥ h0
  refine ⟨U, hU.prop.1, hU.prop.2.1, hU.prop.2.2, fun U' hUU' hU'c hU's hfU' => ?_⟩
  exact hU.eq_of_ge ⟨hU'c, hU's, hfU'⟩ hUU'

theorem exists_sep (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ∉ U) :
    ∃ l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ, (∀ u ∈ U, l u = 0) ∧ l f ≠ 0 := by
  have hq : U.mkQ f ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ ((Formalism.AUTREP.GAf L n → ℂ) ⧸ U), φ (U.mkQ f) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ (U.mkQ f)).mp hcon)
  refine ⟨φ.comp U.mkQ, fun u hu => ?_, hφ⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu, map_zero]

theorem mc_apply (l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ) (f : Formalism.AUTREP.GAf L n → ℂ) (g : Formalism.AUTREP.GAf L n) :
    mc l f g = l (Formalism.L2.NG.rt L n g f) := rfl

theorem mc_rt (l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ) (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    mc l (Formalism.L2.NG.rt L n h f) = Formalism.L2.NG.rt L n h (mc l f) := by
  funext g
  rw [mc_apply, rt_apply, mc_apply, rt_rt]

theorem mc_eq_zero {l : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ} {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (hU : IsStable U)
    (hl : ∀ u ∈ U, l u = 0) {u : Formalism.AUTREP.GAf L n → ℂ} (hu : u ∈ U) : mc l u = 0 := by
  funext g
  rw [mc_apply, Pi.zero_apply]
  exact hl _ (hU g u hu)

theorem heckeG_apply {ι : Type} (s : Finset ι) (γ : ι → Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    heckeG s γ f = ∑ i ∈ s, Formalism.L2.NG.rt L n (γ i) f := by
  simp [heckeG]

def coMaxOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) :=
  (exists_coMax f hf).choose

theorem coMaxOf_spec (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : IsCoMax f (coMaxOf f hf) := by
  exact (exists_coMax f hf).choose_spec

def lOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] ℂ :=
  (exists_sep (coMaxOf f hf) f (coMaxOf_spec f hf).2.2.1).choose

theorem lOf_spec (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) :
    (∀ u ∈ coMaxOf f hf, lOf f hf u = 0) ∧ lOf f hf f ≠ 0 := by
  exact (exists_sep (coMaxOf f hf) f (coMaxOf_spec f hf).2.2.1).choose_spec

def qOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : (Formalism.AUTREP.GAf L n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf L n → ℂ) :=
  mc (lOf f hf)

def SOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) :=
  (cyc f).map (qOf f hf)

theorem SOf_stable (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : IsStable (SOf f hf) := by
  intro h x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact Submodule.mem_map.mpr ⟨_, cyc_stable f h y hy, mc_rt _ h y⟩

theorem qOf_self_mem (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : qOf f hf f ∈ SOf f hf := by
  exact Submodule.mem_map_of_mem (self_mem_cyc f)

theorem qOf_self_ne (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : qOf f hf f ≠ 0 := by
  intro h0
  have h1 := congrFun h0 1
  rw [Pi.zero_apply] at h1
  apply (lOf_spec f hf).2
  have h2 : qOf f hf f 1 = lOf f hf (Formalism.L2.NG.rt L n 1 f) := rfl
  rw [h2, rt_one] at h1
  exact h1

theorem SOf_ne (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) : SOf f hf ≠ ⊥ := by
  intro h
  have hm := qOf_self_mem f hf
  rw [h, Submodule.mem_bot] at hm
  exact qOf_self_ne f hf hm

theorem SOf_irr (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) (S' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ))
    (hle : S' ≤ SOf f hf) (hst : ∀ h, ∀ g ∈ S', Formalism.L2.NG.rt L n h g ∈ S') : S' = ⊥ ∨ S' = SOf f hf := by
  classical
  have hUspec := coMaxOf_spec f hf
  have hl := lOf_spec f hf
  let W : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) := S'.comap (qOf f hf) ⊓ cyc f
  have hWst : IsStable W := by
    intro h g hg
    obtain ⟨hg1, hg2⟩ := Submodule.mem_inf.mp hg
    refine Submodule.mem_inf.mpr ⟨?_, cyc_stable f h g hg2⟩
    show qOf f hf (Formalism.L2.NG.rt L n h g) ∈ S'
    rw [show qOf f hf (Formalism.L2.NG.rt L n h g) = Formalism.L2.NG.rt L n h (qOf f hf g) from mc_rt _ h g]
    exact hst h _ hg1
  have hq0 : ∀ u ∈ coMaxOf f hf, qOf f hf u = 0 := fun u hu => mc_eq_zero hUspec.2.1 hl.1 hu
  have hUW : coMaxOf f hf ≤ W := fun u hu => Submodule.mem_inf.mpr
    ⟨by show qOf f hf u ∈ S'; rw [hq0 u hu]; exact S'.zero_mem, hUspec.1 hu⟩
  by_cases hfW : f ∈ W
  · right
    refine le_antisymm hle ?_
    have hcW : cyc f ≤ W := cyc_le hWst hfW
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact (Submodule.mem_inf.mp (hcW hy)).1
  · left
    have hWU : W = coMaxOf f hf := hUspec.2.2.2 W hUW inf_le_right hWst hfW
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp (hle hx)
    have hyW : y ∈ W := Submodule.mem_inf.mpr ⟨hx, hy⟩
    rw [hWU] at hyW
    rw [Submodule.mem_bot]
    exact hq0 y hyW

theorem SOf_smooth (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) (hsm : ∀ g ∈ cyc f, IsSmoothF g) :
    ∀ x ∈ SOf f hf, ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong L n N κ → Formalism.L2.NG.rt L n κ x = x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨N, hN, hκ⟩ := hsm y hy
  refine ⟨N, hN, fun κ hκN => ?_⟩
  rw [show Formalism.L2.NG.rt L n κ (qOf f hf y) = qOf f hf (Formalism.L2.NG.rt L n κ y) from (mc_rt _ κ y).symm,
    hκ κ hκN]

theorem cyc_smooth (hc : CongConj L n) {f : Formalism.AUTREP.GAf L n → ℂ} (h0 : IsSmoothF f) : ∀ g ∈ cyc f, IsSmoothF g := by
  have cong_dvd : ∀ (a b : ℕ) (κ : Formalism.AUTREP.GAf L n), Formalism.L2.NG.Cong L n (a * b) κ →
      Formalism.L2.NG.Cong L n a κ := by
    intro a b κ hκ
    unfold Formalism.L2.NG.Cong at hκ ⊢
    refine ⟨hκ.1, fun i j => ?_⟩
    obtain ⟨y, hy, hy'⟩ := hκ.2 i j
    refine ⟨(b : _) * y, mul_mem (natCast_mem _ b) hy, ?_⟩
    rw [hy', Nat.cast_mul, mul_assoc]
  let Sm : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) :=
    { carrier := {g | IsSmoothF g}
      zero_mem' := ⟨1, one_pos, fun κ _ => map_zero _⟩
      add_mem' := by
        rintro a b ⟨N1, hN1, h1⟩ ⟨N2, hN2, h2⟩
        refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, fun κ hκ => ?_⟩
        rw [map_add (f := _), h1 κ (cong_dvd N1 N2 κ hκ),
          h2 κ (cong_dvd N2 N1 κ (by rw [mul_comm]; exact hκ))]
      smul_mem' := by
        rintro c a ⟨N1, hN1, h1⟩
        exact ⟨N1, hN1, fun κ hκ => by rw [map_smul, h1 κ hκ]⟩ }
  intro g hg
  have hle : cyc f ≤ Sm := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    obtain ⟨N, hN, hκ⟩ := h0
    obtain ⟨N', hN', hcon⟩ := hc h N hN
    refine ⟨N', hN', fun κ hκ' => ?_⟩
    rw [rt_rt, show κ * h = h * (h⁻¹ * κ * h) by group, ← rt_rt, hκ _ (hcon κ hκ')]
  exact hle hg

def finTypOf (f : Formalism.AUTREP.GAf L n → ℂ) (hf : f ≠ 0) (hsm : ∀ g ∈ cyc f, IsSmoothF g) : Formalism.L2.NG.FinTyp L n where
  S := SOf f hf
  stable := SOf_stable f hf
  smooth := SOf_smooth f hf hsm
  ne := SOf_ne f hf
  irr := SOf_irr f hf

end CoreProofs

section Conc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHost (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ)

structure RowPsi where
  ψ : Formalism.AUTREP.GAf D.host.E n →* GA D V
  inj : Function.Injective ψ
  into : ∀ h, ψ h ∈ GfC V
  onto : ∀ g ∈ GfC V, ∃ h, ψ h = g

variable {V n}


open Classical in
def pre (P : RowPsi V n) (γ : GA D V) : Formalism.AUTREP.GAf D.host.E n :=
  if h : ∃ x, P.ψ x = γ then h.choose else 1

def LevOK (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) : Prop :=
  ∃ N0 : ℕ, 0 < N0 ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N0 κ → P.ψ κ ∈ J ∧ χ (P.ψ κ) = 1

def Hecke₃ (P : RowPsi V n) (R : Finset (GA D V)) :
    (Formalism.AUTREP.GAf D.host.E n → ℂ) →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E n → ℂ) :=
  heckeG R (pre P)

variable {Sp : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def RowRepExists (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Prop :=
  ∃ rep : Mult.IxFull θ M J χ Sb e → Formalism.L2.NG.FinTyp D.host.E n,
    (∀ c c', (rep c).Iso (rep c') → c = c') ∧
    ∀ c, ∃ x ∈ (rep c).S, x ≠ 0 ∧ IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x ∧
      ∀ Pr d R, Mult.Hecke₂ V J χ Sb Pr d R → Hecke₃ P R x = c.1 Pr d • x

end Conc

section ConcProofs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHost' (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ}
variable {Sp : D.what₂.Tau → SPar} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
variable {M : Mult.DSModel V Sp} {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
variable {e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)}

theorem mult_lev {T : Mult.MMap M} (hT : T ∈ Mult.Mult θ M J χ) : ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro v k hk g
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy]
    ring
  | smul a x _ hx =>
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx]
    ring

theorem pre_spec (P : RowPsi V n) {γ : GA D V} (hγ : γ ∈ GfC V) : P.ψ (pre P γ) = γ := by
  unfold pre
  rw [dite_eq_left (P.onto γ hγ)]
  exact (P.onto γ hγ).choose_spec

theorem exists_wit (c : Mult.IxFull θ M J χ Sb e) :
    ∃ T : Mult.MMap M, T ∈ Mult.partFull θ M J χ Sb c.1 ⊓ Mult.goodPart θ M J χ e ∧ ∃ v g0, T v g0 ≠ 0 := by
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot c.2.2
  refine ⟨T, hT, ?_⟩
  by_contra hcon
  push_neg at hcon
  exact hT0 (MultilinearMap.ext fun v => funext fun g => hcon v g)

def witT (c : Mult.IxFull θ M J χ Sb e) : Mult.MMap M := (exists_wit c).choose

def witV (c : Mult.IxFull θ M J χ Sb e) : M.Vec := (exists_wit c).choose_spec.2.choose

def witG (c : Mult.IxFull θ M J χ Sb e) : GA D V := (exists_wit c).choose_spec.2.choose_spec.choose

theorem witT_mem (c : Mult.IxFull θ M J χ Sb e) :
    witT c ∈ Mult.partFull θ M J χ Sb c.1 ⊓ Mult.goodPart θ M J χ e := by
  exact (exists_wit c).choose_spec.1

theorem wit_ne (c : Mult.IxFull θ M J χ Sb e) : witT c (witV c) (witG c) ≠ 0 := by
  exact (exists_wit c).choose_spec.2.choose_spec.choose_spec

def srcOf (P : RowPsi V n) (c : Mult.IxFull θ M J χ Sb e) : Formalism.AUTREP.GAf D.host.E n → ℂ :=
  fun h => witT c (witV c) (witG c * P.ψ h)

theorem srcOf_ne (P : RowPsi V n) (c : Mult.IxFull θ M J χ Sb e) : srcOf P c ≠ 0 := by
  intro h0
  have h1 := congrFun h0 1
  simp only [srcOf, map_one, mul_one, Pi.zero_apply] at h1
  exact wit_ne c h1

theorem srcOf_type (P : RowPsi V n) (c : Mult.IxFull θ M J χ Sb e) :
    IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) (srcOf P c) := by
  intro κ hκ
  funext h
  rw [rt_apply, Pi.smul_apply, smul_eq_mul]
  simp only [srcOf, map_mul, ← mul_assoc]
  exact mult_lev (Submodule.mem_inf.mp (Submodule.mem_inf.mp (witT_mem c)).1).1 (witV c) (P.ψ κ) hκ
    (witG c * P.ψ h)

theorem srcOf_smooth (P : RowPsi V n) (hl : LevOK P J χ) (c : Mult.IxFull θ M J χ Sb e) : IsSmoothF (srcOf P c) := by
  obtain ⟨N0, hN0, hκ⟩ := hl
  refine ⟨N0, hN0, fun κ hκN => ?_⟩
  have h1 := srcOf_type P c κ (hκ κ hκN).1
  simp only [(hκ κ hκN).2, one_smul] at h1
  exact h1

def rowRep (P : RowPsi V n) (hc : CongConj D.host.E n) (hl : LevOK P J χ) (c : Mult.IxFull θ M J χ Sb e) :
    Formalism.L2.NG.FinTyp D.host.E n :=
  finTypOf (srcOf P c) (srcOf_ne P c) (cyc_smooth hc (srcOf_smooth P hl c))

end ConcProofs

end Formalism.IndefR.principalLevelFrame
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
noncomputable section

open Matrix Topology Filter
open scoped ContDiff InnerProductSpace

namespace Formalism.IndefR.PeterssonHilbertSpace

section Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma sm_exp_smul_contDiff (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun s : ℝ => NormedSpace.exp (s • X)) := by
  have h := PI.BesselDerivW.exp_contDiff X
  simpa only [Complex.coe_smul] using h

lemma sm_prod_exp_contDiff : ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ),
    ContDiff ℝ ∞ (fun t : Fin k → ℝ => (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod)
  | 0, Xs => by simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Fin 0 → ℝ => (1 : Matrix (Fin n) (Fin n) ℂ))
  | k + 1, Xs => by
    have ih := sm_prod_exp_contDiff k (fun i => Xs i.succ)
    have h1 : ContDiff ℝ ∞ (fun t : Fin (k + 1) → ℝ => NormedSpace.exp (t 0 • Xs 0)) :=
      (sm_exp_smul_contDiff (Xs 0)).comp (contDiff_apply ℝ (fun _ => ℝ) (0 : Fin (k + 1)))
    have h2 : ContDiff ℝ ∞ (fun t : Fin (k + 1) → ℝ =>
        (List.ofFn fun i : Fin k => NormedSpace.exp (t i.succ • Xs i.succ)).prod) :=
      ih.comp (contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℝ) i.succ)
    simp only [List.ofFn_succ, List.prod_cons]
    exact PI.KFinSmoothW.Gard.contDiff_mat_mul h1 h2

lemma sm_prod_exp_mem (G : Matrix (Fin n) (Fin n) ℂ) : ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ),
    (∀ i, (Xs i)ᴴ * G + G * Xs i = 0) → ∀ t : Fin k → ℝ,
      ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod)ᴴ * G *
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod = G
  | 0, Xs, _, t => by simp
  | k + 1, Xs, hX, t => by
    have ih := sm_prod_exp_mem G k (fun i => Xs i.succ) (fun i => hX i.succ) (fun i => t i.succ)
    have hl : (t 0 • Xs 0)ᴴ * G + G * (t 0 • Xs 0) = 0 := by
      have h := CCRuleCW.lie_smul G (Xs 0) (hX 0) (t 0)
      simpa only [Complex.coe_smul] using h
    have he := CCRuleCW.exp_mem_UH G (t 0 • Xs 0) hl
    have hm := CCRuleCW.UH_mul G _ _ he ih
    simp only [List.ofFn_succ, List.prod_cons]
    exact hm

lemma sm_transfer {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (Lie : Set (Matrix (Fin n) (Fin n) ℂ))
    (hLie : ∀ X ∈ Lie, Xᴴ * G + G * X = 0) (w : H)
    (hs : PI.UpqRep.SmoothOnH (PI.UpqRep.Jm ε) (fun g => σ g w)) :
    Formalism.L2.Theta.SmoothVec Lie (fun g => σ (P * g * P⁻¹)) w := by
  intro k Xs hX
  have hinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hP)
  have hc : ContDiff ℝ ∞ (fun t : Fin k → ℝ =>
      P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) :=
    PI.KFinSmoothW.Gard.contDiff_mat_mul
      (PI.KFinSmoothW.Gard.contDiff_mat_mul contDiff_const (sm_prod_exp_contDiff k Xs)) contDiff_const
  have hmem : ∀ t : Fin k → ℝ, PI.UpqRep.inUH (PI.UpqRep.Jm ε)
      (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) := by
    intro t
    have hQ := sm_prod_exp_mem G k Xs (fun i => hLie _ (hX i)) t
    set Q := (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod
    show (P * Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q * P⁻¹) = Formalism.REAL.Jm ε
    calc (P * Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q * P⁻¹)
        = (P⁻¹)ᴴ * (Qᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * Q) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hG, hQ]
      _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hinv]; simp
  rw [contDiff_iff_contDiffAt]
  intro t0
  obtain ⟨U, F, hU, h0, hF, hEq⟩ := hs _ (hmem t0)
  have hev : (fun t : Fin k → ℝ => σ (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) w)
      =ᶠ[𝓝 t0] fun t => F (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) := by
    filter_upwards [hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hEq _ ht (hmem t)
  exact ((hF.contDiffAt (hU.mem_nhds h0)).comp t0 hc.contDiffAt).congr_of_eventuallyEq hev

lemma sm_isURepOn_bridge (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ :=
  ⟨⟨h.1.1, fun a ha b hb => h.1.2 a ha b hb⟩, fun g hg v => h.2.1 g hg v, fun v => h.2.2 v⟩

end Gen

section MultSec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

end MultSec

end Formalism.IndefR.PeterssonHilbertSpace

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.MeasurableMulGA
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open Formalism.L2.Theta

namespace Formalism.IndefR.PeterssonHilbertSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem countable_GQ (V : HSp D) : Countable (GQ V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem borel_GA (V : HSp D) : BorelSpace (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem petPos (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hH : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) : PetPos V μ 𝓕 := by
  intro F hc hinv hne hint
  have := countable_GQ V
  have := measurableMul_GA V
  have := borel_GA V
  have := hH
  set U : Set (GA D V) := {g | F g ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have hUne : U.Nonempty := by
    by_contra h
    apply hne
    funext g
    by_contra hg
    exact h ⟨g, hg⟩
  have hUpos : 0 < μ U := hUo.measure_pos μ hUne
  have hnn : 0 ≤ᵐ[μ.restrict 𝓕] fun g => ‖F g‖ ^ 2 := ae_of_all _ (fun g => by positivity)
  refine lt_of_le_of_ne (integral_nonneg fun g => by positivity) ?_
  intro h0
  have hz : (fun g => ‖F g‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0.symm
  have hset : {g : GA D V | ¬ (‖F g‖ ^ 2 = (0 : GA D V → ℝ) g)} = U := by
    ext g
    simp [hUdef]
  have hFU : μ (U ∩ 𝓕) = 0 := by
    have h1 := ae_iff.1 hz
    rw [hset, Measure.restrict_apply hUo.measurableSet] at h1
    exact h1
  have key : U ≤ᵐ[μ] (⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) : Set (GA D V)) := by
    filter_upwards [hF.ae_covers] with x hx hxU
    obtain ⟨γ, hγ⟩ := hx
    refine Set.mem_iUnion.2 ⟨γ, ?_, ?_⟩
    · show F ((γ : GA D V) * x) ≠ 0
      rw [hinv _ γ.2 x]
      exact hxU
    · exact hγ
  have hU0 : μ U = 0 := by
    refine le_antisymm ((measure_mono_ae key).trans ?_) bot_le
    refine (measure_iUnion_le _).trans ?_
    simp only [measure_preimage_mul, hFU, tsum_zero, le_refl]
  exact hUpos.ne' hU0

end Formalism.IndefR.PeterssonHilbertSpace

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.CongNormal
noncomputable section

open NumberField

namespace Formalism.IndefR.principalLevelFrame

section SS

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]


def fixN (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (N : ℕ) : Submodule ℂ A where
  carrier := {a | ∀ κ, Formalism.L2.NG.Cong L n N κ → ρ κ a = a}
  zero_mem' := fun κ _ => map_zero _
  add_mem' := fun ha hb κ hκ => by rw [map_add (f := _), ha κ hκ, hb κ hκ]
  smul_mem' := fun c a ha κ hκ => by rw [map_smul, ha κ hκ]

def IsEqvA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (π : Formalism.L2.NG.FinTyp L n) (Φ : π.S →ₗ[ℂ] A) : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (f : π.S), Φ ⟨Formalism.L2.NG.rt L n h f, π.stable h f f.2⟩ = ρ h (Φ f)

end SS

end Formalism.IndefR.principalLevelFrame
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.CongNatCastEqOneTmul
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Cong

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem cong_natCast_eq_tmul_one (k : ℕ) : (k : ReciprocityTheory.Aut.AL L) = (k : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L) := by
  rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]

theorem cong_natCast_eq_one_tmul (k : ℕ) : (k : ReciprocityTheory.Aut.AL L) = (1 : L) ⊗ₜ[L⁺] (k : ReciprocityTheory.Aut.AFplus L) := by
  rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]

theorem cong_adele_nat_denom (a : ReciprocityTheory.Aut.AFplus L) :
    ∃ k : ℕ, 0 < k ∧ ∀ v, ((k : ReciprocityTheory.Aut.AFplus L) * a) v ∈ v.adicCompletionIntegers L⁺ := by
  obtain ⟨d, hd0, hd⟩ := Formalism.UG.P.levelaf_adele_denom (F := L⁺) a
  set k := Ideal.absNorm (Ideal.span {d}) with hk
  have hk0 : k ≠ 0 := by
    rw [hk, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨k, Nat.pos_of_ne_zero hk0, ?_⟩
  have e : (k : ReciprocityTheory.Aut.AFplus L) * a =
      algebraMap (𝓞 L⁺) (ReciprocityTheory.Aut.AFplus L) c * (algebraMap (𝓞 L⁺) (ReciprocityTheory.Aut.AFplus L) d * a) := by
    rw [← mul_assoc, ← map_mul, hc, map_natCast]
  have hm : (k : ReciprocityTheory.Aut.AFplus L) * a ∈ Formalism.UG.intAd L⁺ := by
    rw [e]
    exact Subring.mul_mem _ (Formalism.UG.P.levelaf_int_mem c) hd
  exact hm

theorem cong_nat_denom (x : ReciprocityTheory.Aut.AL L) : ∃ d : ℕ, 0 < d ∧ (d : ReciprocityTheory.Aut.AL L) * x ∈ ReciprocityTheory.Aut.ALint L := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact Subring.zero_mem _⟩
  | tmul l a =>
    have halg : Algebra.IsAlgebraic ℤ L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
    obtain ⟨m, hm0, hm⟩ := (halg.1 l).exists_integral_multiple
    obtain ⟨k, hk0, hk⟩ := cong_adele_nat_denom a
    refine ⟨m.natAbs * k, Nat.mul_pos (Int.natAbs_pos.2 hm0) hk0, ?_⟩
    have hint : IsIntegral ℤ ((m.natAbs : L) * l) := by
      have e : (m.natAbs : L) * l = ((m.sign : ℤ) : L) * (m • l) := by
        rw [zsmul_eq_mul, ← mul_assoc, ← Int.cast_mul, ← Int.cast_natCast, Int.sign_mul_self_eq_natAbs]
      rw [e]
      exact IsIntegral.mul isIntegral_algebraMap hm
    have e2 : ((m.natAbs * k : ℕ) : ReciprocityTheory.Aut.AL L) * (l ⊗ₜ[L⁺] a) =
        (((m.natAbs : L) * l) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) *
          ((1 : L) ⊗ₜ[L⁺] ((k : ReciprocityTheory.Aut.AFplus L) * a)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Nat.cast_mul, cong_natCast_eq_tmul_one m.natAbs,
        cong_natCast_eq_one_tmul k, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e2]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨_, hint⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨_, hk, rfl⟩))
  | add x y hx hy =>
    obtain ⟨dx, hx0, hx⟩ := hx
    obtain ⟨dy, hy0, hy⟩ := hy
    refine ⟨dx * dy, Nat.mul_pos hx0 hy0, ?_⟩
    have e : ((dx * dy : ℕ) : ReciprocityTheory.Aut.AL L) * (x + y) =
        (dy : ReciprocityTheory.Aut.AL L) * ((dx : ReciprocityTheory.Aut.AL L) * x) + (dx : ReciprocityTheory.Aut.AL L) * ((dy : ReciprocityTheory.Aut.AL L) * y) := by
      push_cast; ring
    rw [e]
    exact Subring.add_mem _ (Subring.mul_mem _ (natCast_mem _ _) hx) (Subring.mul_mem _ (natCast_mem _ _) hy)

theorem cong_dvd_mem {x : ReciprocityTheory.Aut.AL L} {d e : ℕ} (hx : (d : ReciprocityTheory.Aut.AL L) * x ∈ ReciprocityTheory.Aut.ALint L) (hde : d ∣ e) :
    (e : ReciprocityTheory.Aut.AL L) * x ∈ ReciprocityTheory.Aut.ALint L := by
  obtain ⟨c, rfl⟩ := hde
  rw [Nat.cast_mul, mul_comm (d : ReciprocityTheory.Aut.AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) hx

end Cong

theorem congConj_holds (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : CongConj L n := by
  classical
  intro h N hN
  choose D hD0 hD using fun x : ReciprocityTheory.Aut.AL L => cong_nat_denom (L := L) x
  set H : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (h.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) with hH
  set Hi : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) :=
    ((h⁻¹ : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) with hHi
  set d : ℕ := ∏ i, ∏ j, (D (H i j) * D (Hi i j)) with hd
  have hd0 : 0 < d := Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => Nat.mul_pos (hD0 _) (hD0 _)
  have hdv : ∀ i j, D (H i j) * D (Hi i j) ∣ d := fun i j =>
    dvd_trans (Finset.dvd_prod_of_mem (fun j => D (H i j) * D (Hi i j)) (Finset.mem_univ j))
      (Finset.dvd_prod_of_mem (fun i => ∏ j, D (H i j) * D (Hi i j)) (Finset.mem_univ i))
  have hHd : ∀ i j, (d : ReciprocityTheory.Aut.AL L) * H i j ∈ ReciprocityTheory.Aut.ALint L := fun i j =>
    cong_dvd_mem (hD _) (dvd_trans (dvd_mul_right _ _) (hdv i j))
  have hHid : ∀ i j, (d : ReciprocityTheory.Aut.AL L) * Hi i j ∈ ReciprocityTheory.Aut.ALint L := fun i j =>
    cong_dvd_mem (hD _) (dvd_trans (dvd_mul_left _ _) (hdv i j))
  refine ⟨N * d * d, Nat.mul_pos (Nat.mul_pos hN hd0) hd0, ?_⟩
  intro κ hκ
  choose Y hYm hYe using hκ.2
  set K : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) with hK
  have hprod : ((h⁻¹ * κ * h : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = Hi * K * H := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  have hHiH : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  have hKY : K - 1 = ((N * d * d : ℕ) : ReciprocityTheory.Aut.AL L) • Matrix.of Y := by
    ext k l
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact hYe k l
  set Z : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) :=
    ((d : ReciprocityTheory.Aut.AL L) • Hi) * Matrix.of Y * ((d : ReciprocityTheory.Aut.AL L) • H) with hZ
  have hZm : ∀ i j, Z i j ∈ ReciprocityTheory.Aut.ALint L := by
    intro i j
    simp only [hZ, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _
      (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hHid i k) (hYm k l)) (hHd l j)
  have hmain : Hi * K * H - 1 = (N : ReciprocityTheory.Aut.AL L) • Z := by
    have e1 : Hi * K * H - 1 = Hi * (K - 1) * H := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hHiH]
    rw [e1, hKY, hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hentry : ∀ i j, (Hi * K * H) i j - (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j =
      (N : ReciprocityTheory.Aut.AL L) * Z i j := by
    intro i j
    rw [← Matrix.sub_apply, hmain, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j => ?_, fun i j => ⟨Z i j, hZm i j, by rw [hprod]; exact hentry i j⟩⟩
  show ((h⁻¹ * κ * h : Formalism.AUTREP.GAf L n).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j ∈ ReciprocityTheory.Aut.ALint L
  rw [hprod]
  have e : (Hi * K * H) i j = (1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j + (N : ReciprocityTheory.Aut.AL L) * Z i j := by
    rw [← hentry i j]; ring
  rw [e, Matrix.one_apply]
  refine Subring.add_mem _ ?_ (Subring.mul_mem _ (natCast_mem _ _) (hZm i j))
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

end Formalism.IndefR.principalLevelFrame
end
end
