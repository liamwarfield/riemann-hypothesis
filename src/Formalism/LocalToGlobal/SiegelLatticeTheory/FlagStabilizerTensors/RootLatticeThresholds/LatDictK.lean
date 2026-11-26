module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatDictK

section DictK

variable {D : D7} (X : HidaSetting D)

def vOf (x : Fin X.B.I.n → X.B.I.E) : (VS D).V := ∑ i, X.ιE (x i) • X.bas i

theorem crd_vOf (x : Fin X.B.I.n → X.B.I.E) : X.crd (vOf X x) = x := by
  funext i
  simp only [HidaSetting.crd, crdOf, vOf]
  rw [X.bas.repr_sum_self]
  simp

theorem fmatK_inv_mul (x : X.B.I.Gf) : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
  show X.B.I.fmat (x⁻¹ * x) = 1
  simp [AutInst.fmat]

theorem fmatK_mul (x y : X.B.I.Gf) : X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := rfl

theorem dict_K (a b : X.B.I.Gf) (S : Set (VS D).V)
    (ha : ∀ y, y ∈ S ↔ X.B.I.fmat a⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf)
    (hb : ∀ y, y ∈ S ↔ X.B.I.fmat b⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf) : a⁻¹ * b ∈ X.B.I.Kset := by
  have hL : PIW.AdelClassFin.abelian₂ X.B.I a = PIW.AdelClassFin.abelian₂ X.B.I b := by
    ext v
    show X.B.I.fmat a⁻¹ *ᵥ PIW.AdelClassFin.iv X.B.I v ∈ X.B.I.Lf ↔
      X.B.I.fmat b⁻¹ *ᵥ PIW.AdelClassFin.iv X.B.I v ∈ X.B.I.Lf
    have e : PIW.AdelClassFin.iv X.B.I v = incl X.B.I (X.crd (vOf X v)) := by rw [crd_vOf]; rfl
    rw [e]
    exact (ha _).symm.trans (hb _)
  obtain ⟨k, hk, hkeq⟩ := PIW.AdelClassFin.lattice_map_injective X.B.I a b hL
  rw [hkeq, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hk

end DictK

end LatDictK

open LatDictK

section DictKMain

variable {D : D7} (X : HidaSetting D)

theorem colLatK {u : D.what₂.Word} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) :
    Formalism.L2.SG.NormCut.ColLatK cs := by
  intro ρ σ h
  refine dict_K X _ _ {y | y ∈ cs.lamOf ρ} (fun y => cs.lat_eq ρ y) (fun y => ?_)
  show y ∈ cs.lamOf ρ ↔ _
  rw [h]
  exact cs.lat_eq σ y

end DictKMain

namespace LatDictK

section DictK2

variable {D : D7} (X : HidaSetting D)

theorem ratLink_incl {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x γ) (w : (VS D).V) :
    X.B.I.fmat x.2 *ᵥ incl X.B.I (X.crd w) = incl X.B.I (X.crd (γ w)) := by
  obtain ⟨M, -, -, hf, hc⟩ := h
  have h3 : incl X.B.I ((M : Matrix _ _ _) *ᵥ X.crd w) =
      (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I (X.crd w) := by
    funext i
    exact RingHom.map_mulVec (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (M : Matrix _ _ _) (X.crd w) i
  rw [hf, hc, h3]

theorem ratLink_incl_inv {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X x γ) (y : (VS D).V) :
    X.B.I.fmat x.2⁻¹ *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd (γ.symm y)) := by
  conv_lhs => rw [← γ.apply_symm_apply y, ← ratLink_incl X h]
  rw [mulVec_mulVec, fmatK_inv_mul, one_mulVec]

end DictK2

end LatDictK

section DictKMain2

variable {D : D7} (X : HidaSetting D)

theorem termK {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows') :
    Formalism.L2.SG.NormCut.TermK F0 F0' cs cs' := by
  intro t
  obtain ⟨hRL, -, hmap, -⟩ := t.rep.2
  have hRL' : RatLink X t.pt t.lin := hRL
  have hmap' : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := hmap
  have hb0 := cs.base_lam t.lam t.mem
  have hb1 := cs'.base_lam t.lam' t.mem'
  have key : ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
      (t.pt.2 * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) ∈ X.B.I.Kset := by
    refine dict_K X _ _ {y | y ∈ t.lam} (fun y => ?_) (fun y => ?_)
    · show y ∈ t.lam ↔ _
      conv_lhs => rw [← hb0]
      exact cs.lat_eq _ y
    · show y ∈ t.lam ↔ _
      have e1 : y ∈ t.lam ↔ t.lin.symm y ∈ t.lam' := by
        rw [← hmap']
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : t.lin.symm y = z := by rw [← hzy]; simp
          rw [this]; exact hz
        · intro h
          exact ⟨t.lin.symm y, h, by simp⟩
      have hlat : ∀ w, w ∈ t.lam' ↔ X.B.I.fmat ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ *ᵥ
          incl X.B.I (X.crd w) ∈ X.B.I.Lf := fun w => by
        have := cs'.lat_eq (cs'.base t.lam') w
        rw [hb1] at this
        exact this
      rw [e1, hlat, show (t.pt.2 * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u'))⁻¹ =
          ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * t.pt.2⁻¹ from _root_.mul_inv_rev _ _,
        fmatK_mul, ← mulVec_mulVec, ratLink_incl_inv X hRL']
  have e : kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt =
      ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)⁻¹ *
        (t.pt.2 * ((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')) := by
    simp only [kOf, mul_assoc]
  rw [e]
  exact key

end DictKMain2

namespace LatDictK

section DictK3

variable {D : D7} (X : HidaSetting D)

theorem nat_split (g : ℕ) : ∀ m : ℕ, 0 < m → ∃ c d : ℕ, m = c * d ∧ Nat.Coprime c g ∧ d ∣ g ^ m :=
  _root_.UpperTheory.Reformulated.B.ExistsCoprimeMulDvdPow.main g

theorem mem_of_loc {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (L : Submodule R M) (x : M)
    (h : ∀ Q : Ideal R, Q.IsMaximal → ∃ s, s ∉ Q ∧ s • x ∈ L) : x ∈ L := by
  let I : Ideal R := L.comap (LinearMap.toSpanSingleton R M x)
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    simpa [I] using h1
  · obtain ⟨Q, hQ, hIQ⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨s, hs, hsx⟩ := h Q hQ
    exact absurd (hIQ (show s ∈ I by simpa [I] using hsx)) hs

theorem crd_nsmul (n : ℕ) (v : (VS D).V) : X.crd (n • v) = n • X.crd v := by
  funext i
  simp [HidaSetting.crd, crdOf, map_nsmul]

theorem incl_nsmul (n : ℕ) (x : Fin X.B.I.n → X.B.I.E) :
    incl X.B.I (n • x) = (n : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I x := by
  funext i
  simp [incl, nsmul_eq_mul]

end DictK3

end LatDictK

section DictKMain3

variable {D : D7} (X : HidaSetting D)

theorem modGAt : Formalism.L2.SG.NormCut.ModGAt X := by
  intro g1 Λ hΛ v hv
  have hg : X.B.g = gS D := X.g_eq
  obtain ⟨m, hm0, hm⟩ := PIW.AdelClassFin.lattice_denominator X.B.I (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v))
  have hmv : m • v ∈ Λ := by
    rw [hΛ, crd_nsmul, incl_nsmul, mulVec_smul]
    exact hm
  obtain ⟨c, d, hmcd, hcop, hdg⟩ := nat_split X.B.g m hm0
  have hcv : c • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := by
    apply mem_of_loc
    intro Q hQ
    by_cases hgQ : ((gS D : ℕ) : 𝓞 D.host.E) ∈ Q
    · have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField _)
      obtain ⟨s, hs, hsv⟩ := hv ⟨Q, hQ.isPrime, hQ0⟩ hgQ
      refine ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact Submodule.smul_of_tower_mem _ c hsv
    · refine ⟨((gS D * d : ℕ) : 𝓞 D.host.E), fun hQd => ?_, ?_⟩
      · rw [Nat.cast_mul] at hQd
        rcases hQ.isPrime.mem_or_mem hQd with h1 | h1
        · exact hgQ h1
        · obtain ⟨k, hk⟩ := hdg
          have h2 : ((X.B.g ^ m : ℕ) : 𝓞 D.host.E) ∈ Q := by
            rw [hk, Nat.cast_mul]; exact Q.mul_mem_right _ h1
          rw [Nat.cast_pow, hg] at h2
          exact hgQ (hQ.isPrime.mem_of_pow_mem _ h2)
      · have e : ((gS D * d : ℕ) : 𝓞 D.host.E) • (c • v) = ((gS D : ℕ) : 𝓞 D.host.E) • (m • v) := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, smul_smul, smul_smul, hmcd]
          ring_nf
        rw [e]
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hmv
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hcv
  obtain ⟨w, hw, hwv⟩ := hcv
  refine ⟨c, hcop, ?_⟩
  have e2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd v)) =
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd w)) := by
    rw [← mulVec_smul, ← mulVec_smul, ← incl_nsmul, ← incl_nsmul, ← crd_nsmul, ← crd_nsmul, ← hwv,
      Nat.cast_smul_eq_nsmul, hg]
  rw [e2]
  exact Submodule.subset_span ⟨_, (hΛ w).1 hw, rfl⟩

end DictKMain3

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierParts
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def instCM (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

attribute [local instance] instCM

structure Parts {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Type 1 where
  Wp : InfinitePlace D.host.E → Type
  Wq : InfinitePlace D.host.E → Type
  [pN : ∀ x, NormedAddCommGroup (Wp x)]
  [pI : ∀ x, InnerProductSpace ℂ (Wp x)]
  [qN : ∀ x, NormedAddCommGroup (Wq x)]
  [qI : ∀ x, InnerProductSpace ℂ (Wq x)]
  [pF : ∀ x, FiniteDimensional ℂ (Wp x)]
  [qF : ∀ x, FiniteDimensional ℂ (Wq x)]
  S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq
  T : ∀ j : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl j)) (Wq (S.pl j))
  f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))
  χ : ℝ → ℝ
  ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ
  m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r
  top : ∀ j : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) → List Formalism.FourierDecayAlt.C.Letter →
    Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ
  A₀ : ℝ
  τ : Fin S.f ≃ InfinitePlace X.B.I.F
  Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ
  Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ
  eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v
  eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v
  L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r
  j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
    Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT
  lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ
  c : Formalism.FourierDecayAlt.LE.Cut
  Cm : Fin S.f → ℝ
  σ : Fin S.f → ℝ
  Lw : ℕ → Fin S.f → ℝ
  Ll : ℕ → ℕ → Fin S.f → ℝ
  Ll' : ℕ → ℕ → Fin S.f → ℝ

attribute [instance] Parts.pN Parts.pI Parts.qN Parts.qI Parts.pF Parts.qF

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def Parts.Pins (P : Parts X u u') (CA : ℝ) (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ)
    (l : ℕ) : Prop :=
  P.S.CA = CA ∧ P.S.G = G0 ∧ P.S.de = de ∧ P.S.de' = de' ∧ P.S.l = l ∧ Formalism.L2.SG.DataInst.Compat P.S u u'

def Parts.Built (P : Parts X u u') : Prop := Formalism.FourierDecayAlt.D.IsBuilt P.S P.T P.f P.χ P.ν' P.m₀ P.top P.A₀

def Parts.FromX (P : Parts X u u') : Prop := BuiltFromX X P.S u u' P.T P.f P.τ P.Q P.Qi P.eP P.eQ

def Parts.Base (P : Parts X u u') (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : Prop :=
  BaseFromX X P.S u u' i0 i0' P.τ P.Q P.Qi P.ν' P.m₀

end Formalism.L2.SG.Pf.Carrier
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbPf
set_option linter.unusedVariables false

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.L2.SG.AmpOrbPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem lowest_K_type_unit {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (hA : GoodS D lam A) :
    PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) := by
  obtain ⟨-, -, -, -, -, hne, ⟨P, hP, hmem⟩, -⟩ := hA
  refine ⟨P, hP, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
  · exact Submodule.smul_mem _ _ hmem

theorem c_ne_zero (D : D7) :
    (((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
  have hrd : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  exact_mod_cast (div_pos (by linarith) (mul_pos hg0 hg1)).ne'

theorem kapN_ne_zero {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (hW : GoodW D τ w w' θ W) : kapN D θ ≠ 0 := by
  intro h0
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, hq, -⟩ := hW
  have hN0 : W.μN = 0 := by rw [hN, h0]; simp [haarLie]
  have hq1 := hq (fun _ => 1) measurable_const
  simp [muS, hN0] at hq1
  exact hG.2.1 hq1

theorem muN_haar {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') :
    IsHaarOn (Nset D.R.k D.R.rS) (toBessel D τ w w' θ W lam A hW hA hT hT').μN :=
  Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero hW) ENNReal.ofReal_ne_top

theorem side_pair {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) :
    Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam h A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) W.z
              (toBessel D τ w w' θ W lam A hW hA hT hT').c (toBessel D τ w w' θ W lam A hW hA hT hT').u W.π W.μW
              (toBessel D τ w w' θ W lam A hW hA hT hT').μN W.μG W.νS ∧
      Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam h A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) W.z'
        (toBessel D τ w w' θ W lam A hW hA hT hT').c (toBessel D τ w w' θ W lam A hW hA hT hT').u' W.π' W.μW'
        (toBessel D τ w w' θ W lam A hW hA hT hT').μN W.μG W.νS' := by
  set L := toBessel D τ w w' θ W lam A hW hA hT hT' with hL
  have hN := muN_haar hW hA hT hT'
  have hc : L.c ≠ 0 := c_ne_zero D
  have hw0 := lowest_K_type_unit hA
  have hW2 := hW
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hWN, hq0, hq0'⟩ := hW2
  have hμN : W.μN = L.μN := hWN
  have hq : PI.BesselPeriodGGP.IsQuotMeas W.μG (Formalism.FourierDecayAlt.ThreeDimData.muSof W.μW L.μN) W.νS := by
    rw [← hμN]; exact hq0
  have hq' : PI.BesselPeriodGGP.IsQuotMeas W.μG (Formalism.FourierDecayAlt.ThreeDimData.muSof W.μW' L.μN) W.νS' := by
    rw [← hμN]; exact hq0'
  exact ⟨⟨hA.1, hA.2.1, hg, hok, hw0, L.hz.1, L.hz.2, hc, L.hπ, L.hμW.1, hN, hG, hq⟩,
    ⟨hA.1, hA.2.1, hg, hok, hw0, L.hz'.1, L.hz'.2, hc, L.hπ', L.hμW'.1, hN, hG, hq'⟩⟩

theorem ls_pair (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hAt : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOne)
    {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W} (hW : GoodW D τ w w' θ W) (hA : GoodS D lam A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) :
    ∃ (l : A.H → W.Wp) (l' : A.H → W.Wq),
      PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
        (psi D.R.k D.R.rS W.z (toBessel D τ w w' θ W lam A hW hA hT hT').c) A.σ W.π l ∧
      PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
        (psi D.R.k D.R.rS W.z' (toBessel D τ w w' θ W lam A hW hA hT hT').c) A.σ W.π' l' ∧
      Formalism.MainNotions.S.Pv.AmpDD.OnePlaceKF (toBessel D τ w w' θ W lam A hW hA hT hT') h W.μG
        (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) l l' := by
  set L := toBessel D τ w w' θ W lam A hW hA hT hT' with hL
  obtain ⟨h1, h2⟩ := side_pair hW hA hT hT' hg hok
  obtain ⟨l, hl, hla, -⟩ := hAt hI _ _ _ _ h _ A.σ _ W.Wp _ _ _ _ _ _ _ _ h1
  obtain ⟨l', hl', hla', -⟩ := hAt hI _ _ _ _ h _ A.σ _ W.Wq _ _ _ _ _ _ _ _ h2
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hw0 := lowest_K_type_unit hA
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0),
      x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  refine ⟨l, l', hl, hl', ⟨⟨hg, hok, c_ne_zero D, hw0, hG, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro x hx v hv
    exact (hla x (hDDs x hx) v (Or.inl hv)).2
  · intro x hx v hv
    exact (hla' x (hDDs x hx) v (Or.inl hv)).2
  · intro x hx v hv
    exact (hla x (hDDs x hx) v (Or.inr hv)).2
  · intro x hx v hv
    exact (hla' x (hDDs x hx) v (Or.inr hv)).2

theorem orbit_mul {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {B l : H → V} (c0 : ℂ)
    (hB : ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = c0 • l v)
    (hlin : ∀ (a : ℂ), ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, l (a • v) = a • l v)
    {w0 : H} (hw0 : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (t : ℂ)
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    B (σ g (t • w0)) = (c0 * t) • l (σ g w0) := by
  have hs : σ g w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ :=
    Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hσ hw0 hg
  rw [map_smul, hB _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul t hs), hlin t _ hs, smul_smul]

theorem ampJ_mul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (νR : Measure (Mt k r)) (cN : ℝ)
    (Φ L1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp)
    (Φ' L1' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wq) (a a' : ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : γ ∈ UH (Hpk k r))
    (hΦ : ∀ g ∈ UH (Hpk k r), Φ g = a • L1 g) (hΦ' : ∀ g ∈ UH (Hpk k r), Φ' g = a' • L1' g)
    (hae : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r)) :
    ampJ νR cN Φ Φ' γ = (((cN : ℂ)⁻¹) * a * (starRingEnd ℂ) a') • ampJ νR 1 L1 L1' γ := by
  unfold ampJ
  have hcongr : (fun x : Mt k r => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) =ᵐ[νR]
      (fun x => (a * (starRingEnd ℂ) a') • (innerSL ℂ (L1' (Matrix.of x))).smulRight (L1 (γ * Matrix.of x))) := by
    filter_upwards [hae] with x hx
    have hγx : γ * Matrix.of x ∈ UH (Hpk k r) := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hγ hx
    rw [hΦ _ hγx, hΦ' _ hx]
    ext η
    simp [smul_smul, mul_comm]
    congr 1; ring
  rw [integral_congr_ae hcongr, integral_smul, smul_smul]
  simp only [Complex.ofReal_one, inv_one, one_smul]
  congr 1; ring

theorem psiGen_const {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    PI.BesselMapUniq.psiGen k r z (fun _ => c) = psi k r z c := by
  funext g
  unfold PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA psi ell
  rw [Finset.mul_sum]

theorem orbInt_smul {k r : ℕ} (L : LocBessel k r) (a : ℂ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) :
    OrbInt L (fun g => a • F g) γ ν = a • OrbInt L F γ ν := by
  unfold OrbInt
  rw [← integral_smul]
  congr 1
  funext p
  unfold besselIntg
  rw [smul_comm]
  congr 1
  ext η
  simp

theorem kfin_coef {k r : ℕ} (L : LocBessel k r) (a : ℂ) (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v) (hv' : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v') :
    IsKFinCoefH L.σ (fun g => a • Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ' g) := by
  refine ⟨a • (innerSL ℂ v).smulRight ξ, (innerSL ℂ ξ').smulRight v', ?_, ?_, ?_⟩
  · intro η
    obtain ⟨S, hS, hvS, hSinv⟩ := hv'
    exact ⟨S, hS, S.smul_mem _ hvS, hSinv⟩
  · intro x
    have hadj : ContinuousLinearMap.adjoint (a • (innerSL ℂ v).smulRight ξ) x =
        ((starRingEnd ℂ) a * ⟪ξ, x⟫_ℂ) • v := by
      apply ext_inner_right ℂ
      intro y
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp [inner_smul_left, inner_smul_right]
      ring
    rw [hadj]
    obtain ⟨S, hS, hvS, hSinv⟩ := hv
    exact ⟨S, hS, S.smul_mem _ hvS, hSinv⟩
  · intro g
    ext η
    simp [Formalism.MainNotions.S.Pv.AmpDD.coefF, smul_smul]

theorem ae_UH_conj {k r : ℕ} {μG μR νR : Measure (Mt k r)}
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    (hG : IsHaarOn (UH (Hpk k r)) μG) (hR : IsHaarOn (RStab k r γ) μR)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR) :
    ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
  have hc : Continuous (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j) := by
    have h1 : Continuous (fun x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => γ⁻¹ * x * γ) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h1
  have hf : Measurable (fun x : Mt k r => fun i j => (γ⁻¹ * Matrix.of x * γ) i j) := hc.measurable
  have hUm : MeasurableSet {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} :=
    Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet
  refine Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 ?_ ?_ hq
  · intro h0
    exact hR.2.1 ((Measure.map_eq_zero_iff hf.aemeasurable).1 h0)
  · rw [Measure.map_apply hf hUm]
    refine measure_mono_null (fun x hx => ?_) hR.2.2.1
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    intro hxR
    exact hx hxR.2.1

end Formalism.L2.SG.AmpOrbPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierPropGram
noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Carrier

theorem propGram_of_vtTensor {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, Formalism.FourierDecayAlt.D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hB : Formalism.FourierDecayAlt.D.IsBuilt S T f χ ν' m₀ top A₀)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : Formalism.FourierDecayAlt.TB.Pt E → H)
    (hVt : Formalism.FourierDecayAlt.JCT.VtTensor S T f ν' m₀ Vt) : Formalism.FourierDecayAlt.C.PropGram S Vt := by
  exact Formalism.FourierDecayAlt.Final.jc_propGramOfPlaces E Wp Wq S
    _ (fun v => Formalism.FourierDecayAlt.JC.vecPlace S T f ν' m₀ v) H Vt hVt
    (Formalism.FourierDecayAlt.Final.jc_gramPlaceBuilt Formalism.FourierDecayAlt.Final.d_ptPermSpec Formalism.FourierDecayAlt.Final.d_ptGSpec
      Formalism.FourierDecayAlt.Final.d_ptRelevant Formalism.FourierDecayAlt.Final.d_muRHaar Formalism.FourierDecayAlt.Final.jc_orbJCutScalar
      E Wp Wq S T f χ ν' m₀ top A₀ hg1 hg2 hB)

end Formalism.L2.SG.Pf.Carrier
end
end
