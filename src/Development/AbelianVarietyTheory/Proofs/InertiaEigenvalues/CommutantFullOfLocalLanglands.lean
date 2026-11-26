module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutationFullnessOfReads
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CommFullAll

section Act
variable {D : D7} (S : RatDat D.ntw)

def hLr (j : ℕ) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) :
    Module.End S.Ks (FmK S j) :=
  ((hL k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx

theorem hkFR_act (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) (hst : RhoStab S j) (hχ : ChiInLL0 S j)
    (hc : ∀ g x, hL k P ((S.A j).ρ g x) = (S.A j).ρ g (hL k P x)) (g : G0g D.nd) (z : Fm S i j b) :
    hkFR S i j b hL hs k P (actG S i j b hst hχ g z) = actG S i j b hst hχ g (hkFR S i j b hL hs k P z) := by
  have hcomm : hLr S j hL hs k P * rhoKG S j hst (S.eG.symm g) = rhoKG S j hst (S.eG.symm g) * hLr S j hL hs k P := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hc (S.eG.symm g) (show ↥(S.A j).WK from x).1
  have h2 := LinearMap.congr_fun (congrArg (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)) hcomm) z
  rw [map_mul, map_mul] at h2
  change Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) ((readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g)) z) =
    (readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g))
        (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) z)
  rw [map_smul]
  congr 1
end Act

section Real
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Cx _root_.Formalism.L2.Pj
variable {D : D7} (X : RealSide D) {S : RatDat D.ntw} (YS : NExpRealS X.R X.cG S) (H : NExpRealH X.R X.cG S YS)

end Real

section Iso

variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
  {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL Ks' WL' W' G'}

theorem iso_smul (Y : NX.FormsIso A A') (c : Ks) (w : WL) : Y.e (c • w) = Y.eK c • Y.e w := by
  rw [← algebraMap_smul LL c w, map_smul, ← Y.eK_LL, algebraMap_smul]

theorem iso_symm_smul (Y : NX.FormsIso A A') (c : Ks') (y : WL') : Y.e.symm (c • y) = Y.eK.symm c • Y.e.symm y := by
  apply Y.e.injective
  rw [iso_smul]
  simp

theorem iso_span (Y : NX.FormsIso A A') (h : Submodule.span Ks' (A'.MK : Set WL') = A'.WK) :
    Submodule.span Ks (A.MK : Set WL) = A.WK := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => by obtain ⟨h, -⟩ := hx; exact h
  · intro x hx
    have h1 : Y.e x ∈ Submodule.span Ks' (A'.MK : Set WL') := h ▸ (Y.wk x).1 hx
    have h2 : ∀ y ∈ Submodule.span Ks' (A'.MK : Set WL'),
        Y.e.symm y ∈ Submodule.span Ks (A.MK : Set WL) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ((Y.mkK _).2 (by simpa using hy))
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [iso_symm_smul]; exact Submodule.smul_mem _ _ ha
    simpa using h2 _ h1

end Iso

section Base
variable {D : D7} (S : RatDat D.ntw) (i : D.ntw.Tw) (j : ℕ) (b : Bool)

def mkF (y : S.WL j) (h : y ∈ (S.A j).WK) : FmK S j := ⟨y, h⟩

def rdF (c : S.Ks) : FractionRing (D.ntw.O i) := ιK S i b c

def rdK (a : KB S i b) : FractionRing (D.ntw.O i) := a

def oneT (x : FmK S j) : Fm S i j b := ((1 : KB S i b) ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j)

theorem oneT_zero : oneT S i j b 0 = 0 := TensorProduct.tmul_zero _ _

theorem oneT_add (x y : FmK S j) : oneT S i j b (x + y) = oneT S i j b x + oneT S i j b y :=
  TensorProduct.tmul_add _ _ _

theorem oneT_smul (c : S.Ks) (x : FmK S j) :
    oneT S i j b (c • x) = (rdF S i b c) • oneT S i j b x := by
  change (1 : KB S i b) ⊗ₜ[S.Ks] (c • x) = (ιK S i b c : KB S i b) • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  congr 1

theorem Bsup_span (hS : Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)) = (S.A j).WK) :
    Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i j b : Set (Fm S i j b)) = ⊤ := by
  let B := Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i j b : Set (Fm S i j b))
  have aux : ∀ y ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)), ∃ h : y ∈ (S.A j).WK,
      oneT S i j b (mkF S j y h) ∈ B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, h'⟩ := id hy
      exact ⟨h, Submodule.subset_span (Submodule.subset_span ⟨mkF S j y h, hy, rfl⟩)⟩
    | zero =>
      refine ⟨(S.A j).WK.zero_mem, ?_⟩
      have : oneT S i j b (mkF S j 0 (S.A j).WK.zero_mem) = 0 := oneT_zero S i j b
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      refine ⟨(S.A j).WK.add_mem h1 h3, ?_⟩
      have : oneT S i j b (mkF S j (x + y) ((S.A j).WK.add_mem h1 h3)) =
          oneT S i j b (mkF S j x h1) + oneT S i j b (mkF S j y h3) :=
        oneT_add S i j b (mkF S j x h1) (mkF S j y h3)
      rw [this]
      exact Submodule.add_mem _ h2 h4
    | smul c x _ hx =>
      obtain ⟨h1, h2⟩ := hx
      refine ⟨(S.A j).WK.smul_mem c h1, ?_⟩
      have : oneT S i j b (mkF S j (c • x) ((S.A j).WK.smul_mem c h1)) =
          (rdF S i b c) • oneT S i j b (mkF S j x h1) :=
        oneT_smul S i j b c (mkF S j x h1)
      rw [this]
      exact Submodule.smul_mem _ _ h2
  have hall : ∀ (a : KB S i b) (x : FmK S j),
      ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) ∈ B := by
    intro a x
    have hx : (show ↥(S.A j).WK from x).1 ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)) := by
      rw [hS]; exact (show ↥(S.A j).WK from x).2
    obtain ⟨h, h'⟩ := aux _ hx
    have e : ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) =
        (rdK S i b a) • oneT S i j b x := by
      change a ⊗ₜ[S.Ks] x = a • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ h'
  refine eq_top_iff.2 fun t _ => ?_
  change t ∈ B
  induction (show KB S i b ⊗[S.Ks] FmK S j from t) using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a x => exact hall a x
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end Base

end GlobalTheory.CommFullAll
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CommFullLayer

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Cx _root_.Formalism.L2.Pj
  GlobalTheory.TwInputs GlobalTheory.CommFullAll
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Raw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) {S : RatDat D.ntw}
  (YS : NExpRealS Rl cG S) (H : NExpRealH Rl cG S YS)

theorem hL_comm_raw (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif)
    (hX : NExpHeckeRowX Rl cG S YS H fun _ => LinearMap.id) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host)
    (hsp : IsSplitPl D.host P) (hso : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) (hi : ∃ i, P ∉ D.ntw.S0 i)
    (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hkr : k ≤ D.R.r)
    (g : S.G) (x : S.WL ((i' : ℕ) + 1)) :
    H.hL ((i' : ℕ) + 1) k P ((S.A ((i' : ℕ) + 1)).ρ g x) = (S.A ((i' : ℕ) + 1)).ρ g (H.hL ((i' : ℕ) + 1) k P x) := by
  obtain ⟨α, Rc, ha, hRc⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hR.lev hR.fam i' hso hkr
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData Rl.toRealDat i' P k α Rc := ⟨hso, hg, hkr, ha, hRc⟩
  let hL' : (Fin (Rl.nW i') → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (Rl.nW i') → D.what₂.LL) :=
    (YS.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (YS.fi i').e.symm.toLinearMap
  have hH : Formalism.L2.Pj.HeckeJ.IsHkJ (sg0 D A3.A) ((Rl.FW i').j (sg0 D A3.A)) (Rl.HW i' (sg0 D A3.A)).e
      (heckeOn (Rl.MW i' (sg0 D A3.A)) Rc)
      ((((Rl.C.mu0 i').val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) hL' := by
    intro y
    have h := hX.tie i' k P hsp hso hi h2 hkr α Rc ha hRc ((YS.fi i').e.symm y) rfl
    simp only [hL', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
    exact h
  have hc := GlobalTheory.HeckeSup.comm_rho_cl (hR.lev.βW i') hR.fam.Sb hR.models.HW hR.models.gW (sg0 D A3.A) hd
    (GlobalTheory.ExportPin.Model.j_injective Rl hU i' _) (hU i' (sg0 D A3.A)).2.2 hH ((YS.fi i').eG g)
  apply (YS.fi i').e.injective
  have h := LinearMap.congr_fun hc ((YS.fi i').e x)
  simp only [hL', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  rw [(YS.fi i').rho, ← h, ← (YS.fi i').rho, LinearEquiv.symm_apply_apply]

theorem commAll_fullAll_raw (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif) (hI : Rl.toRealDat.LIntegral)
    (hX : NExpHeckeRowX Rl cG S YS H fun _ => LinearMap.id)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) : CommAll D ∧ FullAll D := by
  have hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j := fun j h1 h2 =>
    ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine ⟨?_, ?_⟩
  · intro i j hj b k P hk g x
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i', rfl⟩ := hidx j h1 h2
    obtain ⟨-, hkr, hsp, hS0⟩ := hk
    obtain ⟨-, -, -, -, hso, -, h2P, -⟩ :=
      GlobalTheory.ConjPlaceOff.exists_conj_off D (D.ntw.S0 i) Rl.Sb P (hS0c i) (hS02 i) (hS0b i) hsp hS0
    have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      rw [Nat.cast_mul] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hS0 (D.ntw.placesOver_subset_exceptional i 0 h)
      · exact hS0 (D.ntw.placesOver_subset_exceptional i 1 h)
    have hc := hL_comm_raw Rl F cG YS H hR hU hX i' k P hsp hso ⟨i, hS0⟩ h2P hg hkr
    refine (YS.eF i _ b h1 h2).injective ?_
    rw [YS.act, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, YS.act, map_smul,
      hkFR_act S i _ b (H.hL _) (H.hs _ h1 h2) k P (YS.rho _ h1 h2) (YS.chi _ h1 h2) hc]
  · intro i j hj b
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i', rfl⟩ := hidx j h1 h2
    have hF := iso_span (YS.fi i') (hI i').2.1.2
    have hB := Bsup_span S i ((i' : ℕ) + 1) b hF
    obtain ⟨c, hc0, -, hc2⟩ := YS.bsup i ((i' : ℕ) + 1) b h1 h2
    let e := YS.eF i ((i' : ℕ) + 1) b h1 h2
    have hc0' : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c ≠ 0 := by
      intro h0
      apply hc0
      apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
      rw [h0, map_zero]
    have hle : Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i ((i' : ℕ) + 1) b : Set (Fm S i ((i' : ℕ) + 1) b)) ≤
        (Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i ((i' : ℕ) + 1) b : Set (D.nexp.Fm i ((i' : ℕ) + 1) b))).comap e.symm.toLinearMap := by
      refine Submodule.span_le.2 fun z hz => ?_
      have hm : c • e.symm z ∈ D.nexp.Bsup i ((i' : ℕ) + 1) b := hc2 _ (by simpa [e] using hz)
      have hm' : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c • e.symm z ∈
          Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i ((i' : ℕ) + 1) b : Set (D.nexp.Fm i ((i' : ℕ) + 1) b)) := by
        rw [algebraMap_smul]
        exact Submodule.subset_span hm
      have := Submodule.smul_mem _ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c)⁻¹ hm'
      rw [inv_smul_smul₀ hc0'] at this
      exact this
    refine eq_top_iff.2 fun t _ => ?_
    have ht : e t ∈ Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i ((i' : ℕ) + 1) b : Set (Fm S i ((i' : ℕ) + 1) b)) := by
      rw [hB]; exact Submodule.mem_top
    have := hle ht
    simpa using this

end Raw

end GlobalTheory.CommFullLayer
