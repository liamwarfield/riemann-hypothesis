module

public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.BoundaryLocalData
noncomputable section

namespace Formalism.MainNotions.BoundaryLocalData

open Formalism.BasicNotions NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

def vU (p : ℕ) {C : Type} [NormedField C] (u : Cˣ) : ℝ := -Real.logb p ‖(u : C)‖

theorem sqrtMinusD_sq (D : Formalism.BasicNotions.D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
  exact D.host.sqd_sq

theorem half_one_add_sqrt_neg_isIntegral (D : Formalism.BasicNotions.D7) :
    IsIntegral ℤ ((1 + D.host.sqrtMinusD) / 2 : D.host.E) := by
  obtain ⟨-, -, -, hd, -⟩ := D.host.hyp
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((4 * k + 2 : ℕ) : ℤ), ?_, ?_⟩
  · monicity!
  · have h := sqrtMinusD_sq D
    rw [hk] at h
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    push_cast at h
    simp only [eq_intCast, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat]
    have : ((1 + D.host.sqrtMinusD) / 2 : D.host.E) ^ 2 =
        (1 + 2 * D.host.sqrtMinusD + D.host.sqrtMinusD ^ 2) / 4 := by ring
    rw [this, h]
    ring

def w0 (D : Formalism.BasicNotions.D7) : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2, half_one_add_sqrt_neg_isIntegral D⟩

theorem conj_sqrtMinusD (D : Formalism.BasicNotions.D7) :
    D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  have h := D.host.gal_sqd D.host.conj
  have h2 : D.host.gal D.host.conj = D.R.cc := D.host.gal.apply_symm_apply _
  rw [h2] at h
  simpa [Host.sqrtMinusD, Formalism.HC.Frame.cc, c0] using h

theorem one_sub_halfSqrt_eq_conj (D : Formalism.BasicNotions.D7) :
    ((1 - w0 D : 𝓞 D.host.E) : D.host.E) = D.host.conj (w0 D : D.host.E) := by
  have hw : algebraMap (𝓞 D.host.E) D.host.E (w0 D) = (1 + D.host.sqrtMinusD) / 2 := rfl
  change algebraMap (𝓞 D.host.E) D.host.E (1 - w0 D) =
    D.host.conj (algebraMap (𝓞 D.host.E) D.host.E (w0 D))
  rw [map_sub, map_one, hw, map_div₀, map_add (f := _), map_one, conj_sqrtMinusD, map_ofNat]
  ring

structure LocB (D : Formalism.BasicNotions.D7) {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) where

  chX : ∀ {Z : L.Mdl}, L.Pt Z → Type
  [xAdd : ∀ {Z : L.Mdl} (y : L.Pt Z), AddCommGroup (chX y)]
  [xMod : ∀ {Z : L.Mdl} (y : L.Pt Z), Module (𝓞 D.host.E) (chX y)]

  phi : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y ≃+ chX y

  phi_conj : ∀ {Z : L.Mdl} (y : L.Pt Z) (c c' : 𝓞 D.host.E),
    (c' : D.host.E) = D.host.conj (c : D.host.E) → ∀ a : L.Ylat y, phi y (c' • a) = c • phi y a

  tau : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → chX y → ((L.fld y).C)ˣ
  tau_add_left : ∀ {Z : L.Mdl} (y : L.Pt Z) a a' χ, tau y (a + a') χ = tau y a χ * tau y a' χ
  tau_add_right : ∀ {Z : L.Mdl} (y : L.Pt Z) a χ χ', tau y a (χ + χ') = tau y a χ * tau y a χ'
  tau_symm : ∀ {Z : L.Mdl} (y : L.Pt Z) a b, tau y a (phi y b) = tau y b (phi y a)
  tau_smul : ∀ {Z : L.Mdl} (y : L.Pt Z) (c : 𝓞 D.host.E) a χ, tau y (c • a) χ = tau y a (c • χ)

  be_tau : ∀ {Z : L.Mdl} (y : L.Pt Z) a b, L.be y a b = vU p (tau y a (phi y b))

  multiplicationLatticeFirst : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → L.Ylat y → chX y
  multiplicationLatticeSecond : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → L.Ylat y → chX y
  mulC : ∀ {Z : L.Mdl} (y : L.Pt Z), L.Ylat y → L.Ylat y → ((L.fld y).C)ˣ

  psiV_def : ∀ {Z : L.Mdl} (y : L.Pt Z) a, L.psiV y a = vU p (mulC y a (w0 D • a))

  StrictHenselianAcyclic : L.Unim → Type
  squareRootLineBundle : L.Unim → Type
  res2 : ∀ {La}, StrictHenselianAcyclic La → squareRootLineBundle La

  PoiQ : ∀ La, squareRootLineBundle La

  biext : ∀ {La}, StrictHenselianAcyclic La → Prop

  dg : ∀ {La}, StrictHenselianAcyclic La → L.LBG La
  dgq : ∀ {La}, squareRootLineBundle La → L.LBGq La
  dg_res : ∀ {La} (P : StrictHenselianAcyclic La), L.resQ (dg P) = dgq (res2 P)

  PPq_def : ∀ La, L.PPq La = dgq (PoiQ La)

  BPt : Type

  Rl : BPt → Type
  [iRr : ∀ z, CommRing (Rl z)]
  [iRd : ∀ z, IsDomain (Rl z)]
  [iRl : ∀ z, IsLocalRing (Rl z)]
  [iRn : ∀ z, IsNoetherianRing (Rl z)]
  [iRi : ∀ z, IsIntegrallyClosed (Rl z)]
  [iRc : ∀ z, IsAdicComplete (IsLocalRing.maximalIdeal (Rl z)) (Rl z)]

  Yb : BPt → Type
  [iYa : ∀ z, AddCommGroup (Yb z)]
  [iYm : ∀ z, Module (𝓞 D.host.E) (Yb z)]
  Xb : BPt → Type
  [iXa : ∀ z, AddCommGroup (Xb z)]
  [iXm : ∀ z, Module (𝓞 D.host.E) (Xb z)]
  phib : ∀ z, Yb z ≃+ Xb z
  phib_conj : ∀ z (c c' : 𝓞 D.host.E), (c' : D.host.E) = D.host.conj (c : D.host.E) →
    ∀ a : Yb z, phib z (c' • a) = c • phib z a
  taub : ∀ z, Yb z → Xb z → (FractionRing (Rl z))ˣ
  taub_add_left : ∀ z a a' χ, taub z (a + a') χ = taub z a χ * taub z a' χ
  taub_add_right : ∀ z a χ χ', taub z a (χ + χ') = taub z a χ * taub z a χ'
  taub_symm : ∀ z a b, taub z a (phib z b) = taub z b (phib z a)
  taub_smul : ∀ z (c : 𝓞 D.host.E) a χ, taub z (c • a) χ = taub z a (c • χ)

  taub_pos : ∀ z a, ((taub z a (phib z a) : (FractionRing (Rl z))ˣ) : FractionRing (Rl z)) ∈
    (algebraMap (Rl z) (FractionRing (Rl z))).range

  Sg : BPt → Type
  [iSg : ∀ z, AddCommGroup (Sg z)]
  [iSk : ∀ z, Module (FractionRing (Rl z)) (Sg z)]
  [iSm : ∀ z, Module (Rl z) (Sg z)]
  [iSt : ∀ z, IsScalarTower (Rl z) (FractionRing (Rl z)) (Sg z)]

  Sreg : ∀ z, Submodule (Rl z) (Sg z)

  fc : ∀ z, Sg z →ₗ[FractionRing (Rl z)] (Xb z → FractionRing (Rl z))

  trU : ∀ z, Yb z → Xb z → (Rl z)ˣ

  oX : L.Sh L.Xm
  oX_inv : L.IsInv oX

  secOf : ∀ {F : L.Sh L.Xm}, L.GIso oX F → L.Sec F

  nrm_secOf : ∀ {F : L.Sh L.Xm} (φ : L.GIso oX F) y, L.nrm F (secOf φ) y = (p : ℝ) ^ (-(L.vrat φ y))

  keySh_inv : L.IsInv L.piPP → ∀ c, L.IsInv (L.keySh c)

  dimB : L.Pt L.Xm → ℕ
  dimB_add : ∀ y, dimB y + L.dP y = D.R.f * r

  FB : ∀ (y : L.Pt L.Xm) (nW n : ℕ), (Fin nW → chX y) → Type
  [fbAdd : ∀ y nW n χ, AddCommGroup (FB y nW n χ)]
  [fbMod : ∀ y nW n χ, Module (L.fld y).C (FB y nW n χ)]

  nB : ∀ {y nW n χ}, FB y nW n χ → ℝ

  sgc : ∀ y nW n χ, L.Sn y (L.latStd nW) n →ₗ[(L.fld y).C] FB y nW n χ

  trB : ∀ y nW n (a : Fin nW → L.Ylat y) χ,
    FB y nW n χ ≃ₗ[(L.fld y).C] FB y nW n (χ + n • fun i => phi y (a i))
  trB_norm : ∀ y nW n a χ σ, nB (trB y nW n a χ σ) = nB σ

  alp : ℕ → 𝓞 D.host.E
  alp_spec : ∀ n, ModuliIntegralCharts.NHyp D p n →
    (alp n : D.host.E) * D.host.conj (alp n : D.host.E) = (n : D.host.E) ∧
    ((∃ mm : ℕ, n = mm ^ 2 ∧ alp n = (mm : 𝓞 D.host.E)) ∨ (alp n : D.host.E) ∈ D.host.K)

  th1 : ∀ y nW, L.Sn y (L.latStd nW) 1
  pbAl : ∀ y nW n, L.Sn y (L.latStd nW) 1 →ₗ[(L.fld y).C] L.Sn y (L.latStd nW) n
  vth_def : ∀ y nW n, ModuliIntegralCharts.NHyp D p n → L.vth y (L.latStd nW) n = pbAl y nW n (th1 y nW)

  jX : ∀ y nW n DF χ, FB y nW n χ →ₗ[(L.fld y).C] L.Jet y (L.latStd nW) n DF

  intJet_free : ∀ y nW n DF, ∃ (N : ℕ) (b : Module.Basis (Fin N) (L.fld y).C (L.Jet y (L.latStd nW) n DF)),
    ∀ v, v ∈ L.intJet y (L.latStd nW) n DF ↔ ∀ i, ‖b.repr v i‖ ≤ 1

  jX_int : ∀ y nW n DF χ (σ : FB y nW n χ), nB σ ≤ 1 → jX y nW n DF χ σ ∈ L.intJet y (L.latStd nW) n DF

  jet_fourier : ∀ y nW n DF (s : L.Sn y (L.latStd nW) n) (t : (L.fld y).C), t ≠ 0 →
    ∃ F₀ : Finset (Fin nW → chX y), ∀ F : Finset (Fin nW → chX y), F₀ ⊆ F →
      ∃ v ∈ L.intJet y (L.latStd nW) n DF,
        L.jet y (L.latStd nW) n DF s - ∑ χ ∈ F, jX y nW n DF χ (sgc y nW n χ s) = t • v

attribute [instance] LocB.xAdd LocB.xMod LocB.iRr LocB.iRd LocB.iRl LocB.iRn LocB.iRi LocB.iYa LocB.iYm
  LocB.iXa LocB.iXm LocB.iSg LocB.iSk LocB.iSm LocB.iSt LocB.fbAdd LocB.fbMod

structure Prov (D : Formalism.BasicNotions.D7) (X : ModuliIntegralCharts.Prov D) where
  loc : ∀ w p, p.Prime → LocB D (X.loc w p)

namespace LocB

variable {D : Formalism.BasicNotions.D7} {r j p : ℕ} {L : ModuliIntegralCharts.Loc D r j p} (B : LocB D L)

variable {y : L.Pt L.Xm} {nW : ℕ}

variable (y nW)

end LocB

variable (D : Formalism.BasicNotions.D7) (X : ModuliIntegralCharts.Prov D)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

abbrev BaseObjectsAlongFamily : Type 1 := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ModuliIntegralCharts.Prov (Fm.D x i)

abbrev ProvF (XF : BaseObjectsAlongFamily Fm) : Type 1 := ∀ x hx (i : Fm.Ix x), Prov (Fm.D x i) (XF x hx i)

variable (XF : BaseObjectsAlongFamily Fm) (YF : ProvF Fm XF)

end Family

end Formalism.MainNotions.BoundaryLocalData
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
noncomputable section

namespace Formalism.MainNotions.placeRankTwoOne

open Formalism.BasicNotions NumberField IsDedekindDomain

def NN (D : D7) : ℝ := (D.R.N D.R.m : ℝ)

def degLine (D : D7) (r : (D.what₂.LL →+* ℂ) → ℝ) (ρ : D.what₂.places.Pl → ℝ) : ℝ :=
  (∑ᶠ w, ρ w * lw D.what₂.LL (D.plEq w)) - (∑ σ, Real.log (r σ)) / (Module.finrank ℚ D.what₂.LL : ℝ)

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E)

def idOf (D : D7) (τ : D.what₂.Tau)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.what₂.LL) D.what₂.LL :=
  Submodule.span (𝓞 D.what₂.LL) ((embTau D τ) '' {x | x ∈ I})

def ddEK (D : D7) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

def idMul {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (I : Submodule (𝓞 K) K) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) {y | ∃ a ∈ I, ∃ z ∈ M, y = a • z}


open Classical in
def detW (D : D7) (τ : D.what₂.Tau) : D.what₂.Tau → Fin D.R.r → ℤ :=
  fun τ' _ => if τ' = τ then -1 else 0

def IsNV {D : D7} (X : DivX D) (j : ℕ) (c : X.Comp j) (τ : D.what₂.Tau)
    (s : X.geo.Fn (X.Yv j c)) : Prop :=
  s ≠ 0 ∧ s ∈ X.geo.H0 (X.Yv j c) (X.Lw j c (detW D τ)) ∧
    s⁻¹ ∈ X.geo.H0 (X.Yv j c) (-(X.Lw j c (detW D τ)))

structure Loc (D : D7) (X : DivX D) where

  lieCK : HLat D.what₂.LL
  lieCK_good : lieCK.Good
  lieCK_rank : lieCK.rank = 1

  ell : D.what₂.Tau → HLat D.what₂.LL
  ell_good : ∀ τ, (ell τ).Good
  ell_rank : ∀ τ, (ell τ).rank = 1

  ellIso : ∀ τ, lieCK.V ≃ₗ[D.what₂.LL] (ell τ).V
  ellIso_lat : ∀ τ, (ell τ).L = (idMul (idOf D τ (D.host.AA0 * ddEK D)) lieCK.L).map
      ((ellIso τ).toLinearMap.restrictScalars (𝓞 D.what₂.LL))
  ellIso_norm : ∀ τ v (z : lieCK.V),
    Formalism.HermitianLatticesTheory.normAt (ell τ).b (ell τ).X v (ellIso τ z) = Formalism.HermitianLatticesTheory.normAt lieCK.b lieCK.X v z

  ell_Om : ∀ τ, D.gx.logOmMean τ = (ell τ).mu

  eH : ∀ τ, Submodule (𝓞 D.what₂.LL) (ell τ).V

  eH_eq : ∀ τ, eH τ = (idMul (idOf D τ D.host.AA0) lieCK.L).map
      ((ellIso τ).toLinearMap.restrictScalars (𝓞 D.what₂.LL))

  Comp_ne : ∀ j, 1 ≤ j → j ≤ D.R.m → Nonempty (X.Comp j)

  PtF : ∀ j, X.Comp j → D.what₂.places.Pl → Type
  PtF_ne : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c w, Nonempty (PtF j c w)
  pts_ne : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c σ, Nonempty (X.geo.pts (X.Yv j c) σ)

  vHT : ∀ j c, D.what₂.Tau → ∀ w, PtF j c w → ℚ

  vSub : ∀ j c, D.what₂.Tau → ∀ w, PtF j c w → ℚ

  vLie : ∀ j c, D.what₂.Tau → ∀ w, PtF j c w → ℚ

  metH : ∀ j c τ σ, X.geo.Met (X.Yv j c) σ (X.Lw j c (detW D τ))

  vF : ∀ j c, D.what₂.Tau → ∀ w, X.geo.Fn (X.Yv j c) → PtF j c w → ℝ

  vF_smul : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c τ w (a : D.what₂.LL) (f : X.geo.Fn (X.Yv j c)) y, a ≠ 0 → IsNV X j c τ f →
    vF j c τ w (a • f) y = (vAdd (D.plEq w) a : ℝ) + vF j c τ w f y

  degHH_def : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ c τ (s : X.geo.Fn (X.Yv j c)), IsNV X j c τ s →
    ∀ (r : (D.what₂.LL →+* ℂ) → ℝ) (ρ : D.what₂.places.Pl → ℝ), (∀ σ, 0 < r σ) →
      (∀ σ y, X.geo.pn (X.Yv j c) σ _ (metH j c τ σ) (X.geo.cx (X.Yv j c) σ s) y = r σ ^ 2) →
      (∀ w y, vF j c τ w s y = ρ w) → (Function.support ρ).Finite →
      X.degHH j c τ = degLine D r ρ

  thSup : ∀ u i, (D.mem u).C.cls i → (D.mem u).C.cls (i + 1) → ℝ

variable (D : D7) (large₂ : SizeData₂ D) (X : DivX D) (Lc : Loc D X)

def LL0 : ℝ :=
  Real.log (large₂.sc.b * D.host.rdE) * Real.log (Real.log large₂.sc.x) + |large₂.logDerivativeAtOne| + Real.log large₂.sc.x

def dimY : ℕ := D.R.f * (D.R.r.choose 2)

abbrev LocF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i)

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : LocF Fm)

end Fam

end Formalism.MainNotions.placeRankTwoOne

end
end

section -- merged from Formalism.SharpRestriction.Divisibility.PrinLevClass
noncomputable section

namespace Formalism.MainNotions.DIV.Align

open Formalism.BasicNotions Formalism.MainNotions

structure PrinLev {D : D7} (V : DivX D) where

  κg : V.Lev

  κs : V.Lev
  κg_pr : V.levPr κg = {D.host.g 0, D.host.g 1}
  κs_pr : V.levPr κs = {D.host.g 0, D.host.g 1, 3, 5}

def LevB {D : D7} {V : DivX D} (P : PrinLev V) (κ : V.Lev) : Prop := κ = P.κg ∨ κ = P.κs

abbrev PrinLevF {eps : ℝ} (Fm : FamP eps) : Type :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), PrinLev (Fm.X x i)

end Formalism.MainNotions.DIV.Align

end
end

section -- merged from Formalism.SharpRestriction.Divisibility.JumpSets
noncomputable section

namespace Formalism.MainNotions.JumpSetsAlt

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.UG TensorProduct Finset NumberField IsDedekindDomain

abbrev AmbT (R : Type) [CommRing R] (ι : Type) (N : ℕ) : Type :=
  PiTensorProduct R (fun _ : ι => MvPolynomial (Fin N × Fin N) R)

abbrev Cg (R : Type) [CommRing R] (ι : Type) (N : ℕ) : Type := (ι → GL (Fin N) R) × Rˣ

abbrev GE (D : D7) : Type := D.nd.Om ≃ₐ[D.host.E] D.nd.Om

abbrev Ob (l : ℕ) [Fact l.Prime] : ValuationSubring (Om l) :=
  (Valued.v (R := Om l) (Γ₀ := NNReal)).valuationSubring

abbrev kb (l : ℕ) [Fact l.Prime] : Type := IsLocalRing.ResidueField (Ob l)

abbrev ResRep (D : D7) (l : ℕ) [Fact l.Prime] : Type := GE D → Polynomial (kb l)

structure Prov (D : D7) where

  O : ℕ → Type
  [instO : ∀ l, CommRing (O l)]
  [domO : ∀ l, IsDomain (O l)]
  [dvrO : ∀ l, IsDiscreteValuationRing (O l)]
  [czO : ∀ l, CharZero (O l)]
  [algZ : ∀ (l : ℕ) [Fact l.Prime], Algebra ℤ_[l] (O l)]
  [topO : ∀ l, TopologicalSpace (O l)]

  l_mem : ∀ l, l.Prime → ((l : ℕ) : O l) ∈ IsLocalRing.maximalIdeal (O l)

  fin_l : ∀ l, l.Prime → Finite (O l ⧸ Ideal.span {((l : ℕ) : O l)})

  Gf : Type
  [instGf : Group Gf]
  Gam : Subgroup Gf

  gamE : Gam →* GL (Fin D.R.nV) D.host.E
  gamE_inj : Function.Injective gamE

  Lev : ℕ → Type

  hyp : ∀ l, Lev l → Prop
  Kl : ∀ l, Lev l → Subgroup Gf

  fin_class : ∀ l (c : Lev l), Finite (ClassSet Gam (Kl l c))

  fin_stab : ∀ l (c : Lev l) (g : Gf), (stabAt Gam (Kl l c) g).Finite

  kapK : ∀ l (c : Lev l), Kl l c →* (D.what₂.Tau → GL (Fin D.R.nV) (O l))

  typ : ∀ l (c : Lev l), Kl l c →* (O l)ˣ

  cf : ∀ l (_lam : D.what₂.Tau → DomWeight D.R.nV),
    Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) (AmbT (O l) D.what₂.Tau D.R.nV)

  cf_def : ∀ l (lam : D.what₂.Tau → DomWeight D.R.nV) (γ : Cg (O l) D.what₂.Tau D.R.nV)
    (x : D.what₂.Tau → MvPolynomial (Fin D.R.nV × Fin D.R.nV) (O l)),
    cf l lam γ (PiTensorProduct.tprod (O l) x) =
      ((γ.2 : (O l)ˣ) : O l) •
        PiTensorProduct.tprod (O l) (fun τ => roundAct (O l) D.R.nV (lam τ) (γ.1 τ) (x τ))

  Hk : ∀ l, Lev l → Type
  [instHk : ∀ l c, CommRing (Hk l c)]
  [algHk : ∀ l c, Algebra (O l) (Hk l c)]
  [modHk : ∀ l c (A : Type) [AddCommGroup A] [Module (O l) A]
    (ρ : Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) A),
    Module (Hk l c) (AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c))))]
  [towHk : ∀ l c (A : Type) [AddCommGroup A] [Module (O l) A]
    (ρ : Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) A),
    IsScalarTower (O l) (Hk l c)
      (AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c))))]

  hk_transl : ∀ l (c : Lev l) (T : Hk l c), ∃ el : Gf →₀ O l,
    ∀ (A : Type) [AddCommGroup A] [Module (O l) A]
      (ρ : Representation (O l) (Cg (O l) D.what₂.Tau D.R.nV) A)
      (f : AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c)))) (g : Gf),
      ((T • f : AMFK (O l) Gam (Kl l c) (MonoidHom.comp ρ ((kapK l c).prod (typ l c)))) : Gf → A) g =
        el.sum fun x a => a • (f : Gf → A) (g * x)

  bw : ∀ (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l →
    LocBridge l D.host.E D.nd.Om (ReciprocityTheory.Gal.Dec (F := D.host.E) (D.nd.plOm.1 w)) (O l)

  iota : ∀ (l : ℕ) [Fact l.Prime], D.host.E →+* Om l

  ep : ℕ → Bool

  attached : ∀ (l : ℕ) [Fact l.Prime] (_h : ℕ) (c : Lev l), Ideal (Hk l c) → ResRep D l → Prop

attribute [instance] Prov.instO Prov.domO Prov.dvrO Prov.czO Prov.algZ Prov.topO Prov.instGf Prov.instHk Prov.algHk
  Prov.modHk Prov.towHk

variable {D : D7}

def excSet (D : D7) : Finset ℕ := D.host.small ∪ {D.host.q, D.host.d, D.host.pde, D.host.pde'}

def ramSet (D : D7) : Finset ℕ := D.host.small ∪ {D.host.q, D.host.d}

end Formalism.MainNotions.JumpSetsAlt

end
end
