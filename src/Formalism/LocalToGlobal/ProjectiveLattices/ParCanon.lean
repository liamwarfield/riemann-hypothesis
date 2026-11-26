module

public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions MeasureTheory
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Par.Canon (Q : Par D) : Prop :=
  Q.H = hostOfRecord D ∧ ∀ j (hj : InR D j), ∃ hP hd, HEq (Q.Dw j) (datumOfRecord D j hj hP hd)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions

variable {D : D7}

variable (T : Top D)

namespace Top

abbrev PtA (j : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) : Type :=
  PtV (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) (T.G.PY j (WeightAlgebra.resCh la)) (T.G.lies j la) la

def th (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) := thGen (T.Q.Xo j) T.Q.c (T.nab j) (wtA w) w.n

def sh (j : ℕ) (w : WeightFamilies.Wt D j) : Set (T.R j) :=
  shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV (wtA w) w.n (T.dδ j w.n)

end Top

variable {T} (h : LawsP T)

def recPJ (j : ℕ) (hj : InR D j) : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j :=
  mkX T.Q.eO T.C h.toLawsCore.fd T.Vs (fun _ la => isVal_valSet la) T.Ns h.toLawsCore.Nl h.toLawsCore.hNs
    h.toLawsCore.hNl h.toLawsCore.hle T.Cu T.Xc T.Xc_lat T.FJt h.toLawsCore.sg
    T.G.P j hj (h.toLawsCore.mul j hj) (T.G.dat j) (fun hm => (h.datum_condition j hj.1 hm).1) (fun hm => (h.datum_condition j hj.1 hm).2)
    (T.PtA j) (fun _ y => imgV y) (fun _ y => vAtV y) (fun _ y => isVal_vAt y)
    (fun _ f _ => nonneg_iff_of_liesTotal (T.G.liesTotal h.points_condition h.bc66 hj) f) (T.th j) (T.sh j)

def recX : WeightAlgebra.Prov D (recB h.toLawsCore) T.G.P := fun j h1 h2 => recPJ h j ⟨h1, h2⟩

theorem recPJ_vAt_inc (j : ℕ) (hj : InR D j) (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la)
    (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w) :
    (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y F.1 := by
  dsimp only [recPJ, mkX, vG, incG]
  refine le_antisymm (iInf_le_of_le (deg w) (le_of_eq ?_)) (le_iInf fun m => ?_)
  · change vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff (deg w)) = _
    first
      | simp [AddMonoidAlgebra.coeff_single]
      | simp [AddMonoidAlgebra.single_apply]
      | simp [Finsupp.single_apply]
      | exact (0 : Nat)
  · change _ ≤ vAtV y ((AddMonoidAlgebra.single (deg w) F.1).coeff m)
    by_cases hm : deg w = m
    · subst hm
      first
        | simp [AddMonoidAlgebra.coeff_single]
        | simp [AddMonoidAlgebra.single_apply]
        | simp [Finsupp.single_apply]
    · first
        | simp [AddMonoidAlgebra.coeff_single, hm]
        | simp [AddMonoidAlgebra.single_apply, hm]
        | simp [Finsupp.single_apply, hm]
      rw [(isVal_vAt y).zero]
      exact le_top

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Field

variable (c c' : Coeff l) (hle : c.F ≤ c'.F)

abbrev incF : c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def AlgOver (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] : Prop :=
  ∀ a : c.F, algebraMap c'.F S (incF c c' hle a) = algebraMap c.F S a

variable {c c'}

theorem embK_incF (τ : E →+* ℂ) (a : 𝓞 E) : incF c c' hle (embK c τ a) = embK c' τ a :=
  Subtype.ext rfl

theorem sOf_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) :
    sOf c' S = sOf c S := by
  unfold sOf
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  exact h ((IntermediateField.inclusion c.le).toRingHom x)

variable {Xo : Moduli Dw l}

theorem isEigAt_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (τ : E →+* ℂ) (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsEigAt (Xo := Xo) c' τ v ↔ IsEigAt (Xo := Xo) c τ v := by
  have key : ∀ a : 𝓞 E, algebraMap c'.F S (embK c' τ a) = algebraMap c.F S (embK c τ a) := by
    intro a
    rw [← embK_incF hle τ a]
    exact h (embK c τ a)
  unfold IsEigAt
  simp only [key]

def FrPt.res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c' S) : FrPt Xo c S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h)
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).1 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).2 he)
  s := y.s
  gen := y.gen

def FrPt.ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : FrPt Xo c' S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h).symm
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).2 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).1 he)
  s := y.s
  gen := y.gen

theorem FrPt.res_ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S)
    (y : FrPt Xo c S) : (y.ext hle h).res hle h = y := rfl

variable {r : ℕ}

def unfBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) : Unf Xo c' σ' r :=
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  { Comp := (U (σ'.comp (incF c c' hle))).Comp
    fin := (U (σ'.comp (incF c c' hle))).fin
    X := (U (σ'.comp (incF c c' hle))).X
    un := fun k x => FrPt.ext hle (S := CAt σ') (fun _ => rfl) ((U (σ'.comp (incF c c' hle))).un k x) }

def IsBC {m : ℕ} (f' : Rul Xo c') (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
    evR Xo c' f' y = ∑ i, algebraMap c'.F S (as i) * evR Xo c (fs i) (y.res hle h)

def CuspBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f' ∈ cusp Xo c' (unfBC hle U) a n,
    ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ cusp Xo c U a n) ∧ IsBC hle f' as fs

def ActBC {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') :
    Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : G) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) (f' : Rul Xo c'),
    f' ∈ sec Xo c' a n → (∀ i, fs i ∈ sec Xo c a n) →
    IsBC hle f' as fs → IsBC hle (act' g f') as (fun i => act g (fs i))

end Field

section Comparison₂

variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ} {r : ℕ}
  {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

def OneMapTieC (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ0' : c'.F →+* ℂ)
    {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c)
    (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
    (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)]
    (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F) (La : ∀ t, Cl' t → GenLat E n) (Nc : ∀ t, Cl' t → ℕ)
    (gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F) (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
    (thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop) (cc : (unfBC hle U σ0').Comp → ℂ)
    (ph : ℂ) : Prop :=
  LL ≤ c'.F ∧ CuspBC hle U ∧ ActBC hle act act' ∧
    OneMapRow Xo c' V (unfBC hle U σ0') dict mu xr a act' dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unfBC hle U) a n) cc ph

end Comparison₂

end Gen

section Dict

open scoped TensorProduct

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {n r : ℕ}

def MarkBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ}
    {lab : Fin g → D.host.E →+* ℂ} (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (h γ : GA D V) : Prop :=
  γ ∈ GQ V ∧
    ((U.X (dict h).1).Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ (dict h).1 (F.t (ik (dict h).1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w

def CXiVal {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {Tup : Type*} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop :=
  ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧ ∀ t : Tup, IsUnf (U₂ t) ∧ (∀ k, ModelW V hr ((U₂ t).X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif (dδ t).Xo₂ ((σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)).comp
          (IntermediateField.inclusion (dδ t).c₂.le).toRingHom)
        (fun j => relab (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) (e j).1))
      (ik : (U₂ t).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((U₂ t).X k).Λ)
      (th : ∀ k, ((U₂ t).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat (U₂ t) V hr (dict₂ t) ι e F ik φ th x₀ ∧
      ∀ h γ : GA D V, MarkBy (U₂ t) V hr (dict₂ t) ι F ik φ h γ →
        rdU (U₂ t) (dδ t).cδ (dict₂ t h).1 (dict₂ t h).2 =
          c0 * ((xi t (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

variable {c c' : Coeff l} (hle : c.F ≤ c'.F)

def actLev (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (g : G) : Rul Xo c →ₗ[c.F] Rul Xo c :=
  actL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) =>
    levActR (Xo := Xo) (c := c) lev g' y y') g

def ActLev (c : Coeff l) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) : Prop :=
  ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g' y y')

end Dict

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RecCond
namespace Formalism.L2.Pj

open Formalism.BasicNotions

def OKPsi (D : D7) : Prop := ∀ Q : Par D, Q.Pins → ∀ j, InR D j → KPsiIn (Dw := Q.Dw j) Q.c

end Formalism.L2.Pj
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

def ProdInLat (ka : WeightFamilies.Wt D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (n : ℕ) : Prop :=
  ∀ s : Fin n → Fin (N + 1), ∃ F : (recB hL).Cusp j ka, F ∈ (recB hL).Mlat j ka ∧ (F : Tc.R j) = ∏ k, wR (s k)

def SupPTGe (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (ka : WeightFamilies.Wt D j) : Prop :=
  ∀ (Z : Comp (Tc.Q.Xo j) Tc.Q.c) (F : (recB hL).Cusp j ka), F ∈ (recB hL).Mlat j ka →
    evC h Z (F : Tc.R j) ≠ 0 →
    ∃ F' ∈ (recB hL).Mlat j ka, F' ≠ 0 ∧ ∀ sg : Tc.Q.c.F →+* ℂ,
      (recB hL).supN j ka sg F' ≤
        ⨆ P : PT (Ω := Om Z) sg, nrmC fn (yP Z) (wtZ (wtA ka) ka.n) (valC h (wtA ka) ka.n (F : Tc.R j) Z) P

section Ev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evC_prod (h : GenFrEx Xo c) (hgt : GenFromTest Xo c h) (Z : Comp Xo c) {n : ℕ} (f : Fin n → Rul Xo c) :
    evC h Z (∏ k, f k) = ∏ k, evC h Z (f k) := by
  let φ : Rul Xo c →* Om Z :=
    { toFun := evC h Z
      map_one' := evalAt_one _ _ _ (hgt Z)
      map_mul' := fun a b => evalAt_mul _ _ a b _ }
  exact map_prod φ f Finset.univ

theorem evC_add (h : GenFrEx Xo c) (Z : Comp Xo c) (f g : Rul Xo c) :
    evC h Z (f + g) = evC h Z f + evC h Z g := evalAt_add _ _ f g _

theorem evC_zero (h : GenFrEx Xo c) (Z : Comp Xo c) : evC h Z (0 : Rul Xo c) = 0 := evalAt_zero _ _ _

theorem evC_smul (h : GenFrEx Xo c) (Z : Comp Xo c) (a : c.F) (f : Rul Xo c) :
    evC h Z (a • f) = algebraMap c.F (Om Z) a * evC h Z f := evalAt_smul _ _ a f _

theorem smul_single_AC (Z : Comp Xo c) (a : 𝓞 c.F) (G : WTZ E) (e : Om Z) :
    a • (AddMonoidAlgebra.single G e : AC Z) = AddMonoidAlgebra.single G (algebraMap c.F (Om Z) (a : c.F) * e) := by
  first
  | rw [AddMonoidAlgebra.smul_single]
  | erw [AddMonoidAlgebra.smul_single]
  rw [Algebra.smul_def]
  congr 1

theorem valC_smul (h : GenFrEx Xo c) (a : 𝓞 c.F) (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (Z : Comp Xo c) :
    valC h u n ((a : c.F) • f) Z = a • valC h u n f Z := by
  simp only [valC, evC_smul]
  exact (smul_single_AC Z a _ _).symm

end Ev

set_option maxHeartbeats 1000000 in
theorem coe_smul_cusp {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (a : 𝓞 Tc.Q.c.F) (F : (recB hL).Cusp j ka) :
    ((a • F : (recB hL).Cusp j ka) : Tc.R j) = ((a : Tc.Q.c.F) • (F : Tc.R j)) := by
  rfl

def LamConst (large₂ : SizeData₂ D) (C A : ℝ) (ka : WeightFamilies.Wt D j) (P : ℝ) (n : ℕ) (s : ℝ) : Prop :=
  WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size ≤ P * n * s

theorem htLAM_of [Fintype (Comp (Tc.Q.Xo j) Tc.Q.c)] (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (δ : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Tc.Q.Dw j) → ℤ)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR D.host.E)
    (wR : Fin (N + 1) → Tc.R j) (jc : Comp (Tc.Q.Xo j) Tc.Q.c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Tc.R j) (n0 : ℕ) (th0R : Fin n0 → Tc.R j) (uF0 : WtR D.host.E)
    (nk : ℕ) (thkR : Fin nk → Tc.R j) (MR : Set (Tc.R j)) (etR ta1R ta2R : Tc.R j)
    (nu : HeightOneSpectrum (𝓞 Tc.Q.c.F) → ℝ)
    (ip : (Tc.Q.c.F →+* ℂ) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → ℂ)
    (wsize : WTZ D.host.E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (large₂ : SizeData₂ D) (C A : ℝ) (ka : WeightFamilies.Wt D j)
    (hgt : GenFromTest (Tc.Q.Xo j) Tc.Q.c h)
    (hka : wtZ (wtA ka) ka.n = (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 • wtZ uL.1 uL.2)
    (hlam : LAMwAt large₂ (recB hL) j ka C A)
    (hprod : ProdInLat hL j ka wR (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96)
    (hsup : SupPTGe hL j h fn yP ka)
    (hc : LamConst j large₂ C A ka PP0' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 (wsize (wtZ uL.1 uL.2))) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtLAM := by
  classical
  intro Z g hg hgZ
  obtain ⟨F, hFM, rfl⟩ : ∃ F : (recB hL).Cusp j ka, F ∈ (recB hL).Mlat j ka ∧
      g = valC h (wtA ka) ka.n (F : Tc.R j) := by
    clear hgZ
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨F, hFM, hF⟩ := hprod s
      refine ⟨F, hFM, ?_⟩
      funext Z
      rw [hF]
      beta_reduce
      rw [Finset.prod_apply]
      change ∏ k, AddMonoidAlgebra.single (wtZ uL.1 uL.2) (evC h Z (wR (s k))) =
        AddMonoidAlgebra.single (wtZ (wtA ka) ka.n) (evC h Z (∏ k, wR (s k)))
      rw [AddMonoidAlgebra.prod_single, hka, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        evC_prod h hgt Z]
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      funext Z
      simp [valC, evC_zero]
    | add x y _ _ hx hy =>
      obtain ⟨F, hFM, rfl⟩ := hx
      obtain ⟨G, hGM, rfl⟩ := hy
      refine ⟨F + G, Submodule.add_mem _ hFM hGM, ?_⟩
      funext Z
      simp [valC, evC_add, AddMonoidAlgebra.single_add]
    | smul a x _ hx =>
      obtain ⟨F, hFM, rfl⟩ := hx
      refine ⟨a • F, Submodule.smul_mem _ a hFM, ?_⟩
      funext Z
      show a • valC h (wtA ka) ka.n (F : Tc.R j) Z = valC h (wtA ka) ka.n ((a • F : (recB hL).Cusp j ka) : Tc.R j) Z
      rw [coe_smul_cusp hL j ka a F]
      exact (valC_smul h a _ _ _ Z).symm
  have hev : evC h Z (F : Tc.R j) ≠ 0 := fun h0 => hgZ (by simp [valC, h0])
  obtain ⟨F', hF'M, hF'0, hle⟩ := hsup Z F hFM hev
  have hl := hlam F' hF'M hF'0
  refine (neg_le_neg hc).trans (hl.trans ?_)
  unfold WeightFamilies.meanLogSup meanK
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun sg _ => ?_) (Nat.cast_nonneg _)
  have hpos : 0 < (recB hL).supN j ka sg F' :=
    lt_of_le_of_ne ((recB hL).supN_nonneg _ _ _ _)
      (fun h0 => hF'0 (((recB hL).supN_eq_zero _ _ _ _).1 h0.symm))
  refine Real.log_le_log hpos ((hle sg).trans (le_of_eq ?_))
  change _ = ⨆ P : PT (Ω := Om Z) sg, nrmC fn (yP Z) (_ • wtZ uL.1 uL.2) _ P
  rw [hka]

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.DepRun
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem satDir_of (hS : ChartSaturated Xo c) {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntChart T io y) :
    SatDir T (letI := io.toAlgebra; C.ch.uvec) := by
  intro τ
  obtain ⟨⟨w, emb, hw, hbasis⟩, -⟩ := hS T io y C τ
  have huv := C.gen.1.2.2.2.2.2.2
  choose A hA using fun m : Fin (chD C.ch) => (hbasis (Pi.single m 1)).exists
  have hAw : (Matrix.of A) * (Matrix.of w) = 1 := by
    ext m j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [hA m j, Pi.single_apply]
    by_cases hjm : j = m
    · subst hjm; simp
    · simp [hjm, Ne.symm hjm]
  have hwA : (Matrix.of w) * (Matrix.of A) = 1 := by
    first
      | exact mul_eq_one_comm.mp hAw
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hAw
  refine ⟨fun i j => A j (emb i), fun i i' => ?_⟩
  letI := io.toAlgebra
  have e1 : ∀ j, C.ch.uvec ⟨τ, i'⟩ j * algebraMap T.V T.Fr (A j (emb i)) =
      algebraMap T.V T.Fr (w (emb i') j * A j (emb i)) := by
    intro j
    rw [huv, map_mul, hw]
  refine (Finset.sum_congr rfl (fun j _ => e1 j)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  have h3 := congrFun (congrFun hwA (emb i')) (emb i)
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h3
  rw [h3]
  by_cases hii : i' = i
  · subst hii; simp
  · rw [if_neg (fun h' => hii (emb.injective h')), if_neg hii, map_zero]

theorem nuW_le_crude (hE : IntChartEx Xo c) (hS : ChartSaturated Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n) :
    nuW Xo c la k a n ≤ max 0 (crudeBd la (DF Dw a) : EReal) := by
  unfold nuW
  refine max_le_max le_rfl ?_
  unfold nuSup
  refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun ho =>
    iSup_le fun y => iSup_le fun hy => ?_
  obtain ⟨C⟩ := hE T io y hy
  unfold nuLoc
  refine (iInf_le _ C).trans ?_
  letI := io.toAlgebra
  exact (crude_inf C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec (satDir_of hS C) a n ha hn ho).1

omit [StarRing (𝓞 E)] in
theorem card_Lt1_le_finrank_mul : Fintype.card (Lt1 Dw) ≤ Module.finrank ℚ E * (Dw.p + Dw.q) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc ∑ τ : E →+* ℂ, Dw.mult τ ≤ ∑ _τ : E →+* ℂ, (Dw.p + Dw.q) := by
        apply Finset.sum_le_sum
        intro τ _
        unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
        split_ifs <;> omega
    _ = Module.finrank ℚ E * (Dw.p + Dw.q) := by
        rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, smul_eq_mul]

end

variable {D : D7}

theorem nuFinAt_of (T : Core D) (hp : T.Q.Pins) (Dd : DepData D.host.E) [StarRing (𝓞 D.host.E)]
    (hw : ∀ j, InR D j → (∀ τ, Antitone fun i => Dd.aL j (τ, i)) ∧ 2 * D.R.f * D.R.r ≤ Dd.nW j)
    (hE : ∀ j, InR D j → IntChartEx (T.Q.Xo j) T.Q.c) (hS : ∀ j, InR D j → ChartSaturated (T.Q.Xo j) T.Q.c) :
    NuFinAt T Dd := by
  intro j hj la
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [(hp.2.2.2 j hj).1, (hp.2.2.2 j hj).2.1]
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  have hn : Fintype.card (Lt1 (T.Q.Dw j)) ≤ Dd.nW j := by
    refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]; exact (hw j hj).2
  refine ne_top_of_le_ne_top ?_ (nuW_le_crude (hE j hj) (hS j hj) la _ _ _ (fun τ i i' h => (hw j hj).1 τ h) hn)
  rcases le_total (0 : EReal) (crudeBd la (DF (T.Q.Dw j) (Dd.aL j)) : EReal) with h | h
  · rw [max_eq_right h]; exact EReal.coe_ne_top _
  · rw [max_eq_left h]; exact EReal.zero_ne_top

def depRun (T : Core D) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j) : DepData D.host.E :=
  depDataOf T EX Tn vd (fun j => wtA (wL j)) (fun j => wtA (wF j)) (fun j => (wL j).n)
    (fun j => ∑ τ, ∑ i, (ka j).aP τ i) fun j => ∑ τ, ∑ i, (ka j).aM τ i

theorem lawsPi_depRun [StarRing (𝓞 D.host.E)] {T : Core D} (h : LawsM T) (EX : ErrX D) (Tn : ℕ+) (vd : ℕ → ℝ) (wL wF ka : ∀ j, WeightFamilies.Wt D j)
    (hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (wL j).n) : LawsPi T (depRun T EX Tn vd wL wF ka) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl, ?_, ?_, ?_⟩
  · exact tPos_depDataOf ..
  · exact fun j hj => ⟨(dom_wtA (wL j)).1, hn j hj⟩
  · exact piSplit_depDataOf ..
  · exact piHalf_depDataOf _ _ _ _ _ _ _ _ _ h

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem volPair_of_tie (hT : VolTieG D) (V : HSp D) (hs : V.SigOK) : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 := by
  have h := hT V hs
  clear hT
  obtain ⟨⟨μ, hμ⟩, hb⟩ := h
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hb μ hμ
  refine ⟨(μ, 𝓕), ?_⟩
  exact ⟨hμ, h𝓕⟩

theorem quotSupp_of (V : HSp D) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2) :
    QuotSupp V := by
  intro φ hφc hφinv hae g0
  by_contra hg0
  haveI : Countable (GQ V) := by
    unfold GQ
    exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have hvp : IsVolPair D V (volPair V).1 (volPair V).2 := by
    have e : volPair V = hP.choose := by
      unfold volPair
      rw [dite_eq_left hP]
    rw [e]
    exact hP.choose_spec
  haveI : (volPair V).1.IsHaarMeasure := hvp.1.1
  haveI : BorelSpace (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : MeasurableMul (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA _ _
  haveI : MeasurableConstSMul (GQ V) (GA D V) := ⟨fun c => measurable_const_mul (c : GA D V)⟩
  haveI : SMulInvariantMeasure (GQ V) (GA D V) (volPair V).1 :=
    ⟨fun c s _ => measure_preimage_mul (volPair V).1 (c : GA D V) s⟩
  let O : Set (GA D V) := {g | φ g ≠ 0}
  have hO : IsOpen O := isOpen_ne_fun hφc continuous_const
  have hOinv : ∀ γ : GQ V, γ • O = O := by
    intro γ
    ext g
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show φ ((γ : GA D V) * x) ≠ 0
      rw [hφinv _ γ.2]
      exact hx
    · intro hg
      refine ⟨((γ⁻¹ : GQ V) : GA D V) * g, ?_, ?_⟩
      · show φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0
        rw [hφinv _ (γ⁻¹).2]
        exact hg
      · show (γ : GA D V) * (((γ⁻¹ : GQ V) : GA D V) * g) = g
        rw [← mul_assoc, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_mul]
  have hpos : 0 < (volPair V).1 O := hO.measure_pos _ ⟨g0, hg0⟩
  have hOF : (volPair V).1 (O ∩ (volPair V).2) ≠ 0 := fun h =>
    hpos.ne' (hvp.2.measure_zero_of_invariant O hOinv h)
  let S : Set (AutQ V) := {q | ¬ onQ V φ q = (0 : AutQ V → ℂ) q}
  have h0 : muQ1 V S = 0 := ae_iff.mp hae
  have hS : muQ V S = 0 := by
    unfold muQ1 at h0
    rw [if_pos (show muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤ from hV), Measure.smul_apply,
      smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (ENNReal.inv_eq_zero.mp h) hV.2
    · exact h
  have hmeas : AEMeasurable (autMk V) ((volPair V).1.restrict (volPair V).2) := by
    have hm : Measurable (autMk V) := by
      first
      | exact measurable_quotient_mk'
      | exact fun _ hs => hs
    exact hm.aemeasurable
  have hpre : autMk V ⁻¹' S = O := by
    ext g
    have hrel := Quotient.mk_out (s := QuotientGroup.rightRel (GQ V)) g
    rw [QuotientGroup.rightRel_apply] at hrel
    have hv : φ (autMk V g).out = φ g := by
      have e : g = (g * (autMk V g).out⁻¹) * (autMk V g).out := by group
      conv_rhs => rw [e]
      rw [hφinv _ hrel]
    show ¬ φ (autMk V g).out = 0 ↔ φ g ≠ 0
    rw [hv]
  have hle := Measure.le_map_apply hmeas S
  rw [hpre, Measure.restrict_apply hO.measurableSet] at hle
  have e2 : muQ V S = Measure.map (autMk V) ((volPair V).1.restrict (volPair V).2) S := rfl
  rw [← e2, hS] at hle
  exact hOF (le_antisymm hle (zero_le))

section Dom

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem aeDom_of {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2)
    (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) : AeDom U σ V dict mu := by
  intro la P hPm hae k x hx
  have key : ∀ Q ∈ holSub (U σ).X la,
      ((∀ γ ∈ GQ V, ∀ g, adel V dict mu Q (γ * g) = adel V dict mu Q g) ∧
        Continuous (adel V dict mu Q)) ∧
      ∀ k, (∀ x ∈ ((U σ).X k).dom, ∀ b ∈ Bor ((U σ).X k).Ψ r, Q k (rmul x b) = bchar (la k) b * Q k x) ∧
        ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Q k (lact γ x) = ((U σ).X k).χ (la k) γ * Q k x := by
    intro Q hQ
    unfold holSub at hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      refine ⟨hA la Q hQ, fun k => ?_⟩
      have hs := (hQ k).1.1
      exact ⟨hs.2.1, hs.2.2⟩
    | zero =>
      refine ⟨⟨fun γ _ g => by simp, by rw [map_zero]; exact continuous_zero⟩,
        fun k => ⟨fun x _ b _ => by simp, fun γ _ x _ => by simp⟩⟩
    | add Q₁ Q₂ _ _ h1 h2 =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_add (f := _), Pi.add_apply, Pi.add_apply, h1.1.1 γ hγ g, h2.1.1 γ hγ g]
      · rw [map_add (f := _)]
        exact h1.1.2.add h2.1.2
      · simp only [Pi.add_apply]
        rw [(h1.2 k).1 x hx b hb, (h2.2 k).1 x hx b hb, mul_add]
      · simp only [Pi.add_apply]
        rw [(h1.2 k).2 γ hγ x hx, (h2.2 k).2 γ hγ x hx, mul_add]
    | smul a Q _ h =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h.1.1 γ hγ g]
      · rw [map_smul]
        exact h.1.2.const_smul a
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).1 x hx b hb]
        ring
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).2 γ hγ x hx]
        ring
  obtain ⟨⟨hinv, hcont⟩, hlaw⟩ := key P hPm
  have hz := quotSupp_of V hV hP (adel V dict mu P) hcont hinv hae
  obtain ⟨-, -, -, hd4, hd5, -⟩ := hd
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hd5 k x hx
  have h0 : P (dict g).1 (dict g).2 = 0 := by
    have e : mu g * P (dict g).1 (dict g).2 = 0 := hz g
    have hmu0 : mu g ≠ 0 := by
      intro h
      have h1 := hmu.2.1 g
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    exact (mul_eq_zero.mp e).resolve_left hmu0
  have hdom := hd4 g
  rw [hg] at h0 hdom
  exact eq_zero_of_orbit _ (la k) (P k) (hlaw k).1 (hlaw k).2 hx hγ hb hdom h0

end Dom

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.LiftCurveSt
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

structure CurveModel (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (g0 : B.Cusp j wF) where

  A' : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w)
  sA : ∀ i : Fin (WeightFamilies.dimY D j), sfr (xplus X E hM) la G.w i.succ ∈ A'

  h : ↥A'
  h_one : h - 1 ∈ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, sA i⟩ : ↥A'))
  fin : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥A' ⧸ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, sA i⟩ : ↥A')))
  red : IsReduced (↥A' ⧸ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, sA i⟩ : ↥A')))

  loc : ∀ b : ↥(Frac0 (xplus X E hM) la G.w), ∃ m : ℕ, ∃ a : ↥A', (h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * b = a

  base_form_injective : Function.Injective fun a : ↥A' =>
    ((a : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
      (emb (xplus X E hM) la G.N (X.inc wF g0))

  base_form_local : ∀ x : ↥(HK (xplus X E hM) la G.w wF), ∃ m : ℕ, ∃ a : ↥A',
    ((h : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) ^ m * (x : Lw (xplus X E hM) la G.w) =
      ((a : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
        (emb (xplus X E hM) la G.N (X.inc wF g0))

def InCurveSecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    (secQ y hs g0).InCurve

structure LiftModel (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (y : PtsG G la → E.Pt' la)
    (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF) (T : ℕ) where

  Λ : Type
  [cr : CommRing Λ]

  ι : Lw (xplus X E hM) la G.w →+* Λ

  hd : (Idx D j G.N →₀ ℕ) → Λ →+ Λ
  hd_zero : ∀ x, hd 0 x = x
  hd_ι : ∀ β x, hd β (ι x) = ι (hasse (xplus X E hM) la G.w β x)
  hd_mul : ∀ β x z, hd β (x * z) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, hd q.1 x * hd q.2 z

  ev : ∀ ζ, Λ →+* (hs ζ).T.Fr
  ev_ι : ∀ ζ x, ev ζ (ι x) = (hs ζ).lift x

  RG : Subring Λ
  RG_hd : ∀ β, ∀ r ∈ RG, hd β r ∈ RG
  RG_int : ∀ ζ, ∀ r ∈ RG, 0 ≤ nval (hs ζ).T.V 1 (ev ζ r)

  e' : Λ
  e'_hd : ∀ β, β ≠ 0 → hd β e' = 0
  e'_int : ∀ ζ, 0 ≤ nval (hs ζ).T.V 1 (ev ζ e')

  res_ker : ∀ x : ↥(HK (xplus X E hM) la G.w wF), ι (x : Lw (xplus X E hM) la G.w) ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w)) →
    toA0K (xplus X E hM) la G.w wF x = 0

  ball : ∀ a ∈ (secQ y hs g0).A0, ∃ r ∈ RG, ∃ x : ↥(HK (xplus X E hM) la G.w wF),
    toA0K (xplus X E hM) la G.w wF x = a ∧
    ι (x : Lw (xplus X E hM) la G.w) - r * e' ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w))

  approx : ∀ r ∈ RG, ∃ x : ↥(HK (xplus X E hM) la G.w wF),
    ι (x : Lw (xplus X E hM) la G.w) - r * e' ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w)) ^ (a0 D j T)

attribute [instance] LiftModel.cr

def InLiftSecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (Gc Prw : ℝ) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF) (T : ℕ),
    Nonempty (LiftModel G la y hs g0 T) →
    G.TiedW S Gc Prw → (secQ y hs g0).InCurve → (secQ y hs g0).InTie S → (secQ y hs g0).InLift T

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.UnifGen
noncomputable section

namespace Formalism.L2.Pj

open NumberField AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem scal_mul {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem gen_unit {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul, mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one, one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [mul_comm]; exact h1, h1⟩, ha⟩

end Gen

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FreeBridgeU
noncomputable section

namespace Formalism.L2.PjFree

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

open Formalism.L2.Pj (Rul)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

variable {Xo c}

variable (Xo c)

theorem intAll_iff : PjFree.IntAll Xo c ↔ Formalism.L2.Pj.IntAll Xo c := Iff.rfl

end Formalism.L2.PjFree
end
end
