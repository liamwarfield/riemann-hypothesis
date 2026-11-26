module

public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSumOfNoConj

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

def ConjLevel (t : GA D (D.sp.Y 0)) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ)
    (J' : Set (GA D (D.sp.Y 0))) (χ' : GA D (D.sp.Y 0) → ℂ) : Prop :=
  ∀ k, (k ∈ J ↔ t⁻¹ * k * t ∈ J') ∧ (k ∈ J → χ' (t⁻¹ * k * t) = χ k)

def EvalTieT (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) : Prop :=
  ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∃ j : E ≃ₗ[ℂ] EEC X G, ∀ T : E,
    ((j T : EEC X G) : L2X X) =ᵐ[muX X] (fun x => ev M v₀ (T : MMap M) (ι.symm x * t)) ∧
      ‖((j T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re


open Classical in
def sEEofTT (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) :
    E →ₗ⋆[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X :=
  if h : EvalTieT M μ 𝓕 E X G ι t c then (conjHH X G).toLinearMap.comp h.choose_spec.2.choose.toLinearMap else 0

end Formalism.IndefR.AutomorphicEvaluation

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
noncomputable section

open NumberField
open scoped TensorProduct

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

def ActKeeps (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) : Prop :=
  ∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c (O i).lev2 g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n

def RhoGeo (fw : FWTie T R κ v₀) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) : Prop :=
  ∀ i : Fin D.R.m,
    (ActKeeps (κ := κ) O i → ActRho R i (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) (fw.e i) (actLev T.Q.c (O i).lev2)) ∧
      (¬ ActKeeps (κ := κ) O i → ∀ g, (R.FW i).ρ g = 1)

end Formalism.IndefR.FWT
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FWCentral
noncomputable section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.FWT

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.JoinChr Formalism.IndefR.Links
  Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7}


end Loc

section Frame

open ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7}

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

variable {M}


end Frame

section Cut

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)


end Cut

section Central

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G0 : Type} [Group G0] [Fintype G0] (A : FormsL LL Ks WL W G0)

variable {ζ : LLˣ} {z : G0}

end Central

section Mat

open Formalism.IndefR.Cx Formalism.L2.Indef

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
  (i : Fin D.R.m)

theorem principal_form_tensor_expansion (c : Fin (finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → ℂ) :
    Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).w0C b i c) =
      ∑ l, cj (twAt D.what₂.embLL A3.A.v0) (c l) • (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b i l) := by
  have hnP : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < RealDat.nP F.lv2 b := by unfold RealDat.nP; exact_mod_cast Nat.card_pos
    exact_mod_cast (Real.sqrt_pos.2 this).ne'
  show ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (R.toRealDat.WS F.lv2 b i (sg0 D A3.A)).subtype
    (∑ l, cj (twAt D.what₂.embLL A3.A.v0) (c l) •
      (⟨R.toRealDat.bC F.lv2 b i _ l, Submodule.subset_span ⟨l, rfl⟩⟩ : R.toRealDat.WS F.lv2 b i (sg0 D A3.A))) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [LinearMap.map_smul, smul_comm]
  congr 1
  show ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) •
    (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 b i l) = _
  rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hnP, one_smul]

end Mat

section CC

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]
  {D : D7} {V : HSp D} {σ0 : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ0 r} {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
  {mu : GA D V → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ} {G : Type} [Group G] {act : G → Rul Xo c →ₗ[c.F] Rul Xo c} {Tup : Type}
  {dδ : Tup → DeltaDat Xo c n} {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
  {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c.F} {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ}
  {vol : Tup → c.F} {ep : ∀ t, Cl' t → c.F} {io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F}
  {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
  {Cu : Submodule c.F (Rul Xo c)} {cc cc' : U.Comp → ℂ} {ph ph' : ℂ}




end CC

section CCTie

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {hle : c.F ≤ c'.F} {n r : ℕ} {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]
  {LL : IntermediateField ℚ ℂ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ0' : c'.F →+* ℂ} {D : D7} {V : HSp D}
  {dict : GA D V → Σ k, Frame ((unfBC hle U σ0').X k).Ψ r} {mu : GA D V → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ}
  {G : Type} [Group G] {act : G → Rul Xo c →ₗ[c.F] Rul Xo c} {act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c'} {Tup : Type}
  {dδ : Tup → DeltaDat Xo c' n} {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
  {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ}
  {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
  {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {cc cc' : (unfBC hle U σ0').Comp → ℂ} {ph ph' : ℂ}

end CCTie

section CCDat

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

end CCDat

section Phase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_zero {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    phiC T hV a 0 = 0 := by
  subst hV
  show T.phiJ j σ a 0 = 0
  rw [CoreJ.phiJ, map_zero, map_zero, smul_zero]

omit [Algebra T.Q.c.F D.what₂.LL] in
theorem phiC_apply {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (h : σ = σ') {W : HSp D} (hV : T.V j σ = W) (hV' : T.V j σ' = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    phiC T hV a f g = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV' (T.dict j σ'))
      (muPin W (castDict hV' (T.dict j σ')) (castDict hV' (T.mu j σ')) (T.cE j σ')) (rdU (T.U j σ') f) g := by
  subst h
  subst hV
  rfl

theorem FWTie.evaluates_of_lUnif (t : FWTie T R κ v₀) (hU : R.LUnif) : t.Evaluates := by
  intro i σ hσ hV
  refine t.ev i σ hσ hV (Classical.byContradiction fun hn => hn ⟨0, fun f => ?_⟩)
  have h0 := t.ev0 i σ hσ hV hn
  have h1 := (hU i σ).1 _ _ (Pi.basisFun D.what₂.LL (Fin (R.nW i))).linearIndependent
  have h2 : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = 0 :=
    funext fun k => absurd (by rw [h0]; rfl) (h1.ne_zero k)
  have h3 : f = 0 := (t.e i).map_eq_zero_iff.1 (Subtype.ext h2)
  subst h3
  exact (congrArg (fun F : MMap (R.MW i σ) => F (v₀ i σ)) (R.HW i σ).e.map_zero).trans (phiC_zero hV _).symm

theorem FWTie.rat_of_val (t : FWTie T R κ v₀) (ht : t.Evaluates) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} (hσ : GoodEmb T.Q.c (res T σ))
    (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (hinj : Function.Injective (evAt R i σ (v₀ i σ))) {w : (R.HW i σ).H} {n : ℕ}
    (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κ i)
    (h : ∀ g, evAt R i σ (v₀ i σ) w g = ∑ k, σ (a k) * phiC T hV (wtA (κ i)) (f k : T.R ((i : ℕ) + 1)) g) :
    ∃ y, (R.FW i).j σ y = w := by
  refine ⟨∑ k, a k • ((t.e i (f k) : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL), hinj (funext fun g => ?_)⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h g, evAt, map_sum, map_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, map_smul, ← ht i σ hσ hV (f k)]
  rfl

theorem baseEmbedding_restriction_eq_coefficientInclusion (t : FWTie T R κ v₀) {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) :
    res T (sg0 D A) = O.s0 :=
  (congrArg (res T) (sgAt_mk _ R.hv0)).trans ((res_embLL T t.alg_eq t.laws.pins.2.2.1).trans (sOv_eq T.toCore O.c' O.hle).symm)

theorem phi_eq_phiC {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) {σ : T.Q.c.F →+* ℂ} (hs : σ = O.s0)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (g : GA D (Wc D i)) :
    (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) * O.phi (T.cE ((i : ℕ) + 1) O.s0) f g = phiC T hV a f g :=
  (phiC_apply hs hV O.hV a f g).symm

theorem evAt_smul (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) (c : ℂ) (w : (R.HW i σ).H) (g : GA D (Wc D i)) :
    evAt R i σ v (c • w) g = c * (R.HW i σ).e w v g := by
  rw [evAt, map_smul]
  rfl

theorem phase_of_phRat (t : FWTie T R κ v₀) (hU : R.LUnif) {i : Fin D.R.m}
    (hinj : Function.Injective (evAt R i (sg0 D A) (v₀ i (sg0 D A)))) {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) {ph : ℂ} (h : O.PhRat (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph)
    (x : A.fam.amb.FL i A.μ0) : ∃ y, (R.FW i).j (sg0 D A) y = ph • R.thG i A.μ0 (R.jV i A.μ0 x) :=
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) (baseEmbedding_restriction_eq_coefficientInclusion t O)).trans O.hV
  have hg : ∀ y, D.what₂.embLL y = sg0 D A y := fun y => (DFunLike.congr_fun (sgAt_mk _ R.hv0) y).symm
  (h x).elim fun _ h1 => h1.elim fun a h2 => h2.elim fun f hf =>
    t.rat_of_val (t.evaluates_of_lUnif hU) (base_embedding_good T R t.alg_eq t.laws.pins.2.2.1) hV hinj a f fun g =>
      (evAt_smul i _ _ ph _ g).trans ((hf g).trans (Finset.sum_congr rfl fun _ _ =>
        congrArg₂ (· * ·) (hg _) (phi_eq_phiC O (baseEmbedding_restriction_eq_coefficientInclusion t O) hV _ _ g)))

theorem phase_of_oneMap (t : FWTie T R κ v₀) (hU : R.LUnif) {i : Fin D.R.m}
    (hinj : Function.Injective (evAt R i (sg0 D A) (v₀ i (sg0 D A)))) {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) {ph : ℂ} (h : O.OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) O.s0) ph) :
    ‖ph‖ = 1 ∧ ∀ x, ∃ y, (R.FW i).j (sg0 D A) y = ph • R.thG i A.μ0 (R.jV i A.μ0 x) :=
  ⟨h.2.1.2.2.2.2.1, phase_of_phRat t hU hinj O h.2.2⟩

end Phase

end Formalism.IndefR.FWT
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Err

open Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat3

def withErr (R : RealDat3 D A3 Ks) (e : type_of% R.err0) : RealDat3 D A3 Ks :=
  { R with toRealDat := { R.toRealDat with err0 := e } }

variable {R : RealDat3 D A3 Ks} {F : Face3 D A3}

def _root_.Formalism.IndefR.Links.reErr {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Am : DefAmb Bs}
    (X : CxData Am) (e : type_of% X.err0) : CxData Am := { X with err0 := e }

theorem partAt_withErr (e i p v) : (R.withErr e).PartAt F i p v ↔ R.PartAt F i p v := by
  exact Iff.rfl

theorem zs_withErr (e) : ((R.withErr e).toCx3 F).zs = (R.toCx3 F).zs := by
  rfl


set_option maxHeartbeats 1000000 in
theorem weak_characterisation_with_error (h : R.WeakCharacterisation F) (e) : (R.withErr e).WeakCharacterisation F := by
  cases_type* RealDat3.WeakCharacterisation RealDat.BaseW RealDat.IsGrp RealDat.IsFam RealDat.IsModels RealDat.IsChainW RealDat.IsThPW RealDat3.IsInert RealDat3.IsScal RealDat3.IsTup
  repeat' (first | assumption | constructor)

end RealDat3

end Err

section Three

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.WeilFull Formalism.IndefR.Fin Formalism.IndefR.Eqv

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {F : Face3 D A3}

namespace RealDat3

variable (R : RealDat3 D A3 Ks)

def updS (kap : ℝ) (lam : type_of% R.lam3) : RealDat3 D A3 Ks :=
  { R with toRealDat := R.toRealDat.upd6 kap R.lam, lam3 := lam }

def Eig0 (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) (l : ℝ) : Prop :=
  R.Wp3 i p ≠ ⊥ ∧ ∀ x ∈ R.Wp3 i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x


variable (F) in
def EigOff (i : Fin D.R.m) (p : A3.fam3.base3.Ix) (v : InfinitePlace D.what₂.LL) (l : ℝ) : Prop :=
  PartX F.cr (R.toCx3 F) false i p v ∧ SimX F.cr (R.toCx3 F) false i p v l

variable {R}

theorem base_eigenvalue_unique {i t p} (l l' : ℝ) (h : R.Eig0 i t p l) (h' : R.Eig0 i t p l') : l = l' := by
  obtain ⟨hb, hl⟩ := h
  obtain ⟨-, hl'⟩ := h'
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  have hxx : (l : ℂ) • x = (l' : ℂ) • x := (hl x hx).symm.trans (hl' x hx)
  have hc : (l : ℂ) = (l' : ℂ) := by
    by_contra hne
    apply hx0
    have hne' : (l : ℂ) - (l' : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    have h0 : ((l : ℂ) - (l' : ℂ)) • x = 0 := by rw [sub_smul, hxx, sub_self]
    calc x = ((l : ℂ) - (l' : ℂ))⁻¹ • (((l : ℂ) - (l' : ℂ)) • x) := by
          rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
      _ = 0 := by rw [h0, smul_zero]
  exact_mod_cast hc

theorem eigOff_unique {i p v} (l l' : ℝ) (h : R.EigOff F i p v l) (h' : R.EigOff F i p v l') : l = l' := by
  obtain ⟨⟨x, hx, hm⟩, hs⟩ := h
  obtain ⟨-, hs'⟩ := h'
  have e1 := hs x hx x
  have e2 := hs' x hx x
  have hc : ((l : ℝ) : ℂ) = ((l' : ℝ) : ℂ) := mul_right_cancel₀ hm (e1.symm.trans e2)
  exact_mod_cast hc

theorem partAt_updS (kap lam i p v) : (R.updS kap lam).PartAt F i p v ↔ PartX F.cr (R.toCx3 F) false i p v := by
  exact Iff.rfl

theorem sim_updS (kap lam i p v l) : SimX F.cr ((R.updS kap lam).toCx3 F) false i p v l ↔ SimX F.cr (R.toCx3 F) false i p v l := by
  exact Iff.rfl

theorem zs_updS (kap lam) : ((R.updS kap lam).toCx3 F).zs = (R.toCx3 F).zs := by
  rfl

end RealDat3


open Classical in
theorem scalars_exist (R : RealDat3 D A3 Ks) : ∃ kap lam, (R.updS kap lam).IsScal F := by

  have hcan : ∀ {N : Type} [AddCommGroup N] [Module ℂ N] {a b : ℂ} {x : N}, x ≠ 0 → a • x = b • x → a = b := by
    intro N _ _ a b x hx h
    by_contra hne
    apply hx
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : (a - b) • x = 0 := by rw [sub_smul, h, sub_self]
    calc x = (a - b)⁻¹ • ((a - b) • x) := by rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
      _ = 0 := by rw [h0, smul_zero]

  obtain ⟨lam, hlam⟩ : ∃ lam : Fin D.R.m → T → A3.fam3.base3.Ix → InfinitePlace D.what₂.LL → ℝ,
      ∀ i t p v, lam i t p v =
        if v = A3.A.v0 then
          (if h : ∃ l, R.Eig0 i t p l then h.choose else Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i))
        else
          (if h : ∃ l, R.EigOff F i p v l then h.choose else Real.exp ((F.Zsc (R.toCx3 F).zs).l6m i)) :=
    ⟨_, fun _ _ _ _ => rfl⟩

  obtain ⟨kap, hkap⟩ : ∃ kap : ℝ, ∀ κ : ℝ,
      Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 (R.updS 0 lam).lamN κ →
      (∃ t p, R.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p ≠ 0) → kap = κ := by
    by_cases hex : ∃ κ : ℝ,
        Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 (R.updS 0 lam).lamN κ ∧
        (∃ t p, R.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p ≠ 0)
    · obtain ⟨κ0, hk0, -⟩ := hex
      refine ⟨κ0, fun κ hk hnd => ?_⟩
      obtain ⟨t, p, hE, hP⟩ := hnd
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
      have e := hcan hx0 ((hk0 t p x hx).symm.trans (hk t p x hx))
      have e' : κ0 * ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p =
          κ * ∏ j ∈ Finset.Icc 1 D.R.m, (R.updS 0 lam).lamN t j p := by exact_mod_cast e
      exact mul_right_cancel₀ hP e'
    · exact ⟨0, fun κ hk hnd => absurd ⟨κ, hk, hnd⟩ hex⟩
  refine ⟨kap, lam, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i t p l hb hl
    have hE : R.Eig0 i t p l := ⟨hb, hl⟩
    show lam i t p A3.A.v0 = l
    rw [hlam, if_pos rfl, dite_eq_left ⟨l, hE⟩]
    exact RealDat3.base_eigenvalue_unique (R := R) _ _ (Exists.choose_spec _) hE
  · intro κ hk hnd
    exact hkap κ hk hnd
  · intro i p v l hv hP hS
    have hPX : PartX F.cr (R.toCx3 F) false i p v := (RealDat3.partAt_updS kap lam i p v).1 hP
    have hSX : SimX F.cr (R.toCx3 F) false i p v l := (RealDat3.sim_updS kap lam i p v l).1 hS
    have hE : R.EigOff F i p v l := ⟨hPX, hSX⟩
    show lam i A3.A.μ0 p v = l
    rw [hlam, if_neg hv, dite_eq_left ⟨l, hE⟩]
    exact RealDat3.eigOff_unique (R := R) _ _ (Exists.choose_spec _) hE
  · intro i t p hb
    show lam i t p A3.A.v0 = Real.exp ((F.Zsc ((R.updS kap lam).toCx3 F).zs).l6m i)
    rw [RealDat3.zs_updS, hlam, if_pos rfl, dite_eq_right]
    rintro ⟨l, hl⟩
    exact hl.1 hb
  · intro i p v hv hnP
    show lam i A3.A.μ0 p v = Real.exp ((F.Zsc ((R.updS kap lam).toCx3 F).zs).l6m i)
    rw [RealDat3.zs_updS, hlam, if_neg hv, dite_eq_right]
    rintro ⟨l, hl⟩
    exact hnP ((RealDat3.partAt_updS kap lam i p v).2 hl.1)
  · intro i t p v hv
    show lam i t p v = lam i A3.A.μ0 p v
    rw [hlam, hlam, if_neg hv, if_neg hv]


end Three

end Formalism.IndefR.Links

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PublishedAut
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.PublishedAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def AtTauExists (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∀ τ (g : Matrix (Fin V.rank) (Fin V.rank) ℂ), g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) → ∃ x, IsAtTau θ V τ g x

theorem atTauExists_of {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) (V : HSp D) :
    AtTauExists θ V := by
  intro τ g hg
  obtain ⟨x, hx, -⟩ := Formalism.IndefR.Eqv.atTauExUnique_holds (D := D) θ hθ V τ g hg
  exact ⟨x, hx⟩

end Formalism.IndefR.PublishedAut

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfVec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.SchurOrthogonalityAlt
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))


open Classical in
structure EqCont (M : DSModel V S) (T : MMap M) : Prop where
  equiv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)
  cont : ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ}


open Classical in
theorem eqCont_of_mem {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : T ∈ Mult θ M J χ) : EqCont θ M T := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact ⟨hT.equiv, hT.cont⟩
  | zero =>
    refine ⟨fun τ g _ v w _ => ?_, fun τ v x => ⟨0, sobCont_zero, fun w => ?_⟩⟩
    · rw [MultilinearMap.zero_apply, MultilinearMap.zero_apply]; rfl
    · simp
  | add T T' _ _ h h' =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.add_apply, MultilinearMap.add_apply, h.equiv τ g hg v w hw, h'.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      obtain ⟨ℓ', hℓ', e'⟩ := h'.cont τ v x
      exact ⟨ℓ + ℓ', sobCont_add hℓ hℓ', fun w => by
        rw [LinearMap.add_apply, e, e', MultilinearMap.add_apply, Pi.add_apply]⟩
  | smul a T _ h =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.smul_apply, MultilinearMap.smul_apply, h.equiv τ g hg v w hw]; rfl
    · obtain ⟨ℓ, hℓ, e⟩ := h.cont τ v x
      exact ⟨a • ℓ, sobCont_smul a hℓ, fun w => by
        rw [LinearMap.smul_apply, e, MultilinearMap.smul_apply, Pi.smul_apply]⟩




end Formalism.IndefR.AutomorphicEvaluation

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.ThPinsEx
noncomputable section

namespace Formalism.IndefR.FWT

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct nonZeroDivisors

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Gen

section Map

open MvPolynomial

end Map

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem Q_base_empty (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h := (hL.Q_ram A.μ0 PP).2 (Or.inl hPP)
  rw [hL.xi_base] at h
  exact h fun x _ => rfl

section Phi

variable (R : RealDat D A Ks) (i : Fin D.R.m) {K' : Type} [Field K'] (σ' : K' →+* ℂ) (t : T0)
  {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
  (N : Submodule (𝓞 D.host.E) La)

end Phi

section Reps

variable (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)

end Reps

section Place

variable (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
  {K' : Type} [Field K'] {jL : D.what₂.LL →+* K'} {σ' : K' →+* ℂ}

theorem levFn_flag1_mem {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (S : Subfield ℂ)
    (hcg : ∀ c, ∀ PP ∈ L.Pg, ∀ u, ((L.cg c PP u : ℂˣ) : ℂ) ∈ S) (hxq : ∀ PP ∈ L.Q, ∀ u, ((L.xq PP u : ℂˣ) : ℂ) ∈ S)
    (x : GL (Fin n) (Lev.EAf D)) :
    ((Formalism.L2.DIV.levFn β (Lev.flag1L L) x : ℂˣ) : ℂ) ∈ S := by
  unfold Formalism.L2.DIV.levFn
  simp only [Units.val_mul, Units.coe_prod]
  refine S.mul_mem (S.mul_mem ?_ (S.prod_mem fun PP hPP => S.prod_mem fun c _ => hcg _ _ hPP _))
    (S.prod_mem fun PP hPP => hxq _ hPP _)
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · have e : (Lev.flag1L L).P.chi = 1 := rfl
    rw [e, MonoidHom.one_apply, Units.val_one]
    exact S.one_mem
  · simp only [Units.val_one]
    exact S.one_mem


set_option maxHeartbeats 2000000 in
theorem hχ_of (hchi : ∀ PP ∈ R.Pg, ∀ u, ∃ a, ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) = D.what₂.embLL a)
    (hxi : ∀ PP ∈ R.Q t, ∀ u, ∃ a, ((R.xiR t PP u : ℂˣ) : ℂ) = D.what₂.embLL a) :
    ∀ k, ∃ a, (((levEnvOf (Vc D i) (R.βV i) (R.toLevCh.datVt i t) R.pl (A.ok t)).lev.χ k : ℂˣ) : ℂ) = D.what₂.embLL a := by
  intro k
  have hcg : ∀ c, ∀ PP ∈ (R.toLevCh.datVt i t).Pg, ∀ u,
      (((R.toLevCh.datVt i t).cg c PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    intro c PP hPP u
    have e : (R.toLevCh.datVt i t).cg c PP u = (R.chi ((i : ℕ) + 1) PP u)⁻¹ := by
      simp [LevCh.datVt, Lev.datY]
    rw [e, Units.val_inv_eq_inv_val]
    obtain ⟨a, ha⟩ := hchi PP hPP u
    exact Subfield.inv_mem _ ⟨a, ha.symm⟩
  have hxq : ∀ PP ∈ (R.toLevCh.datVt i t).Q, ∀ u,
      (((R.toLevCh.datVt i t).xq PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    intro PP hPP u
    have e : (R.toLevCh.datVt i t).xq PP u = R.xiR t PP u := by
      simp [LevCh.datVt, Lev.datY]
    rw [e]
    obtain ⟨a, ha⟩ := hxi PP hPP u
    exact ⟨a, ha.symm⟩
  obtain ⟨a, ha⟩ := levFn_flag1_mem (R.βV i) (R.toLevCh.datVt i t) D.what₂.embLL.fieldRange hcg hxq _
  exact ⟨a, ha.symm⟩

end Place

section Assemble

end Assemble

end Formalism.IndefR.FWT

end
end
