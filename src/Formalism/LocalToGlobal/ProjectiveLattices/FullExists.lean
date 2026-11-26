module

public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Formalism.LocalToGlobal.ProjectiveLattices.SecPtRed

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FullExists
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Full (D : D7) : Type 1 extends Top D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)
  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ
  half₂ : Ideal (𝓞 D.host.E)

variable {D : D7}

def Full.J (T : Full D) : CoreJ D :=
  { toCore := T.toTop.toCore, cE := T.cE, chiW := T.chiW, x₀ := T.x₀, iota := T.iota }

def Full.XiVal (T : Full D) (j n : ℕ) : Prop :=
  ∃ (hr : (T.V j T.σ₀).rank = D.R.r) (U₂ : _) (dict₂ : _),
    CXiVal (T.V j T.σ₀) hr T.σ₀ (Tup := Unit) (fun _ => T.dδ j n) U₂ dict₂
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (T.x₀ j T.σ₀) fun _ => T.xi

structure LawsFull (T : Full D) : Prop where
  p : LawsP T.toTop
  j : LawsJ T.J
  sh : LawsSh T.toTop

  canon : T.Q.Canon

  lvA : ∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1

  halfI : ∀ j, InR D j → ∀ n, (T.dδ j n).I = T.half₂

  shUniq : ∀ j, InR D j → ∀ n (_ : StarRing (𝓞 D.host.E)) (nab' : NabV (T.dδ j n).Xo₂ (T.dδ j n).c₂),
    IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ nab' → ∀ a, Dom a n →
      shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n { T.dδ j n with nab₂ := nab' } =
        shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)

  xiVal : ∀ j, InR D j → ∀ n, T.XiVal j n

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D} (h : LawsP T)

theorem combAlg_of_combBound (j : ℕ) (hj : InR D j) (hjm : j < D.R.m) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (cb / (2 * (G.iet : ℝ))) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨T', io, e, ho, z, hz, eta, heta, hq⟩ := y0.2
  obtain ⟨η, hη⟩ := T.G.liesTotal h.points_condition h.bc66 hj la T' io e ho z hz
  let y : T.PtA j la := PtV.mk la ho z hz η hη
  have hyv : vAtV y = vAtV y0 := funext fun g => by
    show y.1.1 g = y0.1.1 g
    rw [hq]
    rfl
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hyv]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  obtain ⟨h0, h1⟩ := (hX la y).1 hjm
  rw [hv] at h0 h1
  rw [hd] at h1
  refine ⟨h0, fun htop => ?_⟩
  have h2 := h1 htop
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_toReal htop (vAtV_ne_bot y0 _)] at h2
  exact h2

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ)
  (η : (recB h.toLawsCore).Cusp j (wEt D j i))

def EtCusp : Prop := η ≠ 0 ∧ (recPJ h j hj).NonZeroComp _ η

def EtVal : Prop :=
  ∀ la (y : (recPJ h j hj).Pt la),
    ((2 * i * (recPJ h j hj).phiC la y : ℝ) : EReal) ≤ (recPJ h j hj).vAt la y ((recPJ h j hj).inc _ η)

def EtSup (P : ℝ) : Prop := ∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ η) / i ≤ P

variable (P : ℝ) (Arch : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop)

def ETEx : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j < D.R.m), ∃ i : ℕ, 0 < i ∧ ∃ η : (recB h.toLawsCore).Cusp j (wEt D j i),
    EtCusp h j ⟨h1, h2.le⟩ i η ∧ EtVal h j ⟨h1, h2.le⟩ i η ∧ EtSup h j i η P ∧ Arch j i η

variable {h P Arch}

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

def letE (Dw : Datum H) : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
  (Fintype.equivFin _).symm

def tyOf (c : Coeff l) (σ : c.F →+* ℂ) (Dw : Datum H) : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → (E →+* ℂ) :=
  fun i => relab c σ (letE Dw i).1

def RelabType (c : Coeff l) (σ : c.F →+* ℂ) (Dw : Datum H) : Prop := IsTypeFn H Dw.p Dw.q (tyOf c σ Dw)

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def famOf (hN : N1c) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (hpq : 1 ≤ Dw.p + Dw.q) (hσ : GoodEmb c σ)
    (hR : RelabType c σ Dw) :
    FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (letE Dw j).1) :=
  Classical.choice (hN E H Dw l Xo _ _ _ hpq hσ hR)

structure ModelsOf {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (r : ℕ) : Type 1 where
  X : Fin F.n → Data E r
  φ : ∀ i, (F.Di i).La ≃ₗ[𝓞 E] (X i).Λ

structure ModelBase {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} {F : FamilyUnif Xo σ' ty} (M : ModelsOf F r) :
    Prop where
  rank : r = Dw.p + Dw.q
  type : ∀ k, (M.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (M.X k).Ψ ↔ τ (H.rt : E) = H.rt0
  chi : ∀ k la γ, (M.X k).χ la γ = 1
  ef : ∀ k a b, (((F.Di k).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (M.φ k a : Fin r → E) (M.φ k b))
  gam : ∀ k (γ : GL (Fin r) E), γ ∈ (M.X k).Γ ↔ IsUStab (M.X k).Gm (M.X k).Λ γ ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + (l.M : ℕ) • (M.φ k b : Fin r → E)) ∧
    ∀ a : (F.Di k).La, ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) = (M.φ k a : Fin r → E) + (l.A : ℕ) • (M.φ k b : Fin r → E)
  domStab : ∀ k, ∀ x ∈ (M.X k).dom, (∀ b ∈ Bor (M.X k).Ψ r, rmul x b ∈ (M.X k).dom) ∧
    ∀ γ ∈ (M.X k).Γ, lact γ x ∈ (M.X k).dom

def FrameOK {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (k : Fin F.n) (x : (M.X k).dom) (y : FrPt Xo c (CAt σ)) : Prop :=
  ∃ Pm : (F.Di k).La →+ (Fin g → ℂ),
        (∀ a j, Pm a j = perFr (M.X k) x.1 (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
        IsPeriod (F.Di k) (fun j => relab c σ (e j).1) Pm ∧ y.x = F.u k Pm ∧
        (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
          (y.u τ i)) ∧
        ((∀ τ' i', ‖dmin (M.X k).Gm x.1 τ' i'‖ = 1) →
          ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (F.ex k Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (F.ex k Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
              pt ≫ gxFst y.x = (F.ex k Pm z).left →
              pt ≫ gxSnd y.x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = 1)

def unfOf {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) : Unf Xo c σ r where
  Comp := Fin F.n
  X := M.X
  un := un

def FramesOK {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) : Prop :=
  (∀ k x, FrameOK e F M k x (un k x)) ∧
  (∀ k (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom),
    ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧
      ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b) ∧
  (∀ k, ∀ γ ∈ (M.X k).Γ, ∀ (x : (M.X k).dom) (h : lact γ x.1 ∈ (M.X k).dom),
    ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = 1) ∧
  ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ∀ k, DifferentiableOn ℂ (rdU (unfOf e F M un) f k) (M.X k).dom

theorem rdU_mem (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r} (h : x ∈ (U.X k).dom) :
    rdU U f k x = toC (evR Xo c f (U.un k ⟨x, h⟩)) := by
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos h]

instance (σ : c.F →+* ℂ) : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)

end Fam

section Dict2

variable {Comp : Type}

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}


open Classical in
def DictSpec (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : GA D V) (p : Σ k, Frame (U.X k).Ψ r) : Prop :=
  ∃ γ ∈ GQ V,
      ((U.X p.1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ p.1 (F.t (ik p.1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X p.1).Ψ, mat p.2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th p.1 τ) (γ * h)) * x₀ τ.1



def DetRootMul (V : HSp D) : Prop :=
  ∀ g g' x x', IsDetRoot V g x → IsDetRoot V g' x' → IsDetRoot V (g * g') (x * x')

theorem detRootMul_holds (V : HSp D) : DetRootMul V := by
  intro g g' x x' hx hx'
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

end Dict2

section Base

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


end Base

section Inv

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

end Inv

section Rows

variable {D : D7}

def XiConst (D : D7) : Prop := ∀ τ : D.host.E →+* ℂ, ‖τ D.host.xi0‖ = xiR D

theorem xiConst_holds (D : D7) : XiConst D := by
  intro τ
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, sq_emb, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

end Rows

section Collected

variable {D : D7}

variable {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q}

end Collected

section J

variable {D : D7}

variable {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q}
  {chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle}


end J

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def extAll : PtExt (recPJ h j hj) where
  Pt' la := valSet (T.Q.Xo j) T.Q.c (trivialClassCondition (T.Q.Xo j) T.Q.c) la
  extendedPointBaseChange la _ := (T.G.P.ex (T.G.dat j) (WeightAlgebra.resCh la)).yEta
    (Classical.choice ((T.G.P.ex (T.G.dat j) (WeightAlgebra.resCh la)).genNe _))
  vAt' _ y := vG y.1
  vAt'_zero la y := vG_zero (isVal_valSet la y.1 y.2).zero
  vAt'_ne_bot la y := vG_ne_bot (isVal_valSet la y.1 y.2).zero (isVal_valSet la y.1 y.2).ne_bot
  vAt'_add la y := vG_add (isVal_valSet la y.1 y.2).add
  vAt'_smul la y a F ha := vG_smul (fun r => (isVal_valSet la y.1 y.2).smul a r ha) F
  vAt'_mul la y := vG_mul deg (cutR T.C j) (isVal_valSet la y.1 y.2).zero (isVal_valSet la y.1 y.2).mul

theorem extAll_vAt_inc (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : (extAll h j hj).Pt' la) (w : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j w) : (extAll h j hj).vAt' la y ((recPJ h j hj).inc w F) = y.1 F.1 := by

  have hinc : ∀ m, ((recPJ h j hj).inc w F).coeff m = if deg w = m then F.1 else 0 := by
    intro m
    show (AddMonoidAlgebra.single (deg w) _).coeff m = _
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  have h0 : y.1 0 = ⊤ := by
    first
      | exact (isVal_valSet la y.1 y.2).zero
      | simpa using (isVal_valSet la y.1 y.2).zero
  show vG y.1 ((recPJ h j hj).inc w F) = y.1 F.1
  unfold vG
  simp only [hinc]
  apply le_antisymm
  · exact iInf_le_of_le (deg w) (by simp)
  · refine le_iInf fun m => ?_
    split_ifs with hm
    · exact le_rfl
    · rw [h0]
      exact le_top

theorem intAtExt_extAll : IntAtExt _ (extAll h j hj) := by
  intro w F hF la y
  rw [extAll_vAt_inc]
  exact (h.reg j hj).int (dom_wtA w) (cutR_le T.C j w F.2) hF la y.1 y.2

def recPlus : WeightAlgebra.PJ D (recB h.toLawsCore) T.G.P j := xplus (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CurveSec
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} {g0 : B.Cusp j wF}

namespace CurveModel

variable (M : CurveModel G la g0)

def JA : Ideal ↥M.A' :=
  Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) => (⟨sfr (xplus X E hM) la G.w i.succ, M.sA i⟩ : ↥M.A'))

theorem map_JA : M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)) = Jid (xplus X E hM) la G.w := by
  rw [JA, Ideal.map_span, ← Set.range_comp]
  rfl

theorem bij_quot : Function.Bijective (Ideal.quotientMap (M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)))
    (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)) Ideal.le_comap_map) := by
  refine ReciprocityTheory.ChartRestriction.G.I2.quotientMap_bijective_of_loc M.h M.JA M.h_one (fun b => ?_) Subtype.val_injective
  obtain ⟨m, a, ha⟩ := M.loc b
  exact ⟨m, a, by rw [map_pow]; exact ha⟩

def quotEquiv : (↥M.A' ⧸ M.JA) ≃ₐ[Kp (xplus X E hM) la G.N] OsK (xplus X E hM) la G.w :=
  AlgEquiv.ofBijective
    ((Ideal.quotientEquivAlgOfEq (Kp (xplus X E hM) la G.N) M.map_JA).toAlgHom.comp
      (Ideal.quotientMapₐ (M.JA.map (algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)))
        (IsScalarTower.toAlgHom (Kp (xplus X E hM) la G.N) ↥M.A' ↥(Frac0 (xplus X E hM) la G.w))
        Ideal.le_comap_map))
    ((Ideal.quotientEquivAlgOfEq (Kp (xplus X E hM) la G.N) M.map_JA).bijective.comp M.bij_quot)

theorem toOsK_h : toOsK (xplus X E hM) la G.w (M.h : ↥(Frac0 (xplus X E hM) la G.w)) = 1 := by
  have h1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) - 1) ∈ Jid (xplus X E hM) la G.w := by
    rw [← M.map_JA]
    let f := algebraMap ↥M.A' ↥(Frac0 (xplus X E hM) la G.w)
    change f M.h - 1 ∈ Ideal.map f M.JA
    rw [← f.map_one, ← f.map_sub]
    exact Ideal.mem_map_of_mem f M.h_one
  have h2 := (toOsK_eq_zero_iff (xplus X E hM) la G.w _).2 h1
  rw [map_sub, map_one, sub_eq_zero] at h2
  exact h2

theorem fractionToIntegralSection_smul_eq (b : ↥(Frac0 (xplus X E hM) la G.w)) (n : ↥(HK (xplus X E hM) la G.w wF)) :
    toA0K (xplus X E hM) la G.w wF (b • n) = toOsK (xplus X E hM) la G.w b • toA0K (xplus X E hM) la G.w wF n := by
  rw [map_smul]
  exact (algebraMap_smul (OsK (xplus X E hM) la G.w) b _).symm

theorem coe_smul_base_cusp_form (b : ↥(Frac0 (xplus X E hM) la G.w)) :
    ((b • toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) =
      (b : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w) (emb (xplus X E hM) la G.N (X.inc wF g0)) := by
  rw [Submodule.coe_smul, coe_toHK0]
  rfl

theorem coe_smul' (b : ↥(Frac0 (xplus X E hM) la G.w)) (n : ↥(HK (xplus X E hM) la G.w wF)) : ((b • n : ↥(HK (xplus X E hM) la G.w wF)) : Lw (xplus X E hM) la G.w) = (b : Lw (xplus X E hM) la G.w) * (n : Lw (xplus X E hM) la G.w) := by
  rw [Submodule.coe_smul]
  rfl


set_option maxHeartbeats 1000000 in
theorem JH_mem (z : ↥(HK (xplus X E hM) la G.w wF)) (hz : z ∈ Jid (xplus X E hM) la G.w • (⊤ : Submodule ↥(Frac0 (xplus X E hM) la G.w) ↥(HK (xplus X E hM) la G.w wF))) :
    ∃ m : ℕ, ∃ a' ∈ M.JA, ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • z) = ((a' : ↥(Frac0 (xplus X E hM) la G.w)) •
      toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩) := by
  set e0 : ↥(HK (xplus X E hM) la G.w wF) := toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ with he0
  have key : ∀ r ∈ Jid (xplus X E hM) la G.w, ∀ n : ↥(HK (xplus X E hM) la G.w wF), ∃ m : ℕ, ∃ a' ∈ M.JA,
      ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • (r • n)) = ((a' : ↥(Frac0 (xplus X E hM) la G.w)) • e0) := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro n
      obtain ⟨m, a, ha⟩ := M.base_form_local n
      refine ⟨m, ⟨sfr (xplus X E hM) la G.w i.succ, M.sA i⟩ * a, Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩), ?_⟩
      apply Subtype.ext
      rw [coe_smul', coe_smul', he0, coe_smul_base_cusp_form]
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [mul_left_comm, ha]
      ring
    | zero => intro n; exact ⟨0, 0, Ideal.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      intro n
      obtain ⟨m, a, ha, he⟩ := hx n
      obtain ⟨m', a', ha', he'⟩ := hy n
      refine ⟨m + m', M.h ^ m' * a + M.h ^ m * a', Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha)
        (Ideal.mul_mem_left _ _ ha'), ?_⟩
      have e1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • (x • n) = ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_comm, mul_smul, he, ← mul_smul]
      have e2 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • (y • n) = ((M.h ^ m * a' : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
        rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_smul, he', ← mul_smul]
      rw [add_smul, smul_add, pow_add, e1, e2, ← add_smul, ← AddMemClass.coe_add]
    | smul c x _ hx =>
      intro n
      obtain ⟨m, a, ha, he⟩ := hx ((c • n : ↥(HK (xplus X E hM) la G.w wF)))
      refine ⟨m, a, ha, ?_⟩
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact he
  refine Submodule.smul_induction_on hz (fun r hr n _ => key r hr n) ?_
  rintro x y ⟨m, a, ha, he⟩ ⟨m', a', ha', he'⟩
  refine ⟨m + m', M.h ^ m' * a + M.h ^ m * a', Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha)
    (Ideal.mul_mem_left _ _ ha'), ?_⟩
  have e1 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • x = ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_comm, mul_smul, he, ← mul_smul]
  have e2 : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * (M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m') • y = ((M.h ^ m * a' : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) • e0 := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, mul_smul, he', ← mul_smul]
  rw [smul_add, pow_add, e1, e2, ← add_smul, ← AddMemClass.coe_add]

theorem isGen (M : CurveModel G la g0) : IsGen (OsK (xplus X E hM) la G.w) (resF G la g0) := by
  set e0 : ↥(HK (xplus X E hM) la G.w wF) := toHK0 (xplus X E hM) la G.w wF ⟨emb (xplus X E hM) la G.N (X.inc wF g0), emb_mem_Vw (xplus X E hM) la G.N wF g0⟩ with he0
  have hres : resF G la g0 = toA0K (xplus X E hM) la G.w wF e0 := rfl
  unfold IsGen
  rw [hres]
  constructor
  · intro u v huv
    rw [← sub_eq_zero]
    have hw : (u - v) • toA0K (xplus X E hM) la G.w wF e0 = 0 := by rw [sub_smul]; exact sub_eq_zero.2 huv
    obtain ⟨b, hb⟩ := toOsK_surjective (xplus X E hM) la G.w (u - v)
    obtain ⟨m, a, ha⟩ := M.loc b
    have hta : toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)) = u - v := by
      rw [← ha, map_mul, map_pow, M.toOsK_h, one_pow, one_mul, hb]
    rw [← hta, ← fractionToIntegralSection_smul_eq] at hw
    obtain ⟨m', a', ha', he'⟩ := M.JH_mem _ ((reduction_eq_zero_iff_mem_ideal_smul (xplus X E hM) la G.w wF _).1 hw)
    have hinj : M.h ^ m' * a = a' := by
      apply M.base_form_injective
      have := congrArg (fun n : ↥(HK (xplus X E hM) la G.w wF) => (n : Lw (xplus X E hM) la G.w)) he'
      rw [he0] at this
      simp only [coe_smul', coe_toHK0, SubmonoidClass.coe_pow] at this
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [mul_assoc]
      exact this
    have hJ : ((M.h ^ m' * a : ↥M.A') : ↥(Frac0 (xplus X E hM) la G.w)) ∈ Jid (xplus X E hM) la G.w := by
      rw [hinj, ← M.map_JA]; exact Ideal.mem_map_of_mem _ ha'
    have h0 := (toOsK_eq_zero_iff (xplus X E hM) la G.w _).2 hJ
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, M.toOsK_h, one_pow, one_mul] at h0
    rw [← hta]
    exact h0
  · intro n
    obtain ⟨x, rfl⟩ := reductionMap_surjective (xplus X E hM) la G.w wF n
    obtain ⟨m, a, ha⟩ := M.base_form_local x
    refine ⟨toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)), ?_⟩
    have hx : ((M.h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m • x) = ((a : ↥(Frac0 (xplus X E hM) la G.w)) • e0) := by
      apply Subtype.ext
      rw [coe_smul', he0, coe_smul_base_cusp_form]
      simpa only [Subalgebra.coe_pow, SubmonoidClass.coe_pow] using ha
    show toOsK (xplus X E hM) la G.w (a : ↥(Frac0 (xplus X E hM) la G.w)) • toA0K (xplus X E hM) la G.w wF e0 = toA0K (xplus X E hM) la G.w wF x
    rw [← fractionToIntegralSection_smul_eq, ← hx, fractionToIntegralSection_smul_eq, map_pow, M.toOsK_h, one_pow, one_smul]

end CurveModel

theorem inCurveSec (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : InCurveSecSt (E := E) G la := by
  intro y hs g0 hMod _
  obtain ⟨M⟩ := hMod
  refine ⟨?_, ?_, M.isGen⟩
  · haveI : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥M.A' ⧸ M.JA) := M.fin
    exact LinearEquiv.finiteDimensional M.quotEquiv.toLinearEquiv
  · haveI : IsReduced (↥M.A' ⧸ M.JA) := M.red
    exact isReduced_of_injective M.quotEquiv.symm.toRingHom M.quotEquiv.symm.injective

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ProdInLatPf
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {Tc : Core D} (hL : LawsCore Tc) (j : ℕ)

theorem prodInLat_of (hj : InR D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (wL ka : WeightFamilies.Wt D j) (n : ℕ)
    (hw : ∀ k, ∃ F : (recB hL).Cusp j wL, F ∈ (recB hL).Mlat j wL ∧ (F : Tc.R j) = wR k)
    (hn : 1 ≤ n) (hka : ∀ x, wtA ka x = n * wtA wL x) (hkn : ka.n = n * wL.n) : ProdInLat hL j ka wR n := by
  have hV : ∀ la, ∀ v ∈ Tc.Vs j la, IsVal la v := fun la => isVal_valSet la
  have hw1 : ∀ k, wR k ∈ Tc.C j wL ∧ ∀ la, ∀ v ∈ Tc.Vs j la, 0 ≤ v (wR k) := by
    intro k
    obtain ⟨F, hF, hFk⟩ := hw k
    rw [← hFk]
    exact ⟨cutR_le Tc.C j wL F.2, hF⟩
  have key : ∀ m (s : Fin (m + 1) → Fin (N + 1)), ∃ W : WeightFamilies.Wt D j, (∀ x, wtA W x = (m + 1) * wtA wL x) ∧
      W.n = (m + 1) * wL.n ∧ ∏ k, wR (s k) ∈ Tc.C j W ∧ ∀ la, ∀ v ∈ Tc.Vs j la, 0 ≤ v (∏ k, wR (s k)) := by
    intro m
    induction m with
    | zero =>
      intro s
      refine ⟨wL, fun x => by ring, by ring, ?_, ?_⟩
      · rw [Fin.prod_univ_one]; exact (hw1 _).1
      · rw [Fin.prod_univ_one]; exact (hw1 _).2
    | succ m ih =>
      intro s
      obtain ⟨W, hW1, hW2, hWm, hWv⟩ := ih (fun k => s k.succ)
      refine ⟨WeightAlgebra.wadd wL W, fun x => ?_, ?_, ?_, ?_⟩
      · rw [wtA_wadd, Pi.add_apply, hW1 x]; ring
      · rw [n_wadd, hW2]; ring
      · rw [Fin.prod_univ_succ]; exact hL.mul j hj wL W _ (hw1 _).1 _ hWm
      · intro la v hv
        rw [Fin.prod_univ_succ, (hV la v hv).mul]
        exact add_nonneg ((hw1 _).2 la v hv) (hWv la v hv)
  intro s
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨W, hW1, hW2, hWm, hWv⟩ := key m s
  have hmem : ∏ k, wR (s k) ∈ Tc.C j ka := by
    have hC : Tc.C j ka = Tc.C j W := by
      show Tc.cuspA j (wtA ka) ka.n = Tc.cuspA j (wtA W) W.n
      rw [hkn, hW2, show wtA ka = wtA W from funext fun x => by rw [hka x, hW1 x]]
    rw [hC]; exact hWm
  refine ⟨⟨∏ k, wR (s k), ?_⟩, ?_, rfl⟩
  · show _ ∈ cutR Tc.C j ka
    rw [cutR_eq Tc.C hj]; exact hmem
  · exact hWv

theorem prodInLat_of_wtZ (hj : InR D j) {N : ℕ} (wR : Fin (N + 1) → Tc.R j) (wL ka : WeightFamilies.Wt D j) (n : ℕ)
    (hw : ∀ k, ∃ F : (recB hL).Cusp j wL, F ∈ (recB hL).Mlat j wL ∧ (F : Tc.R j) = wR k)
    (hn : 1 ≤ n) (hkaZ : wtZ (wtA ka) ka.n = n • wtZ (wtA wL) wL.n) : ProdInLat hL j ka wR n := by
  refine prodInLat_of hL j hj wR wL ka n hw hn (fun x => ?_) ?_
  · have h1 := congrFun (congrArg Prod.fst hkaZ) x
    simp only [wtZ, Prod.smul_fst, Pi.smul_apply] at h1
    rw [nsmul_eq_mul] at h1
    exact_mod_cast h1
  · have h2 := congrArg Prod.snd hkaZ
    simp only [wtZ, Prod.smul_snd] at h2
    rw [nsmul_eq_mul] at h2
    exact_mod_cast h2

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ValuedUnif
noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain WithZero

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j}

theorem valued_unif (la : HeightOneSpectrum (𝓞 B.KO)) :
    Valued.v ((unif X la : X.Ol la) : X.Kl la) = exp (-1 : ℤ) := by
  have hu : Irreducible (unif X la) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.intValuation_exists_uniformizer la
  have hπv : Valued.v (algebraMap (𝓞 B.KO) (X.Kl la) π) = exp (-1 : ℤ) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := B.KO) (v := la) π
    rw [HeightOneSpectrum.valuation_of_algebraMap, hπ] at h
    exact h
  set o : X.Ol la := algebraMap (𝓞 B.KO) (X.Ol la) π with ho
  have ho0 : o ≠ 0 := by
    intro h0
    have : Valued.v ((o : X.Ol la) : X.Kl la) = 0 := by rw [h0]; simp
    have h2 : Valued.v (algebraMap (𝓞 B.KO) (X.Kl la) π) = 0 := this
    rw [hπv] at h2
    exact exp_ne_zero h2
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu
  have hu1 : Valued.v ((u : X.Ol la) : X.Kl la) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit
  have hv0 : Valued.v ((unif X la : X.Ol la) : X.Kl la) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro h0
    exact hu.ne_zero (Subtype.ext h0)
  have e1 : Valued.v ((o : X.Ol la) : X.Kl la) = exp (-1 : ℤ) := hπv
  rw [hk] at e1
  push_cast at e1
  rw [map_mul, map_pow, hu1, one_mul, ← exp_log hv0, ← exp_nsmul, exp_inj] at e1
  have h2 : (k : ℤ) * (-log (Valued.v ((unif X la : X.Ol la) : X.Kl la))) = 1 := by
    rw [nsmul_eq_mul] at e1; linarith
  have hk1 : (k : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
  rw [hk1, one_mul] at h2
  rw [← exp_log hv0]
  congr 1
  linarith

theorem valued_Ol (la : HeightOneSpectrum (𝓞 B.KO)) (o : X.Ol la) (m : ℕ)
    (hm : IsDiscreteValuationRing.addVal (X.Ol la) o = m) : Valued.v ((o : X.Ol la) : X.Kl la) = exp (-(m : ℤ)) := by
  have hu : Irreducible (unif X la) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  have ho0 : o ≠ 0 := by
    rintro rfl; rw [IsDiscreteValuationRing.addVal_zero] at hm; exact ENat.top_ne_natCast m hm
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu
  rw [IsDiscreteValuationRing.addVal_def' u hu n, Nat.cast_inj] at hm
  subst hm
  have hu1 : Valued.v ((u : X.Ol la) : X.Kl la) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 u.isUnit
  push_cast
  rw [map_mul, map_pow, hu1, one_mul, valued_unif, ← exp_nsmul]
  congr 1
  simp

section Kap

variable {E : PtExt X} {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF}
  {la : HeightOneSpectrum (𝓞 B.KO)} (h : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N))
  (ζ : PtsG G la) [IsDVRAt ζ] (T : CDVR) (ι : Loc ζ →+* T.V) (hι : AddValPres ζ ι)

def kapA : Kp (xplus X E hM) la G.N →+* T.Fr :=
  (phiAt ζ T.Fr ι h hι).comp (algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))

theorem kapA_Op (y : Op (xplus X E hM) la G.N) :
    kapA h ζ T ι hι (@algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) _ _ _ y) =
      algebraMap T.V T.Fr (ι (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) y)) := by
  show phiAt ζ T.Fr ι h hι (algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)
    (@algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) _ _ _ y)) = _
  rw [← IsScalarTower.algebraMap_apply (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)]
  have e : algebraMap (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) y =
      ((algebraMap (Op (xplus X E hM) la G.N) ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) y :
        ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))) : OsK (xplus X E hM) la G.w) := rfl
  rw [e, phiAt_coe]
  show algebraMap T.V T.Fr (ι (algebraMap ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (Loc ζ)
    (algebraMap (Op (xplus X E hM) la G.N) ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) y))) = _
  rw [← IsScalarTower.algebraMap_apply]

theorem unifO_irr : Irreducible (unifO (xplus X E hM) la G.N) :=
  Op.irreducible_map _ _ _ (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la)))

theorem vV_kapA_Op (y : Op (xplus X E hM) la G.N) (k : ℕ) (hk : IsDiscreteValuationRing.addVal _ y = k) :
    vV T.V (kapA h ζ T ι hι (@algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) _ _ _ y)) =
      ((ep (unifO (xplus X E hM) la G.N) ζ * k : ℕ) : ℤ) := by
  have hϖ := unifO_irr (E := E) (hM := hM) (G := G) (la := la)
  have hy : y ≠ 0 := by
    rintro rfl; rw [IsDiscreteValuationRing.addVal_zero] at hk; exact ENat.top_ne_natCast k hk
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n, Nat.cast_inj] at hk
  subst hk
  rw [kapA_Op]
  apply vV_alg_of_addVal
  have hep : IsDiscreteValuationRing.addVal (Loc ζ) (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) (unifO (xplus X E hM) la G.N)) =
      (ep (unifO (xplus X E hM) la G.N) ζ : ℕ∞) := by
    rw [coe_ep ζ h, vL_eq_addVal, ← IsScalarTower.algebraMap_apply]
  have hu0 : IsDiscreteValuationRing.addVal (Loc ζ) (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ) (u : Op (xplus X E hM) la G.N)) = 0 := by
    rw [← IsUnit.unit_spec (u.isUnit.map (algebraMap (Op (xplus X E hM) la G.N) (Loc ζ)))]
    exact IsDiscreteValuationRing.addVal_eq_zero_of_unit _
  rw [hι, map_mul, map_pow, AddValuation.map_mul, AddValuation.map_pow, hep, hu0]
  push_cast
  ring

theorem overLa_kapA : OverLa la T.V ((kapA h ζ T ι hι).comp ((algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).comp
    (algebraMap B.KO ((xplus X E hM).Kl la)))) (ep (unifO (xplus X E hM) la G.N) ζ) := by
  set io := (kapA h ζ T ι hι).comp ((algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).comp
    (algebraMap B.KO ((xplus X E hM).Kl la))) with hio
  have hint : ∀ x : 𝓞 B.KO, x ≠ 0 → vV T.V (io (algebraMap (𝓞 B.KO) B.KO x)) =
      (ep (unifO (xplus X E hM) la G.N) ζ : ℤ) * vLa la (algebraMap (𝓞 B.KO) B.KO x) := by
    intro x hx
    set o : (xplus X E hM).Ol la := algebraMap (𝓞 B.KO) ((xplus X E hM).Ol la) x with ho
    have ho0 : o ≠ 0 := by
      rw [ho, Ne, ← map_zero (algebraMap (𝓞 B.KO) ((xplus X E hM).Ol la))]
      exact fun h => hx (FaithfulSMul.algebraMap_injective _ _ h)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (mt (IsDiscreteValuationRing.addVal_eq_top_iff).1 ho0)
    have hu := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la))
    have hOp : IsDiscreteValuationRing.addVal (Op (xplus X E hM) la G.N) (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) o) = m := by
      obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho0 hu
      rw [hn, IsDiscreteValuationRing.addVal_def' u hu n] at hm
      rw [hn, map_mul, map_pow]
      have e : algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) (u : (xplus X E hM).Ol la) *
          algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) (unif (xplus X E hM) la) ^ n =
          ((u.isUnit.map (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N))).unit : Op (xplus X E hM) la G.N) *
            unifO (xplus X E hM) la G.N ^ n := by
        rw [IsUnit.unit_spec]; rfl
      erw [e, IsDiscreteValuationRing.addVal_def' _ (unifO_irr (E := E) (hM := hM) (G := G) (la := la)) n]
      exact hm.symm
    have e1 : io (algebraMap (𝓞 B.KO) B.KO x) = kapA h ζ T ι hι (@algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) _ _ _
        (algebraMap ((xplus X E hM).Ol la) (Op (xplus X E hM) la G.N) o)) := by
      show kapA h ζ T ι hι (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N) ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la)) = _
      rw [show ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la) = algebraMap ((xplus X E hM).Ol la) ((xplus X E hM).Kl la) o from rfl,
        ← IsScalarTower.algebraMap_apply]
      rfl
    have e2 : vLa la (algebraMap (𝓞 B.KO) B.KO x) = m := by
      have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := la) (algebraMap (𝓞 B.KO) B.KO x)
      have h2 : Valued.v ((o : (xplus X E hM).Ol la) : (xplus X E hM).Kl la) = exp (-(m : ℤ)) := valued_Ol la o m hm.symm
      unfold vLa
      rw [← h1]
      erw [h2]
      simp
    rw [e1, vV_kapA_Op h ζ T ι hι _ m hOp, e2]
    push_cast; ring
  refine ⟨ep_pos ζ h, fun a => ?_⟩
  by_cases ha : a = 0
  · subst ha; simp [vV, vLa]
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 B.KO) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at ha
  have hX : algebraMap (𝓞 B.KO) B.KO x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hx0
  have hY : algebraMap (𝓞 B.KO) B.KO y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hy0
  have hiX : io (algebraMap (𝓞 B.KO) B.KO x) ≠ 0 := (map_ne_zero io).2 hX
  have hiY : io (algebraMap (𝓞 B.KO) B.KO y) ≠ 0 := (map_ne_zero io).2 hY
  rw [map_div₀, div_eq_mul_inv, vV_mul hiX (inv_ne_zero hiY), vV_inv' hiY, hint x hx0, hint y hy0]
  have hvX : la.valuation B.KO (algebraMap (𝓞 B.KO) B.KO x) ≠ 0 := (Valuation.ne_zero_iff _).2 hX
  have hvY : la.valuation B.KO (algebraMap (𝓞 B.KO) B.KO y) ≠ 0 := (Valuation.ne_zero_iff _).2 hY
  unfold vLa
  rw [map_div₀, WithZero.log_div hvX hvY]
  ring

end Kap

section EvRp

variable {X' : PJ D B P j} (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) {Fd : Type} [Field Fd]
  (kap : Kp X' la N →+* Fd) (χ : X'.Forms →+* Fd)
  (hχ : ∀ (a : B.KO) (f : X'.Forms),
    χ (a • f) = kap (algebraMap (X'.Kl la) (Kp X' la N) (algebraMap B.KO (X'.Kl la) a)) * χ f)

def evRp : Rp X' la N →+* Fd :=
  letI : Algebra (Kp X' la N) Fd := kap.toAlgebra
  letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra
  letI : Algebra B.KO Fd := (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : X'.Forms →ₐ[B.KO] Fd :=
    { χ with
      commutes' := fun a => by
        show χ (algebraMap B.KO X'.Forms a) = _
        rw [Algebra.algebraMap_eq_smul_one, hχ, map_one, mul_one]
        rfl }
  let vl : X'.Vl la →ₐ[X'.Kl la] Fd :=
    Algebra.TensorProduct.lift (Algebra.ofId (X'.Kl la) Fd) g (fun _ _ => Commute.all _ _)
  (Algebra.TensorProduct.lift (Algebra.ofId (Kp X' la N) Fd) vl (fun _ _ => Commute.all _ _)).toRingHom

theorem evRp_alg (k : Kp X' la N) : evRp la N kap χ hχ (algebraMap (Kp X' la N) (Rp X' la N) k) = kap k := by
  letI : Algebra (Kp X' la N) Fd := kap.toAlgebra
  letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra
  letI : Algebra B.KO Fd := (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold evRp
  erw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.lift_tmul]
  erw [map_one, mul_one]
  rfl

theorem evRp_emb (F : X'.Forms) : evRp la N kap χ hχ (emb X' la N F) = χ F := by
  letI : Algebra (Kp X' la N) Fd := kap.toAlgebra
  letI : Algebra (X'.Kl la) Fd := (kap.comp (algebraMap (X'.Kl la) (Kp X' la N))).toAlgebra
  letI : Algebra B.KO Fd :=
    (kap.comp ((algebraMap (X'.Kl la) (Kp X' la N)).comp (algebraMap B.KO (X'.Kl la)))).toAlgebra
  haveI : IsScalarTower B.KO (X'.Kl la) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (X'.Kl la) (Kp X' la N) Fd := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have e : emb X' la N F =
      ((1 : Kp X' la N) ⊗ₜ[X'.Kl la] ((1 : X'.Kl la) ⊗ₜ[B.KO] F : X'.Vl la) :
        TensorProduct (X'.Kl la) (Kp X' la N) (X'.Vl la)) := rfl
  simp only [evRp, e]
  refine (Algebra.TensorProduct.lift_tmul _ _ _ 1 _).trans ?_
  rw [map_one, one_mul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end EvRp

end Formalism.L2.Pj
end
end
