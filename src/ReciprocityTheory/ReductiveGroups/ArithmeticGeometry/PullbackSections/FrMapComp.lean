module

public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnFrameA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

theorem spMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) := RingHom.ext fun x => by ext <;> simp [dualMap]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem frMap_refl {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have e : dualMap (AlgHom.id c.F S).toRingHom = RingHom.id _ :=
    RingHom.ext fun x => by ext <;> simp [dualMap]
  refine ⟨?_, ?_, 𝟙 _, ?_, ?_, ?_⟩
  · rw [spMap_algHom_id, Category.id_comp]
  · intro τ i
    rw [e]
    simp [spMap]
  · exact Category.id_comp _
  · rw [spMap_algHom_id]
    simp
  · intro i h
    rw [show Scheme.Hom.appLE (𝟙 (Gx y.x)) _ _ h = Scheme.Hom.app (𝟙 (Gx y.x)) ((PPx y.x).U i) from
      (Scheme.Hom.app_eq_appLE _).symm, Scheme.Hom.id_app]
    rfl

theorem frMap_trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w := by
  have hc : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := rfl
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  refine ⟨?_, ?_, pm2 ≫ pm1, ?_, ?_, ?_⟩
  · rw [hx2, hx1, hc, spMap_comp, Category.assoc]
  · intro τ i
    rw [hu2, hu1, hc, dualMap_comp, spMap_comp, Category.assoc]
  · rw [Category.assoc, hs1, hs2]
  · rw [Category.assoc, hf1, ← Category.assoc, hf2, Category.assoc, ← spMap_comp, hc]
  · intro i h
    have hb1 : ∀ p, (snd (Over.mk y.x) Xo.univ.t.G).left.base (pm1.base p) =
        (snd (Over.mk z.x) Xo.univ.t.G).left.base p := fun p => by
      rw [← hs1]; rfl
    have hb2 : ∀ p, (snd (Over.mk z.x) Xo.univ.t.G).left.base (pm2.base p) =
        (snd (Over.mk w.x) Xo.univ.t.G).left.base p := fun p => by
      rw [← hs2]; rfl
    have h1 : (PPx z.x).U i ≤ pm1 ⁻¹ᵁ (PPx y.x).U i := by
      intro p hp
      change p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp
      change pm1.base p ∈ (⋂ k, (snd (Over.mk y.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))
      simp only [Set.mem_iInter, Set.mem_preimage] at hp ⊢
      intro k
      rw [hb1]
      exact hp k
    have h2 : (PPx w.x).U i ≤ pm2 ⁻¹ᵁ (PPx z.x).U i := by
      intro p hp
      change p ∈ (⋂ k, (snd (Over.mk w.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _)) at hp
      change pm2.base p ∈ (⋂ k, (snd (Over.mk z.x) Xo.univ.t.G).left.base ⁻¹' ((Xo.univ.t.PP.L.U (i k)) : Set _))
      simp only [Set.mem_iInter, Set.mem_preimage] at hp ⊢
      intro k
      rw [hb2]
      exact hp k
    rw [← Scheme.Hom.appLE_comp_appLE pm2 pm1 _ _ _ h1 h2]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [ha1 i h1, ha2 i h2]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GamAt {D : D7} (T : Top D) : Prop :=
  ∀ (j : ℕ) (_hj : InR D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (γ : GL (Fin D.R.r) D.host.E), IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ →
    (∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y) →
    γ ∈ ((T.U j σ).X k).Γ

def HalfDiffNormSt : Prop :=
  ∀ D : D7, 0 < Ideal.absNorm D.host.𝔟 ∧
    2 * Real.log (Ideal.absNorm D.host.𝔟 : ℝ) ≤ Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)|

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}


open Classical in
theorem rdU_apply_dom {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f : Rul Xo c) (k : U.Comp) (x : (U.X k).dom) : rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := by
  show (if h : x.1 ∈ (U.X k).dom then toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0) = _
  rw [dite_eq_left x.2]

theorem rel_of_frames {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hU3 : ∀ y : FrPt Xo c (CAt σ), ∃ k, ∃ x : (U.X k).dom, ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x) y)
    (hT : ∀ k x, FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x))
    (hF : WtField Xo c) {m : ℕ} (fs : Fin m → Rul Xo c) (hfs : ∀ i, fs i ∈ sec Xo c a n) (g : Fin m → ℂ)
    (hrel : ∀ k (x : (U.X k).dom), ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) = 0)
    (z : FrPt Xo c (CAt σ)) (hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z) :
    ∑ i, g i * toC (evR Xo c (fs i) z) = 0 := by
  obtain ⟨k, x, t, hbor⟩ := hU3 z
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  have hv : ∀ i, evR Xo c (fs i) z = wchar (ex Dw a n) t * evR Xo c (fs i) (U.un k x) :=
    fun i => hF a n (fs i) (hfs i) (CAt σ) t _ z (hT k x) hz hbor
  calc ∑ i, g i * toC (evR Xo c (fs i) z)
      = ∑ i, g i * (toC (wchar (ex Dw a n) t) * toC (evR Xo c (fs i) (U.un k x))) :=
        Finset.sum_congr rfl fun i _ => by rw [hv i]; rfl
    _ = toC (wchar (ex Dw a n) t) * ∑ i, g i * toC (evR Xo c (fs i) (U.un k x)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [hrel k x, mul_zero]

end Frames

theorem jInjRd_of_wt {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (hA : BCEx (T.Q.Xo j) T.Q.c T.σ₀) (hF : WtField (T.Q.Xo j) T.Q.c) :
    JInjRd T j a n := by
  intro m b hb
  have hU : IsUnf (T.U j T.σ₀) := hM.unf j hj T.σ₀ T.good_σ₀
  set_option synthInstance.maxHeartbeats 200000 in
  have hb' := hb.map' (cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype (Submodule.ker_subtype _)
  have hfs : ∀ i, (⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i ∈ sec (T.Q.Xo j) T.Q.c a n :=
    fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) a n (b i).2
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrel : ∀ k (x : ((T.U j T.σ₀).X k).dom),
      ∑ i, g i * toC (evR (T.Q.Xo j) T.Q.c ((⇑(cusp (T.Q.Xo j) T.Q.c (T.U j) a n).subtype ∘ b) i)
        ((T.U j T.σ₀).un k x)) = 0 := by
    intro k x
    have h := congrFun (congrFun hg k) x.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← rdU_apply_dom (T.U j T.σ₀) _ k x]; rfl
  have hall := rel_of_frames (T.U j T.σ₀) hU.2.2.1 (hM.unTest j hj T.σ₀ T.good_σ₀) hF _ hfs g hrel
  let _ : Algebra T.Q.c.F ℂ := T.σ₀.toAlgebra
  have hc := indep_of_complex (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S)
    (fun φ y z => FrMap φ y z) (hM.evalWD j hj) (fun p φ y => hA p y φ)
    _ (fun i => (hfs i).1) hb' g (fun z hz => hall z hz)
  intro i
  exact congrFun hc i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

theorem indepToC_comp {K : Type*} [Field K] {σ : K →+* ℂ} {C C' : Type*} [AddCommGroup C] [Module K C]
    [AddCommGroup C'] [Module K C'] {W : Type*} [AddCommGroup W] [Module ℂ W] (J : C →ₛₗ[σ] W)
    (hJ : IndepToC J) (ι : C' →ₗ[K] C) (hι : Function.Injective ι) : IndepToC (J.comp ι) := by
  intro n b hb
  exact hJ n (fun i => ι (b i)) (hb.map' ι (LinearMap.ker_eq_bot.mpr hι))

variable {D : D7} {T : Top D}

set_option synthInstance.maxHeartbeats 400000 in
def jRec (j : ℕ) (ka : WeightFamilies.Wt D j) :
    cutR T.C j ka →ₛₗ[T.σ₀] FDSec (T.U j T.σ₀).X :=
  (rdC (T.U j) T.σ₀ (wtA ka) ka.n).comp (Submodule.inclusion (cutR_le T.C j ka))

set_option synthInstance.maxHeartbeats 400000 in
theorem spanAt_rec (h : LawsP T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka : WeightFamilies.Wt D j)
    (hJ : JInjRd T j (wtA ka) ka.n) (A : Set (FDSec (T.U j T.σ₀).X))
    (hG : holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ A)
    (hA : A ⊆ Submodule.span ℂ (jRec (T := T) j ka ''
      (((recX h) j h1 h2).shortTh ka : Set ((recB h.toLawsCore).Cusp j ka)))) :
    SpanAt ((recX h) j h1 h2) ka :=
  spanAt_of_chain ((recX h) j h1 h2) ka (jRec (T := T) j ka)
    (indepToC_comp _ hJ _ (Submodule.inclusion_injective _))
    (holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n)) A
    (fun _ => rdC_mem_holSub0 T.good_σ₀ (wtA ka) ka.n _) hG hA

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Tan

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (G : Over X0) [GrpObj G] [IsCommMonObj G]

def tanSub : Subgroup (overAt x0 (DualNumber S) ⟶ G) := (smHom (G := G) x0 0).ker

theorem mem_tanSub {v : overAt x0 (DualNumber S) ⟶ G} : v ∈ tanSub x0 G ↔ smT x0 0 v = 1 := MonoidHom.mem_ker

abbrev TanM : Type := Additive (tanSub x0 G)

variable {x0 G}

def tv (v : TanM x0 G) : overAt x0 (DualNumber S) ⟶ G := ((Additive.toMul v : tanSub x0 G) : overAt x0 (DualNumber S) ⟶ G)

theorem tv_mem (v : TanM x0 G) : smT x0 0 (tv v) = 1 := (mem_tanSub x0 G).1 (Additive.toMul v).2

theorem tanM_ext {u v : TanM x0 G} (h : tv u = tv v) : u = v := Additive.toMul.injective (Subtype.ext h)

theorem tv_add (u v : TanM x0 G) : tv (u + v) = tv u * tv v := rfl
theorem tv_zero : tv (0 : TanM x0 G) = 1 := rfl

def mkT (v : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 v = 1) : TanM x0 G := Additive.ofMul ⟨v, (mem_tanSub x0 G).2 h⟩

theorem tv_mkT (v : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 v = 1) : tv (mkT v h) = v := rfl

theorem smT_mem (a : S) (v : TanM x0 G) : smT x0 0 (smT x0 a (tv v)) = 1 := by
  rw [smT_smT, zero_mul, tv_mem]

instance : SMul S (TanM x0 G) := ⟨fun a v => mkT (smT x0 a (tv v)) (smT_mem a v)⟩

theorem tv_smul (a : S) (v : TanM x0 G) : tv (a • v) = smT x0 a (tv v) := rfl

instance : Module S (TanM x0 G) where
  one_smul v := tanM_ext (smT_unit x0 _)
  mul_smul a b v := tanM_ext (smT_smT x0 a b (tv v)).symm
  smul_zero a := tanM_ext (smT_one' x0 a)
  smul_add a u v := tanM_ext (smT_mul x0 a (tv u) (tv v))
  add_smul a b v := tanM_ext (smT_add x0 (tv v) (tv_mem v) a b)
  zero_smul v := tanM_ext (tv_mem v)

def actL (φ : G ⟶ G) [IsMonHom φ] : TanM x0 G →ₗ[S] TanM x0 G where
  toFun v := mkT (tv v ≫ φ) (by rw [smT_post, tv_mem, MonObj.one_comp])
  map_add' u v := tanM_ext (MonObj.mul_comp (tv u) (tv v) φ)
  map_smul' a v := tanM_ext (smT_post x0 a (tv v) φ).symm

theorem oact_zero {O : Type} [CommRing O] (A : OAct O G) : A.act 0 = 1 := by
  have h := A.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

def actR {O : Type} [CommRing O] (A : OAct O G) : O →+* Module.End S (TanM x0 G) where
  toFun a := @actL _ _ _ x0 G _ _ (A.act a) (A.hom a)
  map_one' := LinearMap.ext fun v => tanM_ext (by
    show tv v ≫ A.act 1 = tv v
    rw [A.one, Category.comp_id])
  map_mul' a b := LinearMap.ext fun v => tanM_ext (by
    show tv v ≫ A.act (a * b) = (tv v ≫ A.act b) ≫ A.act a
    rw [mul_comm a b, A.mul, Category.assoc])
  map_zero' := LinearMap.ext fun v => tanM_ext (by
    show tv v ≫ A.act 0 = 1
    rw [oact_zero A, MonObj.comp_one])
  map_add' a b := LinearMap.ext fun v => tanM_ext (by
    show tv v ≫ A.act (a + b) = (tv v ≫ A.act a) * (tv v ≫ A.act b)
    rw [A.add, MonObj.comp_mul])

theorem tv_actR {O : Type} [CommRing O] (A : OAct O G) (a : O) (v : TanM x0 G) :
    tv (actR A a v) = tv v ≫ A.act a := rfl

end Tan

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTie
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]

def SecTieK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))))
    (σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ)))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval σ (r ≫ m.φ) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

end Comparison₂

def RegUnifSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : V, ∀ i, σ.f i = resG t.G.left le_top ((t.G.hom).appTop.hom (toΓ V a)) * θ.f i) →
    ∀ (M : ℕ), IsUnit (M : V) →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ →
    ∀ (t₀ : 𝟙_ (Over (Sp (FractionRing V))) ⟶ tK.G)
      (F : LB.Sec (LPow tK.G tK.PP.L ((M : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      IsVtOver tK.G tK.PP M (fun u => u ^ (M ^ 2) = 1) (zCast tK.G (Nat.cast_one) θK) t₀ F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((M ^ 2 : ℕ) : ℤ))),
        SecTieK m w (M ^ 2) (zCast tK.G (natCast_sq M) F) σ

section Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def TieMv {X₀ : Scheme.{0}} {t₀ : SAB H X₀} {K : Type} [Field K] {x : Sp K ⟶ X₀} {tK : SAB H (Sp K)}
    (m1 : SABMap tK t₀ x) (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)) (k : ℕ)
    (F : LB.Sec (LPow t₀.G t₀.PP.L (k : ℤ) (Over.mk x)))
    (FK : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp K))))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (Over.mk x ⊗ t₀.G).left)
    (zp' : Z ⟶ (𝟙_ (Over (Sp K)) ⊗ tK.G).left),
    zp ≫ (snd (Over.mk x) t₀.G).left = r ≫ m1.φ → zp ≫ (fst (Over.mk x) t₀.G).left = r ≫ tK.G.hom →
    zp' ≫ (snd (𝟙_ (Over (Sp K))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t₀.G.left) → t₀.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t₀.PP.L z J → Good tK.PP.L z J' →
      sval F zp z J = ((gv w1 r z (fun _ => J (r ≫ m1.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval FK zp' z J'

end Move

def VtMoveSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X₀ : Scheme.{0}) (t₀ : SAB H X₀)
    (K : Type) [Field K] (x : Sp K ⟶ X₀) (tK : SAB H (Sp K)) (m1 : SABMap tK t₀ x)
    (w1 : LB.Iso tK.PP.L (t₀.PP.L.pull m1.φ)), RigIso m1 w1 →
    ∀ (N : ℕ) (ok : (Over.mk x ⟶ t₀.G) → Prop) (s : LB.Sec (LPow t₀.G t₀.PP.L 1 (Over.mk x)))
      (tt : Over.mk x ⟶ t₀.G) (F : LB.Sec (LPow t₀.G t₀.PP.L ((N : ℤ) ^ 2) (Over.mk x))),
      IsVtOver t₀.G t₀.PP N ok s tt F → (∀ u, ok u → u ^ (N ^ 2) = 1) →
    ∀ sK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp K)))),
      TieMv m1 w1 1 (zCast t₀.G Nat.cast_one.symm s) sK →
      ∃ (ttK : 𝟙_ (Over (Sp K)) ⟶ tK.G) (FK : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp K))))),
        IsVtOver tK.G tK.PP N (fun u => u ^ (N ^ 2) = 1) (zCast tK.G Nat.cast_one sK) ttK FK ∧
        TieMv m1 w1 (N ^ 2) (zCast t₀.G (natCast_sq N) F) (zCast tK.G (natCast_sq N) FK)

def ThetaTieSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (Tc : CDVR) (io : c.F →+* Tc.Fr) (y : letI := io.toAlgebra; FrPt Xo c Tc.Fr)
    (I : IntData Xo c Tc io y),
    letI := io.toAlgebra
    ∃ θ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
      (∀ σ : LB.Sec (LB.LinComb I.G.PP.L (K := Fin 1) (fun _ => 𝟙 I.G.G.left) (fun _ => ((1 : ℕ) : ℤ))),
        ∃! a : Tc.V, ∀ i, σ.f i = resG I.G.G.left le_top ((I.G.G.hom).appTop.hom (toΓ Tc.V a)) * θ.f i) ∧
      ∃ θK : LB.Sec (LPow I.t'.G I.t'.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp Tc.Fr)))),
        TieMv I.m1 I.w1 1 (zCast Xo.univ.t.G Nat.cast_one.symm y.s) θK ∧ SecTieK I.m2 I.w2 1 θK θ

section Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

def gsec (G : Over S) : G.left ⟶ (𝟙_ (Over S) ⊗ G).left := (lift (toUnit G) (𝟙 G)).left

theorem gsec_snd (G : Over S) : gsec G ≫ (snd (𝟙_ (Over S)) G).left = 𝟙 _ := by
  rw [gsec, ← Over.comp_left, lift_snd, Over.id_left]

theorem exists_restrict (t : SAB H S) (a : ℤ) (F : LB.Sec (LPow t.G t.PP.L a (𝟙_ (Over S)))) :
    ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => a)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
        sval σ r z J = sval F (r ≫ gsec t.G) z J := by
  have hF : FormEq (Sum.elim (fun k => gsec t.G ≫ (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) k)
      (PEmpty.elim : PEmpty → _)) (Sum.elim (fun _ : Fin 1 => a) (PEmpty.elim : PEmpty → ℤ))
      (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => a) := by
    intro U _ h
    have e := gsec_snd t.G
    simp only [Fintype.prod_sum_type, Sum.elim_inl, e, Finset.univ_eq_empty, Finset.prod_empty, _root_.mul_one]
  obtain ⟨σ, hσ⟩ := exists_sec t.PP.isLB hF
    (pullMulSec (F : LB.Sec (LB.LinComb t.PP.L (fun _ : Fin 1 => (snd (𝟙_ (Over S)) t.G).left) (fun _ => a)))
      (gsec t.G) (LB.oneGen t.PP.L) (fun _ _ => by dsimp only [LB.oneGen]; erw [map_one, map_one, _root_.mul_one]; simp [LB.LinComb]; rfl))
  refine ⟨σ, fun Z r z J hJ => ?_⟩
  refine (hσ Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one]

end Restrict

theorem isUnit_natCast_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} (Tc : CDVR)
    {io : K →+* Tc.Fr} {e : ℕ} (ho : OverLa la Tc.V io e) {M : ℕ} (hM : (M : 𝓞 K) ∉ la.asIdeal) :
    IsUnit (M : Tc.V) := by
  have h1 : la.valuation K (M : K) = 1 := by
    have e1 : (M : K) = algebraMap (𝓞 K) K (M : 𝓞 K) := by simp
    rw [e1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hM
  have h2 := ho.2 (M : K)
  rw [vLa, h1, WithZero.log_one, neg_zero, mul_zero, map_natCast] at h2
  have e2 : ((M : ℕ) : Tc.Fr) = algebraMap Tc.V Tc.Fr (M : Tc.V) := by simp
  rw [e2, vV, valV, HeightOneSpectrum.valuation_of_algebraMap, neg_eq_zero] at h2
  have hne : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) ≠ 0 := by
    refine HeightOneSpectrum.intValuation_ne_zero _ _ ?_
    intro h0
    apply hM
    have : M = 0 := by exact_mod_cast h0
    rw [this, Nat.cast_zero]; exact la.asIdeal.zero_mem
  have h3 : (IsDiscreteValuationRing.maximalIdeal Tc.V).intValuation (M : Tc.V) = 1 := by
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  rw [HeightOneSpectrum.intValuation_eq_one_iff] at h3
  by_contra hu
  exact h3 ((IsLocalRing.mem_maximalIdeal _).2 hu)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlaceB
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def AdaptAt {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ k : ℕ, ((k : 𝓞 K) ∉ la.asIdeal) ∧ Ideal.span {(k : 𝓞 E)} • Λ.La ≤ stdLat E n ∧
    Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ.La

section Ultra

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem le_nval_sum (e : ℕ) {ι : Type} (s : Finset ι) (f : ι → K') (r : EReal) (h : ∀ i ∈ s, r ≤ nval V e (f i)) :
    r ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  unfold nval at h ⊢
  split_ifs with hs
  · exact le_top
  · have hne : s.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty] at hn
      exact hs (by rw [hn, Finset.sum_empty])
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s (fun i => valV V (f i)) hne
    have hle : valV V (∑ i ∈ s, f i) ≤ valV V (f i) := Valuation.map_sum_le _ hmax
    have hfi : f i ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hle
      exact hs ((Valuation.zero_iff _).1 (le_antisymm hle zero_le'))
    have h1 := h i hi
    rw [if_neg hfi] at h1
    refine h1.trans ?_
    have hlog := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hs) ((Valuation.ne_zero_iff _).2 hfi)).2 hle
    refine EReal.coe_le_coe_iff.2 ?_
    have hl : ((-(valV V (f i)).log : ℤ) : ℝ) ≤ ((-(valV V (∑ i ∈ s, f i)).log : ℤ) : ℝ) := by
      exact_mod_cast neg_le_neg hlog
    exact div_le_div_of_nonneg_right hl (Nat.cast_nonneg e)

end Ultra

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IsMixedOver
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Mixed

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

abbrev endT (T : Over X) (φ : A ⟶ A) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ φ)

def IsNormEnd (φ : A ⟶ A) (a b : ℤ)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) : Prop :=
  LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (eSec A))
    (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))

def IsMixedOver (φ : A ⟶ A) (n k : ℕ) {T : Over X} (ok : (T ⟶ A) → Prop) (s : LB.Sec (LPow A L.L 1 T))
    (t₁ b : T ⟶ A) (hh : LB.Sec (LPow A L.L (k : ℤ) T)) : Prop :=
  ∃ (F₁ : LB.Sec (LPow A L.L ((n : ℤ) ^ 2) T))
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (h₁ : LB.Sec (LPow A L.L (k : ℤ) T)) (U : ThetaGrp A L.L (k : ℤ) T),
    IsVtOver A L n ok s t₁ F₁ ∧ α₀.IsGen ∧ IsNormEnd A L φ (k : ℤ) ((n : ℤ) ^ 2) α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (endT A T φ) (snd T A ≫ φ) (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ ∧
    SymLift A L.L (k : ℤ) k b U ∧ IsActOf A L.L (k : ℤ) U h₁ hh

end Mixed

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeB
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

def cpθ : ChartPull (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (PPx x) (gxU x) :=
  (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk x) Xo.univ.t.G).left).cp
    (PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)) (gxU x) (gxU_snd x)

def cpV : ChartPull (PPx x) (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (gxV x) :=
  (PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).cp
    (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk x) Xo.univ.t.G).left) (gxV x) (gxV_fst x)

def cpσ : ChartPull ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ)))
    (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)) (pullback.fst _ (spMap ψ)) :=
  chartPullPull _ _ _ rfl

def cpU' : ChartPull ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ))) (PPx (spMap ψ ≫ x)) (bcU ψ x) :=
  (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left).cp
    ((PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).pull _) (bcU ψ x) (bcU_snd ψ x)

def cpV' : ChartPull (PPx (spMap ψ ≫ x)) ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).pull
      (pullback.fst (pullback.snd Xo.univ.t.G.hom x) (spMap ψ))) (bcV ψ x) :=
  ((PullOf.lin (K := PUnit) Xo.univ.t.PP.L (pullback.fst Xo.univ.t.G.hom x)).pull _).cp
    (PullOf.lin (K := Fin 1) Xo.univ.t.PP.L (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left) (bcV ψ x)
    (bcV_snd' ψ x)

def cpS : ChartPull (PPx (spMap ψ ≫ x)) (PPx x) (bcPm ψ x) :=
  cpSame Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left)
    (fun _ => (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left) (fun _ => 1) (bcPm ψ x) (fun _ => bcPm_snd ψ x)

def tA : SAB H (Sp S) := sabT ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt x Xo.univ.t
def mA : SABMap (tA x) Xo.univ.t x := sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt x Xo.univ.t

def tB : SAB H (Sp T) := sabT ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap ψ) (tA x)
def mB : SABMap (tB ψ x) (tA x) (spMap ψ) := sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap ψ) (tA x)

def θA (s0 : LB.Sec (PPx x)) : LB.Sec (tA x).PP.L := secCP (cpθ x) s0

def σB (s0 : LB.Sec (PPx x)) : LB.Sec (tB ψ x).PP.L := secCP (cpσ ψ x) (θA x s0)

theorem hθ_of (s0 : LB.Sec (PPx x)) (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i)
    (σ : LB.Sec (tA x).PP.L) : ∃ a : S, ∀ i, σ.f i = constFn (tA x).G.hom _ a * (θA x s0).f i := by
  obtain ⟨a, ha, -⟩ := hgen (secCP (cpV x) σ)
  refine ⟨a, (sec_eq_iff _ σ (θA x s0) a).2 fun i q hq => ?_⟩
  have hJ : gxU x q ∈ (PPx x).U (fun _ => i PUnit.unit) := (cpθ x).le i hq
  have h2 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (gxU x) q hJ ((scal_eq_iff x _ _ a).1 ha _ (gxU x q) hJ)
  rw [gs_secCP (cpV x) σ (gxU x) q _ hJ, gxU_gxV, gxU_fst] at h2
  have e3 : gs (𝟙 _) q ((tA x).PP.L.U i) ((θA x s0).f i) =
      gs (gxU x) q ((PPx x).U (fun _ => i PUnit.unit)) (s0.f (fun _ => i PUnit.unit)) :=
    (gs_secCP (cpθ x) s0 (𝟙 _) q i hq).trans (by rw [Category.id_comp]; rfl)
  rw [e3]
  exact h2

theorem hσ_of (s0 : LB.Sec (PPx x)) (y : (tB ψ x).G.left) (j : PUnit → Xo.univ.t.PP.L.ι)
    (k : PUnit → PUnit → Xo.univ.t.PP.L.ι) (hj : (mB ψ x).φ y ∈ (tA x).PP.L.U j) (hk : y ∈ (tB ψ x).PP.L.U k) :
    gs (mB ψ x).φ y _ ((θA x s0).f j) =
      (gw (idIso ((tA x).PP.L.pull (mB ψ x).φ)) (𝟙 _) y j k).val * gs (𝟙 _) y _ ((σB ψ x s0).f k) := by
  have hk' : (mB ψ x).φ y ∈ (tA x).PP.L.U (k PUnit.unit) := mem_pull.1 hk
  have e1 := gm_pull_g (tA x).PP.L (mB ψ x).φ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hk
  rw [Category.id_comp] at e1
  have e2 : gs (𝟙 _) y ((tB ψ x).PP.L.U k) ((σB ψ x s0).f k) =
      gs (mB ψ x).φ y ((tA x).PP.L.U (k PUnit.unit)) ((θA x s0).f (k PUnit.unit)) :=
    (gs_secCP (cpσ ψ x) (θA x s0) (𝟙 _) y k hk).trans (by rw [Category.id_comp]; rfl)
  rw [e2, gs_compat (θA x s0) (mB ψ x).φ y hj hk']
  exact congrArg (· * _) (congrArg Units.val e1.symm)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PPSemichar
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj MonObj
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem hermForm_zero_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  unfold hermForm
  simp

theorem hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  unfold hermForm
  rw [add_dotProduct]

theorem hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  unfold hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hji : star (Hm i j) = Hm j i := by
    have := congrFun (congrFun hH j) i
    rwa [Matrix.conjTranspose_apply] at this
  simp only [Pi.star_apply, star_star, hji]
  ring

theorem hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (t • z) w = t * hermForm Hm z w := by
  unfold hermForm
  rw [smul_dotProduct, smul_eq_mul]

theorem hermForm_real_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z ((t : ℂ) • w) = t * hermForm Hm z w := by
  unfold hermForm
  have h1 : star ((t : ℂ) • w) = (t : ℂ) • star w := by
    ext i
    simp [Complex.conj_ofReal]
  rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

section Prim

variable {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)

end Prim

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMulPf
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem lieFacAdd : LieFacAddSt := by
  intro E _ _ _ H Dw x a a'
  simp only [Formalism.L2.Pj.lieFac, ← Real.exp_add]
  congr 1
  simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  ring

theorem pnormMul : PnormMulSt := by
  intro E _ _ _ r X la la' P Q x hx
  have hne : ∀ τ j, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ j ≠ 0 := fun τ j h => by
    have h1 := (hx τ).2 j
    rw [h, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl 0 h1
  have hpos : ∀ τ (i : Fin r), 0 < ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := fun τ i =>
    norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))
  have key : ∀ τ (i : Fin r), ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-((la + la') τ i : ℝ) / 2) =
      ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la τ i : ℝ) / 2) *
        ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la' τ i : ℝ) / 2) := fun τ i => by
    rw [← Real.rpow_add (hpos τ i)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [Pi.mul_apply, norm_mul]
  simp only [key, Finset.prod_mul_distrib]
  ring

theorem pnorm_nonneg' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : 0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x)

theorem supCMul : SupCMulSt := by
  intro E _ _ _ H Dw l Xo c r U x σ a a' n n' f g _ hn hn' hf hg
  unfold supC
  rw [lieFacAdd E H Dw x a a', rdU_mul]
  have hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n' :=
    funext fun k => laU_add (U σ) a a' n n' hn hn' k
  rw [hla]
  have hE : Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g) ≤
      Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) *
        Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) := by
    unfold Formalism.L2.Pj.supE
    refine iSup_le fun p => ?_
    have e := pnormMul E r ((U σ).X p.1) (laU (U σ) a n p.1) (laU (U σ) a' n' p.1) (rdU (U σ) f p.1)
      (rdU (U σ) g p.1) p.2.1 p.2.2
    refine le_trans (le_of_eq ?_) (mul_le_mul' (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a n q.1) (rdU (U σ) f q.1) q.2)) p)
      (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a' n' q.1) (rdU (U σ) g q.1) q.2)) p))
    rw [← ENNReal.ofReal_mul (pnorm_nonneg' _ _ _ _)]
    exact congrArg ENNReal.ofReal e
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hf hg) hE
  rw [ENNReal.toReal_mul] at h1
  unfold Formalism.L2.Pj.supN
  calc lieFac Dw x a * lieFac Dw x a' *
        (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g)).toReal
      ≤ lieFac Dw x a * lieFac Dw x a' * ((Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f)).toReal *
          (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g)).toReal) :=
        mul_le_mul_of_nonneg_left h1 (mul_pos (lieFac_pos _ _ _) (lieFac_pos _ _ _)).le
    _ = _ := by ring

theorem recSubMul : RecSubMulSt := by
  intro D T h j hj σ w w' F G H hH
  have hFm : (F : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := cutR_le T.C j w F.2
  have hGm : (G : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w') w'.n := cutR_le T.C j w' G.2
  have hprod : (H : T.R j) = (F : T.R j) * (G : T.R j) := by
    have h1 := congrArg (fun x : AddMonoidAlgebra (T.R j) (Deg D j) => x.coeff (deg (Formalism.MainNotions.WeightAlgebra.wadd w w'))) hH
    change (incG deg (cutR T.C j) (Formalism.MainNotions.WeightAlgebra.wadd w w') H).coeff _ =
      (incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G).coeff _ at h1
    rw [incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, ← deg_wadd] at h1
    simpa [AddMonoidAlgebra.coeff_single] using h1
  show cutN T.C T.Ns j (Formalism.MainNotions.WeightAlgebra.wadd w w') σ H ≤ cutN T.C T.Ns j w σ F * cutN T.C T.Ns j w' σ G
  unfold cutN
  rw [if_pos hj, if_pos hj, if_pos hj]
  unfold Core.Ns
  rw [hprod, wtA_wadd]
  exact supCMul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (goodEmb_goodOf _ σ) w.n_even w'.n_even
    (supE_cusp_ne_top (goodEmb_goodOf _ σ) hFm) (supE_cusp_ne_top (goodEmb_goodOf _ σ) hGm)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
