module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frMapUniq_scal_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x (1 : S) i = 1 := by
  unfold scal ReciprocityTheory.ChartRestriction.G.Out.liftFun
  simp only [map_one]

theorem frMapUniq_chart_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem frMapUniq_refl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    FrMap (AlgHom.id c.F S) y y := by
  have eid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 _ := Spec.map_id _
  have did : spMap (dualMap (AlgHom.id c.F S).toRingHom) = 𝟙 _ := by
    have hd : dualMap (RingHom.id S) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    show spMap (dualMap (RingHom.id S)) = _
    rw [hd]
    exact Spec.map_id _
  refine ⟨by rw [eid, Category.id_comp], fun τ i => by rw [did, Category.id_comp], 𝟙 _, by simp,
    by rw [eid]; simp, ?_⟩
  intro i h
  have e : Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx y.x).presheaf.map_id]
    rfl
  rw [e, CommRingCat.hom_id, RingHom.id_apply]

theorem frMap_unique_refl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), (∀ z z' : FrPt Xo c T, FrMap φ y z → FrMap φ y z' → z = z') ∧ FrMap (AlgHom.id c.F S) y y ∧ ∀ z : FrPt Xo c T, FrMap φ y z ↔ (z.x = spMap φ.toRingHom ≫ y.x ∧ (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧ SecBC φ.toRingHom 1 y.x z.x y.s z.s) := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y
  refine ⟨?_, frMapUniq_refl y, fun z => ?_⟩
  · rintro ⟨x, xo, u, t, e, b, s, g⟩ ⟨x', xo', u', t', e', b', s', g'⟩ ⟨hx, hu, pm, hs, hf, ha⟩
      ⟨hx', hu', pm', hs', hf', ha'⟩
    dsimp only at hx hu hx' hu' pm pm' hs hf ha hs' hf' ha'
    have h1 : x = x' := hx.trans hx'.symm
    subst h1
    have h2 : u = u' := by
      funext τ i
      exact (hu τ i).trans (hu' τ i).symm
    subst h2
    have h3 : pm = pm' := by
      apply pullback.hom_ext
      · exact hf.trans hf'.symm
      · exact hs.trans hs'.symm
    subst h3
    have h4 : s = s' := by
      have : s.f = s'.f := by
        funext i
        have h := frMapUniq_chart_le pm hs i
        exact (ha i h).symm.trans (ha' i h)
      cases s; cases s'
      congr
    subst h4
    rfl
  · have k : ∀ i : (PPx y.x).ι, scal y.x (1 : S) i * y.s.f i = y.s.f i := fun i => by
      rw [frMapUniq_scal_one, _root_.one_mul]
    constructor
    · rintro ⟨hx, hu, pm, hs, hf, ha⟩
      exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).trans (ha i h)⟩
    · rintro ⟨hx, hu, pm, hs, hf, ha⟩
      exact ⟨hx, hu, pm, hs, hf, fun i h => (congrArg _ (k i)).symm.trans (ha i h)⟩

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_baseChange_unique_refl_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), (∀ z z' : FrPt Xo c T, FrMap φ y z → FrMap φ y z' → z = z') ∧ FrMap (AlgHom.id c.F S) y y ∧ ∀ z : FrPt Xo c T, FrMap φ y z ↔ (z.x = spMap φ.toRingHom ≫ y.x ∧ (∀ τ i, z.u τ i = spMap (dualMap φ.toRingHom) ≫ y.u τ i) ∧ SecBC φ.toRingHom 1 y.x z.x y.s z.s) := by
  exact @GlobalTheory.Frames.frMap_unique_refl_iff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.Frames.ChgBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem dualMap_alg {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    (dualMap φ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp φ :=
  RingHom.ext fun a => by
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_eps {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) :
    (dualMap φ).comp (epsMul a) = (epsMul (φ a)).comp (dualMap φ) :=
  RingHom.ext fun x => by
    ext <;> simp [dualMap, epsMul, mul_comm]

theorem isCombAt_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} (hx : x' = spMap φ ≫ x) {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    {v' : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, v' j = spMap (dualMap φ) ≫ v j)
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} {w' : Sp (DualNumber T) ⟶ Xo.univ.t.G.left}
    (hw : w' = spMap (dualMap φ) ≫ w) (h : IsCombAt x v cf w) : IsCombAt x' v' (fun j => φ (cf j)) w' := by
  obtain ⟨u, hu, hprod⟩ := h
  let D : tEps x' ⟶ tEps x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap T (DualNumber T)) ≫ x'
    rw [hx, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_alg])
  have hL : ∀ L : List (tEps x ⟶ Xo.univ.t.G), (L.map (D ≫ ·)).prod = D ≫ L.prod := by
    intro L
    induction L with
    | nil => simp [MonObj.comp_one]
    | cons a L ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih, MonObj.comp_mul]
  refine ⟨fun j => D ≫ u j, fun j => ?_, ?_⟩
  · show spMap (dualMap φ) ≫ (u j).left = spMap (epsMul (φ (cf j))) ≫ v' j
    rw [hu j, hv j, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, dualMap_eps]
  · have e : (List.ofFn fun j => D ≫ u j) = (List.ofFn u).map (D ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, hL, Over.comp_left, hprod, hw]
    rfl

theorem isCombAt_unique {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' := by
  obtain ⟨u, hu, hprod⟩ := h
  obtain ⟨u', hu', hprod'⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [← hprod, ← hprod', e]

theorem ppx_le_cov {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem scal_pull {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm

theorem can_exists {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) :
    ∃ pm : Gx x' ⟶ Gx x, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ := by
  let pm : Gx x' ⟶ Gx x :=
    pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ)
      (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ ≫ x =
          pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition)
  exact ⟨pm, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem gx_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Z : Scheme.{0}} {p q : Z ⟶ Gx x}
    (hs : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left) : p = q :=
  pullback.hom_ext (f := (Over.mk x).hom) (g := Xo.univ.t.G.hom) hf hs

theorem square {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {y y' : Sp S ⟶ Xo.X}
    {z z' : Sp T ⟶ Xo.X} (pmA : Gx z ⟶ Gx y) (pmB : Gx z' ⟶ Gx y') (pmC : Gx y' ⟶ Gx y) (pm : Gx z' ⟶ Gx z)
    (hsA : pmA ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk z) Xo.univ.t.G).left)
    (hfA : pmA ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk z) Xo.univ.t.G).left ≫ spMap φ)
    (hsB : pmB ≫ (snd (Over.mk y') Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hfB : pmB ≫ (fst (Over.mk y') Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap φ)
    (hsC : pmC ≫ (snd (Over.mk y) Xo.univ.t.G).left = (snd (Over.mk y') Xo.univ.t.G).left)
    (hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left ≫ spMap (RingHom.id S))
    (hs : pm ≫ (snd (Over.mk z) Xo.univ.t.G).left = (snd (Over.mk z') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left ≫ spMap (RingHom.id T))
    (sy : LB.Sec (PPx y)) (sy' : LB.Sec (PPx y')) (sz : LB.Sec (PPx z))
    (haA : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z).U i ≤ pmA ⁻¹ᵁ (PPx y).U i),
      (pmA.appLE _ _ h).hom (sy.f i) = sz.f i)
    (haC : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y').U i ≤ pmC ⁻¹ᵁ (PPx y).U i),
      (pmC.appLE _ _ h).hom (scal y a i * sy.f i) = sy'.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx z').U i ≤ pm ⁻¹ᵁ (PPx z).U i)
    (hB : (PPx z').U i ≤ pmB ⁻¹ᵁ (PPx y').U i) :
    (pm.appLE _ _ h).hom (scal z (φ a) i * sz.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
  rw [spMap_id] at hfC hf
  replace hfC : pmC ≫ (fst (Over.mk y) Xo.univ.t.G).left = (fst (Over.mk y') Xo.univ.t.G).left :=
    hfC.trans (Category.comp_id _)
  replace hf : pm ≫ (fst (Over.mk z) Xo.univ.t.G).left = (fst (Over.mk z') Xo.univ.t.G).left :=
    hf.trans (Category.comp_id _)
  have hcomp : pm ≫ pmA = pmB ≫ pmC := by
    apply gx_ext
    · rw [Category.assoc, hsA, hs, Category.assoc, hsC, hsB]
    · rw [Category.assoc, hfA, Category.assoc, hfC]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap φ) hf)).trans hfB.symm
  have hA := ppx_le_cov pmA hsA i
  have hC := ppx_le_cov pmC hsC i
  have key : ∀ (q : Gx z' ⟶ Gx y), q = pmB ≫ pmC → ∀ hh : (PPx z').U i ≤ q ⁻¹ᵁ (PPx y).U i,
      (q.appLE _ _ hh).hom (scal y a i * sy.f i) = (pmB.appLE _ _ hB).hom (sy'.f i) := by
    rintro q rfl hh
    have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC ≫ pmB.appLE _ _ hB :=
      (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC hB).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC]
  rw [← haA i hA, ← scal_pull φ pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
  have e2 := congrArg (fun f => f.hom (scal y a i * sy.f i))
    (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [e2]
  exact key _ hcomp _

theorem frChg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : S), FrChg g a y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z') := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ φ y y' z z' g a hb hz
  obtain ⟨hx, hcomb, pmC, hsC, hfC, haC⟩ := hb
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  constructor
  · rintro ⟨hx2, hu2, pmB, hsB, hfB, haB⟩
    have hxz : z'.x = z.x := by rw [hx2, hx1, hx]
    refine ⟨hxz, fun τ i => isCombAt_pull φ.toRingHom hx1 (hu1 τ) (hu2 τ i) (hcomb τ i), ?_⟩
    obtain ⟨pm, hs, hf⟩ := can_exists (RingHom.id T) (x := z.x) (x' := z'.x)
      (by rw [spMap_id, Category.id_comp, hxz])
    refine ⟨pm, hs, hf, fun i h => ?_⟩
    have hB := ppx_le_cov pmB hsB i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).trans
      (haB i hB)
  · rintro ⟨hxz, hc2, pm, hs, hf, ha⟩
    have hx2 : z'.x = spMap φ.toRingHom ≫ y'.x := by rw [hxz, hx1, hx]
    refine ⟨hx2, fun τ i => isCombAt_unique (hc2 τ i)
      (isCombAt_pull φ.toRingHom hx1 (hu1 τ) rfl (hcomb τ i)), ?_⟩
    obtain ⟨pmB, hsB, hfB⟩ := can_exists φ.toRingHom hx2
    refine ⟨pmB, hsB, hfB, fun i hB => ?_⟩
    have h := ppx_le_cov pm hs i
    exact (square φ.toRingHom a pmA pmB pmC pm hsA hfA hsB hfB hsC hfC hs hf y.s y'.s z.s haA haC i h hB).symm.trans
      (ha i h)

end GlobalTheory.Frames.ChgBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameChange_comm_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T) (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : S), FrChg g a y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ a) z z') := by
  first | exact @GlobalTheory.Frames.ChgBC.frChg_baseChange | exact GlobalTheory.Frames.ChgBC.frChg_baseChange | (intros; apply GlobalTheory.Frames.ChgBC.frChg_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.SecCalc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem scal_mul' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a * b))) = _
  rw [map_mul, map_mul, map_mul]
  rfl

theorem scal_add' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a + b) i = scal x a i + scal x b i := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S (a + b))) = _
  rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  rfl

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x 1 i = 1 := by
  show ((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S 1)) = _
  rw [map_one, map_one, map_one]

theorem ppx_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (Formalism.L2.PjFree.gxFst (x)) = (Formalism.L2.PjFree.gxFst (x')))
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  dsimp only [Formalism.L2.PjFree.gxFst] at e
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem scal_pull' {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (Formalism.L2.PjFree.gxSnd (x)) = (Formalism.L2.PjFree.gxSnd (x')) ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm

theorem pm_ext {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {Y : Scheme.{0}} (p q : Y ⟶ Gx x)
    (hs : p ≫ (snd (Over.mk x) Xo.univ.t.G).left = q ≫ (snd (Over.mk x) Xo.univ.t.G).left)
    (hf : p ≫ (fst (Over.mk x) Xo.univ.t.G).left = q ≫ (fst (Over.mk x) Xo.univ.t.G).left) : p = q :=
  pullback.hom_ext (f := (Over.mk x).hom) (g := Xo.univ.t.G.hom) hf hs

theorem pm_exists {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (hx : x' = spMap φ ≫ x) : ∃ pm : Gx x' ⟶ Gx x,
      pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left ∧
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ :=
  ⟨pullback.lift (pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ)
      (pullback.snd (Over.mk x').hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x').hom Xo.univ.t.G.hom ≫ spMap φ ≫ x =
          pullback.snd (Over.mk x').hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition), pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem secBC_iff {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (a : S) {x : Sp S ⟶ Xo.X}
    {x' : Sp T ⟶ Xo.X} (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) :
    SecBC φ a x x' s s' ↔ ∀ i : Fin 1 → Xo.univ.t.PP.L.ι,
      s'.f i = scal x' (φ a) i * (pm.appLE _ _ (ppx_le pm hs i)).hom (s.f i) := by
  constructor
  · rintro ⟨q, qs, qf, ha⟩ i
    obtain rfl : q = pm := pm_ext _ _ (qs.trans hs.symm) (qf.trans hf.symm)
    rw [← ha i (ppx_le q hs i), map_mul, scal_pull' φ q hf]
  · intro h
    refine ⟨pm, hs, hf, fun i hi => ?_⟩
    rw [h i, map_mul, scal_pull' φ pm hf]

theorem sec_calc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T U : Type) [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (x'' : Sp U ⟶ Xo.X), x' = spMap φ ≫ x → x'' = spMap ψ ≫ x' → (∀ (a : S) s s' s'', SecBC φ a x x' s s' → (SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'')) ∧ (∀ (a : S) (s t : LB.Sec (PPx x)), SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i) ∧ (∀ (a : S) s (s' t' : LB.Sec (PPx x')), SecBC φ 1 x x' s s' → (SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i)) ∧ (∀ (a b : S) i, scal x (a * b) i = scal x a i * scal x b i ∧ scal x (a + b) i = scal x a i + scal x b i ∧ scal x 1 i = 1) := by
  intro E _ _ _ H Dw l Xo S T U _ _ _ φ ψ x x' x'' hx hx'
  obtain ⟨p, ps, pf⟩ := pm_exists φ hx
  obtain ⟨q, qs, qf⟩ := pm_exists ψ hx'
  refine ⟨fun a s s' s'' h => ?_, fun a s t => ?_, fun a s s' t' h => ?_,
    fun a b i => ⟨scal_mul' x a b i, scal_add' x a b i, scal_one' x i⟩⟩
  · have rs : (q ≫ p) ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x'') Xo.univ.t.G).left := by
      rw [Category.assoc, ps, qs]
    have rf : (q ≫ p) ≫ (fst (Over.mk x) Xo.univ.t.G).left =
        (fst (Over.mk x'') Xo.univ.t.G).left ≫ spMap (ψ.comp φ) := by
      rw [Category.assoc, pf, ← Category.assoc, qf, Category.assoc, spMap_comp']
    rw [secBC_iff φ a p ps pf] at h
    rw [secBC_iff ψ 1 q qs qf, secBC_iff (ψ.comp φ) a (q ≫ p) rs rf]
    refine forall_congr' fun i => ?_
    have e : (q ≫ p).appLE _ _ (ppx_le (q ≫ p) rs i) = p.appLE _ _ (ppx_le p ps i) ≫ q.appLE _ _ (ppx_le q qs i) :=
      (Scheme.Hom.appLE_comp_appLE q p _ _ _ _ _).symm
    rw [e, CommRingCat.hom_comp, RingHom.comp_apply, h i, map_one, scal_one' x'' i, _root_.one_mul, map_mul,
      scal_pull' ψ q qf]
    rfl
  · rw [secBC_iff (RingHom.id S) a (𝟙 (Gx x)) (Category.id_comp _)
      (by rw [spMap_id']; exact (Category.id_comp _).trans (Category.comp_id _).symm)]
    refine forall_congr' fun i => ?_
    have e : ∀ hh : (PPx x).U i ≤ (𝟙 (Gx x) : Gx x ⟶ Gx x) ⁻¹ᵁ (PPx x).U i,
        (𝟙 (Gx x) : Gx x ⟶ Gx x).appLE _ _ hh = 𝟙 _ := by
      intro hh
      exact (Scheme.Hom.appLE_eq_app (𝟙 (Gx x) : Gx x ⟶ Gx x)).trans (Scheme.Hom.id_app _)
    rw [e]
    rfl
  · rw [secBC_iff φ 1 p ps pf] at h
    rw [secBC_iff φ a p ps pf]
    refine forall_congr' fun i => ?_
    rw [h i, map_one, scal_one' x' i, _root_.one_mul]

end GlobalTheory.Frames.SecCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledBaseChange_fibreSection_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T U : Type) [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (x'' : Sp U ⟶ Xo.X), x' = spMap φ ≫ x → x'' = spMap ψ ≫ x' → (∀ (a : S) s s' s'', SecBC φ a x x' s s' → (SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'')) ∧ (∀ (a : S) (s t : LB.Sec (PPx x)), SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i) ∧ (∀ (a : S) s (s' t' : LB.Sec (PPx x')), SecBC φ 1 x x' s s' → (SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i)) ∧ (∀ (a b : S) i, scal x (a * b) i = scal x a i * scal x b i ∧ scal x (a + b) i = scal x a i + scal x b i ∧ scal x 1 i = 1) := by
  first | exact @GlobalTheory.Frames.SecCalc.sec_calc | exact GlobalTheory.Frames.SecCalc.sec_calc | (intros; apply GlobalTheory.Frames.SecCalc.sec_calc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSection
noncomputable section

namespace GlobalTheory.Frames.SecPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem exists_pull_linComb {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (φ' : K → (Z ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (e : (fun k => h ≫ φ k) = φ') (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (j : K → L.ι)
      (hle : (LB.LinComb L φ' ε).U j ≤ h ⁻¹ᵁ (LB.LinComb L φ ε).U j), (h.appLE _ _ hle).hom (s.f j) = s'.f j := by
  subst e
  exact ⟨DVR.pullSec L φ ε s h, fun _ _ => rfl⟩

theorem lbSec_ext {X : Scheme.{0}} {L : LB X} {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t
  congr 1
  exact funext h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem ppx_chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem res_res_top {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (g : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom g) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom g := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem scal_res {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (i j : (PPx x).ι) :
    ((Gx x).presheaf.map (homOfLE (inf_le_left : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U i)).op).hom (scal x a i) =
      ((Gx x).presheaf.map (homOfLE (inf_le_right : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U j)).op).hom
        (scal x a j) := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun]
  rw [res_res_top, res_res_top]

def gxMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') : Gx x' ⟶ Gx x :=
  ((Over.homMk (spMap ψ) h : Over.mk x' ⟶ Over.mk x) ▷ Xo.univ.t.G).left

theorem gxMap_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') :
    gxMap ψ x x' h ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left := by
  unfold gxMap
  rw [← Over.comp_left, whiskerRight_snd]

theorem gxMap_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') :
    gxMap ψ x x' h ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap ψ := by
  unfold gxMap
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  rfl

theorem gx_hom_ext {S : Type} [CommRing S] {W : Scheme.{0}} {x : Sp S ⟶ Xo.X} (f₁ f₂ : W ⟶ Gx x)
    (h₁ : f₁ ≫ (fst (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : f₁ ≫ (snd (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (snd (Over.mk x) Xo.univ.t.G).left) : f₁ = f₂ :=
  Over.tensorObj_ext f₁ f₂ h₁ h₂

def scalSec {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) : LB.Sec (PPx x) where
  f i := scal x a i * s.f i
  compat i j := by
    rw [map_mul, map_mul, s.compat i j, scal_res x a i j]
    ring

theorem existsUnique_secBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (a : S) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s : LB.Sec (PPx x), ∃! s' : LB.Sec (PPx x'), SecBC φ a x x' s s' := by
  intro E _ _ _ H Dw l Xo S T _ _ φ a x x' hx s
  have hs := gxMap_snd φ x x' hx.symm
  have hf := gxMap_fst φ x x' hx.symm
  obtain ⟨s', hs'⟩ := exists_pull_linComb Xo.univ.t.PP.L (K := Fin 1)
    (fun _ => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (snd (Over.mk x') Xo.univ.t.G).left) _
    (gxMap φ x x' hx.symm) (funext fun _ => hs) (scalSec x a s)
  refine ⟨s', ⟨_, hs, hf, hs'⟩, ?_⟩
  rintro t ⟨pm, ps, pf, ht⟩
  obtain rfl : pm = gxMap φ x x' hx.symm :=
    gx_hom_ext _ _ (pf.trans hf.symm) (ps.trans hs.symm)
  exact lbSec_ext fun i => (ht i (ppx_chart_le _ hs i)).symm.trans (hs' i (ppx_chart_le _ hs i))

end GlobalTheory.Frames.SecPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (a : S) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s : LB.Sec (PPx x), ∃! s' : LB.Sec (PPx x'), SecBC φ a x x' s s' := by
  first | exact @GlobalTheory.Frames.SecPull.existsUnique_secBC | exact GlobalTheory.Frames.SecPull.existsUnique_secBC | (intros; apply GlobalTheory.Frames.SecPull.existsUnique_secBC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReducedFiniteTypeIffTestRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem reduced_finiteType_iff_testRing :
    ∀ (K : Type) [Field K], (∀ (R : Type) [CommRing R] [Algebra K R], Algebra.FiniteType K R → IsReduced R → ∃ p : TRing K, Nonempty (p.R ≃ₐ[K] R)) ∧ ∀ p : TRing K, Algebra.FiniteType K p.R ∧ IsReduced p.R := by
  intro K _
  refine ⟨fun R _ _ hft hred => ?_, fun p => ⟨inferInstance, ?_⟩⟩
  · obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
    have hrad : (RingHom.ker f).IsRadical := by
      intro x hx
      obtain ⟨m, hm⟩ := hx
      rw [RingHom.mem_ker, map_pow] at hm
      exact (RingHom.mem_ker).2 (IsReduced.eq_zero _ ⟨m, hm⟩)
    exact ⟨⟨n, RingHom.ker f, hrad⟩, ⟨Ideal.quotientKerAlgEquivOfSurjective hf⟩⟩
  · exact (Ideal.isRadical_iff_quotient_reduced p.I).1 p.3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFactorOpenImmersion
namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem exists_factor_openImmersion {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (j : Sp R ⟶ X)
    [IsOpenImmersion j] (x : Sp S ⟶ X) (p : Sp S) (hp : x p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] (lam : S →+* T), IsUnit (lam g) →
      ∃ ψ : R →+* T, spMap lam ≫ x = spMap ψ ≫ j := by
  have hU : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage x.continuous
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hU
  refine ⟨g, hpg, fun T _ lam hu => ?_⟩
  have hr : Set.range (spMap lam ≫ x) ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap lam q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
      intro h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
    exact hsub hq
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j (spMap lam ≫ x) hr)).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem openChart_factor_near_prime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R), OpenChart j y₀ → ∀ (S : Type) [CommRing S] [Algebra c.F S] (xF : Sp S ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) → ∀ p : Sp S, xF p ∈ Set.range j → ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) → ∃ ψ : R →ₐ[c.F] T, spMap lam.toRingHom ≫ xF = spMap ψ.toRingHom ≫ j := by
  intro E _ _ _ H Dw l Xo c R _ _ j y₀ hj S _ _ xF hx p hp
  haveI := hj.1
  obtain ⟨g, hg, h⟩ := exists_factor_openImmersion j xF p hp
  refine ⟨g, hg, fun T _ _ lam hu => ?_⟩
  obtain ⟨ψ, hψ⟩ := h T lam.toRingHom hu
  have h2 := congrArg (· ≫ pullback.snd _ _) hψ
  simp only [Category.assoc] at h2
  rw [hx, hj.2.2, ← Spec.map_comp, ← Spec.map_comp] at h2
  have h3 := congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  refine ⟨{ ψ with commutes' := fun a => ?_ }, hψ⟩
  have h4 := RingHom.congr_fun h3 a
  exact h4.symm.trans (lam.commutes a)

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIff
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_mem_basicOpen_iff_of_isPullback {P X Y Z : Scheme.{0}} {pm : P ⟶ X} {g' : P ⟶ Y} {g : X ⟶ Z}
    {f : Y ⟶ Z} (hP : IsPullback pm g' g f) {J : Type} (U : J → X.Opens) (U' : J → P.Opens)
    (hU : ∀ i, U' i = pm ⁻¹ᵁ U i) (s : ∀ i, Γ(X, U i)) (s' : ∀ i, Γ(P, U' i))
    (hs : ∀ i, (pm.appLE _ _ (hU i).le).hom (s i) = s' i) (p' : Y) :
    (∃ (q : P) (i : J), g' q = p' ∧ q ∈ P.basicOpen (s' i)) ↔
      ∃ (q : X) (i : J), g q = f p' ∧ q ∈ X.basicOpen (s i) := by
  have key : ∀ (i : J) (q : P), q ∈ P.basicOpen (s' i) ↔ pm q ∈ X.basicOpen (s i) := by
    intro i q
    have e := Scheme.basicOpen_appLE pm (U' i) (U i) (hU i).le (s i)
    have e' : P.basicOpen (s' i) = U' i ⊓ pm ⁻¹ᵁ (X.basicOpen (s i)) := by
      rw [← hs i]; exact e
    rw [e']
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [hU i]
    exact X.basicOpen_le (s i) h
  constructor
  · rintro ⟨q, i, rfl, hq⟩
    refine ⟨pm q, i, ?_, (key i q).1 hq⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hP.w]
  · rintro ⟨q, i, hq, hq'⟩
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback hP q p' hq
    exact ⟨z, i, hz, (key i z).2 hq'⟩

theorem secBC_nonvanishing_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s s', SecBC φ 1 x x' s s' → ∀ p' : Sp T, (∃ (q : Gx x') (i : (PPx x').ι), Formalism.L2.PjFree.gxSnd x' q = p' ∧ q ∈ (Gx x').basicOpen (s'.f i)) ↔ ∃ (q : Gx x) (i : (PPx x).ι), Formalism.L2.PjFree.gxSnd x q = spMap φ p' ∧ q ∈ (Gx x).basicOpen (s.f i) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x x' hx s s' hbc p'
  obtain ⟨pm, h1, h2, h3⟩ := hbc
  have hA : IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left
      Xo.univ.t.G.hom x := (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip
  have hB : IsPullback (snd (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x') Xo.univ.t.G).left
      Xo.univ.t.G.hom x' := (IsPullback.of_hasPullback x' Xo.univ.t.G.hom).flip
  have hP : IsPullback pm (fst (Over.mk x') Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left (spMap φ) := by
    refine IsPullback.of_right ?_ h2 hA
    rw [h1]
    exact hx ▸ hB
  have hU : ∀ i : Fin 1 → Xo.univ.t.PP.L.ι, (PPx x').U i = pm ⁻¹ᵁ (PPx x).U i := by
    intro i
    ext y
    change y ∈ ⋂ k : Fin 1, (snd (Over.mk x') Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) ↔
      pm y ∈ ⋂ k : Fin 1, (snd (Over.mk x) Xo.univ.t.G).left ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
    rw [← h1]
    simp only [Set.mem_iInter, Set.mem_preimage, Scheme.Hom.comp_apply]
  have h1' : ∀ i, scal x 1 i = 1 := fun i => by
    simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]
  refine exists_mem_basicOpen_iff_of_isPullback hP (PPx x).U (PPx x').U hU s.f s'.f (fun i => ?_) p'
  have := h3 i (hU i).le
  rwa [h1' i, _root_.one_mul] at this

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s s', SecBC φ 1 x x' s s' → ∀ p' : Sp T, (∃ (q : Gx x') (i : (PPx x').ι), Formalism.L2.PjFree.gxSnd x' q = p' ∧ q ∈ (Gx x').basicOpen (s'.f i)) ↔ ∃ (q : Gx x) (i : (PPx x).ι), Formalism.L2.PjFree.gxSnd x q = spMap φ p' ∧ q ∈ (Gx x).basicOpen (s.f i) := by
  first | exact @GlobalTheory.Frames.secBC_nonvanishing_iff | exact GlobalTheory.Frames.secBC_nonvanishing_iff | (intros; apply GlobalTheory.Frames.secBC_nonvanishing_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicHermitianFormGaloisMemOfMemCompletion
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

theorem hermA_tmul_right (z : Fin n → RA F E) (t : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    hermA c G z (fun i => t ⊗ₜ[F] x i) = (t ⊗ₜ[F] (1 : E)) * hermA c G z (fv F x) := by
  simp only [hermA, fv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : sg (FiniteAdeleRing (𝓞 F) F) c (t ⊗ₜ[F] x b) = (t ⊗ₜ[F] (1 : E)) *
      sg (FiniteAdeleRing (𝓞 F) F) c ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x b) := by
    simp [sg, Algebra.TensorProduct.tmul_mul_tmul]
  rw [h]; ring

theorem hermA_fv_fv (x y : Fin n → E) :
    hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) := by
  simp [hermA, fv, sg, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sum]

theorem adelicHermitianFormGalois_mem_of_mem_completion {S : Set (Fin n → E)} {J : Set E} {z : Fin n → RA F E}
    (hz : ∀ y ∈ S, hermA c G z (fv F y) ∈ hat1 F J) {w : Fin n → RA F E} (hw : w ∈ hat F S) :
    hermA c G z w ∈ hat1 F J := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨t, ht, x, hx, rfl⟩ := hw
    rw [hermA_tmul_right]
    exact mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := {1}) (fun a ha b hb => by
      rw [Set.mem_singleton_iff.1 ha, one_mul]; exact hb) (tmul_mem_adelicCompletion_of_integral F ht rfl) (hz x hx)
  | zero =>
    have : hermA c G z 0 = 0 := by simp [hermA]
    rw [this]; exact zero_mem _
  | add w w' _ _ h h' =>
    have : hermA c G z (w + w') = hermA c G z w + hermA c G z w' := by
      simp only [hermA, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
    rw [this]; exact add_mem h h'
  | neg w _ h =>
    have : hermA c G z (-w) = - hermA c G z w := by
      simp only [hermA, Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]
    rw [this]; exact neg_mem h

end

theorem latOf_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) → G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) → (∀ x y, hermA c G ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ x) ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ y) = hermA c G x y) → ∀ v : Fin n → E, (∀ y ∈ latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L := by
  intro F E _ _ _ _ _ n L c G J g hfg hspan hc hG hdet hJ hL hg v
  have hd := GlobalTheory.T.adelicCompletion_selfDual_of_selfDual_lattice F E n L c G J hfg hspan hc hG hdet hJ hL
  obtain ⟨Λ, hΛ, -, -, hhat⟩ := GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hfg hspan
  constructor
  · intro hv
    have hz : (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ
        (((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F v) = fv F v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨_, (hd _).1 fun y hy => ?_, hz⟩
    rw [← hg, hz]
    refine adelicHermitianFormGalois_mem_of_mem_completion c G (S := (Λ : Set (Fin n → E))) (fun y' hy' => ?_) ?_
    · rw [hermA_fv_fv]
      exact one_tmul_mem_adelicCompletionOfElementSet F (hv y' (hΛ ▸ hy'))
    · have : (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F y ∈
          (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) := by
        rw [hhat]
        exact ⟨fv F y, AddSubgroup.subset_closure ⟨1, adele_one_integral F, y, hy, rfl⟩, rfl⟩
      exact this
  · rintro ⟨z, hz, hzv⟩ y ⟨w, hw, hwy⟩
    rw [← one_tmul_mem_adelicCompletion_fractionalIdeal_iff F, ← hermA_fv_fv, ← hzv, ← hwy, hg]
    exact adelicHermitianFormGalois_mem_of_mem_completion c G ((hd z).2 hz) hw

end GlobalTheory.AdLat
end
