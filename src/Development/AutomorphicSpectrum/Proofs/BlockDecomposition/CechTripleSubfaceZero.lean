module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDifferentialOneInclusion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TerminalRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleSubfaceZero
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.CompanionTheory.KummerPrimitive

theorem res_d_neg {R : Type} [CommRing R] (F : Shv R) : (res R F).d (-1) 0 = 0 := by
  have : (res R F).IsStrictlyGE 0 := by
    unfold res
    infer_instance
  exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 (-1) (by omega)).eq_of_src _ _

theorem cechPt_congr {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} {x x' : U ⟶ X}
    {y y' : Fin (k + 1) → (U ⟶ Y)} (h : ∀ i, y i ≫ f = x) (h' : ∀ i, y' i ≫ f = x') (hx : x = x')
    (hy : ∀ i, y i = y' i) : cechPt f k x y h = cechPt f k x' y' h' := by
  subst hx
  obtain rfl := funext hy
  rfl

def pt0 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b : V ⟶ Y) : Sx (cech f) 0 V :=
  cechPt f 0 (b ≫ f) ![b] (by intro i; fin_cases i; rfl)

def pt1 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : Sx (cech f) 1 V :=
  cechPt f 1 (b ≫ f) ![b, c] (by
    intro i; fin_cases i
    · rfl
    · exact h.symm)

def pt2 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    Sx (cech f) 2 V :=
  cechPt f 2 (b ≫ f) ![b, c, e] (by
    intro i; fin_cases i
    · rfl
    · exact h.symm
    · exact (h.trans h').symm)

section Simplices

variable (hC : CechPt) {Y X : Scheme.{0}} (f : Y ⟶ X) {V V' : Scheme.{0}}
include hC

theorem cechPoint_augmentation (b : V ⟶ Y) : Sx.map (GlobalTheory.EtC.cechAug f) (pt0 f b) = b ≫ f :=
  (((hC Y X f 0 V).2.2 _ _ _).1)

theorem cechPoint_restrict (g : V' ⟶ V) (b : V ⟶ Y) : Sx.res g (pt0 f b) = pt0 f (g ≫ b) := by
  refine ((hC Y X f 0 V).2.2 _ _ _).2.1 V' g |>.trans (cechPt_congr _ _ _ _ (Category.assoc _ _ _).symm ?_)
  intro i; fin_cases i; rfl

theorem cechPair_restrict (g : V' ⟶ V) (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : (g ≫ b) ≫ f = (g ≫ c) ≫ f) :
    Sx.res g (pt1 f b c h) = pt1 f (g ≫ b) (g ≫ c) h' := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.1 V' g |>.trans (cechPt_congr _ _ _ _ (Category.assoc _ _ _).symm ?_)
  intro i; fin_cases i <;> rfl

theorem cechPair_face_zero (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : (pt1 f b c h).face 0 = pt0 f c := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.2 0 (SimplexCategory.δ 0) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i; rfl

theorem cechPair_face_one (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : (pt1 f b c h).face 1 = pt0 f b := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.2 0 (SimplexCategory.δ 1) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i; rfl

theorem cechTriple_face_zero (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 0 = pt1 f c e h' := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 0) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_face_one (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 1 = pt1 f b e (h.trans h') := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 1) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_face_two (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 2 = pt1 f b c h := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 2) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_subface_zero (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) (hs : 0 + 1 ≤ 2) :
    (pt2 f b c e h h').sub 0 1 hs = pt1 f b c h := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.subinterval 0 1 hs) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_subface_one (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) (hs : 1 + 1 ≤ 2) :
    (pt2 f b c e h h').sub 1 1 hs = pt1 f c e h' := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.subinterval 1 1 hs) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i <;> rfl

end Simplices

section Coboundary

variable (hD : EvDel) {R : Type} [CommRing R] {E : Spc} {I : GlobalTheory.EtC.Cx R} (β : Cochain ((chains R).obj E) I 1)
  (U : Scheme.{0})
include hD

theorem del_one (z : Sx E 1 U) : ev (δ 1 2 β) 1 1 (by simp) U z =
    Sec.map (I.d 0 1) (ev β 1 0 (by simp) U z) +
      (ev β 0 1 (by simp) U (z.face 0) - ev β 0 1 (by simp) U (z.face 1)) := by
  refine ((hD R E I 1 2 (by norm_num) β U).2 0 0 1 (by simp) (by simp) z).trans ?_
  rw [Int.negOnePow_even 2 (by decide), one_smul, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

theorem del_two (z : Sx E 2 U) : ev (δ 1 2 β) 2 0 (by simp) U z =
    Sec.map (I.d (-1) 0) (ev β 2 (-1) (by simp) U z) +
      (ev β 1 0 (by simp) U (z.face 0) - ev β 1 0 (by simp) U (z.face 1) + ev β 1 0 (by simp) U (z.face 2)) := by
  refine ((hD R E I 1 2 (by norm_num) β U).2 1 (-1) 0 (by simp) (by simp) z).trans ?_
  rw [Int.negOnePow_even 2 (by decide), one_smul, Fin.sum_univ_three]
  simp [sub_eq_add_neg]

end Coboundary

theorem main : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.EvDel → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.CechPt →
    CrystallineSemistableComparison.E.FirstChernCoboundary := by
  intro hExt hNat hDel hConc hBasic hCech hC1 q _ X D L hL hInv x hx
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := hC1 q (cech D.f) L hInv
  obtain ⟨a, ha⟩ := (hBasic (ZMod q) (res _ (tw q 1)) X 2).1 x
  obtain ⟨α, hαc, hαx⟩ := (hConc (ZMod q) (res _ (tw q 1)) X 2 a).2.1 x ha
  have hmk : CohomologyClass.mk (γ - zcomp (Cocycle.ofHom ((chains (ZMod q)).map (GlobalTheory.EtC.cechAug D.f))) α (zero_add 2)) = 0 := by
    rw [CohomologyClass.mk_sub, hγ, ← hx, ← hαx]
    exact sub_self _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)] at hmk
  obtain ⟨β, hβ⟩ := hmk
  have hv : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 2 = s) (U : Scheme.{0}) (z : Sx (cech D.f) p U),
      ev (δ 1 2 β) p s h U z = ev γ.1 p s h U z - ev α.1 p s h U (Sx.map (GlobalTheory.EtC.cechAug D.f) z) := by
    intro p s h U z
    have e : δ 1 2 β = γ.1 - (Cochain.ofHom ((chains (ZMod q)).map (GlobalTheory.EtC.cechAug D.f))).comp α.1 (zero_add 2) := hβ
    rw [e, ((hExt _ _ _ _ _ _).2 p s h U z).2.1, ((hNat _ _ _ _ α.1 p s h U).2 _ _ z)]
  have hv1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 2 = s) (U : Scheme.{0}) (z : Sx (cech D.f) (p + 1) U),
      ev (δ 1 2 β) (p + 1) s h U z = ev γ.1 (p + 1) s h U z := by
    intro p s h U z
    rw [hv, show ev α.1 (p + 1) s h U (Sx.map (GlobalTheory.EtC.cechAug D.f) z) = 0 from hαc.2 p s h U (Sx.map (GlobalTheory.EtC.cechAug D.f) z), sub_zero]
  refine ⟨a, fun V b => - ev β 0 1 (by simp) V (pt0 D.f b), fun V b c h => ev β 1 0 (by simp) V (pt1 D.f b c h),
    ha, ?_, ?_, ?_, ?_, ?_⟩
  · intro V V' g b
    have e := (hNat _ _ _ _ β 0 1 (by simp) V).1 V' g (pt0 D.f b)
    rw [cechPoint_restrict hCech] at e
    simp only [map_neg]
    exact congrArg Neg.neg e.symm
  · intro V V' g b c h h'
    rw [← (hNat _ _ _ _ β 1 0 (by simp) V).1 V' g (pt1 D.f b c h), cechPair_restrict hCech]
  · intro V b
    have h0 := ((hDel _ _ _ 1 2 (by norm_num) β V).1 (pt0 D.f b))
    rw [hv, hγ0, cechPoint_augmentation hCech, show ev α.1 0 2 (by simp) V (b ≫ D.f) = Sec.res (b ≫ D.f) a from hαc.1 V _, zero_sub] at h0
    simp only [map_neg]
    exact (congrArg Neg.neg h0).symm.trans (neg_neg _)
  · intro V b c h v hv'
    have hu : v ^ q = lineUnit L (pt1 D.f b c h) := hv'.trans (hL V _ ![b, c] _).symm
    have h1 := del_one hDel β V (pt1 D.f b c h)
    rw [hv1 0 1 _ V (pt1 D.f b c h), hγ1 V _ v hu, cechPair_face_zero hCech, cechPair_face_one hCech] at h1
    simp only [map_sub]
    change -ev β 0 1 (by simp) V (pt0 D.f c) - -ev β 0 1 (by simp) V (pt0 D.f b) =
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (ev β 1 0 (by simp) V (pt1 D.f b c h)) -
        Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V v)
    rw [h1]
    abel
  · intro V b c e h h' v w hv' hw'
    have hu : v ^ q = lineUnit L ((pt2 D.f b c e h h').sub 0 1 (by omega)) := by
      rw [cechTriple_subface_zero hCech]
      exact hv'.trans (hL V _ ![b, c] _).symm
    have hu' : w ^ q = lineUnit L ((pt2 D.f b c e h h').sub 1 1 (by omega)) := by
      rw [cechTriple_subface_one hCech]
      exact hw'.trans (hL V _ ![c, e] _).symm
    have h2 := del_two hDel β V (pt2 D.f b c e h h')
    have hz : ∀ y : Sec ((res (ZMod q) (tw q 1)).X (-1)) V, Sec.map ((res (ZMod q) (tw q 1)).d (-1) 0) y = 0 := by
      intro y
      rw [res_d_neg]
      rfl
    rw [hv1 1 0 _ V (pt2 D.f b c e h h'), hγ2 V _ v w hu hu', cechTriple_face_zero hCech, cechTriple_face_one hCech, cechTriple_face_two hCech,
      hz, zero_add] at h2
    exact h2.symm

end GlobalTheory.CompanionTheory.KummerPrimitive
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleZeroAlt
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Onto

universe u v w

noncomputable section

namespace GlobalTheory.CompanionTheory.CovDescent

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {C : Type u} [Category.{v} C]
  (F : C ⥤ ModuleCat.{w} R) (U : ι → ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q)

theorem cosieve_capU (hU : ∀ α, Cosieve (U α)) (S : Finset ι) : Cosieve (capU U S) := fun _ _ φ h =>
  ⟨h.1.imp fun a ha => hU a φ ha, fun α hα => hU α φ (h.2 α hα)⟩

variable {U} in
theorem capU_mono {S T : Finset ι} (h : S ⊆ T) {X : C} (hX : capU U T X) : capU U S X :=
  ⟨hX.1, fun α hα => hX.2 α (h hα)⟩

variable {U} in
theorem capU_cons {n : ℕ} {a : ι} {i : Fin n → ι} {T : C} (ha : U a T) (hi : capU U (ent i) T) :
    capU U (ent (Fin.cons (α := fun _ => ι) a i)) T := by
  refine ⟨⟨a, ha⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  refine Fin.cases ?_ (fun k => ?_) k
  · exact ha
  · exact hi.2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))

def liftC (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : ComposableArrows (capU U S).FullSubcategory n :=
  (capU U S).lift s fun k => cosieve_capU U hU S (s.map (homOfLE (Fin.zero_le k))) h

abbrev Tm (n : ℕ) : PM.{max u v w} R ι := (covSy F U hQ).term n

def evL (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (s : ComposableArrows C n)
    (h : capU U S (s.obj 0)) : (Tm F U hQ n).M S →ₗ[R] F.obj (s.obj (Fin.last n)) :=
  (LinearMap.proj (R := R) (φ := fun t : ComposableArrows (capU U S).FullSubcategory n =>
    ((capU U S).ι ⋙ F).obj (t.obj (Fin.last n))) (liftC U hU S s h)) ∘ₗ
    (relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n).subtype

variable {F U hQ}

theorem evL_congr (hU : ∀ α, Cosieve (U α)) {n p : ℕ} (f : ∀ i : Fin p → ι, (Tm F U hQ n).M (ent i))
    {i i' : Fin p → ι} (e : i = i') (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0))
    (h' : capU U (ent i') (s.obj 0)) : evL F U hQ hU _ s h (f i) = evL F U hQ hU _ s h' (f i') := by
  subst e; rfl

theorem evL_d (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X p)
    (i : Fin (p + 2) → ι) (s : ComposableArrows C n) (h : capU U (ent i) (s.obj 0)) :
    evL F U hQ hU _ s h ((Tm F U hQ n).cech.d p y i) =
      ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
        evL F U hQ hU _ s (capU_mono (ent_comp i k.succAbove) h) (y (i ∘ k.succAbove)) := by
  have e := congrArg ((evL F U hQ hU _ s h) ∘ₗ
    (LinearMap.proj (R := R) (φ := fun i : Fin (p + 2) → ι => (Tm F U hQ n).M (ent i)) i))
    (Cos.d_apply (Tm F U hQ n).cech p y)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at e
  simp only [map_zsmul] at e
  exact e

theorem capU_const {b : ι} {T : C} (hb : U b T) : capU U (ent fun _ : Fin 1 => b) T := by
  refine ⟨⟨b, hb⟩, fun α hα => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  exact hb

theorem cons_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Function.comp]

theorem cons_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (Fin.cons (α := fun _ => ι) a i : Fin (n + 2) → ι) ∘ j.succ.succAbove =
      Fin.cons (α := fun _ => ι) a (i ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Function.comp]
  · simp [Function.comp]

theorem M_ext (hU : ∀ α, Cosieve (U α)) {n : ℕ} {S : Finset ι} {x y : (Tm F U hQ n).M S}
    (h : ∀ t : ComposableArrows (capU U S).FullSubcategory n,
      evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property x =
        evL F U hQ hU S (t ⋙ (capU U S).ι) (t.obj 0).property y) : x = y :=
  Subtype.ext (funext h)

def mkM {n : ℕ} (S : Finset ι) (f : CH.Cn ((capU U S).ι ⋙ F) n)
    (hf : ∀ t : ComposableArrows (capU U S).FullSubcategory n, Q (t.obj 0).obj → f t = 0) :
    (Tm F U hQ n).M S :=
  (⟨f, hf⟩ : relS ((capU U S).ι ⋙ F) (fun T => Q T.obj) n)

theorem evL_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (S : Finset ι) (x : (Tm F U hQ n).M S)
    (s : ComposableArrows C n) (h : capU U S (s.obj 0)) (hs : Q (s.obj 0)) :
    evL F U hQ hU S s h x = 0 :=
  x.2 (liftC U hU S s h) hs

theorem cocycle_eq (hU : ∀ α, Cosieve (U α)) {p n : ℕ} (y : (Tm F U hQ n).cech.X (p + 1))
    (hy : (Tm F U hQ n).cech.d (p + 1) y = 0) (i : Fin (p + 2) → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d (p + 1) y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_succ] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 : ∀ j : Fin (p + 2),
      evL F U hQ hU _ s (capU_mono (ent_comp _ j.succ.succAbove) h')
        (y ((Fin.cons (α := fun _ => ι) b i : Fin (p + 3) → ι) ∘ j.succ.succAbove)) =
      evL F U hQ hU _ s (capU_cons hb (capU_mono (ent_comp i j.succAbove) h))
        (y (Fin.cons (α := fun _ => ι) b (i ∘ j.succAbove))) :=
    fun j => evL_congr hU y (cons_succ _ i j) s _ _
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

theorem cocycle_zero (hU : ∀ α, Cosieve (U α)) {n : ℕ} (y : (Tm F U hQ n).cech.X 0)
    (hy : (Tm F U hQ n).cech.d 0 y = 0) (i : Fin 1 → ι) (s : ComposableArrows C n)
    (h : capU U (ent i) (s.obj 0)) (b : ι) (hb : U b (s.obj 0)) :
    evL F U hQ hU _ s h (y i) = evL F U hQ hU _ s (capU_const hb) (y fun _ => b) := by
  have h' := capU_cons hb h
  have e := evL_d hU y _ s h'
  have z : evL F U hQ hU _ s h' ((Tm F U hQ n).cech.d 0 y (Fin.cons (α := fun _ => ι) b i)) = 0 := by
    rw [hy]; exact map_zero _
  rw [z, Fin.sum_univ_two] at e
  have e0 := evL_congr hU y (cons_zero b i) s (capU_mono (ent_comp _ _) h') h
  have e1 := evL_congr hU y (i := (Fin.cons (α := fun _ => ι) b i : Fin 2 → ι) ∘ (1 : Fin 2).succAbove)
    (i' := fun _ => b) (funext fun k => by
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      rfl) s (capU_mono (ent_comp _ _) h') (capU_const hb)
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, e0, e1] at e
  exact add_neg_eq_zero.1 e.symm

def hh (hU : ∀ α, Cosieve (U α)) (a : ∀ T, (∃ b, U b T) → ι) (ha : ∀ T h, U (a T h) T) {p n : ℕ}
    (y : (Tm F U hQ n).cech.X (p + 1)) : (Tm F U hQ n).cech.X p := fun i =>
  mkM (ent i) (fun t => evL F U hQ hU _ (t ⋙ (capU U (ent i)).ι)
      (capU_cons (ha _ (t.obj 0).property.1) (t.obj 0).property)
      (y (Fin.cons (α := fun _ => ι) (a _ (t.obj 0).property.1) i)))
    fun t ht => evL_zero hU _ _ _ _ ht

theorem desc (hU : ∀ α, Cosieve (U α)) (n : ℕ) : (Tm F U hQ n).Ex := by
  have hc : ∀ T : C, ∀ h : ∃ b, U b T, ∃ b, U b T := fun _ h => h
  choose a ha using hc
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun m y hy => ?_⟩
  · funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU _ i _ _).trans ?_
    refine Eq.trans ?_ (map_zero (evL F U hQ hU _ _ _)).symm
    rw [Fin.sum_univ_two]
    change (-1 : ℤ) ^ 0 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x +
      (-1 : ℤ) ^ 1 • evL F U hQ hU ∅ _ (capU_mono (Finset.empty_subset _) (t.obj 0).property) x = 0
    simp
  · rw [one_smul]
    refine M_ext hU fun t => ?_
    have hb := ha _ (t.obj 0).property.1
    have h1 := congrArg (evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const hb))
      (congrFun hx fun _ => a _ (t.obj 0).property.1)
    exact (h1.trans (map_zero _)).trans (map_zero _).symm
  · refine ⟨mkM ∅ (fun t => evL F U hQ hU _ (t ⋙ (capU U ∅).ι) (capU_const (ha _ (t.obj 0).property.1))
      (y fun _ => a _ (t.obj 0).property.1)) fun t ht => evL_zero hU _ _ _ _ ht, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    exact (cocycle_zero hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
  · refine ⟨hh hU a ha y, ?_⟩
    rw [one_smul]
    funext i
    refine M_ext hU fun t => ?_
    refine (evL_d hU (hh hU a ha y) i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property).trans ?_
    refine Eq.trans ?_ (cocycle_eq hU y hy i (t ⋙ (capU U (ent i)).ι) (t.obj 0).property _
      (ha _ (t.obj 0).property.1)).symm
    rfl

theorem covDesc : CovDesc := fun _ _ _ _ _ _ _ _ _ _ hU n => desc hU n

end GlobalTheory.CompanionTheory.CovDescent
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHEmptyBij
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

universe w w'

namespace GlobalTheory.CompanionTheory.Onto

variable {R : Type} [CommRing R]

abbrev prodCx {I : Type} (K : I → Cx.{w} R) : Cx.{w} R where
  X n := ∀ i, (K i).X n
  d n := LinearMap.pi fun i => ((K i).d n).comp (LinearMap.proj i)
  dd n x := funext fun i => (K i).dd n (x i)

def prodHom {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R)) : Cx.Hom (prodCx K) (prodCx L) (RingHom.id R) where
  f n := LinearMap.pi fun i => ((φ i).f n).comp (LinearMap.proj i)
  comm n x := funext fun i => (φ i).comm n (x i)

theorem mem_B_prod {I : Type} (K : I → Cx.{w} R) (n : ℕ) (a : (prodCx K).X n) :
    a ∈ (prodCx K).B n ↔ ∀ i, a i ∈ (K i).B n := by
  cases n with
  | zero =>
    constructor
    · intro h i
      have h0 : a = 0 := h
      rw [h0]
      exact Submodule.zero_mem _
    · intro h
      exact funext fun i => h i
  | succ n =>
    constructor
    · rintro ⟨b, rfl⟩ i
      exact ⟨b i, rfl⟩
    · intro h
      choose b hb using h
      exact ⟨b, funext hb⟩

theorem prod_bij {I : Type} {K : I → Cx.{w} R} {L : I → Cx.{w'} R}
    (φ : ∀ i, Cx.Hom (K i) (L i) (RingHom.id R))
    (h : ∀ i n, Function.Bijective ((φ i).mapH n)) (n : ℕ) :
    Function.Bijective ((prodHom φ).mapH n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx K) n).1 x
    have hb : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hb, (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hb, mem_B_prod] at hx
    rw [(CrystallineSemistableComparison.P.cls_surj _ n).2.1, mem_B_prod]
    intro i
    have hai : (K i).d n (a i) = 0 := congrFun ha i
    have hbi : (L i).d n ((φ i).f n (a i)) = 0 := by rw [(φ i).comm, hai, map_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj _ n).2.1 _ hai]
    apply (injective_iff_map_eq_zero _).1 (h i n).1
    rw [CrystallineSemistableComparison.P.mapH_cls _ n _ hai hbi, (CrystallineSemistableComparison.P.cls_surj _ n).2.1]
    exact hx i
  · intro y
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (prodCx L) n).1 y
    have hbi : ∀ i, (L i).d n (b i) = 0 := fun i => congrFun hb i
    have key : ∀ i, ∃ a, ∃ ha : (K i).d n a = 0, (φ i).f n a - b i ∈ (L i).B n := by
      intro i
      obtain ⟨x, hx⟩ := (h i n).2 ((L i).cls (b i) (hbi i))
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (K i) n).1 x
      have hc : (L i).d n ((φ i).f n a) = 0 := by rw [(φ i).comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls _ n a ha hc] at hx
      exact ⟨a, ha, ((CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc (hbi i)).1 hx⟩
    choose a ha hab using key
    have ha' : (prodCx K).d n a = 0 := funext ha
    have hc : (prodCx L).d n ((prodHom φ).f n a) = 0 := by rw [(prodHom φ).comm, ha', map_zero]
    refine ⟨(prodCx K).cls a ha', ?_⟩
    rw [CrystallineSemistableComparison.P.mapH_cls (prodHom φ) n a ha' hc, (CrystallineSemistableComparison.P.cls_surj _ n).2.2.1 _ _ hc hb, mem_B_prod]
    exact hab

variable {ι : Type} [DecidableEq ι]

abbrev cechCos (A : Sy.{w} R ι) : CosCx.{w} R where
  K p := prodCx fun i : Fin (p + 1) → ι => A.K (ent i)
  δ p k :=
    { f := fun q => (A.term q).cech.δ p k
      comm := fun q x => funext fun t => (A.res (ent_comp t k.succAbove)).comm q (x (t ∘ k.succAbove)) }
  rel p j i q x := (A.term q).cech.rel p j i x

def cechAug (A : Sy.{w} R ι) (hA : A.Desc) : DCx.AugRow (A.K ∅) (cechCos A).dcx where
  ε q := (A.term q).aug
  hε q x := (hA q).1 x
  comm q x := funext fun t => (A.res (Finset.empty_subset (ent t))).comm q x

theorem cechAug_row (A : Sy.{w} R ι) (hA : A.Desc) (q : ℕ) :
    ((cechCos A).dcx.row q).ResUpTo 1 ((cechAug A hA).ε q) := hA q

def cechHom {A B : Sy.{w} R ι} (m : A.Hom B) :
    DCx.Hom (cechCos A).dcx (cechCos B).dcx (RingHom.id R) where
  f p q := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).f q
  ch p q x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Cos.d_apply, Cos.d_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    refine congrArg _ (funext fun t => ?_)
    exact (m.nat (ent_comp t k.succAbove) q (x (t ∘ k.succAbove))).symm
  cv p q x := (prodHom fun i : Fin (p + 1) → ι => m.φ (ent i)).comm q x

theorem cechHom_col {A B : Sy.{w} R ι} (m : A.Hom B)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (p q : ℕ) :
    Function.Bijective (((cechHom m).col p).mapH q) :=
  prod_bij (fun i : Fin (p + 1) → ι => m.φ (ent i))
    (fun i n => h _ ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ n) q

theorem upTo_one {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) : UpTo (1 : R) f ↔ Function.Bijective f := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, fun y => ?_⟩
    · simpa using h1 x hx
    · simpa using h2 y
  · intro h
    refine ⟨fun x hx => ?_, fun y => ?_⟩
    · rw [one_smul]
      exact (injective_iff_map_eq_zero f).1 h.1 x hx
    · simpa using h.2 y

theorem cls_congr {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h; rfl

theorem edge_square {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc) (n : ℕ) (a : (A.K ∅).X n) :
    (cechHom m).tot.f n ((cechAug A hA).edge.f n a) = (cechAug B hB).edge.f n ((m.φ ∅).f n a) := by
  apply Subtype.ext
  funext p q
  by_cases h : p = 0 ∧ q = n
  · obtain ⟨rfl, rfl⟩ := h
    change (cechHom m).f 0 q ((cechCos A).dcx.sgl 0 q ((cechAug A hA).ε q a) 0 q) =
      (cechCos B).dcx.sgl 0 q ((cechAug B hB).ε q ((m.φ ∅).f q a)) 0 q
    rw [DCx.sgl_self, DCx.sgl_self]
    funext t
    exact m.nat (Finset.empty_subset (ent t)) q a
  · have h' : p ≠ 0 ∨ q ≠ n := by omega
    change (cechHom m).f p q ((cechCos A).dcx.sgl 0 n ((cechAug A hA).ε n a) p q) =
      (cechCos B).dcx.sgl 0 n ((cechAug B hB).ε n ((m.φ ∅).f n a)) p q
    rw [DCx.sgl_ne _ _ h', DCx.sgl_ne _ _ h', map_zero]

theorem mapH_empty_bij {A B : Sy.{w} R ι} (m : A.Hom B) (hA : A.Desc) (hB : B.Desc)
    (h : ∀ S : Finset ι, S.Nonempty → ∀ n, Function.Bijective ((m.φ S).mapH n)) (n : ℕ) :
    Function.Bijective ((m.φ ∅).mapH n) := by
  have eA : Function.Bijective ((cechAug A hA).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug A hA) 1 (cechAug_row A hA) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eB : Function.Bijective ((cechAug B hB).edge.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_row (cechAug B hB) 1 (cechAug_row B hB) n
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have eT : Function.Bijective ((cechHom m).tot.mapH n) := by
    have := CrystallineSemistableComparison.P.dc_map_col (cechHom m) 1 n fun p q _ => (upTo_one _).2 (cechHom_col m h p q)
    rw [one_pow] at this
    exact (upTo_one _).1 this
  have sq : ∀ x, (cechAug B hB).edge.mapH n ((m.φ ∅).mapH n x) =
      (cechHom m).tot.mapH n ((cechAug A hA).edge.mapH n x) := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (A.K ∅) n).1 x
    have c1 : (B.K ∅).d n ((m.φ ∅).f n a) = 0 := by rw [(m.φ ∅).comm, ha, map_zero]
    have c2 : (cechCos B).dcx.tot.d n ((cechAug B hB).edge.f n ((m.φ ∅).f n a)) = 0 := by
      rw [(cechAug B hB).edge.comm, c1, map_zero]
    have c3 : (cechCos A).dcx.tot.d n ((cechAug A hA).edge.f n a) = 0 := by
      rw [(cechAug A hA).edge.comm, ha, map_zero]
    have c4 : (cechCos B).dcx.tot.d n ((cechHom m).tot.f n ((cechAug A hA).edge.f n a)) = 0 := by
      rw [(cechHom m).tot.comm, c3, map_zero]
    rw [CrystallineSemistableComparison.P.mapH_cls (m.φ ∅) n a ha c1, CrystallineSemistableComparison.P.mapH_cls (cechAug B hB).edge n _ c1 c2,
      CrystallineSemistableComparison.P.mapH_cls (cechAug A hA).edge n a ha c3, CrystallineSemistableComparison.P.mapH_cls (cechHom m).tot n _ c3 c4]
    exact cls_congr (edge_square m hA hB n a).symm c2 c4
  constructor
  · intro x y hxy
    apply eA.1
    apply eT.1
    rw [← sq, ← sq, hxy]
  · intro y
    obtain ⟨u, hu⟩ := eT.2 ((cechAug B hB).edge.mapH n y)
    obtain ⟨x, rfl⟩ := eA.2 u
    refine ⟨x, eB.1 ?_⟩
    rw [sq, hu]

theorem mvBij : CrystallineSemistableComparison.Onto.MVBij := fun _ _ _ _ _ _ m hA hB h n => mapH_empty_bij m hA hB h n

end GlobalTheory.CompanionTheory.Onto
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemInjectiveExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemInjectiveExtension
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

section Tuples
variable {ι : Type}

theorem cons_comp_zero {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons a i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext k
  simp [Fin.succAbove_zero]

theorem cons_comp_succ {n : ℕ} (a : ι) (i : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons a i : Fin (n + 2) → ι) ∘ k.succ.succAbove = Fin.cons a (i ∘ k.succAbove) := by
  funext t
  cases t using Fin.cases with
  | zero => simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.cons_zero]
  | succ t => simp only [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]

theorem mem_ent_cons [DecidableEq ι] {n : ℕ} {a x : ι} {i : Fin n → ι}
    (h : x ∈ ent (Fin.cons a i : Fin (n + 1) → ι)) : x = a ∨ x ∈ ent i := by
  simp only [ent, Finset.mem_image, Finset.mem_univ, true_and] at h ⊢
  obtain ⟨k, rfl⟩ := h
  cases k using Fin.cases with
  | zero =>
    left
    simp only [Fin.cons_zero]
  | succ k =>
    right
    exact ⟨k, by simp only [Fin.cons_succ]⟩

end Tuples

section Coordinates
variable {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W] [Module K W] {Λ : Type}
  (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι)

def Sup (S : Finset ι) (w : W) : Prop := ∀ l, b.repr w l ≠ 0 → good' l ∧ T l ⊆ S

theorem mem_span_iff (S : Finset ι) (w : W) :
    w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S}) ↔ Sup b good' T S w := by
  rw [Module.Basis.mem_span_image]
  constructor
  · intro h l hl
    exact h (Finsupp.mem_support_iff.2 hl)
  · intro h l hl
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hl
    exact h l hl

theorem coord_sum {n : ℕ} (D : Fin n → W) (l : Λ) :
    b.repr (∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) • D k) l = ∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) • b.repr (D k) l := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Finsupp.smul_apply]


open Classical in
def contr {n : ℕ} (C : (Fin (n + 1) → ι) → W) (a : ∀ l, good' l → ι) (i : Fin n → ι) : W :=
  b.repr.symm (Finsupp.onFinset (Finset.univ.biUnion fun a' : ι => (b.repr (C (Fin.cons a' i))).support)
    (fun l => if h : good' l then b.repr (C (Fin.cons (a l h) i)) l else 0) (by
      intro l hl
      by_cases h : good' l
      · rw [dif_pos h] at hl
        exact Finset.mem_biUnion.2 ⟨a l h, Finset.mem_univ _, Finsupp.mem_support_iff.2 hl⟩
      · rw [dif_neg h] at hl
        exact absurd rfl hl))

open Classical in
theorem contr_apply {n : ℕ} (C : (Fin (n + 1) → ι) → W) (a : ∀ l, good' l → ι) (i : Fin n → ι) (l : Λ) :
    b.repr (contr b good' C a i) l = if h : good' l then b.repr (C (Fin.cons (a l h) i)) l else 0 := by
  unfold contr
  rw [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply]

theorem contr_sup {n : ℕ} (C : (Fin (n + 1) → ι) → W) (hC : ∀ i, Sup b good' T (ent i) (C i))
    (a : ∀ l, good' l → ι) (ha : ∀ l h, a l h ∉ T l) (i : Fin n → ι) :
    Sup b good' T (ent i) (contr b good' C a i) := by
  intro l hl
  rw [contr_apply] at hl
  by_cases h : good' l
  · rw [dif_pos h] at hl
    obtain ⟨-, hT⟩ := hC _ l hl
    refine ⟨h, fun x hx => ?_⟩
    rcases mem_ent_cons (hT hx) with rfl | hx'
    · exact absurd hx (ha l h)
    · exact hx'
  · rw [dif_neg h] at hl
    exact absurd rfl hl

theorem homotopy {n : ℕ} (C : (Fin (n + 1) → ι) → W) (hC : ∀ i, Sup b good' T (ent i) (C i))
    (hZ : ∀ i : Fin (n + 2) → ι, ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • C (i ∘ k.succAbove) = 0)
    (a : ∀ l, good' l → ι) (i : Fin (n + 1) → ι) :
    ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • contr b good' C a (i ∘ k.succAbove) = C i := by
  apply b.repr.injective
  ext l
  rw [coord_sum]
  simp only [contr_apply]
  by_cases h : good' l
  · simp only [dif_pos h]
    have hz := congrArg (fun w => b.repr w l) (hZ (Fin.cons (a l h) i))
    rw [Fin.sum_univ_succ] at hz
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Fin.val_zero, pow_zero, one_smul, cons_comp_zero, Fin.val_succ, cons_comp_succ,
      map_add, map_sum, map_zsmul, Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply, pow_succ, mul_neg, mul_one,
      neg_smul, Finset.sum_neg_distrib, map_neg, Finsupp.coe_neg, Pi.neg_apply] at hz
    rw [← sub_eq_add_neg, sub_eq_zero] at hz
    exact hz.symm
  · simp only [dif_neg h, smul_zero, Finset.sum_const_zero]
    by_contra hne
    exact h (hC i l (Ne.symm hne)).1

end Coordinates

section Main

theorem j_dZ {ι : Type} [DecidableEq ι] {W : Type} [AddCommGroup W] (M : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W)
    (hr : ∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    j (ent i) (dZ M r m c i) = ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dZ, map_sum, map_zsmul, hr]

theorem exP_of_basis : ∀ {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W]
    [Module K W] {Λ : Type} (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι),
    (∀ l, good' l → T l ≠ Finset.univ) → ∀ (M : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W), (∀ S, Function.Injective (j S)) →
    (∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) →
    (∀ S w, (∃ x, j S x = w) ↔ w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S})) → ExP M r := by
  intro K _ ι _ _ W _ _ Λ b good' T hT M _ r j hj hr hspan
  have hout : ∀ l, good' l → ∃ y, y ∉ T l := by
    intro l hl
    by_contra hc
    push Not at hc
    exact hT l hl (Finset.eq_univ_iff_forall.2 hc)
  choose a ha using hout
  have hsup : ∀ S (x : M S), Sup b good' T S (j S x) := fun S x =>
    (mem_span_iff b good' T S _).1 ((hspan S _).1 ⟨x, rfl⟩)
  have hlift : ∀ S w, Sup b good' T S w → ∃ x, j S x = w := fun S w h =>
    (hspan S w).2 ((mem_span_iff b good' T S w).2 h)
  refine ⟨fun x hx => ?_, fun c hc => ?_, fun m c hc => ?_⟩
  · have hw : j ∅ x = 0 := by
      apply b.repr.injective
      ext l
      rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
      by_contra hne
      obtain ⟨hg, -⟩ := hsup ∅ x l hne
      have h0 := hr (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x
      have hx0 : r (Finset.empty_subset (ent (fun _ : Fin 1 => a l hg))) x = 0 := hx _
      rw [hx0, map_zero] at h0
      rw [← h0] at hne
      exact hne (by rw [map_zero, Finsupp.coe_zero, Pi.zero_apply])
    exact hj ∅ (hw.trans (map_zero (j ∅)).symm)
  · have hZ : ∀ i : Fin (0 + 2) → ι,
        ∑ k : Fin (0 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0 := by
      intro i
      rw [← j_dZ M r j hr 0 c i, hc, Pi.zero_apply, map_zero]
    have hCs : ∀ i : Fin (0 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i)) := fun i => hsup _ (c i)
    have hw := contr_sup b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs a ha Fin.elim0
    have he : ent (Fin.elim0 : Fin 0 → ι) = ∅ := by simp [ent]
    rw [he] at hw
    obtain ⟨x, hx⟩ := hlift ∅ _ hw
    refine ⟨x, fun i => hj _ ?_⟩
    rw [hr, hx]
    have hh := homotopy b good' T (fun i : Fin (0 + 1) → ι => j (ent i) (c i)) hCs hZ a i
    rw [Fin.sum_univ_succ] at hh
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero,
      one_smul] at hh
    convert hh using 2
  · have hZ : ∀ i : Fin (m + 1 + 2) → ι,
        ∑ k : Fin (m + 1 + 2), (-1 : ℤ) ^ (k : ℕ) • j _ (c (i ∘ k.succAbove)) = 0 := by
      intro i
      rw [← j_dZ M r j hr (m + 1) c i, hc, Pi.zero_apply, map_zero]
    have hCs : ∀ i : Fin (m + 1 + 1) → ι, Sup b good' T (ent i) (j (ent i) (c i)) :=
      fun i => hsup _ (c i)
    have hb : ∀ i' : Fin (m + 1) → ι, ∃ x : M (ent i'),
        j (ent i') x = contr b good' (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) a i' :=
      fun i' => hlift _ _ (contr_sup b good' T _ hCs a ha i')
    choose b' hb' using hb
    refine ⟨b', funext fun i => hj _ ?_⟩
    rw [j_dZ M r j hr m b' i]
    simp only [hb']
    exact homotopy b good' T (fun i : Fin (m + 1 + 1) → ι => j (ent i) (c i)) hCs hZ a i

end Main

end GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemInjectiveExtensionStatement
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finset_system_injective_extension : ∀ {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W] [Module K W] {Λ : Type} (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι), (∀ l, good' l → T l ≠ Finset.univ) → ∀ (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W), (∀ S, Function.Injective (j S)) → (∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) → (∀ S w, (∃ x, j S x = w) ↔ w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S})) → ExP M r := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis <;> assumption)
end
end
