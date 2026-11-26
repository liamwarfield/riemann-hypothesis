module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.FrameRingGlRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames

namespace GlobalTheory.Reg.BorelGroupoid

section Tri

variable {S : Type} [CommRing S] {n : ℕ}

theorem lower_mul (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) : ∀ i j, i < j → (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i < k
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (lt_of_le_of_lt (not_lt.mp hk) hij), mul_zero]

theorem lower_mul_diag (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hB k i h, mul_zero]
  · rw [hA i k h, zero_mul]

theorem lower_of_mul_eq_one (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : B * A = 1) : ∀ i j, i < j → B i j = 0 := by
  have h : A.BlockTriangular OrderDual.toDual := fun i j hij => hA i j hij
  have hd : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hB
  letI := Matrix.invertibleOfIsUnitDet A hd
  have h' := Matrix.blockTriangular_inv_of_blockTriangular h
  rw [Matrix.inv_eq_left_inv hB] at h'
  exact fun i j hij => h' hij

end Tri

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem chg_refl (y : FrPt Xo c S) : FrChg (fun _ => 1) 1 y y := by
  refine ⟨rfl, fun τ i => ?_, (Model.secBC_id_iff _ _ _ _).2 fun i => ?_⟩
  · have h := Formalism.L2.PjFree.isCombAt_single (y.tan τ) i
    have e : (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) i = Pi.single i 1 := by
      funext j
      rw [Matrix.one_apply, Pi.single_apply]
      simp only [eq_comm]
    rw [← e] at h
    exact h
  · rw [Model.scal_one, _root_.one_mul]

theorem chg_comp {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a a' : S}
    {y y' y'' : FrPt Xo c S} (h : FrChg g a y y') (h' : FrChg g' a' y' y'') :
    FrChg (fun τ => g' τ * g τ) (a' * a) y y'' := by
  obtain ⟨hx, hc, hs⟩ := h
  obtain ⟨hx', hc', hs'⟩ := h'
  obtain ⟨x', xo', u', t', e', b', s', gen'⟩ := y'
  obtain ⟨x'', xo'', u'', t'', e'', b'', s'', gen''⟩ := y''
  dsimp only at hx hx' hc hc' hs hs'
  subst hx'
  subst hx
  refine ⟨rfl, fun τ i => ?_, (Model.secBC_id_iff _ _ _ _).2 fun i => ?_⟩
  · have h := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (u' τ) (g τ).transpose
      (g' τ i) (u'' τ i) (fun k => hc τ k) (hc' τ i)
    have e : (g τ).transpose.mulVec (g' τ i) = (g' τ * g τ) i := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => _root_.mul_comm _ _
    rw [e] at h
    exact h
  · have e1 := (Model.secBC_id_iff _ _ _ _).1 hs i
    have e2 := (Model.secBC_id_iff _ _ _ _).1 hs' i
    dsimp only
    rw [e2, e1, Model.scal_mul, _root_.mul_assoc]

end Geo

theorem frBor_groupoid : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ y : FrPt Xo c S, FrBor 1 y y) ∧ (∀ (t t' : Ix Dw → Sˣ) (y y' y'' : FrPt Xo c S), FrBor t y y' → FrBor t' y' y'' → FrBor (t * t') y y'') ∧ (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t⁻¹ y' y) ∧ ∀ (t t' : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t' y y' → t = t' := by
  intro E _ _ _ H Dw l Xo c S _ _
  refine ⟨fun y => ?_, fun t t' y y' y'' h h' => ?_, fun t y y' h => ?_, fun t t' y y' h h' => ?_⟩
  · refine (Model.frBor_iff _ _ _).2 ⟨fun _ => 1, fun τ i => ?_, fun τ i j hij => ?_, chg_refl y⟩
    · exact Matrix.one_apply_eq i
    · exact Matrix.one_apply_ne hij.ne
  · obtain ⟨g, hd, hz, hc⟩ := (Model.frBor_iff _ _ _).1 h
    obtain ⟨g', hd', hz', hc'⟩ := (Model.frBor_iff _ _ _).1 h'
    refine (Model.frBor_iff _ _ _).2 ⟨fun τ => g' τ * g τ, fun τ i => ?_,
      fun τ => lower_mul _ _ (hz' τ) (hz τ), ?_⟩
    · show (g' τ * g τ) i i = _
      rw [lower_mul_diag _ _ (hz' τ) (hz τ), hd, hd', Pi.mul_apply, Units.val_mul, _root_.mul_comm]
    · rw [Pi.mul_apply, Units.val_mul, _root_.mul_comm]
      exact chg_comp hc hc'
  · obtain ⟨g, hd, hz, hc⟩ := (Model.frBor_iff _ _ _).1 h
    obtain ⟨g', a', hc'⟩ := Model.exists_frChg y' y hc.1.symm
    obtain ⟨e1, e2⟩ := Model.frChg_unique (chg_comp hc hc') (chg_refl y)
    have hinv : ∀ τ, g' τ * g τ = 1 := fun τ => congrFun e1 τ
    have hz' : ∀ τ i j, i < j → g' τ i j = 0 := fun τ => lower_of_mul_eq_one _ _ (hz τ) (hinv τ)
    refine (Model.frBor_iff _ _ _).2 ⟨g', fun τ i => ?_, hz', ?_⟩
    · have h2 := lower_mul_diag _ _ (hz' τ) (hz τ) i
      rw [hinv, Matrix.one_apply_eq, hd] at h2
      rw [Pi.inv_apply]
      exact Units.eq_inv_of_mul_eq_one_right h2.symm
    · have : a' = ((t⁻¹ none : Sˣ) : S) := by
        rw [Pi.inv_apply]
        exact Units.eq_inv_of_mul_eq_one_right e2
      exact this ▸ hc'
  · obtain ⟨g, hd, -, hc⟩ := (Model.frBor_iff _ _ _).1 h
    obtain ⟨g', hd', -, hc'⟩ := (Model.frBor_iff _ _ _).1 h'
    obtain ⟨e1, e2⟩ := Model.frChg_unique hc hc'
    funext k
    apply Units.ext
    rcases k with _ | ⟨τ, i⟩
    · exact e2
    · rw [← hd, ← hd', e1]

end GlobalTheory.Reg.BorelGroupoid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidPropertiesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameBorel_groupoid_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ y : FrPt Xo c S, FrBor 1 y y) ∧ (∀ (t t' : Ix Dw → Sˣ) (y y' y'' : FrPt Xo c S), FrBor t y y' → FrBor t' y' y'' → FrBor (t * t') y y'') ∧ (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t⁻¹ y' y) ∧ ∀ (t t' : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t' y y' → t = t' := by
  first | exact @GlobalTheory.Reg.BorelGroupoid.frBor_groupoid | exact GlobalTheory.Reg.BorelGroupoid.frBor_groupoid | (intros; apply GlobalTheory.Reg.BorelGroupoid.frBor_groupoid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombination
noncomputable section

namespace GlobalTheory.Reg.VecComb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {M : MChart Y}
  {R : Type} [CommRing R]

theorem comb_unique {x : Sp R ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)} {a : Fin m → R}
    {w w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by
  obtain ⟨u, hu1, hu2⟩ := h
  obtain ⟨u', hu1', hu2'⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu1 i).trans (hu1' i).symm)
  rw [← hu2, ← hu2', e]

theorem comb_exists {x : Sp R ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, v j ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (a : Fin m → R) :
    ∃ w, IsCombAt x v a w := by
  refine ⟨_, fun i => Over.homMk (spMap (epsMul (a i)) ≫ v i) ?_, fun i => rfl, rfl⟩
  show (spMap (epsMul (a i)) ≫ v i) ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x
  have e : (epsMul (a i)).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) :=
    RingHom.ext fun r => by simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [Category.assoc, hv i, ← Category.assoc, ← spMap_comp, e]

variable [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x : Sp R ⟶ Xo.X}

theorem exists_frame (Λ : M.Lift f x) : ∃ V : Fin M.n → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left),
    (∀ j, IsTanAt x (V j)) ∧ ∀ cv w, Λ.Vec cv w ↔ IsCombAt x V cv w := by
  obtain ⟨v', hv1, ⟨htan, -⟩, -⟩ := M.lie R f Λ.t' Λ.m2
  have p1 : IsGrpPullback Λ.t'.G Xo.univ.t.G x Λ.m1.φ := Λ.m1.2
  have p2 : IsGrpPullback Λ.t'.G Y.t.G (spMap f ≫ M.hU.fromSpec) Λ.m2.φ := Λ.m2.2
  refine ⟨fun j => (v' j).left ≫ Λ.m1.φ, fun j => ?_, fun cv w => ?_⟩
  · unfold IsTanAt
    constructor
    · rw [Category.assoc, p1.1.w, ← Category.assoc, Over.w (v' j)]
      rfl
    · exact (Chart.tan_push p1 (v' j)).1 (htan j)
  · unfold MChart.Lift.Vec IsCombAt
    constructor
    · rintro ⟨v'', u', hv'', hc, hw⟩
      have e : v'' = v' := funext fun j => Chart.inj_over p2 ((hv'' j).trans (hv1 j).symm)
      rw [e] at hc
      obtain ⟨u, hu1, hu2⟩ := (Chart.comb_push p1 cv v' u').1 hc
      exact ⟨u, fun i => hu1 i, hu2.trans hw⟩
    · rintro ⟨u, hu1, hu2⟩
      have hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
        rw [← hu2]
        exact Over.w (List.ofFn u).prod
      let u' : epsR R ⟶ Λ.t'.G :=
        Over.homMk (p1.1.lift w (spMap (algebraMap R (DualNumber R))) hw) (p1.1.lift_snd _ _ _)
      have hl : u'.left ≫ Λ.m1.φ = w := p1.1.lift_fst _ _ _
      exact ⟨v', u', hv1, (Chart.comb_push p1 cv v' u').2 ⟨u, fun i => hu1 i, hu2.trans hl.symm⟩, hl⟩

theorem isCombAt_iff_vec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (m : ℕ) (cv : Fin m → Fin M.n → R) (w : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (a : Fin m → R) (w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), (∀ i, Λ.Vec (cv i) (w i)) → (IsCombAt x w a w' ↔ Λ.Vec (∑ i, a i • cv i) w') := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ m cv w a w' hw
  obtain ⟨V, hV, hVec⟩ := exists_frame Λ
  have hwc : ∀ i, IsCombAt x V (cv i) (w i) := fun i => (hVec _ _).1 (hw i)
  have e : (∑ i, a i • cv i) = (Matrix.of fun j i => cv i j).mulVec a := by
    funext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have key : ∀ w'', IsCombAt x w a w'' → IsCombAt x V (∑ i, a i • cv i) w'' := by
    intro w'' h
    rw [e]
    exact GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo R x V hV w _ a w'' (fun i => hwc i) h
  have hov : ∀ {k : Fin M.n → R} {w0}, IsCombAt x V k w0 →
      w0 ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
    rintro k w0 ⟨u, -, hu⟩
    rw [← hu]
    exact Over.w (List.ofFn u).prod
  rw [hVec]
  constructor
  · exact key w'
  · intro h
    obtain ⟨w'', h''⟩ := comb_exists (fun i => hov (hwc i)) a
    exact comb_unique (key w'' h'') h ▸ h''

end GlobalTheory.Reg.VecComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombinationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCombAt_iff_coordinate_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (m : ℕ) (cv : Fin m → Fin M.n → R) (w : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (a : Fin m → R) (w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), (∀ i, Λ.Vec (cv i) (w i)) → (IsCombAt x w a w' ↔ Λ.Vec (∑ i, a i • cv i) w') := by
  first | exact @GlobalTheory.Reg.VecComb.isCombAt_iff_vec | exact GlobalTheory.Reg.VecComb.isCombAt_iff_vec | (intros; apply GlobalTheory.Reg.VecComb.isCombAt_iff_vec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUnique
noncomputable section

namespace GlobalTheory.Reg.ReframeEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FrameTangent

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]

def toM {x : Sp S ⟶ Xo.X} {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    TanM x Xo.univ.t.G :=
  mkT (ovT (t := Xo.univ.t) hv) (smT_zero_ovT (t := Xo.univ.t) hv)

theorem comb_iff {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsCombAt x v cf w ↔ (tv (∑ i, cf i • toM (hv i))).left = w := by
  have e := isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hv j)) cf w
  refine e.trans ?_
  rw [tv_comb]
  rfl

theorem comb_unique {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' :=
  ((comb_iff hv cf w).1 h).symm.trans ((comb_iff hv cf w').1 h')

theorem comb_single {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) (i : Fin m) : IsCombAt x v (Pi.single i 1) (v i) := by
  rw [comb_iff hv]
  have : ∑ j, (Pi.single i (1 : S) : Fin m → S) j • toM (hv j) = toM (hv i) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [this]
  rfl

theorem comb_exists [Algebra c.F S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (τ : E →+* ℂ)
    (hv : ∀ j, IsTanAt x (v j)) (he : ∀ j, IsEigAt c τ (v j)) (cf : Fin m → S) :
    ∃ w, IsCombAt x v cf w ∧ IsTanAt x w ∧ IsEigAt c τ w := by
  refine ⟨_, (comb_iff hv cf _).2 rfl, isTanAtG_of (t := Xo.univ.t) _ (tv_zero' _), ?_⟩
  refine (isEigAt_iff τ (tv (∑ i, cf i • toM (hv i)))).2 fun a => ?_
  have hU : ∀ i, actL (x0 := x) Xo.univ.t.act a (toM (hv i)) = algebraMap c.F S (embK c τ a) • toM (hv i) :=
    fun i => tv_injective ((isEigAt_iff τ (ovT (t := Xo.univ.t) (hv i))).1 (he i) a)
  have : actL (x0 := x) Xo.univ.t.act a (∑ i, cf i • toM (hv i)) =
      algebraMap c.F S (embK c τ a) • ∑ i, cf i • toM (hv i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hU, smul_comm]
  exact congrArg tv this

theorem exists_reframe [Algebra c.F S] (y : FrPt Xo c S)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hg : ∀ τ, IsUnit (g τ).det) :
    ∃ y', Reframe g y y' := by
  choose u hu ht he using fun τ i => comb_exists τ (y.tan τ) (y.eig τ) (fun j => g τ j i)
  refine ⟨⟨y.x, y.x_over, u, ht, he, fun τ w hw hw' => ?_, y.s, y.gen⟩, rfl, hu⟩
  obtain ⟨a, ha, hua⟩ := y.basis τ w hw hw'
  have key : ∀ b w', IsCombAt y.x (u τ) b w' → IsCombAt y.x (y.u τ) ((g τ).mulVec b) w' := fun b w' h =>
    GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (u τ) (g τ) b w' (hu τ) h
  refine ⟨(g τ)⁻¹.mulVec a, ?_, fun b hb => ?_⟩
  · obtain ⟨w', h1, -, -⟩ := comb_exists τ (ht τ) (he τ) ((g τ)⁻¹.mulVec a)
    have h2 := key _ _ h1
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hg τ), Matrix.one_mulVec] at h2
    show IsCombAt y.x (u τ) ((g τ)⁻¹.mulVec a) w
    rw [comb_unique (y.tan τ) ha h2]
    exact h1
  · rw [← hua _ (key b w hb), Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hg τ), Matrix.one_mulVec]

theorem existsUnique_reframe [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) :
    ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S,
      (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' := by
  have ht' : ∀ τ i, IsTanAt y.x (y'.u τ i) := fun τ i => hx ▸ y'.tan τ i
  have hb' : ∀ τ w, IsTanAt y.x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt y.x (y'.u τ) a w := by
    rw [← hx]; exact y'.basis
  choose a ha hua using fun τ i => y.basis τ (y'.u τ i) (ht' τ i) (y'.eig τ i)
  choose b hb _ using fun τ i => hb' τ (y.u τ i) (y.tan τ i) (y.eig τ i)
  refine ⟨fun τ => Matrix.of fun j i => a τ i j, ⟨fun τ => ?_, hx, ha⟩, fun g hg => ?_⟩
  · have hm : (Matrix.of fun j i => a τ i j) * (Matrix.of fun j i => b τ i j) = 1 := by
      ext j i
      have h1 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (y'.u τ)
        (Matrix.of fun j i => a τ i j) (b τ i) (y.u τ i) (ha τ) (hb τ i)
      have h2 := (y.basis τ (y.u τ i) (y.tan τ i) (y.eig τ i)).unique h1 (comb_single (y.tan τ) i)
      have h3 := congrFun h2 j
      rw [Pi.single_apply] at h3
      rw [Matrix.one_apply, ← h3]
      rfl
    exact Matrix.isUnit_det_of_right_inverse hm
  · funext τ
    ext j i
    exact congrFun (hua τ i _ (hg.2.2 τ i)) j

theorem reframe_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), (∀ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) → ∃ y', Reframe g y y') ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ y => ⟨exists_reframe y, existsUnique_reframe y⟩

end GlobalTheory.Reg.ReframeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTriangularReframe_exists_and_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), (∀ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) → ∃ y', Reframe g y y') ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' := by
  first | exact @GlobalTheory.Reg.ReframeEx.reframe_exists_unique | exact GlobalTheory.Reg.ReframeEx.reframe_exists_unique | (intros; apply GlobalTheory.Reg.ReframeEx.reframe_exists_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCBaseValAtCx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.exists_cBase_valAtCx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∃ yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)), (∀ Z, CBase h Z (yP Z)) ∧ ValAtCx h yP ∧ GenFromTest Xo c h := by
  intro E _ _ _ H Dw l Xo c hL h
  have hex : ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ z : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) z :=
    fun Z P => hL.bc _ _ (PAlg P) (genFr h Z)
  choose yP hyP using hex
  refine ⟨yP, fun Z P => hyP Z P, fun Z P a n f hf => ?_, fun Z => hL.test _ _⟩
  have e := GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf (Om Z) (CAt (sgOf P)) (PAlg P)
    (genFr h Z) (yP Z P) (hyP Z P)
  rw [e]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularReframeCompBaseChangeBorel
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularReframeCompBaseChangeBorel
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]

theorem reframe_scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  unfold scal Out.liftFun
  simp only [map_mul]

theorem reframe_scal_one (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  unfold scal Out.liftFun
  simp only [map_one]

theorem generators_unit {x : Sp S ⟶ Xo.X} (s s' : LB.Sec (PPx x))
    (hs : ∀ r : LB.Sec (PPx x), ∃! a : S, ∀ i, r.f i = scal x a i * s.f i)
    (hs' : ∀ r : LB.Sec (PPx x), ∃! a : S, ∀ i, r.f i = scal x a i * s'.f i) :
    ∃ a : Sˣ, ∀ i, s'.f i = scal x (a : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c, -, hc⟩ := hs s
  have h1 : b * a = c := hc _ fun i => by rw [reframe_scal_mul, _root_.mul_assoc, ← ha i, ← hb i]
  have h2 : (1 : S) = c := hc _ fun i => by rw [reframe_scal_one, _root_.one_mul]
  exact ⟨⟨a, b, by rw [mul_comm, h1, ← h2], by rw [h1, ← h2]⟩, ha⟩

variable [Algebra c.F S]

theorem Reframe.trans {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {y y' y'' : FrPt Xo c S}
    (h : Reframe g y y') (h' : Reframe g' y' y'') : Reframe (fun τ => g τ * g' τ) y y'' := by
  obtain ⟨hx, hc⟩ := h
  obtain ⟨hx', hc'⟩ := h'
  refine ⟨hx'.trans hx, fun τ i => ?_⟩
  have h2 := hc' τ i
  rw [hx] at h2
  exact GlobalTheory.TangentLinear.isCombAt_mulVec _ _ _ _ _ _ _ (y.u τ) (y.tan τ) (y'.u τ) (g τ) (fun j => g' τ j i)
    (y''.u τ i) (hc τ) h2

theorem Reframe.baseChange {T : Type} [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T}
    (h : Reframe g y y') (hz : FrMap φ y z) (hz' : FrMap φ y' z') : Reframe (fun τ => (g τ).map φ) z z' := by
  obtain ⟨hx, hc⟩ := h
  obtain ⟨hzx, hzu, -⟩ := hz
  obtain ⟨hzx', hzu', -⟩ := hz'
  refine ⟨by rw [hzx', hzx, hx], fun τ i => ?_⟩
  exact isCombAt_pull φ.toRingHom hzx (hzu τ) (hzu' τ i) (hc τ i)

private theorem appLE_id_apply' {X : Scheme} (U : X.Opens) (e : U ≤ (𝟙 X) ⁻¹ᵁ U) (r : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U e).hom r = r := by
  change (X.presheaf.map (𝟙 (Opposite.op U))).hom r = r
  rw [X.presheaf.map_id]
  rfl

theorem frBor_iff_reframe (y y' : FrPt Xo c S) : (∃ t : Ix Dw → Sˣ, FrBor t y y') ↔
    ∃ b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S,
      (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧ Reframe b y y' := by
  constructor
  · rintro ⟨t, hx, hcomb, -⟩
    choose cf hcf1 hcf2 hcf3 using hcomb
    refine ⟨fun τ j i => cf τ i j, fun τ => ⟨fun p q hpq => hcf2 τ q p hpq, fun p => ?_⟩, hx, fun τ i => hcf3 τ i⟩
    show IsUnit (cf τ p p)
    rw [hcf1 τ p]
    exact Units.isUnit _
  · rintro ⟨b, hb, hx, hcomb⟩
    cases y'
    dsimp only at hx hcomb ⊢
    subst hx
    obtain ⟨a, ha⟩ := generators_unit y.s _ y.gen ‹_›
    obtain ⟨t, ht0, ht1⟩ : ∃ t : Ix Dw → Sˣ, t none = a ∧ ∀ τ i, (t (some ⟨τ, i⟩) : S) = b τ i i :=
      ⟨fun o => o.elim a fun p => ((hb p.1).2 p.2).unit, rfl, fun τ i => ((hb τ).2 i).unit_spec⟩
    refine ⟨t, rfl, fun τ i => ⟨fun j => b τ j i, (ht1 τ i).symm, fun j hij => (hb τ).1 hij, hcomb τ i⟩,
      𝟙 _, Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
    rw [ht0, ← ha i]
    exact appLE_id_apply' _ _ _

end

theorem reframe_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' y'' : FrPt Xo c S), Reframe g y y' → Reframe g' y' y'' → Reframe (fun τ => g τ * g' τ) y y'') ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), Reframe g y y' → FrMap φ y z → FrMap φ y' z' → Reframe (fun τ => (g τ).map φ) z z') ∧ ∀ y y' : FrPt Xo c S, (∃ t : Ix Dw → Sˣ, FrBor t y y') ↔ ∃ b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧ Reframe b y y' := by
  intro E _ _ _ H Dw l Xo c S _ _
  exact ⟨fun g g' y y' y'' h h' => Reframe.trans h h',
    fun T _ _ φ g y y' z z' h hz hz' => Reframe.baseChange φ h hz hz', fun y y' => frBor_iff_reframe y y'⟩

end GlobalTheory.Reg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularReframeCompBaseChangeBorelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangularReframe_comp_baseChange_borel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' y'' : FrPt Xo c S), Reframe g y y' → Reframe g' y' y'' → Reframe (fun τ => g τ * g' τ) y y'') ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), Reframe g y y' → FrMap φ y z → FrMap φ y' z' → Reframe (fun τ => (g τ).map φ) z z') ∧ ∀ y y' : FrPt Xo c S, (∃ t : Ix Dw → Sˣ, FrBor t y y') ↔ ∃ b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, IsUnit (b τ i i)) ∧ Reframe b y y' := by
  first | exact @GlobalTheory.Reg.reframe_calculus | exact GlobalTheory.Reg.reframe_calculus | (intros; apply GlobalTheory.Reg.reframe_calculus <;> assumption)
end
end
