module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsChartPull
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRham

open GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.Published GlobalTheory.Published.AbelianDeRham

variable {R R' : Type} [CommRing R] [CommRing R']

theorem tanVal_baseChange {σ : R →+* R'} {A : Over (Sp R)} {B : Over (Sp R')} {φ : B.left ⟶ A.left}
    (m : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R') (B.hom ≫ 𝟙 _) σ φ) {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (e : v'.left ≫ φ = spMap (dualMap σ) ≫ v.left) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal v' (m.pullForm f) = σ (tanVal v f) := by
  let E := SqExt.dual R
  let E' := SqExt.dual R'
  have hy := pt_w v
  have hy' := pt_w v'
  have hc : ∀ r : R, dualMap σ (algebraMap R (DualNumber R) r) = algebraMap R' (DualNumber R') (σ r) := fun r => by
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have e₀ : spMap σ ≫ spMap (E.π : E.C →+* E.B) ≫ v.left = (spMap (E'.π : E'.C →+* E'.B) ≫ v'.left) ≫ φ := by
    rw [Category.assoc, e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    ext a <;> simp [dualMap, E, E', TrivSqZeroExt.algebraMap_eq_inl]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { dualMap σ with commutes' := hc }
      φ₀ := σ
      comm := fun b => by
        change σ b.fst = (dualMap σ b).fst
        simp [dualMap]
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => by
        have ha' : a.fst = 0 := ha
        change (dualMap σ a).fst = 0
        simp [dualMap, ha']
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { dualMap σ with commutes' := hc } e.symm
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { σ with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => (hc c).symm
  have k : E'.val v'.left hy' (m.pullForm f).1 = dualMap σ (E.val v.left hy f.1) :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      ((add_sub_add_right_eq_sub (G := E'.C) _ _ _).trans (map_sub (dualMap σ) _ _).symm)
  rw [tanVal_apply, tanVal_apply]
  refine (congrArg (TrivSqZeroExt.snd (R := R')) k).trans ?_
  exact zero_add _

section

variable [Algebra R R'] {A : Over (Sp R)} [GrpObj A] {B : Over (Sp R')} [GrpObj B] {φ : B.left ⟶ A.left}
  {hφ : IsGrpPullback B A (spMap (algebraMap R R')) φ}

theorem mem_Fil_of_corr (hF : PrimitiveSubmodule B = Submodule.span R' ((bcMor hφ).pull '' (PrimitiveSubmodule A))) {h : HdR A}
    {h' : HdR B} (e : (bcMor hφ).Corr h h') (hh : h ∈ Fil A) : h' ∈ Fil B := by
  rw [Fil, hF, Submodule.mem_dualAnnihilator]
  intro c hc
  refine (Submodule.span_le (p := LinearMap.ker h')).2 (fun c hc => ?_) hc
  obtain ⟨c, hc, rfl⟩ := hc
  exact (e c).trans (by rw [(Submodule.mem_dualAnnihilator _).1 hh c hc, map_zero])

theorem IsLieImage.baseChange (hF : PrimitiveSubmodule B = Submodule.span R' ((bcMor hφ).pull '' (PrimitiveSubmodule A)))
    (hL : LieExact B) {h : HdR A} {h' : HdR B} (e : (bcMor hφ).Corr h h') {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (ev : v'.left ≫ φ = spMap (dualMap (algebraMap R R')) ≫ v.left) (hv : IsLieImage h v) : IsLieImage h' v' := open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in open scoped CategoryTheory.Obj in by
  have ht : IsTangent v' := ArcQ.NormalForm.isTangent_baseChange hφ ev hv.1
  obtain ⟨k, hk⟩ := hL.2 v' ht
  have : h' - k ∈ Fil B := by
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro c hc
    refine (Submodule.span_le (p := LinearMap.ker (h' - k))).2 (fun c hc => ?_) hc
    obtain ⟨⟨c, hc'⟩, hc, rfl⟩ := hc
    change c ∈ F1 _ at hc
    rw [hodgeFiltration_eq_range] at hc
    obtain ⟨f, rfl⟩ := hc
    change h' _ - k _ = 0
    rw [e, hv.2 f hc', ← tanVal_baseChange (bcMor hφ).isMor ev f, sub_eq_zero]
    exact (hk.2 _ ((bcMor hφ).pullback_mem_primitive hc')).symm
  refine ⟨ht, fun f hf => ?_⟩
  rw [← hk.2 f hf, ← sub_eq_zero]
  exact mem_Fil.1 this f hf


set_option maxHeartbeats 1000000 in
theorem IsKSValue.baseChange (P : AbelianDeRham) {A' : Over (Sp (DualNumber R))} [GrpObj A']
    {B' : Over (Sp (DualNumber R'))} [GrpObj B'] {g : ℕ} (hA : IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {i : A.left ⟶ A'.left} {j : B.left ⟶ B'.left}
    {h : IsGrpPullback A A' (epsRed R) i} (h' : IsGrpPullback B B' (epsRed R') j) {φ' : B'.left ⟶ A'.left}
    (hφ' : IsGrpPullback B' A' (spMap (dualMap (algebraMap R R'))) φ') (sq : j ≫ φ' = φ ≫ i)
    {f : HdR A} {f' : HdR B} (e : (bcMor hφ).Corr f f') {v : epsR R ⟶ A} {v' : epsR R' ⟶ B}
    (ev : v'.left ≫ φ = spMap (dualMap (algebraMap R R')) ≫ v.left) (hv : IsKSValue h f v) :
    IsKSValue h' f' v' := by
  obtain ⟨-, PH, PB, PR, -⟩ := P
  have st : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {b : S' ⟶ S}
      {q : G'.left ⟶ G.left}, IsGrpPullback G' G b q → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom →
      IsAbelianScheme G' ∧ SmoothOfRelativeDimension g G'.hom := fun k l =>
    ⟨PolPull.isAbelianScheme_of_isGrpPullback l.1 k,
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback k.1 l.2⟩
  have a₀ := st h ⟨hA, hg⟩
  have b₁ := st hφ' ⟨hA, hg⟩
  have b₀ := st hφ a₀
  let : Algebra (DualNumber R) (DualNumber R') := (dualMap (algebraMap R R')).toAlgebra
  obtain ⟨bc₀, hF₀⟩ := PB R A g a₀.1 a₀.2 R' B φ hφ
  obtain ⟨bc₁, hF₁⟩ := PB _ A' g hA hg _ B' φ' hφ'
  have su : ∀ (S : Type) [CommRing S], Function.Surjective (TrivSqZeroExt.fstHom S S S).toRingHom :=
    fun S _ r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have rA := PR _ A' g hA hg _ (epsDP R) (isDPNilpotent_squareZero _) R _ (su R) rfl A i h
  have rB := PR.crysToDR_bijective b₁.1 b₁.2 (κ := epsDP R') (isDPNilpotent_squareZero _) (su R') rfl h'
  obtain ⟨k, ⟨d, hd, ed⟩, hk⟩ := hv
  obtain ⟨k', ek⟩ := bc₀.exists k
  obtain ⟨x', ex⟩ := bc₁.exists (crysToDR (epsDP R) h d)
  obtain ⟨d', rfl⟩ := rB.2 x'
  have m : GrpMor (epsDP R) (epsRed R) A (epsDP R') (epsRed R') B (dualMap (algebraMap R R'))
      (spMap (algebraMap R R')) φ :=
    GrpMor.of_isGrpPullback (isDPMorphism_sqDP _ _ _ fun a ha => by
      have ha' : a.fst = 0 := ha
      change (dualMap (algebraMap R R') a).fst = 0
      simp [dualMap, ha']) (by
      rw [← Cris.spMap_comp, ← Cris.spMap_comp]
      congr 1
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]) hφ
  have em : m.Corr d d' := fun c => by
    obtain ⟨c, rfl⟩ := rA.2 c
    have n := (liftMor (epsDP R) h).comp m
    rw [GrpMor.pull_pull (liftMor (epsDP R) h) m n (fun _ => rfl) rfl c,
      ← GrpMor.pull_pull (bcMor hφ') (liftMor (epsDP R') h') n (fun _ => rfl) sq c]
    exact ex c
  refine ⟨k', ⟨d', mem_Fil_of_corr (hφ := hφ') hF₁ ex hd, fun c => ?_⟩,
    hk.baseChange (hφ := hφ) hF₀ (PH R' B g b₀.1 b₀.2).1 ek ev⟩
  obtain ⟨z, rfl⟩ := bc₀.2 c
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero, LinearMap.map_zero, LinearMap.map_zero]
    simp
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy]
    ext <;> simp
  | tmul r c =>
    have n := (constMor A).comp m
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, map_smul,
      GrpMor.pull_pull (bcMor hφ) (constMor B) n (fun _ => by
        ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c,
      ← GrpMor.pull_pull (constMor A) m n (fun _ => rfl) rfl c, em, ed, e, ek]
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def, mul_comm]

end

theorem IsPolForm.pull_comp {A : Over (Sp R)} [GrpObj A] {B : Over (Sp R')} [GrpObj B] {σ : R →+* R'}
    {b : Sp R' ⟶ Sp R} {φ : B.left ⟶ A.left} (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) B σ b φ)
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {π : A.left ⟶ X} {ψ : LinearMap.BilinForm R (HdR A)}
    (h : IsPolForm (dp0 R) (𝟙 _) A (L.pull π) ψ) :
    ∃ ψ', IsPolForm (dp0 R') (𝟙 _) B (L.pull (φ ≫ π)) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hc, e⟩, h'⟩ := h.pull m
  refine ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (pull_isLB hL _) _)
    (pull_isLB hL _) ?_ _ hc, e⟩, h'⟩
  exact LBIso.chartPull (Geo.Tor.chartPullPull (L.pull π) φ φ rfl) (chartPullSame L _ _ _ φ fun _ => rfl)
    (ChernExists.lbIso_refl (pull_isLB hL π))

end GlobalTheory.DeRham

namespace GlobalTheory.FlagTan

open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Field

variable {K K' : Type} [Field K] [Algebra c.F K] [Field K'] [Algebra c.F K'] {K₀ : Type} [CommRing K₀]
  [Algebra c.F K₀] {ι : Type} [Fintype ι] {Φ : Finset (E →+* ℂ)} {ψ : K →ₐ[c.F] K'} {y : FrPt Xo c K}
  {y' : FrPt Xo c K'}


open scoped CategoryTheory.Obj in
theorem exists_isGrpPullback {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    ∃ (G' : Over S') (_ : GrpObj G') (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ :=
  ⟨_, inferInstance, _, isGrpPullback_pullback G f⟩

theorem IsKS.baseChange (P : AbelianDeRham) (h : FrMap ψ y y') {x : Sp (DualNumber K) ⟶ Xo.X} {M : HIx Dw Φ → K}
    (hM : IsKS Φ y x M) : IsKS Φ y' (spMap (dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in open scoped CategoryTheory.Obj in by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  let : Algebra K K' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap K K'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (dualMap (algebraMap K K')))
  have e₀ : spMap (algebraMap K K') ≫ DeRham.epsRed K = DeRham.epsRed K' ≫ spMap (dualMap (algebraMap K K')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ DeRham.epsRed K') ≫ spMap (dualMap (algebraMap K K')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (DeRham.epsRed K') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 K A _ hA gA K' B φ hφ
  have hL := (P.2.1 K' B _ (PolPull.isAbelianScheme_of_isGrpPullback hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  choose tv htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1]
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, ArcQ.NormalForm.isLieComb_baseChange hφ (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp

end Field

section Norm

variable {T T' : CDVR} {io : c.F →+* T.Fr} {io' : c.F →+* T'.Fr} {K₀ : Type} [CommRing K₀] [Algebra c.F K₀]
  {ι : Type} [Fintype ι] {Φ : Finset (E →+* ℂ)}

variable (P : AbelianDeRham) (ψ : letI := io.toAlgebra; CoefHom c io' T.Fr) {r : ℕ} (hr : 0 < r)
  (hψ : ∀ x, vV T'.V (ψ x) = (r : ℤ) * vV T.V x) {φ : CoefHom c io K₀} {φ' : CoefHom c io' K₀}
  (hφ : ∀ a, ψ (φ a) = φ' a) {y : IntFr Xo c T io} {y' : IntFr Xo c T' io'}
  (h : letI := io.toAlgebra; letI := io'.toAlgebra; FrMap ψ y.1 y'.1) {e : Ix Dw → ℤ} {s₀ : RulK Xo c K₀}
  (h₀ : s₀ ∈ secK Xo c K₀ e) {s : ι → RulK Xo c K₀} (hs : ∀ i, s i ∈ secK Xo c K₀ e)



variable (k : letI := io.toAlgebra; KSIso Φ y.1) (k' : letI := io'.toAlgebra; KSIso Φ y'.1)

end Norm

end GlobalTheory.FlagTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCmPtFrPolyNeZero
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj GlobalTheory.LamT

namespace GlobalTheory.CMDetect

theorem exists_half_max {α : Type} (s : Set α) (f : α → ℝ) (C : ℝ) (hC : ∀ x ∈ s, f x ≤ C) {x₁ : α} (hx₁ : x₁ ∈ s)
    (hpos : 0 < f x₁) : ∃ z ∈ s, (∀ x ∈ s, f x ≤ 2 * f z) ∧ 0 < f z := by
  have hb : BddAbove (f '' s) := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  have hle : ∀ x ∈ s, f x ≤ sSup (f '' s) := fun x hx => le_csSup hb ⟨x, hx, rfl⟩
  have h1 := hle x₁ hx₁
  obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (s := f '' s) ⟨_, x₁, hx₁, rfl⟩
    (show sSup (f '' s) / 2 < sSup (f '' s) by linarith)
  exact ⟨z, hz, fun x hx => by linarith [hle x hx], by linarith⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_maj_lower (X : FD.DataX E r) (hr : 0 < r) {z : FD.Frame X.Ψ r} (hz : z ∈ X.dom) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ v ∈ X.L', v ≠ 0 → s ^ 2 ≤ ∑ τ, X.maj z τ (FD.Data.emb τ.1 v) := by
  have hnn : ∀ τ v, 0 ≤ X.maj z τ v := fun τ v => FD.MajorantConjugateTransfer.maj_nonneg X.toData hz τ v
  have hc : ∀ τ, X.c τ = X.k0 := fun τ => by
    unfold FD.Data.c
    rw [X.ξ0_abs τ]
    ring
  have hk := X.minWeight_pos
  have hN : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  have hla : 0 < X.firstMinimumSq z := Real.sqrt_pos.1 (AR.Up.ModeHalfC.first_minimum_pos X.toData hz (by
    by_contra h
    push Not at h
    have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      exact h
    rw [X.Λ_span] at h1
    have : (Pi.single ⟨0, hr⟩ (1 : E) : Fin r → E) ∈ (⊤ : Submodule E (Fin r → E)) := Submodule.mem_top
    rw [h1, Submodule.mem_bot] at this
    have := congrFun this ⟨0, hr⟩
    simp at this))
  have hm : 0 < X.firstMinimumSq z / (X.k0 * (X.NC : ℝ) ^ 2) := by positivity
  refine ⟨Real.sqrt (min 1 (X.firstMinimumSq z / (X.k0 * (X.NC : ℝ) ^ 2))), Real.sqrt_pos.2 (lt_min one_pos hm),
    Real.sqrt_le_one.2 (min_le_left _ _), fun v hv hv0 => ?_⟩
  rw [Real.sq_sqrt (lt_min one_pos hm).le]
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj z τ (FD.Data.emb τ.1 v)} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, -, -, rfl⟩
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (by rw [hc]; exact hk.le) (hnn τ _)
  have hne : (X.NC : E) • v ≠ 0 := smul_ne_zero (by exact_mod_cast X.NC_pos.ne') hv0
  have h1 : X.firstMinimumSq z ≤ ∑ τ, X.c τ * X.maj z τ (FD.Data.emb τ.1 ((X.NC : E) • v)) :=
    csInf_le hb ⟨_, X.NC_sub v hv, hne, rfl⟩
  refine h1.trans (le_of_eq ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : FD.Data.emb τ.1 ((X.NC : E) • v) = (((X.NC : ℝ) : ℂ)) • FD.Data.emb τ.1 v := by
    funext a
    simp [FD.Data.emb]
  rw [e, FD.FlowMajorantFlags.maj_smul X.toData hz, hc]
  ring

theorem exists_cm_frame (X : FD.DataX E r) (Y : FD.Data E r) (hX : X.toData = Y) (hr : 0 < r) (la : FD.Wt Y.Ψ r)
    (P : FD.Frame Y.Ψ r → ℂ) (hP : Y.IsBddSec la P) {x₁ : FD.Frame Y.Ψ r} (hx₁ : x₁ ∈ Y.dom) (hne : P x₁ ≠ 0) :
    ∃ (La : ℝ) (x : FD.Frame Y.Ψ r) (lam : Fin r → Fin r → E), x ∈ Y.dom ∧ FD.LamBasis X La (hX ▸ x) lam ∧
      P x ≠ 0 := by
  subst hX
  obtain ⟨hS, C, hC⟩ := hP
  have hpos : 0 < X.pnorm la P x₁ := by
    have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), FD.dmin X.Gm x₁ τ i ≠ 0 := fun τ i h => by
      have := (hx₁ τ).2 i
      rw [h, Complex.zero_re, mul_zero] at this
      exact lt_irrefl _ this
    refine mul_pos (norm_pos_iff.2 hne) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos ?_ _)
    exact norm_pos_iff.2 (div_ne_zero (hd τ _) (hd τ _))
  obtain ⟨z, hz, hhalf, hzpos⟩ := exists_half_max X.dom (X.pnorm la P) C hC hx₁ hpos
  obtain ⟨s, hs0, hs1, hs⟩ := exists_maj_lower X hr hz
  obtain ⟨x, lam, hx, hB, hPx, -⟩ := Formalism.L2.Pj.FundamentalDomainD5.t41H_statement r X la P z s (max 1 (∑ τ, X.spread la τ)) hS hz
    hhalf hzpos (le_max_right _ _) (le_max_left _ _) hr hs0 hs1 hs
  exact ⟨_, x, lam, hx, hB, hPx⟩

theorem exists_good_cmPt_frPoly_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), IsUnf U → 0 < r → (∀ k, ∃ (Xx : FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), Xx.toData = U.X k ∧ 𝔄 ≠ 0 ∧ Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u}) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, F ≠ 0 → (∀ k, (U.X k).IsBddSec (laU U a n k) (rdU U F k)) → ∃ (z : CMPt Xo c) (La : ℝ), z.Good (Module.finrank ℚ E / 2) La ∧ ∀ G, IsFrPoly F z.y G → G ≠ 0 := by
  intro E _ _ _ H Dw l Xo c _ hstar r U hU hr hdat a n F hF hF0 hbdd
  classical
  have hinj := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ r
    (Formalism.L2.PjFree.Unf.ofPj U) ((Formalism.L2.PjFree.isUnf_ofPj U).2 hU) a n).2 F hF
  have hex : ∃ k, ∃ x ∈ (U.X k).dom, rdU U F k x ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (hinj h)
  obtain ⟨k, x₁, hx₁, hne₁⟩ := hex
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := hdat k
  obtain ⟨La, x, lam, hx, hB, hne⟩ := exists_cm_frame Xx (U.X k) hX hr _ _ (hbdd k) hx₁ hne₁
  obtain ⟨z, σ₁, hz, hzx⟩ := GlobalTheory.LamT.exists_good_cmPt_at_frame E H Dw l Xo c hstar r U hU hr k ⟨x, hx⟩ Xx hX 𝔄 h𝔄 hΛ
    La lam hB
  have hev : evR Xo c F (U.un k ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x ∈ (U.X k).dom then toC (evR Xo c F (U.un k ⟨x, h⟩)) else 0) = 0
    rw [dite_eq_left hx]
    exact h0
  exact ⟨z, La, hz, fun G hG =>
    (GlobalTheory.LamT.isFrPoly_equiv_and_ne_zero E H Dw l Xo c z.K z.y a n F hF G hG).2 _ σ₁ _ hzx hev⟩

end GlobalTheory.CMDetect
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatVacSign

variable {D : D7} {S T : HSp D}

theorem cA_incA' (w : D.host.E) : cA D (incA D w) = incA D (star w) := rfl

theorem hO_smul_smul (c c' : AE D) (x y : WO S T) :
    hO S T (c • x) (c' • y) = c * cA D c' * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symplO_smul_smul (w w' : D.host.E) (x y : WO S T) :
    symplO S T (incA D w • x) (incA D w' • y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D (D.host.xi0 * (w * star w')) * hO S T x y) := by
  rw [symplO, hO_smul_smul, cA_incA', map_mul (incA D), map_mul (incA D)]
  congr 1
  ring

theorem symplOH_smul_norm {w : D.host.E} {n : ℤ} (hw : w * star w = 2 * n) (x y : WO S T) :
    symplOH S T (incA D w • x) (incA D w • y) = (n : AF D.host.F) * symplO S T x y := by
  have e : incA D (D.host.xi0 * (w * star w)) * hO S T x y =
      ((2 * n : ℤ) : AE D) * (incA D D.host.xi0 * hO S T x y) := by
    rw [hw]
    simp only [map_mul, map_intCast, map_ofNat]
    push_cast
    ring
  rw [symplOH, symplO_smul_smul, e, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, ← symplO]
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  push_cast
  linear_combination ((n : AF D.host.F) * symplO S T x y) * h2

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem char_symplOH_smul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) {w : D.host.E} {n : ℤ} (hw : w * star w = 2 * n) {x y : WO S T}
    (hx : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hy : y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    ψ (symplOH S T (incA D w • x) (incA D w • y)) = 1 := by
  rw [symplOH_smul_norm hw, ← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow,
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hx hy, _root_.one_zpow]

theorem incA_smul_finTens {m k : ℕ} (w : D.host.E) (α : Af D.host.F) (M : Matrix (Fin m) (Fin k) D.host.E) :
    incA D w • GlobalTheory.LatVac.finTens α M = GlobalTheory.LatVac.finTens α (w • M) := by
  ext i j
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] w : AE D) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j) =
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (w * M i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_mem_latO' {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (w : 𝓞 D.host.E)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    incA D (w : D.host.E) • u ∈ latO S T LS LT fun _ => True := by
  refine GlobalTheory.LatVac.latO_induction (p := fun u => incA D (w : D.host.E) • u ∈ latO S T LS LT fun _ => True)
    ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    rw [incA_smul_finTens]
    exact GlobalTheory.LatVac.finTens_mem_latO hα (GlobalTheory.LatVac.smul_mem_latRat w hM)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

def fixGroup (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (c : AE D)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplOH S T (c • x) (c • y)) = 1) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ Λ ∧ ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T (c • u) f = f}
  zero_mem' := ⟨zero_mem _, fun f _ => by rw [smul_zero, GlobalTheory.LatVac.heisO_zero]⟩
  add_mem' := by
    rintro a b ⟨ha, fa⟩ ⟨hb, fb⟩
    refine ⟨add_mem ha hb, fun f hf => ?_⟩
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ (c • a) (c • b) f
    rw [fb f hf, fa f hf, hΛ a ha b hb, one_smul, ← smul_add] at h1
    exact h1.symm
  neg_mem' := by
    rintro a ⟨ha, fa⟩
    refine ⟨neg_mem ha, fun f hf => ?_⟩
    have h1 := GlobalTheory.LatVac.heisO_heisO ψ (c • -a) (c • a) f
    rw [fa f hf, hΛ (-a) (neg_mem ha) a ha, one_smul, ← smul_add, neg_add_cancel,
      smul_zero, GlobalTheory.LatVac.heisO_zero] at h1
    exact h1

theorem mem_fixGroup {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {c : AE D}
    {hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplOH S T (c • x) (c • y)) = 1} {u : WO S T} :
    u ∈ fixGroup ψ Λ c hΛ ↔ u ∈ Λ ∧ ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T (c • u) f = f := Iff.rfl

theorem heisO_smul_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (w : 𝓞 D.host.E) {n : ℤ} (hw : (w : D.host.E) * star (w : D.host.E) = 2 * n)
    {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (f : WO S T → ℂ)
    (hf : IsLatVac (heisO ψ S T)
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f) :
    heisO ψ S T (incA D (w : D.host.E) • u) f = f := by
  have hΛ : ∀ x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ψ (symplOH S T (incA D (w : D.host.E) • x) (incA D (w : D.host.E) • y)) = 1 :=
    fun x hx y hy => char_symplOH_smul hψ hS hT hw hx hy
  have h2 : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      2 • u ∈ fixGroup ψ _ _ hΛ := by
    intro u hu
    refine mem_fixGroup.2 ⟨nsmul_mem hu 2, fun f hf => ?_⟩
    have e : incA D (w : D.host.E) • (2 • u) = 2 • (incA D (w : D.host.E) • u) := by
      rw [two_nsmul, two_nsmul, smul_add]
    rw [e]
    exact hf.1 _ (smul_mem_latO' w hu)
  have hh : ∀ e, IsSplitIdem D e →
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf e u → u ∈ fixGroup ψ _ _ hΛ := by
    intro e he u hu hh
    refine mem_fixGroup.2 ⟨hu, fun f hf => hf.2 e he _ (smul_mem_latO' w hu) fun i j => ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hh i j]
  exact (mem_fixGroup.1 (GlobalTheory.LatVac.le_of_two_of_half _ h2 hh hu)).2 f hf

theorem hRat_smul_smul (a b : D.host.E) (M N : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (a • M) (b • N) = a * star b * GlobalTheory.LatVac.hRat S T M N := by
  simp only [GlobalTheory.LatVac.hRat, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, star_mul']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem finRat_eq (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.VacUnique.finRat S T M = GlobalTheory.LatVac.finTens 1 M := by
  ext i j; rfl

theorem algebraMap_mul_pair (c : D.host.F) (β : Af D.host.F) :
    algebraMap D.host.F (AF D.host.F) c * pairA D.host.F 0 β =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) c * β) :=
  Prod.ext (mul_zero _) rfl

end GlobalTheory.LatVacSign


open GlobalTheory.LatVacSign in
theorem GlobalTheory.LatVacSign.heisO_finRat_sign : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T v v) ∧ heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) f = ((-1 : ℂ) ^ k) • f := by
  intro D ψ S T ΛS ΛT hψ hS hT f hf v hv
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have hst : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have := D.host.isCMField_hostE
    have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
      NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
    rw [h2, map_neg, h1]
    simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (D.host.d : ℤ) + 1 = 8 * n :=
    ⟨((D.host.d : ℤ) + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  have hnE : (D.host.d : D.host.E) = 8 * n - 1 := by
    have := congrArg (Int.cast (R := D.host.E)) hn
    push_cast at this
    linear_combination this
  set w₀ : D.host.E := (1 + D.host.sqrtMinusD) / 2 with hw₀
  have hstw : star w₀ = 1 - w₀ := by
    rw [hw₀, star_div₀, star_add, star_one, hst, star_ofNat]
    ring
  have hnorm : w₀ * (1 - w₀) = 2 * n := by
    rw [hw₀]
    linear_combination (-1 / 4 : D.host.E) * hsq + (1 / 4 : D.host.E) * hnE
  have hint : IsIntegral ℤ w₀ := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * n), by monicity!, ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, eq_intCast]
    push_cast
    linear_combination (-1 : D.host.E) * hnorm
  let W : 𝓞 D.host.E := ⟨w₀, hint⟩
  let W' : 𝓞 D.host.E := 1 - W
  have hW : (W : D.host.E) = w₀ := rfl
  have hW' : (W' : D.host.E) = 1 - w₀ := by
    change algebraMap (𝓞 D.host.E) D.host.E (1 - W) = 1 - w₀
    rw [map_sub, map_one]
    rfl
  have nW : (W : D.host.E) * star (W : D.host.E) = 2 * n := by rw [hW, hstw, hnorm]
  have nW' : (W' : D.host.E) * star (W' : D.host.E) = 2 * n := by
    rw [hW', star_sub, star_one, hstw, sub_sub_cancel, mul_comm, hnorm]
  set u := GlobalTheory.VacUnique.finRat S T (-v) with hu_def
  have h1 := heisO_smul_fix hψ hS hT W nW hv f hf
  have h2 := heisO_smul_fix hψ hS hT W' nW' hv f hf
  have hsum : incA D (W : D.host.E) • u + incA D (W' : D.host.E) • u = u := by
    rw [← add_smul, ← map_add (f := _), hW, hW', add_sub_cancel, map_one, one_smul]
  have key := GlobalTheory.LatVac.heisO_heisO ψ (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u) f
  rw [h2, h1, hsum] at key

  set z : D.host.E := D.host.xi0 * w₀ ^ 2 * GlobalTheory.LatVac.hRat S T v v with hz
  have hpair : symplO S T (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (Algebra.trace D.host.F D.host.E z)) := by
    rw [hu_def, finRat_eq, incA_smul_finTens, incA_smul_finTens, GlobalTheory.LatVac.symplO_finTens, one_mul, one_mul]
    congr 3
    rw [hz, ← neg_one_smul D.host.E v, smul_smul, smul_smul, hRat_smul_smul, hW, hW', star_mul', star_sub,
      star_one, hstw, star_neg, star_one]
    ring
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Algebra.trace ℚ D.host.E z = k := by
    have := GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (smul_mem_latO' W hv) (smul_mem_latO' W' hv)
    rw [hpair] at this
    exact (GlobalTheory.LatVac.char_rat hψ z).1 this
  have hsign : ψ (symplOH S T (incA D (W : D.host.E) • u) (incA D (W' : D.host.E) • u)) = (-1 : ℂ) ^ k := by
    rw [symplOH, hpair, algebraMap_mul_pair, ← map_mul, GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace D ψ hψ]
    have e : Algebra.trace ℚ D.host.F (1 / 2 * Algebra.trace D.host.F D.host.E z) = (1 / 2 : ℚ) * k := by
      have h12 : (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) := by simp
      rw [h12, ← Algebra.smul_def, map_smul, Algebra.trace_trace, hk, smul_eq_mul]
    rw [e, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  rw [hsign] at key
  refine ⟨k, hk.symm, ?_⟩
  have hsq1 : ((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_zpow]; norm_num
  calc heisO ψ S T u f = (((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k) • heisO ψ S T u f := by rw [hsq1, one_smul]
    _ = (-1 : ℂ) ^ k • f := by rw [mul_smul, ← key]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSignStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_finitePart_latticeVacuum_sign : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T v v) ∧ heisO ψ S T (GlobalTheory.VacUnique.finRat S T (-v)) f = ((-1 : ℂ) ^ k) • f := by
  first | exact @GlobalTheory.LatVacSign.heisO_finRat_sign | exact GlobalTheory.LatVacSign.heisO_finRat_sign | (intros; apply GlobalTheory.LatVacSign.heisO_finRat_sign <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricExpansionOfParts
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMult

theorem strictAnti_of_gap {r : ℕ} (hr : Odd r) {lam : Fin r → ℤ} (h : Gap lam) : StrictAnti lam := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by obtain ⟨k, hk⟩ := hr; omega⟩
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  have := h i.castSucc i.succ (by simp)
  push_cast at this
  omega

end GlobalTheory.TrMult

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEllipticElementsOfLocalLatticeIsomet
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEllipticElementsOfLocalLatticeIsomet
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory

theorem trEll_latticeConj_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n n' : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin n' → E)) (v : HeightOneSpectrum (𝓞 F)) (j : GLoc σ J v ≃ₜ* GLoc σ J' v), IsLatticeConj L L' j → XSet P (Fv F v) J' = XSet P (Fv F v) J ∧ ∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin n → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), ∃ (φ' : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)) (h' : IsIsom P (Fv F v) J' x.1.1 φ'), gam h' = j (gam h) ∧ ∀ t, torEmb h' t = j (torEmb h t) := by
  intro F E _ _ _ _ _ σ _ r n n' P J J' L L' v j hj
  obtain ⟨a, ha, -, hja⟩ := hj
  have iso : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J x φ → IsIsom P (Fv F v) J' x (φ.trans a) := by
    intro x φ h y y'
    have e := ha (φ y) (φ y')
    simp only [GlobalTheory.AdelicU.hLin, hR] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e]
    exact h y y'
  have iso' : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)),
      IsIsom P (Fv F v) J' x φ → IsIsom P (Fv F v) J x (φ.trans a.symm) := by
    intro x φ h y y'
    have e := ha (a.symm (φ y)) (a.symm (φ y'))
    simp only [GlobalTheory.AdelicU.hLin, hR, LinearEquiv.apply_symm_apply] at e
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← e]
    exact h y y'
  have tor : ∀ (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E))
      (h : IsIsom P (Fv F v) J x φ) (t : Tor P (Fv F v)), torEmb (iso x φ h) t = j (torEmb h t) := by
    intro x φ h t
    apply GlobalTheory.AdelicU.matHom_injective (Fv F v) σ J'
    apply Units.ext
    have key : ∀ w, (GlobalTheory.AdelicU.matHom _ σ J' (torEmb (iso x φ h) t)).1 *ᵥ w =
        (GlobalTheory.AdelicU.matHom _ σ J' (j (torEmb h t))).1 *ᵥ w := by
      intro w
      obtain ⟨y, rfl⟩ := (φ.trans a).surjective w
      rw [LinearEquiv.trans_apply, hja]
      change mulMat (φ.trans a) (torUnit t).1 *ᵥ (φ.trans a) y = a (mulMat φ (torUnit t).1 *ᵥ φ y)
      rw [mulMat_mulVec, mulMat_mulVec]
      rfl
    exact Matrix.ext_of_mulVec_single fun i => key _
  refine ⟨?_, fun x φ h => ⟨φ.trans a, iso _ φ h, tor _ φ h _, tor _ φ h⟩⟩
  ext q
  constructor
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a.symm, e, iso' _ φ h⟩
  · rintro ⟨x, φ, e, h⟩
    exact ⟨x, φ.trans a, e, iso _ φ h⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEllipticElementsOfLocalLatticeIsometStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTorusEllipticElements_of_localLatticeIsometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n n' : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin n' → E)) (v : HeightOneSpectrum (𝓞 F)) (j : GLoc σ J v ≃ₜ* GLoc σ J' v), IsLatticeConj L L' j → XSet P (Fv F v) J' = XSet P (Fv F v) J ∧ ∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin n → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), ∃ (φ' : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)) (h' : IsIsom P (Fv F v) J' x.1.1 φ'), gam h' = j (gam h) ∧ ∀ t, torEmb h' t = j (torEmb h t) := by
  first | exact @GlobalTheory.trEll_latticeConj_move | exact GlobalTheory.trEll_latticeConj_move | (intros; apply GlobalTheory.trEll_latticeConj_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometry
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsomPhi

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (gam centMeas orbCls torEmb)

theorem tor_mul_comm {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] (a b : Tor P k) : a * b = b * a := by
  apply Subtype.ext
  show a.1 * b.1 = b.1 * a.1
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem map_isHaar_rightInv {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k] [TopologicalSpace k] {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [MeasurableSpace (Tor P k)] [BorelSpace (Tor P k)]
    [IsTopologicalGroup (Tor P k)] (e : Tor P k ≃ₜ* H) (dt : Measure (Tor P k)) [dt.IsHaarMeasure] :
    (dt.map e).IsHaarMeasure ∧ (dt.map e).IsMulRightInvariant := by
  haveI h1 : (dt.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map dt e.toMulEquiv e.continuous e.symm.continuous
  refine ⟨h1, ⟨fun g => ?_⟩⟩
  have hc : (fun x : H => x * g) = fun x => g * x := funext fun x => by
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tor_mul_comm]
  rw [hc]
  exact map_mul_left_eq_self _ g


set_option maxHeartbeats 4000000 in
open GlobalTheory.Orb in
theorem phi_map : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  intro D V V' r P v j hj μ dt f hμ hdt hok hok'
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  obtain ⟨hX, hmv⟩ := GlobalTheory.T.unitaryTorusEllipticElements_of_localLatticeIsometry _ _ D.sp.cm.sig hcm r V.rank V'.rank P V.gram V'.gram (frameLat V) (frameLat V')
    v j hj
  unfold Phi
  rw [← finsum_comp_equiv (Equiv.subtypeEquivRight (fun c => by rw [hX]))]
  refine finsum_congr fun q => ?_
  obtain ⟨c, h2⟩ := q
  obtain ⟨x, φ, hc, h⟩ := id h2
  subst hc
  obtain ⟨φ'', h'', hγ, ht⟩ := hmv x φ h
  obtain ⟨e, he, hme⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure _ _ D.sp.cm.sig hcm r V.rank P V.gram (isHermND_gram V) (Fv D.host.F v) x φ h
  obtain ⟨e'', he'', hme''⟩ :=
    GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure _ _ D.sp.cm.sig hcm r V'.rank P V'.gram (isHermND_gram V') (Fv D.host.F v) x φ'' h''
  haveI := hμ
  haveI := hdt
  obtain ⟨i1, i2⟩ := map_isHaar_rightInv P (Fv D.host.F v) e dt
  haveI : (centMeas h dt).IsHaarMeasure := by rw [hme dt]; exact i1
  haveI : (centMeas h dt).IsMulRightInvariant := by rw [hme dt]; exact i2
  have v1 := (hok.2 x φ h).orbInt_eq
  have v2 := (hok'.2 x φ'' h'').orbInt_eq
  have hm : centMeas h'' dt = (centMeas h dt).map (centEquiv j (gam h) hγ.symm) := by
    rw [hme'', hme dt, Measure.map_map (map_continuous (centEquiv j (gam h) hγ.symm)).measurable (map_continuous e).measurable]
    congr 1
    funext t
    apply Subtype.ext
    rw [he'', ht, ← he]
    rfl
  calc orbCls (J := V'.gram) (μ.map j) dt (f ∘ j.symm) ((Equiv.subtypeEquivRight (fun c => by rw [hX])) ⟨QuotientGroup.mk x, h2⟩)
      = orbInt (μ.map j) (gam h'') (centMeas h'' dt) (f ∘ j.symm) := v2.symm
    _ = orbInt (μ.map j) (gam h'') ((centMeas h dt).map (centEquiv j (gam h) hγ.symm)) (f ∘ j.symm) := by rw [hm]
    _ = orbInt μ (gam h) (centMeas h dt) ((f ∘ j.symm) ∘ j) := (hasOrbInt_map j hγ.symm (f ∘ j.symm) 0).2
    _ = orbInt μ (gam h) (centMeas h dt) f := by
      congr 1
      ext g
      simp
    _ = orbCls (J := V.gram) μ dt f ⟨QuotientGroup.mk x, h2⟩ := v1

end GlobalTheory.IsomPhi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometryStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableOrbitalIntegral_preserved_latticeIsometry : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (P : PPol D.sp.cm.sig r) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) (dt : Measure (Tor P (Fv D.host.F v))) (f : GLoc D.sp.cm.sig V.gram v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → PhiOK (J := V.gram) μ dt f → PhiOK (J := V'.gram) (μ.map j) dt (f ∘ j.symm) → Phi (J := V'.gram) (μ.map j) dt (f ∘ j.symm) = Phi (J := V.gram) μ dt f := by
  first | exact @GlobalTheory.IsomPhi.phi_map | exact GlobalTheory.IsomPhi.phi_map | (intros; apply GlobalTheory.IsomPhi.phi_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem finiteDimensional_fixed_openSubgroup_GLw : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∀ (n : ℕ) (w : Pl E) (σ : SmIrr (GLw n w)) (U : Subgroup (GLw n w)), IsOpen (U : Set (GLw n w)) →
      FiniteDimensional ℂ (fixed σ.ρ U) := by
  intro E _ _ _ n w σ U hU
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have hadm : IsAdmissible σ.ρ :=
    GlobalTheory.FourClauses.irreducibleAdmissibleGL (w.adicCompletion E) n σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hK : FiniteDimensional ℂ (fixed σ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n))) :=
    hadm.2 _ (hU.inter ho) (hc.inter_left (U.isClosed_of_isOpen hU))
  have hle : fixed σ.ρ U ≤ fixed σ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n)) := fun v hv h => hv ⟨h.1, h.2.1⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.NuPow

theorem pow_mem_H_and_nu_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ n : ℕ, f ^ n ∈ P.H (n * a) (n * b) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (n * a) (n * b) σ y (f ^ n) = P.nu a b σ y f ^ n := by
  intro k _ X _ p P a b f hf n
  induction n with
  | zero =>
    refine ⟨fun x i j _ _ => ⟨1, by simp [Pair.loc]⟩, fun σ y => ?_⟩
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    simp [Pair.nu, Pair.loc, e]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P _ _ a b _ f ih.1 hf
    have ea : ((n + 1 : ℕ) : ℤ) * a = n * a + a := by push_cast; ring
    have eb : ((n + 1 : ℕ) : ℤ) * b = n * b + b := by push_cast; ring
    rw [ea, eb, pow_succ]
    exact ⟨h1, fun σ y => by rw [h2 σ y, ih.2 σ y, pow_succ]⟩

end GlobalTheory.VolBr.NuPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ n : ℕ, f ^ n ∈ P.H (n * a) (n * b) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (n * a) (n * b) σ y (f ^ n) = P.nu a b σ y f ^ n := by
  first | exact @GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow | exact GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow | (intros; apply GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow <;> assumption)
end
end
