module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.ProjectiveLattices.FrCovA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

def CongE {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (c : ℕ)
    (g g' : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ x ∈ stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • (g x - g' x) ∈ stdAt E n P

theorem congE_refl {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (c : ℕ)
    (g : Sp E n ≃ₗ[E] Sp E n) : CongE P c g g := fun x _ => by
  rw [sub_self, smul_zero]
  exact Submodule.zero_mem _

theorem CongE.symm {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {c : ℕ}
    {g g' : Sp E n ≃ₗ[E] Sp E n} (h : CongE P c g g') : CongE P c g' g := fun x hx => by
  rw [← neg_sub, smul_neg]
  exact Submodule.neg_mem _ (h x hx)

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

abbrev sm : Seam (I.rec7 l Z) B.fields := seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G

abbrev SBof (a : I.ι) : Finset (HeightOneSpectrum (𝓞 B.fields.E)) := rowSG (B.primes X) I.sel (I.tup a)

abbrev Charts (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) {Ch : Type}
    (chOf : (I.stp u a i).Cl → Ch) : Type 1 :=
  ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
    (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))

abbrev ReadsAt {u : B.Word} {a : I.ι} {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch} (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)) : Prop :=
  I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
    (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k

def ChiFin {T i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ κ : S.U, (∀ v ∈ badG (I.rec7 l Z), bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → S.chi κ ^ n = 1

def FrNear (a : I.ι) {n : ℕ} (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E) : Prop :=
  ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (k⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) ∧
    GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P))⁻¹ * k)

def LiftsInv {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (κ : (I.stp u a i).G b) (P : SBof I a)
    (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) : Prop :=
  g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
    (∀ h : P.1 ∈ (B.primes X).vGs, ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1,
      redV P.1 (g x) = ((κ.2.1.1 ⟨P.1, h⟩)⁻¹).1.mulVec (redV P.1 x)) ∧
    ∀ h : P.1 ∈ I.Q a, g = ((κ.2.2.1 ⟨P.1, h⟩)⁻¹).1

abbrev MidAt {u : B.Word} {a : I.ι} {i : ℕ} (hi : i < B.R.m) (b : (I.stp u a i).β) (P : SBof I a)
    (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K) : Prop :=
  GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i (Idx.get b hi) P) g z

def Keeps {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) : Prop :=
  (I.stp u a i).gam b κ = 1 ∧ cosetIn ((I.stp u a i).act b κ p) = cosetIn p

theorem keeps_one {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (p : (I.stp u a i).D b) :
    Keeps I (1 : (I.stp u a i).G b) p :=
  ⟨map_one _, congrArg cosetIn (@one_smul _ _ _ ((I.stp u a i).actD b) p)⟩

end GlobalTheory.Mem.Col2.AdT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem admissibleBase_of_completeNormalLocalCharZero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) :
    AdmBase R (maximalIdeal R) :=
  ⟨h.1, inferInstance, h.2.1, h.2.2.1⟩

theorem pullSt : PullSt := by
  intro E _ _ _ H R R' _ _ _ _ _ _ φ t P hR hR' hφ hloc _
  obtain ⟨h1, -, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aR' := admissibleBase_of_completeNormalLocalCharZero hR'
  have : CharZero R' := hR'.2.2.2
  have hI : (maximalIdeal R).map φ ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff φ a).2 ha
  obtain ⟨t', m₀, P', hD, -, -, -, -, xl, -⟩ :=
    GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5 aR aR' t P φ hφ hI
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  exact ⟨t', m₀, P', e, GlobalTheory.FlatTors.torsionIso_holds E H R' _ aR' t' P',
    fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩

end GlobalTheory.TorRef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col)

namespace GlobalTheory.ShFam.BdArc

instance mono_spMap_ringOfIntegers (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) :=
  have : IsPreimmersion (spMap (algebraMap (𝓞 K) K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 K))
  inferInstance

def imTop : Filter ℂ := Filter.comap Complex.im Filter.atTop

def IsHolPts {A : Type} [CommRing A] (ψ : ℂ → (A →+* ℂ)) (r : ℝ) : Prop :=
  0 < r ∧ ∀ a, DifferentiableOn ℂ (fun u => ψ u a) (Metric.ball 0 r)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Frames

variable {N : ℕ} (X : Data E N)

def IsOrbit (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N) : Prop :=
  0 < M ∧ γ ∈ X.Γ ∧ DifferentiableOn ℂ x {w | T < w.im} ∧ (∀ w : ℂ, T < w.im → x w ∈ X.dom) ∧
    ∀ w : ℂ, T < w.im → ∃ b ∈ Bor X.Ψ N, (∀ τ i, b τ i i = 1) ∧ x (w + M) = rmul (lact γ (x w)) b

def SamePos (x x' : Frame X.Ψ N) : Prop :=
  ∀ τ : X.Ψ, Submodule.span ℂ (col (mat x τ) '' {a | (a : ℕ) < X.p0}) =
    Submodule.span ℂ (col (mat x' τ) '' {a | (a : ℕ) < X.p0})

end Frames

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type}
  [CommRing O] {β : O →+* c.F}

def IsArc (Z : Model Xo c β) (σ : c.F →+* ℂ) {A : Type} [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z)
    (ψ : ℂ → (A →+* ℂ)) (r : ℝ) : Prop :=
  IsHolPts ψ r ∧ x ≫ genStr Z = spMap φ ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp φ = σ

def IsBdArc (Z : Model Xo c β) (σ : c.F →+* ℂ) {A : Type} [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z)
    (ψ : ℂ → (A →+* ℂ)) (r : ℝ) : Prop :=
  IsArc Z σ φ x ψ r ∧ (∀ s, (spMap (ψ 0) ≫ x) s ∈ genBd Z) ∧
    ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z

def Matches {Z : Model Xo c β} {σ : c.F →+* ℂ} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z}
    (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : A →+* ℂ) (y : FrPt Xo c (CAt σ)) : Prop :=
  GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (show A →+* CAt σ from ψ) ≫ x ∧
    ∀ τ i, ∃ w : Sp (DualNumber (CAt σ)) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap (CAt σ) (DualNumber (CAt σ))) ≫ GlobalTheory.AllWt.ptF y ∧
        w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (show A →+* CAt σ from ψ)) ≫ fr.v τ i

def SameLie {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : Prop :=
  y.x = y'.x ∧ ∀ τ i, y.u τ i = y'.u τ i

def IsLift {σ : c.F →+* ℂ} {N : ℕ} (U : Unf Xo c σ N) (k : U.Comp) (y : ℂ → FrPt Xo c (CAt σ)) (T : ℝ)
    (x : ℂ → Frame (U.X k).Ψ N) : Prop :=
  ∀ w : ℂ, T < w.im → ∃ h : x w ∈ (U.X k).dom, SameLie (U.un k ⟨x w, h⟩) (y (eTwoPi w))

end GlobalTheory.ShFam.BdArc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.OpenReg

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Transfer

variable {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {R : Type} [CommRing R] {x : Sp R ⟶ S'} {x' : Sp R ⟶ S}

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (h : A →+* B) :
    spMap g ≫ spMap h = spMap (g.comp h) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem epsMul_over (s : R) : spMap (epsMul s) ≫ spMap (algebraMap R (DualNumber R)) =
    spMap (algebraMap R (DualNumber R)) := by
  rw [spMap_comp]
  congr 1
  ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_lift {T : Scheme.{0}} (q : T ⟶ S') (v : T ⟶ t.G.left) (hv : v ≫ t.G.hom = q ≫ f) :
    ∃ w : T ⟶ t'.G.left, w ≫ t'.G.hom = q ∧ w ≫ m.φ = v :=
  ⟨m.cart.1.lift v q hv, m.cart.1.lift_snd _ _ _, m.cart.1.lift_fst _ _ _⟩

theorem tan_iff (hx : x ≫ f = x') {w : Sp (DualNumber R) ⟶ t'.G.left}
    (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsTanAtG t x' (w ≫ m.φ) ↔ IsTanAtG t' x w := by
  subst hx
  have e : (1 : Over.mk x ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x ≫ f) ⟶ t.G).left :=
    congrArg (fun z => z.left) (map_one (pushHom m.cart (Over.mk x)))
  constructor
  · intro h
    refine ⟨hw, m.cart.1.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h.2.trans e.symm
    · have hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
        RingHom.ext fun r => by simp
      rw [Category.assoc, hw, ← Category.assoc, spMap_comp, hid, Over.w]
      exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp _)
  · intro h
    refine ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw, Category.assoc], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) h.2).trans e

theorem eig_iff {w : Sp (DualNumber R) ⟶ t'.G.left}
    (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (a : 𝓞 E) (s : R) :
    (w ≫ m.φ) ≫ (t.act.act a).left = spMap (epsMul s) ≫ w ≫ m.φ ↔
      w ≫ (t'.act.act a).left = spMap (epsMul s) ≫ w := by
  have e : (w ≫ m.φ) ≫ (t.act.act a).left = (w ≫ (t'.act.act a).left) ≫ m.φ := by
    rw [Category.assoc, Category.assoc, m.act]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc (spMap _)]; exact h
    · rw [Category.assoc, Over.w, Category.assoc, hw, ← Category.assoc, epsMul_over]
  · intro h
    rw [h, Category.assoc]

theorem prod_iff {q : Sp (DualNumber R) ⟶ S'} {q' : Sp (DualNumber R) ⟶ S} (hq : q ≫ f = q') {n : ℕ}
    {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} (hv : ∀ i, v i ≫ t'.G.hom = q)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = q) :
    (∃ u : Fin n → (Over.mk q' ⟶ t.G), (∀ i, (u i).left = v i ≫ m.φ) ∧ ((List.ofFn u).prod).left = w ≫ m.φ) ↔
      ∃ u : Fin n → (Over.mk q ⟶ t'.G), (∀ i, (u i).left = v i) ∧ ((List.ofFn u).prod).left = w := by
  subst hq
  have push : ∀ u : Fin n → (Over.mk q ⟶ t'.G), ((List.ofFn u).prod).left ≫ m.φ =
      ((List.ofFn fun i => pushHom m.cart (Over.mk q) (u i)).prod).left := fun u => by
    have := map_list_prod (pushHom m.cart (Over.mk q)) (List.ofFn u)
    rw [List.map_ofFn] at this
    exact congrArg (fun z => z.left) this
  constructor
  · rintro ⟨u, hu, hw'⟩
    let u' : Fin n → (Over.mk q ⟶ t'.G) := fun i => Over.homMk (v i) (hv i)
    have e : u = fun i => pushHom m.cart (Over.mk q) (u' i) := funext fun i => Over.OverMorphism.ext (hu i)
    refine ⟨u', fun i => rfl, m.cart.1.hom_ext ?_ ?_⟩
    · rw [e] at hw'
      exact (push u').trans hw'
    · rw [Over.w, hw]; rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushHom m.cart (Over.mk q) (u i), fun i => ?_, (push u).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu]

theorem comb_iff (hx : x ≫ f = x') {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)}
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (cf : Fin n → R)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsCombAtG t x' (fun i => v i ≫ m.φ) cf (w ≫ m.φ) ↔ IsCombAtG t' x v cf w := by
  have := prod_iff m (q := spMap (algebraMap R (DualNumber R)) ≫ x) (q' := spMap (algebraMap R (DualNumber R)) ≫ x')
    (by rw [Category.assoc, hx]) (v := fun i => spMap (epsMul (cf i)) ≫ v i)
    (fun i => by rw [Category.assoc, hv, ← Category.assoc, epsMul_over]) hw
  simp only [Category.assoc] at this
  exact this

end Transfer

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}

theorem exists_frPt_of_eigFrame {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.F R] (xF : Sp R ⟶ Xo.XF c)
    (hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) {x : Sp R ⟶ Z.X} (hx : xF ≫ Z.jQ ≫ pullback.fst _ _ = x)
    (f : EigFrame Z (algebraMap c.F R) x) :
    ∃ (y : FrPt Xo c R) (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.oF.t.G.left)),
      y.x = xF ≫ pullback.fst _ _ ∧ ∀ τ i, w τ i ≫ Z.oF.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ xF ∧
        w τ i ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w τ i ≫ Z.m.φ = f.v τ i := by
  have hover : (xF ≫ pullback.fst _ _) ≫ Xo.s = sOf c R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp]; rfl
  obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frPt (c := c) _ hover
  choose w hw1 hw2 using fun τ i => exists_lift Z.m (spMap (algebraMap R (DualNumber R)) ≫ xF) (f.v τ i)
    (by rw [(f.tan τ i).1, ← hx, Category.assoc])
  refine ⟨⟨z.x, z.x_over, fun τ i => w τ i ≫ Z.m0.toSABMap.φ, fun τ i => ?_, fun τ i a => ?_, fun τ v hv he => ?_,
    z.s, z.gen⟩, w, hz, fun τ i => ⟨hw1 τ i, rfl, hw2 τ i⟩⟩
  · exact (tan_iff Z.m0.toSABMap hz.symm (hw1 τ i)).2 ((tan_iff Z.m hx (hw1 τ i)).1 (hw2 τ i ▸ f.tan τ i))
  · exact (eig_iff Z.m0.toSABMap (hw1 τ i) a _).2 ((eig_iff Z.m (hw1 τ i) a _).1 (hw2 τ i ▸ f.eig τ i a))
  · obtain ⟨v', h1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap R (DualNumber R)) ≫ xF) v
      (by rw [hv.1, hz, Category.assoc])
    have hb := f.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hz.symm h1).1 hv))
      fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))
    have e : f.v τ = fun i => w τ i ≫ Z.m.φ := funext fun i => (hw2 τ i).symm
    rw [e] at hb
    exact (existsUnique_congr fun cf => (comb_iff Z.m0.toSABMap hz.symm (hw1 τ) cf h1).trans
      (comb_iff Z.m hx (hw1 τ) cf h1).symm).2 hb

variable {F : Type} [Field F] {e : F ≃+* c.F}

theorem mono_spMap_algebraMap (A K : Type) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Mono (spMap (algebraMap A K)) := by
  have : IsPreimmersion (spMap (algebraMap A K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors A)
  infer_instance

end GlobalTheory.ShFam.OpenReg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

theorem twArgs_lev : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t), HEq a.x.R.C (Top.Fr.at (w.st Z) f) ∧ HEq a.x.R.Pg (B.primes w.px).vGs ∧ (∀ μ, Formalism.IndefR.RecTie.Used0 (w.st Z).toD7 μ → HEq (a.x.R.Q (a.x.Y.tupT μ)) (w.I.Q μ) ∧ HEq (a.x.R.toLevCh.xiH (a.x.Y.tupT μ)) (w.I.xi μ)) ∧ (∀ i p v s, a.x.R.EEp3 p ≠ ⊥ → ∃ p' s', HEq p' p ∧ HEq s' s ∧ a.x.R.lam3 i s p v = t.r.z.R.lam3 i s' p' v) := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tupT = t.r.Y.tupT := eq_of_heq htupT
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact heq_of_eq (t.r.z.lev.C.trans (congrArg _ w.C_eq))
  · exact heq_of_eq t.r.z.lev.Pg
  · change ∀ μ, Formalism.IndefR.RecTie.Used0 (w.st Z).toD7 μ →
      HEq (t.r.z.R.Q (Y.tupT μ)) (w.I.Q μ) ∧ HEq (t.r.z.R.xiH (Y.tupT μ)) (w.I.xi μ)
    intro μ hμ
    have hix : ixOf w.I (usedOf w.I T Wt) (t.r.Y.tupT μ) = μ := (t.r.tup_ix _).symm.trans (t.r.Y.tupTie μ hμ)
    rw [hT', t.r.z.lev.Q, t.r.z.lev.xiH, hix]
    exact ⟨HEq.rfl, HEq.rfl⟩
  · intro i p v s hp
    refine ⟨p, s, HEq.rfl, HEq.rfl, ?_⟩
    change t.r.z.R.EEp3 p ≠ ⊥ at hp
    change lam i s p v = t.r.z.R.lam3 i s p v
    exact lam_eq i s p v hp


end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

def EigFrame.Coord {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (A : Mat Dw.mult R') : Prop :=
  x' = spMap ψ ≫ x ∧ φ' = ψ.comp φ ∧
    ∀ τ i, IsCombAtG Z.t x' (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) (A τ i) (g.v τ i)

def EigFrame.Stable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (ψ : R →+* R'),
    ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i

theorem EigFrame.tri_iff {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x) (ψ : R →+* R') (g : EigFrame Z φ' x')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ) :
    f.Tri ψ g t ↔ ∃ A : Mat Dw.mult R', f.Coord ψ g A ∧ (∀ τ i, A τ i i = t τ i) ∧ ∀ τ i k, i < k → A τ i k = 0 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    choose A hA hA' hA'' using h3
    exact ⟨A, ⟨h1, h2, hA''⟩, hA, hA'⟩
  · rintro ⟨A, ⟨h1, h2, h3⟩, hA, hA'⟩
    exact ⟨h1, h2, fun τ i => ⟨A τ i, hA τ i, hA' τ i, h3 τ i⟩⟩

variable {F : Type} [Field F]

def Tied (e : F ≃+* c.F) (Y : GlobalTheory.ProjVar.Var F) (π : Y.X ⟶ gen Z)
    (f₀ : EigFrame Z (constF e Y) (genericPt Y ≫ π ≫ genι Z)) {k : (E →+* ℂ) → ℕ} (S : Fr (ratOf Y) Dw.mult k)
    (A₀ : Mat Dw.mult Y.Fn) : Prop :=
  A₀ ∈ S.S (genericPoint Y.X) ∧ ∀ y : Y.X, ∀ A ∈ S.S y, ∃ (φ : c.F →+* Y.X.presheaf.stalk y)
    (f : EigFrame Z φ (stalkPt Y y ≫ π ≫ genι Z)),
    f.Coord (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) f₀ (A₀ * A⁻¹)

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocM.FrameBC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X}

theorem tv_sum' {κ : Type} (s : Finset κ) (f : κ → TanM x t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  simp only [tv, toMul_sum]
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

def Full {κ : Type} [Fintype κ] (v : κ → TanM x t.G) : Prop :=
  ∀ n : TanM x t.G, ∃! a : κ → S, n = ∑ k, a k • v k

theorem full_equiv {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ' ≃ κ) {v : κ → TanM x t.G} (hv : Full v) :
    Full (fun i => v (e i)) := fun n => by
  obtain ⟨a, ha, hu⟩ := hv n
  refine ⟨fun i => a (e i), ha.trans (e.sum_comp (fun k => a k • v k)).symm, fun b hb => ?_⟩
  have := hu (fun k => b (e.symm k)) (hb.trans (by
    rw [← e.sum_comp]; simp only [Equiv.symm_apply_apply]))
  funext i; rw [← this]; simp

theorem full_iff {m : ℕ} {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → TanM x t.G}
    (e : ∀ i, pushHom h (epsR S) (u i) = tv (v i)) : IsLieBasis u ↔ Full v := by
  have key : ∀ a p n, pushHom h (epsR S) p = tv n → (IsLieComb a u p ↔ n = ∑ k, a k • v k) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    exact ⟨fun q => tanM_ext (q.trans (by rw [tv_sum']; rfl)), fun q => (congrArg tv q).trans (by rw [tv_sum']; rfl)⟩
  refine ⟨fun hu n => ?_, fun hv => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv n)
    simpa only [key _ p n hp] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem n))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using hv (mkT _ ((isTangent_iff h p).1 hp))

def resM (ψ : S →+* T) (n : TanM x t.G) : TanM (spMap ψ ≫ x) t.G := tanOf (isTan_map ψ rfl (isTan_tv n))

theorem full_bc {m : ℕ} (ψ : S →+* T) {v : Fin m → TanM x t.G} (hv : Full v) : Full fun i => resM ψ (v i) := by
  have h₀ := isGrpPullback_pullback t.G x
  have h := isGrpPullback_pullback t.G (spMap ψ ≫ x)
  choose u hu using fun i => push_surj h₀ (tv (v i))
  choose u' hu' using fun i => push_surj h (tv (resM ψ (v i)))
  have := t.semi.smooth
  have : Smooth ((Over.pullback x).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (full_iff h hu').1 (Chart.frameLieBCR _ ((full_iff h₀ hu).2 hv) ψ (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (PullbackSections.dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

variable {l : Level H} (c : Coeff l) [Algebra c.F S]

theorem eig_iff (τ : E →+* ℂ) (n : TanM x t.G) :
    (∀ a : 𝓞 E, (tv n).left ≫ (t.act.act a).left = spMap (epsMul (algebraMap c.F S (embK c τ a))) ≫ (tv n).left) ↔
      IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n :=
  forall_congr' fun _ => ⟨fun h => tan_ext h, fun h => congrArg (fun V => (tv V).left) h⟩

theorem eig_comb' (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v i)) (a : Fin m → S) :
    IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hv i b, smul_comm]

theorem full_of_eig {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hv : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hb : ∀ τ n, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n → ∃! a : Fin (d τ) → S, n = ∑ i, a i • v τ i) :
    Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2) := by
  classical
  intro m
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End S (TanM x t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => hb τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), a k.1 k.2 • v k.1 k.2
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), b k • v k.1 k.2 := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • v τ i)
      (fun τ => eig_comb' c τ _ (fun i => hv τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

theorem eig_of_full {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hE : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hfull : Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2)) (τ : E →+* ℂ) (w : TanM x t.G)
    (hm : IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) w) : ∃! a : Fin (d τ) → S, w = ∑ i, a i • v τ i := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hproj : proj ρ (embK c) α τ w = w := by
    have := proj_sum_eig ρ (embK c) α hinj (fun σ' => if σ' = τ then w else 0)
      (fun σ' => by
        split_ifs with h
        · subst h; exact hm
        · exact fun a => by simp) τ
    simpa [Finset.sum_ite_eq'] using this
  obtain ⟨A, hA, hAu⟩ := hfull w
  have hcomp : proj ρ (embK c) α τ w = ∑ i, A ⟨τ, i⟩ • v τ i := by
    have h1 := proj_sum_eig ρ (embK c) α hinj (fun σ' => ∑ i, A ⟨σ', i⟩ • v σ' i)
      (fun σ' => eig_comb' c σ' _ (fun i => hE σ' i) _) τ
    rw [← Fintype.sum_sigma (fun k : (Σ σ : E →+* ℂ, Fin (d σ)) => A k • v k.1 k.2), ← hA] at h1
    exact h1
  refine ⟨fun i => A ⟨τ, i⟩, hproj.symm.trans hcomp, fun b hb => ?_⟩
  have hb : w = ∑ i, b i • v τ i := hb
  let B : (Σ σ : E →+* ℂ, Fin (d σ)) → S := fun k => if h : k.1 = τ then b (h ▸ k.2) else 0
  have hB : w = ∑ k, B k • v k.1 k.2 := by
    rw [Fintype.sum_sigma, hb, Finset.sum_eq_single τ]
    · exact Finset.sum_congr rfl fun i _ => by simp [B]
    · intro σ _ hσ
      exact Finset.sum_eq_zero fun i _ => by simp [B, hσ]
    · intro h; exact absurd (Finset.mem_univ τ) h
  have := hAu B hB
  funext i
  have := congrFun this ⟨τ, i⟩
  simpa [B] using this

end GlobalTheory.LocM.FrameBC


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM.FrameBC in
theorem GlobalTheory.LocM.isFrame_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  intro E _ _ _ H Dw l c X t R S _ _ f φ x u hu
  letI : Algebra c.F R := f.toAlgebra
  letI : Algebra c.F S := (φ.comp f).toAlgebra
  let v : ∀ τ, Fin (Dw.mult τ) → TanM x t.G := fun τ i => tanOf (hu.1 τ i).1
  have he : ∀ τ i (a : 𝓞 E), u.bc φ τ i ≫ (t.act.act a).left =
      spMap (epsMul ((φ.comp f) (embK c τ a))) ≫ u.bc φ τ i := fun τ i a => by
    show (spMap (dualMap φ) ≫ u τ i) ≫ _ = _ ≫ spMap (dualMap φ) ≫ u τ i
    rw [Category.assoc, (hu.1 τ i).2 a, ← Category.assoc, Formalism.L2.Pj.FrCov.eps_dual, Category.assoc, RingHom.comp_apply]
  have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (hu.1 τ i).2) fun τ n hn => by
    exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (hu.2 τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
  have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM φ (v k.1 k.2) := by
    have h := full_equiv (eB Dw).symm (full_bc φ (full_equiv (eB Dw) h1))
    exact (funext fun k => congrArg (fun j : IxB Dw => resM φ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
  refine ⟨fun τ i => ⟨isTan_map φ rfl (hu.1 τ i).1, he τ i⟩, fun τ w hw hwe => ?_⟩
  have h3 := eig_of_full c (fun τ i => resM φ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
    ((eig_iff c τ _).1 hwe)
  exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM φ (v τ i)) a (tanOf hw)).2 h3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT

namespace GlobalTheory.KeyFourth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def Tied {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (s : LB.Sec (PPx x)) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (Φ : FibKey Xo S x) : Prop :=
  SecTie Φ.m Φ.th s ∧ ∃ hg : Φ.T.g = g, ∀ i : Fin Φ.T.g,
    (Φ.v i).left ≫ Φ.m.φ = u (e (i.cast hg)).1 (e (i.cast hg)).2

def kch {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : Sˣ := ∏ i, t i ^ keyEx Dw i

theorem kch_mul {S : Type} [CommRing S] (t t' : Ix Dw → Sˣ) : kch (t * t') = kch t * kch t' := by
  simp only [kch, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem kch_inv {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : kch t⁻¹ = (kch t)⁻¹ := by
  simp only [kch, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem kch_eq {S : Type} [CommRing S] (t : Ix Dw → Sˣ) :
    kch t = (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t (some x)) * (t none ^ 2)⁻¹ := by
  rw [kch, Fintype.prod_option, mul_comm]
  simp only [keyEx, zpow_one, zpow_neg]
  rfl

def RootVal {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (y : FrPt Xo c (CAt σ)) (v : ℂ) : Prop :=
  ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ)

end GlobalTheory.KeyFourth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.LatDRFree

attribute [local instance] Over.cartesianMonoidalCategory

theorem intO_isLocalRing (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] : IsLocalRing ↥(intO C) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have hu : ∀ b : ↥(intO C), ‖(b : C)‖ = 1 → IsUnit b := fun b hb => by
    have h0 : (b : C) ≠ 0 := fun h => by simp [h] at hb
    have hi : (b : C)⁻¹ ∈ intO C := by
      show ‖(b : C)⁻¹‖ ≤ 1
      rw [norm_inv, hb, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  have ha : ‖(a : C)‖ ≤ 1 := a.2
  rcases ha.eq_or_lt with h | h
  · exact Or.inl (hu a h)
  · refine Or.inr (hu _ ?_)
    have : ‖(1 : C) + (-(a : C))‖ = max ‖(1 : C)‖ ‖-(a : C)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact h.ne')
    rw [norm_neg, norm_one, max_eq_left h.le, ← sub_eq_add_neg] at this
    exact this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

open MonObj in
theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem latDR_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (xO : Sp ↥(intO C) ⟶ X), (∀ xO' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO' = spMap (intO C).subtype ≫ xO → xO' = xO) → ∃ (g : ℕ) (v : Fin g → (Sp (DualNumber C) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO C).subtype ≫ xO) (v i)) ∧ (∀ w, IsTanAtG t (spMap (intO C).subtype ≫ xO) w → ∃! cf : Fin g → C, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w) ∧ ∀ (cf : Fin g → C) w, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w → (w ∈ latDR t (spMap (intO C).subtype ≫ xO) ↔ ∀ i, ‖cf i‖ ≤ 1) := by
  intro E _ _ _ H X t C _ _ xO huniq
  have := intO_isLocalRing C
  obtain ⟨n, D, hD, hDb⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t (↥(intO C)) xO
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hD0 : ∀ w, IsTanAtG t xO w → ∃! a : Fin n → ↥(intO C), IsCombAtG t xO D a w := by
    have h := hDb _ (RingHom.id ↥(intO C))
    simp only [h1, h3, Category.id_comp] at h
    exact h
  have hDk := fun j => isTanAtG_map t (intO C).subtype (hD j)
  refine ⟨n, fun e => spMap (dualMap (intO C).subtype) ≫ D e, hDk, hDb C _, fun cf w hw => ⟨?_, fun hc => ?_⟩⟩
  · rintro ⟨xO', hx, vO, hv, rfl⟩
    obtain rfl := huniq xO' hx
    obtain ⟨a, ha, -⟩ := hD0 vO hv
    have e := (hDb C _ _ (isTanAtG_map t (intO C).subtype hv)).unique hw (comb_map t (intO C).subtype ha)
    intro i
    rw [e]
    exact (a i).2
  · let a : Fin n → ↥(intO C) := fun i => ⟨cf i, hc i⟩
    have ha : IsCombAtG t xO D a (combT xO (fun j => ovT (hD j)) a).left :=
      (isCombAtG_iff t xO (fun j => ovT (hD j)) a _).2 rfl
    refine ⟨xO, rfl, _, isTanAtG_of _ (combT_tan _ (fun j => ovT (hD j)) (fun j => smT_zero_ovT _) a), ?_⟩
    have hb := comb_map t (intO C).subtype ha
    exact ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hb).symm.trans
      ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hw)

end GlobalTheory.LatDRFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.GoodDual

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare Formalism.L2.DIV GlobalTheory.BI

theorem isChar_inv {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) :
    IsChar ℂ ℂ fun g => χ g⁻¹ := by
  obtain ⟨n, ρ, hρ⟩ := h
  let e : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun
  let σ : Representation ℂ G (Fin n → ℂ) :=
    { toFun := fun g => e.conj (ρ.dual g)
      map_one' := by rw [map_one]; exact LinearEquiv.conj_id e
      map_mul' := fun a b => by rw [map_mul]; exact LinearEquiv.conj_comp e _ _ }
  refine ⟨n, σ, fun g => ?_⟩
  have : σ.character g = ρ.dual.character g := LinearMap.trace_conj' _ e
  show χ g⁻¹ = _
  rw [Algebra.algebraMap_self, RingHom.id_apply, this, Representation.char_dual, hρ, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem goodIdempotent_coeff_inv_eq_coeff {D : D7} {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (h : G0g D.nd) :
    D.ntypes.e0.coeff h⁻¹ = D.ntypes.e0.coeff h := by
  obtain ⟨x, rfl⟩ := pull_bijective.2 h
  have e : (pull x)⁻¹ = pull x⁻¹ := rfl
  rw [e, hI, hI]
  exact GlobalTheory.GoodIdemFlip.coeff_goodIdem_flip _ D.host om Set.univ x x⁻¹
    (fun v _ => by rw [Pi.inv_apply]) (fun v hv => absurd (Set.mem_univ v) hv)

theorem goodStable_of_coeff {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] (emb : K →+* ℂ)
    (X : Finset (G → K)) (hirr : ∀ χ ∈ X, IsAbsIrrChar χ)
    (hsym : ∀ g, (idemOf X).coeff g⁻¹ = (idemOf X).coeff g) : GoodStable X := by
  classical
  intro χ hχ
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf emb X hirr X
    (fun ψ g => emb (ψ g⁻¹)) (fun ψ hψ => by
      obtain ⟨n, ρ, -, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar emb (hirr ψ hψ)
      exact isChar_inv ⟨n, ρ, hρ⟩) (fun g => by
      rw [← hsym g]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [idemOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_chiIdem, map_sum, map_mul, map_div₀,
        map_natCast, inv_one, inv_inv, Nat.card_eq_fintype_card]) hχ
  convert hψ using 1
  funext g
  apply emb.injective
  simpa using hψe g⁻¹

end GlobalTheory.Mem.R3.GoodDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
noncomputable section

namespace GlobalTheory.UnifComp

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ptF_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    ptF z = spMap φ.toRingHom ≫ ptF y := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, Category.assoc, ptF, pullback.lift_fst, h.1]
  · rw [ptF, pullback.lift_snd, Category.assoc, ptF, pullback.lift_snd, ← Spec.map_comp]
    congr 1
    ext a
    exact (φ.commutes a).symm

theorem ptF_frBor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y z : FrPt Xo c S}
    (h : FrBor t y z) : ptF z = ptF y := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, ptF, pullback.lift_fst, h.1]
  · rw [ptF, pullback.lift_snd, ptF, pullback.lift_snd]

attribute [local instance 1100] Subalgebra.algebra in
theorem liesOn_chart {h : GenFrEx Xo c} (C : GlobalTheory.Reg.FChart h) : LiesOn C.Z C.y := by
  intro s
  let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
  let s₀ : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
  have e : spMap C.R.val.toRingHom s₀ = η :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
  have h1 : ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
    have := liesOn_genFr h C.Z s₀
    rw [← ptF_frBor C.bor, ptF_frMap C.gen, Scheme.Hom.comp_apply, e] at this
    exact this
  have h2 : η ⤳ s := (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
  exact (h2.map (ptF C.y).continuous).mem_closed (isClosed_of_mem_irreducibleComponents _ C.Z.2) h1

attribute [local instance 1100] Subalgebra.algebra in
theorem exists_liesOn {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) : ∃ Z : Comp Xo c, ∀ x : (U.X k).dom, LiesOn Z (U.un k x) := by
  obtain ⟨-, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneComp.exists_comp_of_charts E H Dw l Xo c σ r U hU h k
  refine ⟨Z, fun x s => ?_⟩
  let : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) (U.un k x)
  rw [← hZ x C ψ z t hz hb, ptF_frBor hb, ptF_frMap hz, Scheme.Hom.comp_apply]
  exact liesOn_chart C _

theorem eq_of_carries {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} {h : GenFrEx Xo c} {k : U.Comp}
    {Z Z' : Comp Xo c} (hk : GlobalTheory.CompModel.CarriesGeneric U h k Z) (h' : ∀ x : (U.X k).dom, LiesOn Z' (U.un k x)) :
    Z' = Z := by
  obtain ⟨P, w, x, t, hw, ht⟩ := hk
  by_contra hne
  let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z' Z hne) (h' x s) ?_
  rw [← ptF_frBor ht, ptF_frMap hw, Scheme.Hom.comp_apply]
  exact liesOn_genFr h Z _

theorem exists_equiv_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → FnAlgClosed (Xo := Xo) (c := c) → ∃ q : U.Comp ≃ Comp Xo c, ∀ k (x : (U.X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF (U.un k x) s ∈ (q k).1 := by
  intro E _ _ _ H Dw l Xo c σ N U hσ hU _ hF
  obtain ⟨-, -, h, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  choose q hq using exists_liesOn U hU
  refine ⟨Equiv.ofBijective q ⟨fun k k' e => ?_, fun Z => ?_⟩, fun k x s => hq k x s⟩
  · obtain ⟨Z, hZ⟩ := GlobalTheory.CompModel.exists_comp U hσ hU h k
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp U hσ hU h k'
    obtain rfl : Z = Z' := (eq_of_carries hZ (hq k)).symm.trans (e.trans (eq_of_carries hZ' (hq k')))
    obtain ⟨P, w, x, t, hw, ht⟩ := hZ
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact GlobalTheory.GeomConn.comp_eq_of_fnAlgClosed E H Dw l Xo c σ N U.toPj hσ hU hF h Z k k' x x'
      ⟨P, w, t, hw, ht⟩ ⟨P', w', t', hw', ht'⟩
  · obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model U hU h Z
    exact ⟨k, eq_of_carries hk (hq k)⟩

end GlobalTheory.UnifComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

open GlobalTheory.FramePull GlobalTheory.ConstFam

section Move

variable {S Z : Scheme.{0}} {G₀ : Over S} {G : Over Z} {L₀ : LB G₀.left} {L : LB G.left} {F : G.left ⟶ G₀.left}
  {π : Z ⟶ S} {N : ℕ} {w : LB.Iso L (L₀.pull F)}

end Move

theorem exists_pt {S : Scheme.{0}} {G : Over S} (T : Over S) {Y : Scheme.{0}} (a : Y ⟶ T.left) (b : Y ⟶ G.left)
    (h : a ≫ T.hom = b ≫ G.hom) : ∃ ρ : Y ⟶ (T ⊗ G).left, ρ ≫ (fst T G).left = a ∧ ρ ≫ (snd T G).left = b :=
  ⟨pullback.lift a b h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end Frames

end GlobalTheory.TorRef
end
end
