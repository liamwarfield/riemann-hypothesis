module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundFromCharactersPointDatum
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirections
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivPointsOfIsPowGrp
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPref
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceHarmonic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorsOfHodgeTateChartBou

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsUnitIffNotIsUnitOfCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColumnsToTupleHarmonicValues
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartFromPointDatumOfLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GsSpMapGermAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LinkSec

theorem comp_psum_two {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (s : T ⟶ T') (x₀ x₁ : T' ⟶ G)
    (I : Finset (Fin 2)) : s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![s ≫ x₀, s ≫ x₁] I).left := by
  have e : s ≫ psum G ![x₀, x₁] I = psum G ![s ≫ x₀, s ≫ x₁] I := by
    fin_cases I
    · exact MonObj.comp_one _
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))
    · exact MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·)
        (MonObj.comp_mul _ _ _ |>.trans (congrArg (_ * ·) (MonObj.comp_one _))))
  exact congrArg CommaMorphism.left e

theorem psum_mem {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] (w : G ⟶ G) (x : T ⟶ G)
    (I : Finset (Fin 2)) : ∃ k, (psum G ![x, x ≫ w] I).left = x.left ≫ JetSer.primφ w k := by
  have e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w) := (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have e₄ : x ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  have p₀ : psum G ![x, x ≫ w] ∅ = 1 := rfl
  have p₁ : psum G ![x, x ≫ w] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x ≫ w] {1} = x ≫ w := _root_.mul_one _
  have p₄ : psum G ![x, x ≫ w] {0, 1} = x * (x ≫ w) := congrArg (x * ·) (_root_.mul_one _)
  have hI : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {0, 1} := by revert I; decide
  rcases hI with rfl | rfl | rfl | rfl
  · exact ⟨4, congrArg CommaMorphism.left (p₀.trans e₄.symm)⟩
  · exact ⟨0, (congrArg CommaMorphism.left p₁).trans (Category.comp_id _).symm⟩
  · exact ⟨3, congrArg CommaMorphism.left p₂⟩
  · exact ⟨1, congrArg CommaMorphism.left (p₄.trans e₁.symm)⟩

theorem change_index {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (w : G ⟶ G)
    (x : T ⟶ G) (s : T ⟶ T') (x₀ x₁ : T' ⟶ G) (h₀ : s ≫ x₀ = x) (h₁ : s ≫ x₁ = x ≫ w)
    (e : LB.Gen (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (cε 2)))
    (he : e.IsGen) (ρ : LB.Gen (LB.LinComb L (JetSer.primφ w) JetSer.primε)) (hρ : ρ.IsGen) (q : ℕ) (σ : H0 L q)
    (j : L.ι) (y : T.left) (hj : x.left y ∈ LB.wchart L (JetSer.primφ w) (fun _ => j)) (J) (hJ : Good L y J) :
    s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (fun _ => j) ∧
    ∃ c : (T.left.presheaf.stalk y)ˣ,
      sval σ x.left y J = (c ^ q).val * gs x.left y _ (σ.f fun _ => j) ∧
      val ρ x.left y J * val e s.left y J =
        c * (gm x.left y _ (ρ.s fun _ => j) * gm s.left y _ (e.s fun _ => j)) := by
  have E : ∀ I : Finset (Fin 2), s.left ≫ (psum G ![x₀, x₁] I).left = (psum G ![x, x ≫ w] I).left := fun I => by
    rw [comp_psum_two, h₀, h₁]
  have hs : s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left)
      (fun _ => j) := Set.mem_iInter.2 fun I => by
    obtain ⟨k, hk⟩ := psum_mem w x I.down
    have a : (x.left ≫ JetSer.primφ w k) y ∈ L.U j := Set.mem_iInter.1 hj k
    rw [← hk, ← E] at a
    exact a
  have hx : x.left y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hj 0
  let h : (T.left ⟶ G.left) → (T.left.presheaf.stalk y)ˣ := fun ψ => gm ψ y (L.U (J ψ) ⊓ L.U j) (L.g (J ψ) j)
  refine ⟨hs, h x.left, ?_, ?_⟩
  · refine (sec_trans σ x.left y (hJ.mem _ _) hx).trans (congrArg (· * _) (congrArg Units.val ?_))
    show ∏ _k : Fin 1, h (x.left ≫ 𝟙 _) ^ (q : ℤ) = _
    rw [Fintype.prod_unique, Category.comp_id, zpow_natCast]
  · have a : val ρ x.left y J = (∏ k, h (x.left ≫ JetSer.primφ w k) ^ JetSer.primε k) *
        gm x.left y _ (ρ.s fun _ => j) := gen_trans hρ x.left y (hJ.mem _ _) hj
    have b : val e s.left y J = (∏ I : ULift.{0} (Finset (Fin 2)),
        h (s.left ≫ (psum G ![x₀, x₁] I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card))) *
        gm s.left y _ (e.s fun _ => j) := gen_trans he s.left y (hJ.mem _ _) hs
    simp only [E] at b
    rw [a, b, JetSer.prod_prim, JetSer.prod_lam, _root_.mul_mul_mul_comm]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

def germAt (A : Type) [CommRing A] (y : Sp A) : A →+* (Sp A).presheaf.stalk y :=
  ((Sp A).presheaf.germ ⊤ y trivial).hom.comp (toΓ A)

theorem gs_toΓ_eq {A : Type} [CommRing A] (y : Sp A) (a : A) : gs (𝟙 _) y ⊤ (toΓ A a) = germAt A y a :=
  gs_eq (𝟙 _) y ⊤ trivial _

theorem gs_spMap_germAt {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (y : Sp B) (a : A) :
    gs (Geo.Tor.spMap f) y ⊤ (toΓ A a) = germAt B y (f a) := by
  have e := gs_pull (𝟙 _) (Geo.Tor.spMap f) y ⊤ trivial (toΓ A a)
  rw [Category.id_comp] at e
  refine e.symm.trans (Eq.trans ?_ (gs_toΓ_eq y _))
  exact congrArg (gs (𝟙 _) y ⊤)
    (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

variable {V : Type} [CommRing V]

theorem psJet_pow {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) (q : ℕ) :
    psJet m (f ^ q) = psJet m f ^ q := by
  induction q with
  | zero => rw [pow_zero, pow_zero, FBIdJet.psJet_one]
  | succ q ih => rw [pow_succ, pow_succ, FBIdJet.psJet_mul, ih]

theorem toJet_eq {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) :
    JetSer.toJet m f = psJet m f := (congrArg (Ideal.Quotient.mk _) (FBIdJet.psTrunc_eq m f)).symm

theorem ev_pt_one {d : ℕ} (f : PS V 1 d) : ev (n := 1) ![pt V (n := 1) d 0] f = f := by
  have : (![pt V d 0] : Fin 1 → Pt V 1 d) = fun j => pt V d j := by
    funext j; fin_cases j; rfl
  rw [this]
  unfold ev
  exact congrFun MvPowerSeries.subst_self f

theorem gs_of_isSer1 {G : Over (Sp V)} {d : ℕ} (xT : JetPts G (Fin 1 × Fin d)) (x : JetSer.Fam G (Fin d))
    (hM : Match (oneCol d) xT x) (U : G.left.Opens) (f : Γ(G.left, U)) (g : PS V 1 d) (h : JetSer.IsSer1 x U f g)
    (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) :
    (xT m).left y ∈ U ∧ gs (xT m).left y U f = germAt _ y (psJet m g) := by
  have R : JetSer.Rep x (pt V (n := 1) d 0) (fun m => LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m) := by
    refine ⟨fun j => by simp [pt], fun m => ?_⟩
    obtain ⟨e, he1, he2⟩ := hM m
    refine ⟨(e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m), fun j => ?_, ?_⟩
    · exact (he1 j).trans (JetSer.toJet_X m ((0 : Fin 1), j)).symm
    · apply Over.OverMorphism.ext
      exact (Category.id_comp _).trans he2
  obtain ⟨h1, h2⟩ := h 1 _ _ R m
  have e : (LinkLaw.toAt (V := V) (Jet V (Fin 1 × Fin d) m) ≫ xT m).left = (xT m).left := Category.id_comp _
  have h1' : ⊤ ≤ (xT m).left ⁻¹ᵁ U := e ▸ h1
  have h2' : JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U f = psJet m g :=
    (congrArg (fun p => JetSer.fnVal (A := Jet V (Fin 1 × Fin d) m) p U f) e).symm.trans
      (h2.trans (by rw [ev_pt_one]; exact toJet_eq m g))
  refine ⟨h1' (show y ∈ (⊤ : (Sp (Jet V (Fin 1 × Fin d) m)).Opens) from trivial), ?_⟩
  rw [← h2']
  exact (JetSer.valSer_germ_fnVal (A := Jet V (Fin 1 × Fin d) m) (xT m).left U h1' y f).symm

def diagSub {d : ℕ} (m : ℕ) (φ : Pt V 1 d) : Jet V (Fin 2 × Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (φ j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) V) p.1 p.2

theorem psIn_one {d : ℕ} (m : ℕ) (f : PS V 1 d) : psIn d m ![(0 : Fin 1)] f = psTrunc m f := by
  unfold psIn
  have : (fun p : Fin 1 × Fin d => ((![(0 : Fin 1)] : Fin 1 → Fin 1) p.1, p.2)) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [this, MvPolynomial.rename_id_apply]

theorem diagSub_zero {d : ℕ} (m : ℕ) (φ : Pt V 1 d) : (diagSub m φ).comp (jetCopy d m 0) = AlgHom.id V _ := by
  refine Chart.jet_ext (R := V) fun p => ?_
  obtain ⟨a, i⟩ := p
  obtain rfl : a = 0 := Subsingleton.elim _ _
  show diagSub m φ (jetCopy d m 0 (Ideal.Quotient.mk _ (MvPolynomial.X _))) = Ideal.Quotient.mk _ (MvPolynomial.X _)
  rw [jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord]
  simp

theorem diagSub_one {d : ℕ} (m : ℕ) (φ : Pt V 1 d) :
    (diagSub m φ).comp (jetCopy d m 1) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2) := by
  refine Chart.jet_ext (R := V) fun p => ?_
  show diagSub m φ (jetCopy d m 1 (Ideal.Quotient.mk _ (MvPolynomial.X _))) =
    jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) (Ideal.Quotient.mk _ (MvPolynomial.X _))
  rw [jetCopy, LinkLaw.jetMap_coord, diagSub, jetSubstP, LinkLaw.jetMap_coord, jetSubstP, LinkLaw.jetMap_coord]
  simp [psIn_one]

theorem diagSub_psJet {d : ℕ} (m : ℕ) (φ : Pt V 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (ε : PS V 2 d) :
    diagSub m φ (psJet m ε) = psJet m (ev (n := 1) ![pt V (n := 1) d 0, comp1 φ (pt V (n := 1) d 0)] ε) := by
  have c : comp1 φ (pt V (n := 1) d 0) = φ := funext fun i => ev_pt_one _
  rw [c]
  have h0 : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) = 0 := by
    rintro ⟨a, i⟩
    fin_cases a
    · simp [pt]
    · exact hφ i
  obtain ⟨Φ, hΦ, hsub⟩ := LinkLaw.exists_subst
    (fun p : Fin 2 × Fin d => (![pt V (n := 1) d 0, φ] : Fin 2 → Pt V 1 d) p.1 p.2) h0 m
  have e : diagSub m φ = Φ := by
    refine Chart.jet_ext (R := V) fun p => Eq.trans ?_ (hΦ p).symm
    obtain ⟨a, i⟩ := p
    fin_cases a
    · refine Eq.trans ?_ (JetSer.toJet_X m ((0 : Fin 1), i)).symm
      have := AlgHom.congr_fun (diagSub_zero m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord] at this
      exact this
    · have := AlgHom.congr_fun (diagSub_one m φ) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
      rw [AlgHom.comp_apply, jetCopy, LinkLaw.jetMap_coord,
        LinkLaw.jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)] at this
      exact this
  rw [e, ← toJet_eq, ← toJet_eq]
  exact hsub ε

theorem homAt_comp' {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  exact (Spec.map_comp _ _).symm

theorem val_prim_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (hp : Function.Surjective t.G.hom.appTop.hom) (wP : PrimTyG t) (hw : IsPrimG t wP)
    (ρ : LB.Gen (LB.LinComb t.PP.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ ρ (eSec t.G)) t.PP.rig)
    {Z : Scheme.{0}} (r : Z ⟶ t.G.left) (z : Z) (J) (hJ : Good t.PP.L z J) : val wP r z J = val ρ r z J := by
  have he : eSec t.G ≫ t.G.hom = 𝟙 S := Over.w η[t.G]
  refine gen_unique' t.PP.isLB (fun U _ k => ?_) t.G.hom (eSec t.G) he hp hw.1 hρ (fun y J hJ => ?_) Z r z J hJ
  · have P := JetSer.prod_prim (t.act.act H.w0) (𝟙 t.G) k
    simp only [Over.id_left, Category.id_comp] at P
    refine P.trans (Eq.symm ((DVR.prod_sum₂ (K := Fin 1) (U := U) _ (c := k (𝟙 _))
      (by rw [Fintype.prod_unique]; exact zpow_one _)
      (DVR.prod_neg _ _ (JetSer.prod_lam (𝟙 t.G) (t.act.act H.w0) k))).trans ?_))
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, Over.id_left]
    abel
  · have a := val_corr hJ hw.2 (𝟙 _)
    have b := val_corr hJ hc (𝟙 _)
    rw [val_pull hJ, Category.id_comp] at a b
    exact a.trans b.symm

theorem linkSec : LinkSecSt := by
  intro E _ _ _ H V _ _ t hp d BT tg xT eT wPT hC hF hW x _ hM j _ ρ hρ hc ε hε q σ r S g hr hS hg m y J hJ
  letI := H.starRing
  obtain ⟨hj, vr⟩ := gs_of_isSer1 xT x hM _ _ r hr m y
  obtain ⟨-, vS⟩ := gs_of_isSer1 xT x hM _ _ S hS m y
  let s := Formalism.L2.Pj.homAt (𝟙 (Sp V)) (diagSub m (BT.A.act H.w0))
  have h₀ : s ≫ jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2) = xT m := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_zero]
    refine Eq.trans (congrArg (· ≫ xT m) ?_) (Category.id_comp _)
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  have h₁ : s ≫ jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2) = xT m ≫ t.act.act H.w0 := by
    rw [jptG, ← Category.assoc, homAt_comp', diagSub_one]
    exact (hC.act m H.w0).symm
  obtain ⟨hs, c, c₁, c₂⟩ := change_index (t.act.act H.w0) (xT m) s _ _ h₀ h₁ (eT m) (hF.gen m) ρ hρ q σ j y hj J hJ
  obtain ⟨J₂, hJ₂, e₂⟩ := exists_good t.PP.L t.PP.isLB (s.left y)
    (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j)
    (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 hs I)
  have e₂' : ∀ I, J₂ (𝟙 _ ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j :=
    fun I => (congrArg J₂ (Category.id_comp _)).trans (e₂ I)
  have v₂ := hε m (s.left y) J₂ hJ₂ e₂'
  have v₃ := (gs_unit (𝟙 _) (s.left y) _ hs _).trans
    ((congrArg Units.val (val_of (L := t.PP.L) (ε := cε 2) (eT m) (𝟙 _) (s.left y) J₂ (fun _ => j) e₂')).symm.trans v₂)
  have vε : (gm s.left y _ ((eT m).s fun _ => j)).val = germAt _ y (psJet m (diagSer BT H.w0 ε)) :=
    (gs_unit s.left y _ hs _).symm.trans ((gs_stalkMap s.left y _ hs _).trans
      ((congrArg (s.left.stalkMap y).hom v₃).trans ((gs_stalkMap s.left y ⊤ trivial _).symm.trans
        ((gs_spMap_germAt _ y _).trans (congrArg (germAt _ y) (diagSub_psJet m _ (BT.A.const H.w0) ε))))))
  have vρ : (gm (xT m).left y _ (ρ.s fun _ => j)).val = germAt _ y (psJet m r) :=
    (gs_unit (xT m).left y _ hj _).symm.trans vr
  have vL : val (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m) (𝟙 (Sp (Jet V (Fin 1 × Fin d) m))) y J =
      c * (gm (xT m).left y _ (ρ.s fun _ => j) * gm s.left y _ ((eT m).s fun _ => j)) := by
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) c₂)
    · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_prim_eq t hp wPT hW ρ hρ hc (xT m).left y J hJ))
      exact congrArg (fun p => val wPT p y J) (Category.id_comp _)
    · refine (val_pull hJ _ _ _).trans ?_
      exact congrArg (fun p => val (L := t.PP.L) (ε := cε 2) (eT m) p y J) (Category.id_comp _)
  rw [vL, gs_toΓ_eq]
  refine c₁.trans ((congrArg (_ * ·) vS).trans ?_)
  rw [← hg, FBIdJet.psJet_mul, psJet_pow, FBIdJet.psJet_mul, map_mul, map_pow, map_mul, ← vε, ← vρ]
  simp only [Units.val_pow_eq_pow_val, Units.val_mul]
  ring

end GlobalTheory.LinkSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartFromPointDatumOfLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartLink

theorem cubical_eq {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (h : Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom) {L : RigLB G} (c c' : CubicalStr G L) : c = c' := by
  have e : c.t.s = c'.t.s := by
    refine JetSer.gen_ext_val (φ := thφ G (x3 G)) (ε := thε) L.isLB c.isGen c'.isGen fun y J hJ => ?_
    refine gen_unique L.isLB (G ⊗ G ⊗ G).hom (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left (Over.w _) h c.isGen c'.isGen
      (fun y J hJ => ?_) _ _ y J hJ
    exact ((isCub_cubV c (T := 𝟙_ (Over S)) hJ).face 1 1).trans ((isCub_cubV c' (T := 𝟙_ (Over S)) hJ).face 1 1).symm
  obtain ⟨⟨s⟩, _, _, _, _, _⟩ := c
  obtain ⟨⟨s'⟩, _, _, _, _, _⟩ := c'
  obtain rfl : s = s' := e
  rfl

theorem surjective_of_sq {S : Scheme.{0}} {G : Over S} (h : Function.Surjective (G ⊗ G).hom.appTop.hom) :
    Function.Surjective G.hom.appTop.hom := by
  intro f
  obtain ⟨a, ha⟩ := h ((fst G G).left.appTop.hom f)
  refine ⟨a, ?_⟩
  have e₁ : (lift (𝟙 G) (𝟙 G)).left ≫ (G ⊗ G).hom = G.hom := Over.w _
  have e₂ : (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 G) (𝟙 G))
  have := congrArg (lift (𝟙 G) (𝟙 G)).left.appTop.hom ha
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, e₁, e₂] at this
  simpa using this

theorem psJet_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (g : MvPowerSeries κ R) : psJet m (MvPowerSeries.map f g) = jetCoef f κ m (psJet m g) := by
  unfold psJet jetCoef
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
  congr 1
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem germA_comb {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {κ : Type} [Fintype κ] [DecidableEq κ] (z : JetPts G κ) (τ : Frames U.LG.L z) (hτ : τ.Gen)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ)
    {l : ℕ} (c : Fin l → F) (σ : Fin l → H0 U.LG.L q) (g : Fin l → MvPowerSeries κ V)
    (hσ : ∀ i m (y : Sp (Jet V κ m)) J, Good U.LG.L y J →
      sval (σ i) (z m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m (g i))) * (val (τ m) (𝟙 _) y J ^ q).val)
    (σ' : U.SecGF F q)
    (hlin : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (q : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (q : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i))) :
    GermA U z τ F q σ' (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)) := by
  intro m
  have hL := U.LG.isLB
  have key : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
      sval (σ i) (r ≫ (z m).left) y J = cst r y (psJet m (g i)) * (val (τ m) r y J ^ q).val := by
    intro i
    obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet V κ m) hL (σ i) (z m).left
      (GeneratorPullback.powGen U.LG.L _ _ (τ m) q) (powGen_isGen_of_isGen _ (hτ m) q)
      (fun W _ h => by simp only [Category.comp_id, _root_.mul_one])
    have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V κ m)) (y : Z) (J), Good U.LG.L y J →
        sval (σ i) (r ≫ (z m).left) y J = cst r y v * (val (τ m) r y J ^ q).val := fun Z r y J hJ =>
      (hv Z r y J hJ).trans (congrArg (fun u => cst r y v * Units.val u) (map_pow _ _ _))
    obtain rfl : v = psJet m (g i) := H1.cst_ext fun y => by
      obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
      have e := hv' _ (𝟙 _) y J hJ
      rw [Category.id_comp] at e
      exact (Units.mul_left_inj _).1 (e.symm.trans (hσ i m y J hJ))
    exact hv'
  obtain ⟨a, a₁, a₂⟩ := GermBasic.exists_jetPt (F := F) z m
  refine ⟨a, a₁, a₂, fun y J hJ => ?_⟩
  refine (BoxExpansion.secLin_val hlin a y hJ).trans ?_
  have e : gs (𝟙 _) y ⊤ (toΓ _ (psJet m (∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i)))) =
      ∑ i, cst (𝟙 _) y (algebraMap F (Jet F κ m) (c i)) *
        cst (𝟙 _) y (psJet m (MvPowerSeries.map (algebraMap V F) (g i))) := by
    refine (congrArg (cst (𝟙 _) y) (GermBasic.psJet_sum m c _)).trans ((ExpansionValueZero.cst_sum _ _ _ _).trans ?_)
    exact Finset.sum_congr rfl fun i _ => H1.cst_mul _ _ _ _
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a₂, key i _ _ y J hJ, _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ rfl)
  · refine (gs_pull a _ y ⊤ trivial _).trans ?_
    rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
    rfl
  · rw [psJet_map, ← ExpansionValueZero.cst_comp, Category.id_comp]

theorem exists_chartData {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {V : Type} [CommRing V]
    [IsLocalRing V] (t : SAB H (Sp V)) (Lr : RigLB t.G) (h : Lr = t.PP) (c : CubicalStr t.G Lr)
    (s₂ : Function.Surjective (t.G ⊗ t.G).hom.appTop.hom)
    (s₃ : Function.Surjective (t.G ⊗ t.G ⊗ t.G).hom.appTop.hom) :
    letI := H.starRing
    ∀ (d : ℕ) (BT : FB V d (𝓞 E)) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
      (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
      IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
      IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT →
      IsUnivJ t.G (Fin 1 × Fin d) xT → FrTrunc t (𝟙 (Sp V)) d xT eT →
    ∀ τ : Frames Lr.L (κ := Fin 1 × Fin d) xT,
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
        Good Lr.L y J → val (τ m) (𝟙 _) y J =
          val (genCast (congrArg RigLB.L h).symm _ _ (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m)) (𝟙 _) y J) →
    ∃ (x : JetSer.Fam t.G (Fin d)) (j : Lr.L.ι)
      (u : ∀ a : 𝓞 E, LB.Gen (LB.LinComb Lr.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε))
      (B : FB V d (𝓞 E)) (ρ : LB.Gen (LB.LinComb Lr.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)) (ε : PS V 2 d),
      Chart.IsUnivChart t.G d x ∧ ⊤ ≤ η[t.G].left ⁻¹ᵁ Lr.L.U j ∧ (∀ a, JetSer.IsNormRos Lr.L _ _ (u a)) ∧
      JetSer.IsFBOf Lr c t.act u x j B ∧ ρ.IsGen ∧ JetSer.Related B BT (pt V (n := 1) d 0) (pt V (n := 1) d 0) ε ∧
      ∀ (q : ℕ) (σ : H0 Lr.L q) (r S g : PS V 1 d), JetSer.IsSer1 x _ (ρ.s (fun _ => j)).val r →
        JetSer.IsSer1 x _ (σ.f (fun _ => j)) S → g * (diagSer BT H.w0 ε * r) ^ q = S →
        ∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → Lr.L.ι),
          Good Lr.L y J →
          sval σ (xT m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (τ m) (𝟙 _) y J ^ q).val := by
  subst h
  obtain rfl : c = t.cub := cubical_eq s₃ _ _
  letI := H.starRing
  intro d BT tg xT eT wPT hC hF hW hU hT τ hEL
  obtain ⟨x, hx, hM⟩ := univConv V t.G _ xT hU d (oneCol d)
  obtain ⟨j, hj⟩ := JetSer.exists_index_of_local t.PP.L t.PP.isLB η[t.G].left
  have hu : ∀ a : 𝓞 E, ∃ u, JetSer.IsNormRos t.PP.L (t.act.act a) (t.act.act (star a)) u := fun a => by
    have := t.act.hom a
    have := t.act.hom (star a)
    exact (NormRos.normRos_of_lbIso _ t.G t.PP.L t.PP.isLB _ _ (t.adj a)).1
  choose u hu using hu
  obtain ⟨B, hB⟩ := JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.1 V t.G s₂ s₃ t.PP t.cub (𝓞 E) t.act u hu d x hx j hj
  have := t.act.hom H.w0
  obtain ⟨ρ, hρ, hρc⟩ := (JetSer.exists_unique_normPrim _ t.G t.PP (t.act.act H.w0) t.prim).1
  obtain ⟨ε, hε⟩ := GlobalTheory.T.truncation_frames_local_series E H V t d _ _ _ _ _ _ tg xT eT wPT hC hF hW hT j hj
  refine ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ,
    LinkRel.linkRel E H V t s₂ d BT tg xT eT wPT hC hF hW x hx hM j hj u hu B hB ε hε,
    fun q σ r S g hr hS hg m y J hJ => ?_⟩
  rw [hEL m y J hJ]
  exact LinkSec.linkSec E H V t (surjective_of_sq s₂) d BT tg xT eT wPT hC hF hW x hx hM j hj ρ hρ hρc ε hε q σ r S g
    hr hS hg m y J hJ

theorem isUnit_diagSer {V : Type} [CommRing V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B B' : FB V d O}
    {φ φi : Pt V 1 d} {ε : PS V 2 d} (h : JetSer.Related B B' φ φi ε) (w0 : O) : IsUnit (diagSer B' w0 ε) := by
  have e₀ : MvPowerSeries.constantCoeff ε = 1 := by
    rw [← GaugeAdjoint.constantCoeff_ev (a := ![0, pt V (n := 1) d 0]) (fun j i => by fin_cases j <;> simp [pt]) ε,
      h.ax0, map_one]
  have c : comp1 (B'.A.act w0) (pt V (n := 1) d 0) = B'.A.act w0 := funext fun i => LinkSec.ev_pt_one _
  rw [MvPowerSeries.isUnit_iff_constantCoeff, diagSer, c, GaugeAdjoint.constantCoeff_ev (fun j i => ?_) ε, e₀]
  · exact isUnit_one
  · fin_cases j
    · simp [pt]
    · exact B'.A.const w0 i

theorem linkSt_holds : LinkSt := by
  intro E _ _ _ H V _ _ _ hc t P tors ϖ hϖ Q hQ F _ _ _ _ v hv d BT tg xT eT wPT hC hF hW hU hT τ hτ hEL
  letI := H.starRing
  obtain ⟨s₂, s₃⟩ := FamGerm.surjective_appTop_sq_cube P.U.toUnifPre
  obtain ⟨x, j, u, B, ρ, ε, hx, hj, hu, hB, hρ, hR, hS⟩ := exists_chartData H t P.U.LG P.bundle P.U.cubG s₂ s₃
    d BT tg xT eT wPT hC hF hW hU hT τ hEL
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hR, ?_⟩
  rintro q s f f' ⟨l, c, σ, fi, g, r, h₁, h₂, h₃, h₄, h₅⟩ hf
  obtain ⟨w, hw⟩ := (isUnit_diagSer hR H.w0).exists_right_inv
  obtain ⟨σ', hσ'⟩ := BoxExpansion.exists_secLin P.U.LG.isLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj t.G)).left (UnifPre.gFK (R := V) (G := t.G) F)
    (fun _ : Fin 1 => UnifPre.gFK (R := V) (G := t.G) F) (fun _ => (Category.comp_id _).symm) σ c
  refine ⟨σ', ⟨l, c, σ, fi, h₁, hσ', h₂⟩, ?_⟩
  have eV : TWO.algVF (V := V) (F := F) = algebraMap V F := (IsScalarTower.algebraMap_eq V _ F).symm
  have e : f' = ∑ i, c i • MvPowerSeries.map (algebraMap V F) (g i * w ^ q) := by
    have e₁ : f' = f * MvPowerSeries.map (algebraMap V F) (w ^ q) := by
      rw [← hf, _root_.mul_assoc, ← map_pow, ← map_mul, ← mul_pow, hw, one_pow, map_one, _root_.mul_one]
    rw [e₁, h₅, Finset.sum_mul, eV]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, MvPowerSeries.smul_eq_C_mul, _root_.mul_assoc]
  rw [e]
  refine germA_comb P.U.toUnifPre xT τ hτ F q c σ _ (fun i m y J hJ => ?_) σ' hσ'
  obtain ⟨S, hS₁, hS₂⟩ := h₄ i
  refine hS q (σ i) r S _ h₃ hS₁ ?_ m y J hJ
  rw [← hS₂, _root_.mul_assoc, ← mul_pow, ← _root_.mul_assoc, _root_.mul_comm w, hw, _root_.one_mul]

theorem link : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → LinkSt := fun _ _ _ _ => linkSt_holds

end GlobalTheory.ChartLink
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartFromPointDatumOfLawsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFromPointDatum_of_laws : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → LinkSt := by
  first | exact @GlobalTheory.ChartLink.link | exact GlobalTheory.ChartLink.link | (intros; apply GlobalTheory.ChartLink.link <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxTupOfColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxTupOfColumns
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem boxTup_of_columns : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxTupSt := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ Q hQ F _ _ _ _ v g g' π hg hg' hπ τ hτ hEL n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
    s s₂ t₀ t p w ζ x σ f h
  have hG := hL.globalFns
  have hk : 1 ≤ g' * g := Nat.mul_pos hg' hg
  have hA : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F g'
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F (g' * g)
  obtain ⟨p', hp'⟩ := BoxQk.exists_isBoxQk hG T.V n P.D.toPre D'.toPre pD F (g' * g) p
  have hw : ∀ i, (w i).IsGen := fun i => (h i).2.2.1
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (g' * g) p' p hp' w hw
  obtain ⟨σ', hσ', -⟩ := (expandsG_bijective_of_dvr hL hL2 hL4 hT T.V D' A' G' U' F (g' * g) hk).2 (bx t)
  let x' : TFK (R := T.V) F ⟶ A'.A := pA.lim.lift (Fan.mk _ x)
  have hx' : ∀ i, x' ≫ pA.pr i = x i := fun i => pA.lim.fac (Fan.mk _ x) ⟨i⟩
  have hπ' : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, _root_.mul_comm, hπ]
  refine ⟨bx₁ s, bx s₂, p', w', ∏ i, ζ i, x', bx t₀, bx t, σ', ⟨?_, ?_, ⟨hw', ?_, ?_⟩, ?_, ?_, ?_, ?_, hσ', ?_⟩, hx'⟩
  · have := NuBox.main T.V ϖ hϖ n P.D D' pD Q hQ F v g' s (bx₁ s) ((hbx₁ _ _).2 rfl) (fun _ => 0) (fun i => (h i).1)
    rw [Finset.sum_const_zero] at this
    exact this
  · exact BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact (star π) g g' hg hg' hπ' s s₂ _ _
      (fun i => (h i).2.1) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  · exact Finset.prod_ne_zero_iff.2 fun i _ => (h i).2.2.2.1
  · exact finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (g' * g) hk p' p hp' w w' hw hw' hΦ ζ (fun i => (h i).2.2.2.2.1)
  · exact ProdTorsion.qkToAk_box hL T.V _ n P.D D' P.A A' C.I.G.G G' pD pA pG U' P.U PU
      (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ P.U) (expBijF_of_admissible_base hL hL2 T.V _ hA _ _ _ U') F (g' * g) hk
      p' p hp' x' x hx' (fun i => (h i).2.2.2.2.2.1)
  · intro i
    rw [← Category.assoc, hx']
    exact (h i).2.2.2.2.2.2.1
  · exact hΦ s₂ t₀ _ _ (fun i => (h i).2.2.2.2.2.2.2.1) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl)
  · refine (isSmul_iff _ _ _).2 ?_
    calc
      bx t = bx (fun i => ζ i • t₀ i) :=
        congrArg bx (funext fun i => (isSmul_iff _ _ _).1 (h i).2.2.2.2.2.2.2.2.1)
      _ = (∏ i, ζ i) • bx t₀ := by simpa using bx.map_smul_univ ζ t₀
  · exact GlobalTheory.T.germ_boxProduct_eq_prod_germs hL hL2 hL4 hT E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
      C.chartT C.frameT C.primT τ hτ hEL n D' A' G' pD pA pG U' PU F (g' * g) hk σ t f σ' (bx t)
      (fun i => (h i).2.2.2.2.2.2.2.2.2) ((hbx _ _).2 rfl) hσ'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BoxTupOfColumnsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxTupSt_of_laws_of_twistBaseChange : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxTupSt := by
  first | exact @GlobalTheory.boxTup_of_columns | exact GlobalTheory.boxTup_of_columns | (intros; apply GlobalTheory.boxTup_of_columns <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColumnsToTupleHarmonicValues
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Transfer

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer GlobalTheory.PowGerm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem dLin_id : dLin (pt R (n := 1) d 0) = 1 := by
  classical
  ext i j
  simp only [dLin, pt, coeff_X, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg]
    intro e
    exact h (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero e)).symm

theorem law_eq {B B' : FB R d O} {ε : PS R 2 d} (h : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε) :
    B.G.F = B'.G.F := funext fun i => ((Related.refl B).law i).trans (h.law i).symm

theorem act_eq {B B' : FB R d O} {ε : PS R 2 d} (h : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε) :
    B.A.act = B'.A.act := funext fun a => ((Related.refl B).act a).trans (h.act a).symm

theorem const_diagSer {B B' : FB R d O} {φ φi : Pt R 1 d} {ε : PS R 2 d} (h : Related B B' φ φi ε) (w0 : O) :
    constantCoeff (diagSer B' w0 ε) = 1 := by
  have h1 := congrArg constantCoeff h.ax1
  rw [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), map_one] at h1
  unfold diagSer
  rw [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (B'.A.const w0) (gp_pt 0))), h1]

theorem exists_inv_pow {σ : Type} (s : MvPowerSeries σ R) (hs : constantCoeff s = 1) (q : ℕ) :
    ∃ un : MvPowerSeries σ R, constantCoeff un = 1 ∧ un * s ^ q = 1 := by
  have hu : IsUnit (s ^ q) := (MvPowerSeries.isUnit_iff_constantCoeff.2 (hs ▸ isUnit_one)).pow q
  obtain ⟨un, hun⟩ := hu.exists_left_inv
  refine ⟨un, ?_, hun⟩
  have := congrArg constantCoeff hun
  rwa [map_mul, map_pow, hs, one_pow, mul_one, map_one] at this

theorem const_gauge {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d}
    (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have h1 := congrArg constantCoeff hh.ax1
  rwa [gt_const_ev_eq _ (pair_points_zero_constant (gp_pt 0) gp_zero₂), map_zero] at h1

theorem exists_gauge {B B' : FB R d O} {ε : PS R 2 d} (hr : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε)
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {R' : Type} [CommRing R'] [Algebra R' k] (B₂ : FB R' d O)
    (hF : B'.FK k = B₂.FK k) (hA : ∀ a, B'.actK k a = B₂.actK k a)
    (hG : ∀ h, B'.IsCanonGauge k h ↔ B₂.IsCanonGauge k h) (h₀ : PS k 2 d) (hh : B.IsCanonGauge k h₀) :
    ∃ h' : PS k 2 d, B₂.IsCanonGauge k h' ∧ ∀ (w0 : O) (m : ℕ) (f f' : PS k 1 d),
      f' * MvPowerSeries.map (algebraMap R k) (diagSer B' w0 ε) ^ m = f →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (P : MvPolynomial Λ k),
        B₂.nabVal k h' w0 m f' u P = B.nabVal k h₀ w0 m f u P := by
  obtain ⟨h', hh', hv⟩ := GlobalTheory.JetRoad.jetRoad.2.2.2.2.2.2.2.2.2.2.2.2.1 R d O B B' _ _ ε hr k h₀ hh
  refine ⟨h', (hG h').1 hh', fun w0 m f f' hf Λ _ u P => ?_⟩
  have e : (fun i => FB.toK k (pt R (n := 1) d 0 i)) = pt k (n := 1) d 0 := by
    funext i
    simp [pt]
  have h1 := hv w0 m f f' (by rw [e, gt_ev_pt_self]; exact hf) Λ u P
  rw [dLin_id, Matrix.map_one _ (map_zero _) (map_one _)] at h1
  simp only [Matrix.one_mulVec] at h1
  rw [← h1]
  unfold FB.nabVal FB.hL
  rw [hF, hA]

theorem eig_map {k : Type} [CommRing k] [Algebra R k] (B : FB R d O) (a : O) (u : Fin d → R) (s : R)
    (h : (dAct R B a).mulVec u = s • u) :
    (dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k s • fun i => algebraMap R k (u i) := by
  funext i
  have h1 := congrArg (algebraMap R k) (congrFun h i)
  simpa [Matrix.mulVec, dotProduct, dAct, FB.actK, coeff_map] using h1

theorem value_eq [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] {B B' : FB R d O} {ε : PS R 2 d}
    (hr : Related B B' (pt R (n := 1) d 0) (pt R (n := 1) d 0) ε)
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {R' : Type} [CommRing R'] [Algebra R' k] (B₂ : FB R' d O)
    (hF : B'.FK k = B₂.FK k) (hA : ∀ a, B'.actK k a = B₂.actK k a)
    (hG : ∀ h, B'.IsCanonGauge k h ↔ B₂.IsCanonGauge k h) (h₀ h : PS k 2 d) (hh₀ : B.IsCanonGauge k h₀)
    (hh : B₂.IsCanonGauge k h) {T : Type} [Fintype T] (r : T → ℕ) (cc : T → T) (σ : T → O →+* k)
    (hcc : ∀ τ, cc (cc τ) = τ) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) (u : (Σ τ : T, Fin (r τ)) → Fin d → k)
    (hu : ∀ l a, (dAct k B₂ a).mulVec (u l) = σ l.1 a • u l) {n : ℕ}
    (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)
    (hQ : ∀ (τ : T) (i : Fin (r τ)) (i' : Fin (r (cc τ))), ∑ b : Fin n,
      MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b)
        (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0)
    (w0 : O) (q : ℕ) (f f' : Fin n → PS k 1 d)
    (hf : ∀ b, f' b * MvPowerSeries.map (algebraMap R k) (diagSer B' w0 ε) ^ q = f b)
    {Ix : Type} [Fintype Ix] (e : (Σ τ : T, Fin (r τ)) × Fin n → Ix) (cp : Ix → Fin n) (u' : Ix → Fin d → k)
    (hcp : ∀ p, cp (e p) = p.2) (hu' : ∀ p, u' (e p) = u p.1) :
    Formalism.L2.Pj.nabValN B₂ k h w0 q (boxSer f') cp u' (MvPolynomial.rename e Q) =
      ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h₀ w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) := by
  obtain ⟨h', hh', hval⟩ := exists_gauge hr B₂ hF hA hG h₀ hh₀
  rw [nabValN_boxSer R' d O B₂ k h w0 (const_gauge hh) q n f' _ Ix e cp u u' hcp hu' Q,
    canonGauge_independence_harmonic R' d O k B₂ h h' hh hh' T r cc (fun _ => True) σ hcc (fun _ => Or.inl trivial)
      hσ hsep u hu n Q (fun τ _ => hQ τ) w0 q f']
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [Finset.prod_congr rfl fun b _ => hval w0 q (f b) (f' b) (hf b) _ u (MvPolynomial.monomial (colM mo b) 1)]

end GlobalTheory.Transfer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory


set_option maxHeartbeats 400000 in
theorem transfer_columns : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (tors : P.TorsionIso) (ϖ : T.V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v), letI := io.toAlgebra; ∃ x hx j hj u hu B hB ρ hρ, B.G.F = C.FT ∧ B.A.act = C.actT ∧ ∀ (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (s : Fin n → Fam P.D.toPre F g') (s' t : Fin n → Fam P.D.toPre F (g' * g)) (f : Fin n → PS F 1 (chD C.ch)), (∀ b, NuGe P.D Q F v g' (s b) 0 ∧ PullAl P.D F P.oD (star π) g' g (s b) (s' b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Transl (g' * g) π (s' b) (t b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Germ (g' * g) (t b) (f b)) → ∃ (S : Fam D'.toPre F g') (S₂ : Fam D'.toPre F (g' * g)) (p' : QkPt D'.toPre F (g' * g)) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε (g' * g)))) (ζ' : F) (x' : TFK (R := T.V) F ⟶ A'.A) (T₀ T₁ : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) (un : PS T.V 1 (chD C.ch)), BoxTup C P Q F v g g' π pG PU oD' S S₂ p' w' ζ' x' T₀ T₁ σ' h ∧ MvPowerSeries.constantCoeff un = 1 ∧ h = boxSer (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un) ∧ ∀ h₀ : PS F 2 (chD C.ch), B.IsCanonGauge F h₀ → ∀ (rk : (E →+* ℂ) → ℕ) (hrk : ∀ τ, rk τ ≤ Dw.mult τ) (Pp : MvPolynomial ((Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n) F), (∀ (τ : E →+* ℂ) (i : Fin (rk τ)) (i' : Fin (rk (ComplexEmbedding.conjugate τ))), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) (MvPolynomial.pderiv ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) Pp) = 0) → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.rename (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n)) Pp) = (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).colVal h₀ (g' * g) (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) Pp f := by
  intro L1 L2 L4 TW E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hFr P tors ϖ hϖ Q hQ F _ _ _ _ _ _ v hv
  letI := io.toAlgebra
  haveI := T.cpl
  obtain ⟨BT, e1, e2, e3, e4, e5, e6, e7⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨hF, hA, hG, hcan⟩ := e7 F
  obtain ⟨τ, hτ, hEL, -⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT
  obtain ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, ε, hrel, hgerm⟩ := GlobalTheory.T.chartFromPointDatum_of_laws L1 L2 L4 TW E H T.V T.cpl C.I.G P tors ϖ hϖ
    Q hQ F v hv (chD C.ch) BT C.tgT C.xT C.eT C.wPT (by rw [e1, e2]; exact C.chartT)
    (by rw [e1, e2, e3, e4, e5, e6]; exact C.frameT) C.primT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C) hFr τ hτ
    (by rw [e2]; exact hEL)
  refine ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, (Transfer.law_eq hrel).trans e1, (Transfer.act_eq hrel).trans e2, ?_⟩
  intro g g' π hg hg' hπ n D' A' G' _ _ pD pA pG U' PU _ oD' hxe hon s s' t f hcol
  obtain ⟨un, hun1, hun⟩ := Transfer.exists_inv_pow _ (Transfer.const_diagSer hrel H.w0) (g' * g)
  have hf : ∀ b, (f b * MvPowerSeries.map (algebraMap T.V F) un) *
      MvPowerSeries.map (algebraMap T.V F) (diagSer BT H.w0 ε) ^ (g' * g) = f b := fun b => by
    rw [_root_.mul_assoc, ← map_pow, ← map_mul, hun, map_one, _root_.mul_one]
  choose σ hσ1 hσ2 using fun b => hgerm (g' * g) (t b) (f b) _ (hcol b).2.2.2 (hf b)
  choose p xx w ζ t₀ h1 h2 h3 h4 h5 h6 h7 using fun b => (hcol b).2.2.1
  obtain ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', hbox, -⟩ := GlobalTheory.T.boxTupSt_of_laws_of_twistBaseChange L1 L2 L4 TW E H Dw l Xo c T io y C P ϖ hϖ Q hQ F v
    g g' π hg hg' hπ τ hτ hEL n D' A' G' pD pA pG U' PU oD' hxe hon s s' t₀ t p w ζ xx σ
    (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un)
    (fun b => ⟨(hcol b).1, (hcol b).2.1, h3 b, h4 b, h5 b, h1 b, h2 b, h6 b, h7 b, hσ1 b, hσ2 b⟩)
  refine ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', _, un, hbox, hun1, rfl, ?_⟩
  intro h₀ hh₀ rk hrk Pp hPp
  have huv : ∀ ℓ i, algebraMap T.Fr F (C.ch.uvec ℓ i) = algebraMap T.V F (C.uvecT ℓ i) := fun ℓ i => by
    rw [C.gen.1.2.2.2.2.2.2 ℓ i, ← IsScalarTower.algebraMap_apply]
  refine Transfer.value_eq hrel C.ch.B hF hA hG h₀ _ hh₀ hcan rk ComplexEmbedding.conjugate
    (fun τ => (algebraMap T.Fr F).comp (io.comp (embK c τ))) (fun τ => ComplexEmbedding.involutive_conjugate E τ) ?_ ?_
    (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) ?_ Pp hPp
    H.w0 (g' * g) f _ hf
    (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n))
    (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
    (fun _ => rfl) (fun p => funext fun i => huv _ i)
  · intro τ a
    have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    exact congrArg (fun z => algebraMap T.Fr F (io z)) h
  · intro τ τ' hne
    obtain ⟨a, ha⟩ := EigDir.embK_sep c τ τ' hne
    refine ⟨a, ?_⟩
    simp only [RingHom.comp_apply]
    rw [← map_sub, ← map_sub]
    exact ((isUnit_iff_ne_zero.2 (sub_ne_zero.2 ha)).map io).map _
  · intro ℓ a
    have h := Transfer.eig_map (k := F) C.ch.B a _ _
      (eigDirSt E H Dw l Xo c T io y C a ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩)
    have e : (fun i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩ i)) =
        fun i => algebraMap T.V F (C.uvecT ⟨ℓ.1, Fin.castLE (hrk ℓ.1) ℓ.2⟩ i) := funext fun i => huv _ i
    exact e ▸ h

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartColumnsToTupleHarmonicValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralChart_columns_to_tuple_harmonicValues : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (tors : P.TorsionIso) (ϖ : T.V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v), letI := io.toAlgebra; ∃ x hx j hj u hu B hB ρ hρ, B.G.F = C.FT ∧ B.A.act = C.actT ∧ ∀ (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (s : Fin n → Fam P.D.toPre F g') (s' t : Fin n → Fam P.D.toPre F (g' * g)) (f : Fin n → PS F 1 (chD C.ch)), (∀ b, NuGe P.D Q F v g' (s b) 0 ∧ PullAl P.D F P.oD (star π) g' g (s b) (s' b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Transl (g' * g) π (s' b) (t b) ∧ (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).Germ (g' * g) (t b) (f b)) → ∃ (S : Fam D'.toPre F g') (S₂ : Fam D'.toPre F (g' * g)) (p' : QkPt D'.toPre F (g' * g)) (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε (g' * g)))) (ζ' : F) (x' : TFK (R := T.V) F ⟶ A'.A) (T₀ T₁ : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) (un : PS T.V 1 (chD C.ch)), BoxTup C P Q F v g g' π pG PU oD' S S₂ p' w' ζ' x' T₀ T₁ σ' h ∧ MvPowerSeries.constantCoeff un = 1 ∧ h = boxSer (fun b => f b * MvPowerSeries.map (algebraMap T.V F) un) ∧ ∀ h₀ : PS F 2 (chD C.ch), B.IsCanonGauge F h₀ → ∀ (rk : (E →+* ℂ) → ℕ) (hrk : ∀ τ, rk τ ≤ Dw.mult τ) (Pp : MvPolynomial ((Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n) F), (∀ (τ : E →+* ℂ) (i : Fin (rk τ)) (i' : Fin (rk (ComplexEmbedding.conjugate τ))), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) (MvPolynomial.pderiv ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (rk τ)), b) Pp) = 0) → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.rename (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin n => (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw n)) Pp) = (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H T.V F).colVal h₀ (g' * g) (fun (l : Σ τ : E →+* ℂ, Fin (rk τ)) i => algebraMap T.V F (C.uvecT ⟨l.1, Fin.castLE (hrk l.1) l.2⟩ i)) Pp f := by
  first | exact @GlobalTheory.transfer_columns | exact GlobalTheory.transfer_columns | (intros; apply GlobalTheory.transfer_columns <;> assumption)
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem isAdicComplete_ov_of_range {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (O : Type) [CommRing O]
    [Algebra O F] (hinj : Function.Injective (algebraMap O F))
    (hr : ∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) (g : ℕ)
    (hc : IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O) :
    IsAdicComplete (Ideal.span {((g : ℕ) : TWO.Ov v)}) (TWO.Ov v) := by
  let φ : O →+* TWO.Ov v := (algebraMap O F).codRestrict (TWO.Ov v) fun a => (hr _).2 ⟨a, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun z => ?_⟩
    obtain ⟨a, ha⟩ := (hr z).1 z.2
    exact ⟨a, Subtype.ext ha⟩
  have h := (IsAdicComplete.congr_ringEquiv (Ideal.span {((g : ℕ) : O)}) (RingEquiv.ofBijective φ hφ)).2 hc
  rwa [Ideal.map_span, Set.image_singleton, map_natCast] at h

theorem isUnit_iff_not_isUnit_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {x y u u' : R}
    (h : ¬ IsUnit (x * y)) (h1 : u * x + u' * y = 1) : IsUnit x ↔ ¬ IsUnit y := by
  refine ⟨fun hx hy => h (hx.mul hy), fun hy => ?_⟩
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h2 | h2
  · exact isUnit_of_mul_isUnit_right h2
  · exact absurd (isUnit_of_mul_isUnit_right h2) hy

theorem card_filter_val_lt (n₁ n₂ : ℕ) :
    (Finset.univ.filter fun b : Fin (n₁ + n₂) => b.val < n₁).card = n₁ := by
  rw [Fin.card_filter_val_lt]; omega

theorem lemmaBT_of_characters : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → LemmaBT := by
  intro L1 L2 L4 TB hch E _ _ _ H Dw l Xo c inst hst
  obtain rfl := starSt E H inst hst
  letI := H.starRing
  intro T io y hy C hfr P tors ϖ hϖ Q hQ g g' hg hg' hne og og' π π' hπ hπ' hcop hcop' hcard hnd hnu F _ _ _ _ _ _ v hv
    O _ _ _ _ hinj hO hOc I Φ M0 r b hΦ hb1 hb2 n₁ n₂ hn D' A' G' _ _ pD pA pG U' PU _ oD' hx1 hx2 m hm hd1 hd2 hd3 ρg hρg
  letI := io.toAlgebra
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  obtain ⟨σ, e, hσ, he1, -, heig, hval, hconj, ⟨lam, hlam⟩, hε, hgu⟩ :=
    GlobalTheory.T.exists_integral_types_and_directions' E H Dw l Xo c T io y C ϖ hϖ g hg hnu hcard hnd F v hv
  obtain ⟨x, hx, j, hj, u, hu, B, hB, ρ, hρ, -, hact, htr⟩ :=
    GlobalTheory.T.integralChart_columns_to_tuple_harmonicValues L1 L2 L4 TB E H Dw l Xo c T io y C hfr P tors ϖ hϖ Q hQ F v hv
  obtain ⟨BT, -, hBT, -, -, -, -, hBF⟩ := integralChart_formalBiext E H Dw l Xo c T io y C
  have hdA : ∀ a, dAct F B a = dAct F C.ch.B a := by
    intro a
    have h1 : B.actK F a = C.ch.B.actK F a := by
      rw [← (hBF F).2.1 a]
      unfold FB.actK
      rw [hact, hBT]
    unfold dAct
    rw [h1]
  obtain ⟨rk, hrk, col, m', hcol, hty, hdeg, hmin⟩ :=
    minorSt E H Dw F (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₁ n₂ (by convert hm)
  obtain ⟨h₀, hh₀⟩ := canonGauge_exists T.V (chD C.ch) (𝓞 E) F B
  have hππ : star π * star (star π) = (g : 𝓞 E) := by rw [star_star, mul_comm, hπ]
  obtain ⟨u₁, u₂, hu12⟩ := hcop
  have hg'0 : (0 : ℝ) < g' := by exact_mod_cast hg'.pos
  have hred : (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ :
      FamGerm.Pt1 E H T.V F).Red r b Φ (max M0 0) := by
    refine ⟨hΦ, le_max_right _ _, hb1, fun i z => ?_⟩
    have h1 := hb2 i z
    have h2 : (0 : ℝ) ≤ Q z := by
      by_cases hz : z = 0
      · rw [hz, Q_zero hϖ P.D hQ, Int.cast_zero]
      · have h3 := Q_pos hϖ P.D hQ hz
        exact_mod_cast (by omega : 0 ≤ Q z)
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h2)
  obtain ⟨s, s', t, f, gm, hs, hgm, hle⟩ := GlobalTheory.T.depth_bound_from_characters_pointDatum L1 L2 L4 TB hch g E H T.V F
    (FamGerm.Pt1.mk ϖ hϖ T.cpl C.I.G P tors Q hQ v hv (chD C.ch) x hx j hj u hu B hB ρ hρ)
    (isAdicComplete_ov_of_range v O hinj hO g hOc) hgu Dw I r b Φ (max M0 0) hred (star π) g' hππ
    ⟨u₂, u₁, by rw [star_star, add_comm, hu12]⟩ ((Nat.coprime_primes hg hg').2 hne) (E →+* ℂ) rk σ
    (fun l => e ⟨l.1, Fin.castLE (hrk l.1) l.2⟩)
    (fun a l => by rw [show dAct F _ a = dAct F C.ch.B a from hdA a]; exact heig a _)
    (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))))
    (fun τ h => (hval τ _).1 (by rw [hσ]; exact h)) (fun τ h => (hval τ _).2 (by rw [hσ]; exact h))
    ⟨fun l => lam ⟨l.1, Fin.castLE (hrk l.1) l.2⟩, fun l l' => by
      refine (hlam _ _).trans (if_congr ?_ rfl rfl)
      obtain ⟨τ, i⟩ := l
      obtain ⟨τ', i'⟩ := l'
      constructor
      · intro h
        obtain rfl : τ = τ' := congrArg Sigma.fst h
        have h2 := eq_of_heq (Sigma.mk.inj h).2
        obtain rfl : i = i' := Fin.castLE_injective _ h2
        rfl
      · intro h
        rw [h]⟩
    (by convert hε) (n₁ + n₂) (Finset.univ.filter fun b => b.val < n₁) col m' hcol
    (fun τ i => by rw [Finset.mem_filter, ← hty τ i]; simp) (degOf Dw m) hdeg.symm hd1 hd2
    (by
      rcases le_total M0 0 with h | h
      · rw [max_eq_right h, mul_zero]; exact hg'0
      · rw [max_eq_left h]; exact hd3)
    h₀ hh₀ ρg hρg
  simp only [star_star] at hs
  obtain ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, un, hbox, -, -, hvl⟩ :=
    htr g g' π hg.one_le hg'.one_le hπ (n₁ + n₂) D' A' G' pD pA pG U' PU oD' hx1 hx2 s s' t f hs
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hbox
  refine ⟨S, S₂, p', w', ζ', x', T₀, T₁, σ', h, gm, b1, b2, b3, b4, b5, b6, b7, b8, b9, ?_, ?_⟩
  · rw [hmin, hvl h₀ hh₀ rk hrk (FamGerm.minorsP F col m') ?_, ← hgm]
    · simp only [he1]
    · intro τ
      refine minors_disjoint_columns_harmonic F _ rk _ col m' _ rfl τ _ fun i i' hii => ?_
      have k1 := hty τ i
      have k2 := hty _ i'
      rw [hii, k2, ← hσ, ← hσ, hconj, star_star] at k1
      have k3 : ∀ a, 0 < v (σ τ a : F) ↔ ¬ IsUnit (σ τ a) := fun a =>
        ⟨fun h hu => hgu (isUnit_of_dvd_unit (Ideal.mem_span_singleton.1 ((hval τ a).1 h)) hu),
          fun h => by_contra fun h' => h ((hval τ a).2 h')⟩
      rw [k3, k3] at k1
      have k4 : IsUnit (σ τ π) ↔ ¬ IsUnit (σ τ (star π)) :=
        isUnit_iff_not_isUnit_of_coprime (u := σ τ u₁) (u' := σ τ u₂) (by rw [← map_mul, hπ, map_natCast]; exact hgu)
          (by rw [← map_mul, ← map_mul, ← map_add (f := _), hu12, map_one])
      tauto
  · rw [card_filter_val_lt] at hle
    have h1 : (0 : ℝ) ≤ (degOf Dw m : ℝ) ^ 2 * Φ / g' := by positivity
    have h2 : 2 * (degOf Dw m : ℝ) ^ 2 * Φ / g' = 2 * ((degOf Dw m : ℝ) ^ 2 * Φ / g') := by ring
    rw [h2, mul_comm (ρg : ℝ)]
    linarith

end GlobalTheory.PowGerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBelowOneOfHodgeTateChartForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowGerm

theorem lemmaBT_of_hodgeTate_chart : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → LemmaBT := fun h =>
  lemmaBT_of_characters GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 GlobalTheory.firstFiveLaws.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.1 (GlobalTheory.T.exists_characters_boundedMinors_of_hodgeTateChartBound h)

end GlobalTheory.PowGerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBelowOneOfHodgeTateChartFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthBelowOne_of_hodgeTate_chart_form : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → LemmaBT := by
  first | exact @GlobalTheory.PowGerm.lemmaBT_of_hodgeTate_chart | exact GlobalTheory.PowGerm.lemmaBT_of_hodgeTate_chart | (intros; apply GlobalTheory.PowGerm.lemmaBT_of_hodgeTate_chart <;> assumption)
end
