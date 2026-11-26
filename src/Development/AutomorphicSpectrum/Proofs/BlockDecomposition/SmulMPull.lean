module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ExistsDpPow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDifferentialOneInclusion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TerminalRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.LmLeStd
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ThickeningIdealNilpotent
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.GDSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Diso

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]

structure OL : Prop where
  tf : R.TF (S := O)
  unit : ∀ u : ℕ, ¬ l ∣ u → IsUnit (u : O)

variable {l O}

abbrev Om (l : ℕ) (O : Type) [CommRing O] (m : ℕ) : Type := O ⧸ Ideal.span {(l : O) ^ m}

abbrev Iom (l : ℕ) (O : Type) [CommRing O] (m : ℕ) : Ideal (Om l O m) := (Ideal.span {(l : O)}).map (Ideal.Quotient.mk _)

def pdm (h : OL l O) (m : ℕ) : DividedPowers (Iom l O m) := (exists_pd_l l h.unit h.tf m).choose

theorem isPdm (h : OL l O) (m : ℕ) : R.IsPd (Ideal.Quotient.mk _) (Ideal.span {(l : O)}) (pdm h m) :=
  (exists_pd_l l h.unit h.tf m).choose_spec

abbrev κm (l : ℕ) (O : Type) [CommRing O] (m : ℕ) : O →+* Om l O m ⧸ Iom l O m :=
  (Ideal.Quotient.mk _).comp (Ideal.Quotient.mk _)

abbrev Lm (h : OL l O) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) : (nlBase (Om l O m) (Iom l O m) (pdm h m) l).Fun :=
  nlFun (pdm h m) l X q (κm l O m)

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

abbrev lm (T : Thick (smFun X q)) (m : ℕ) : Ideal T.B := Ideal.span {(l : T.B) ^ m}

abbrev GI (T : Thick (smFun X q)) : Ideal T.B := T.J ⊔ Ideal.span {(l : T.B)}

abbrev GB (T : Thick (smFun X q)) (m : ℕ) : Type := T.B ⧸ lm (l := l) T m

abbrev GJ (T : Thick (smFun X q)) (m : ℕ) : Ideal (GB (l := l) T m) := (GI (l := l) T).map (Ideal.Quotient.mk _)

theorem lm_le (T : Thick (smFun X q)) (m : ℕ) : Ideal.span {(l : O) ^ m} ≤ (lm (l := l) T m).comap T.i := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change T.i ((l : O) ^ m) ∈ lm (l := l) T m
  rw [map_pow, map_natCast]
  exact Ideal.mem_span_singleton_self _

def iG (T : Thick (smFun X q)) (m : ℕ) : Om l O m →+* GB (l := l) T m := Ideal.quotientMap _ T.i (lm_le T m)

def thG (T : Thick (smFun X q)) (m : ℕ) : T.B ⧸ T.J →+* GB (l := l) T m ⧸ GJ (l := l) T m :=
  Ideal.quotientMap _ (Ideal.Quotient.mk _) fun _ hx => Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hx)

def Good (T : Thick (smFun X q)) (m : ℕ) : Prop :=
  R.TF (S := T.B) ∧ R.PdI (GI (l := l) T) ∧
    ∀ x ∈ GI (l := l) T, x ∈ lm (l := l) T m → ∀ j : ℕ, j ≠ 0 → ∀ y : T.B, (j.factorial : T.B) * y = x ^ j → y ∈ lm (l := l) T m

def GD (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) : DividedPowers (GJ (l := l) T m) :=
  (RL.pd_quot hT.1 (GI (l := l) T) (lm (l := l) T m) hT.2.1 hT.2.2).choose

theorem GD_spec (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) :
    R.IsPd (Ideal.Quotient.mk (lm (l := l) T m)) (GI (l := l) T) (GD T m hT) :=
  (RL.pd_quot hT.1 (GI (l := l) T) (lm (l := l) T m) hT.2.1 hT.2.2).choose_spec

end CrystallineSemistableComparison.Pb.Diso
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Diso

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem l_mem_GI (T : Thick (smFun X q)) : ∀ x ∈ Ideal.span {(l : O)}, T.i x ∈ GI (l := l) T := by
  intro x hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, map_natCast]
  exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem Iom_le (T : Thick (smFun X q)) (m : ℕ) : Iom l O m ≤ (GJ (l := l) T m).comap (iG T m) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  exact Ideal.mem_map_of_mem _ (l_mem_GI T x hx)

def psG (T : Thick (smFun X q)) (m : ℕ) : Om l O m ⧸ Iom l O m →+* GB (l := l) T m ⧸ GJ (l := l) T m :=
  Ideal.quotientMap _ (iG T m) (Iom_le T m)

theorem ptCond (T : Thick (smFun X q)) (m : ℕ) :
    (Spec.map (CommRingCat.ofHom (thG (l := l) T m)) ≫ pt T) ≫ q =
      Spec.map (CommRingCat.ofHom ((psG T m).comp (κm l O m))) := by
  rw [Category.assoc]
  have h2 : pt T ≫ q = Spec.map (CommRingCat.ofHom (T.y.1.1.comp (Ideal.Quotient.mk ⊥))) := T.y.2
  rw [h2, ← Spec.map_comp]
  congr 1
  ext a
  change thG (l := l) T m (T.y.1.1 (Ideal.Quotient.mk ⊥ a)) = psG T m (κm l O m a)
  rw [show T.y.1.1 (Ideal.Quotient.mk ⊥ a) = Ideal.Quotient.mk T.J (T.i a) from T.w a]
  rfl

def ptG (T : Thick (smFun X q)) (m : ℕ) (h : OL l O) :
    (Lm h q m).Pt.obj (CommRingCat.of (GB (l := l) T m ⧸ GJ (l := l) T m)) :=
  ⟨(psG T m, Spec.map (CommRingCat.ofHom (thG (l := l) T m)) ≫ pt T), ptCond T m⟩

theorem thickening_ideal_nilpotent (T : Thick (smFun X q)) (m : ℕ) :
    (l ≠ 0 → IsNilpotent ((l : ℕ) : GB (l := l) T m)) ∧ (l = 0 → IsNilpotent (GJ (l := l) T m)) := by
  refine ⟨fun _ => ⟨m, ?_⟩, fun h => absurd h (Fact.out : l.Prime).ne_zero⟩
  rw [← map_natCast (Ideal.Quotient.mk (lm (l := l) T m)), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

theorem dp_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) :
    IsDPMorphism (pdm h m) (GD T m hT) (iG T m) :=
  RL.pd_mor (Ideal.Quotient.mk _) (Ideal.Quotient.mk _) (Ideal.span {(l : O)}) (GI (l := l) T) (pdm h m) (GD T m hT) T.i
    (iG T m) Ideal.Quotient.mk_surjective (pdI_l l h.unit) (isPdm h m) (GD_spec T m hT) (l_mem_GI T) (fun _ => rfl)

def GObj (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) : Thick (Lm h q m) :=
  mkT (GB (l := l) T m) (iG T m) (GJ (l := l) T m) (GD T m hT) (thickening_ideal_nilpotent T m) (dp_G h T m hT) (ptG T m h) (fun _ => rfl)

theorem lm_map {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) : lm (l := l) T m ≤ (lm (l := l) T' m).comap φ.φ := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change φ.φ ((l : T.B) ^ m) ∈ lm (l := l) T' m
  rw [map_pow, map_natCast]
  exact Ideal.mem_span_singleton_self _

def gφ {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) : GB (l := l) T m →+* GB (l := l) T' m :=
  Ideal.quotientMap _ φ.φ (lm_map φ m)

theorem GI_map {T T' : Thick (smFun X q)} (φ : T ⟶ T') : ∀ x ∈ GI (l := l) T, φ.φ x ∈ GI (l := l) T' := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  refine add_mem (Ideal.mem_sup_left (φ.hle hy)) (Ideal.mem_sup_right ?_)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem dp_gφ {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) (hT : Good (l := l) T m) (hT' : Good (l := l) T' m) :
    IsDPMorphism (GD T m hT) (GD T' m hT') (gφ φ m) :=
  RL.pd_mor (Ideal.Quotient.mk _) (Ideal.Quotient.mk _) (GI (l := l) T) (GI (l := l) T') (GD T m hT) (GD T' m hT') φ.φ
    (gφ φ m) Ideal.Quotient.mk_surjective hT.2.1 (GD_spec T m hT) (GD_spec T' m hT') (GI_map φ) (fun _ => rfl)

theorem GJ_le {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) : GJ (l := l) T m ≤ (GJ (l := l) T' m).comap (gφ φ m) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro x hx
  exact Ideal.mem_map_of_mem _ (GI_map φ x hx)

theorem ptG_map (h : OL l O) {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) :
    (Lm h q m).Pt.map (CommRingCat.ofHom (Ideal.quotientMap (GJ (l := l) T' m) (gφ φ m) (GJ_le φ m))) (ptG T m h) =
      ptG T' m h := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change (Ideal.quotientMap (GJ (l := l) T' m) (gφ φ m) (GJ_le φ m)).comp (psG T m) = psG T' m
    refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_))
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (φ.φ (T.i a))) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (T'.i a))
    rw [φ.comm]
  · change Spec.map (CommRingCat.ofHom (Ideal.quotientMap (GJ (l := l) T' m) (gφ φ m) (GJ_le φ m))) ≫
        (Spec.map (CommRingCat.ofHom (thG (l := l) T m)) ≫ pt T) = Spec.map (CommRingCat.ofHom (thG (l := l) T' m)) ≫ pt T'
    rw [Site.pt_hom φ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext x
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (φ.φ x)) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (φ.φ x))
    rfl

def GMap (h : OL l O) {T T' : Thick (smFun X q)} (φ : T ⟶ T') (m : ℕ) (hT : Good (l := l) T m) (hT' : Good (l := l) T' m) :
    GObj h T m hT ⟶ GObj h T' m hT' :=
  mkH (gφ φ m) (fun r => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk _ (φ.φ (T.i a)) = Ideal.Quotient.mk _ (T'.i a)
      rw [φ.comm]) (dp_gφ φ m hT hT') (GJ_le φ m) (ptG_map h φ m)

def GF (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m) :
    Q.FullSubcategory ⥤ Thick (Lm h q m) where
  obj T := GObj h T.obj m (hQ _ T.property)
  map φ := GMap h φ.hom m _ _
  map_id T := by
    refine CrystallineSemistableComparison.Pb.hom_ext ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    rfl
  map_comp φ ψ := by
    refine CrystallineSemistableComparison.Pb.hom_ext ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    rfl

end CrystallineSemistableComparison.Pb.Diso
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Diso

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}}

abbrev OMm (h : OL l O) (q : X ⟶ Spec (CommRingCat.of O)) (m : ℕ) : Thick (Lm h q m) ⥤ ModuleCat.{0} O :=
  B.OM (Lm h q m) (Ideal.Quotient.mk _)

variable {q : X ⟶ Spec (CommRingCat.of O)}

theorem lm_le_std (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (T : Q.FullSubcategory) :
    lm (l := l) T.obj m ≤ (stdI Q none ((l : O) ^ m)).S T := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  refine Ideal.mem_sup_right (Ideal.subset_span ?_)
  change (l : T.obj.B) ^ m = T.obj.i ((l : O) ^ m)
  rw [map_pow, map_natCast]

def gMor (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m) :
    CH.Mor (OMm h q m) (sq (IdF.top (sP Q).A) (stdI Q none ((l : O) ^ m))) (RingHom.id O) where
  G := GF h Q m hQ
  τ T :=
    { toFun := fun x => ⟨Ideal.Quotient.factor (lm_le_std Q m T) (show GB (l := l) T.obj m from x), by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
        rw [← hy]
        exact Ideal.mem_map_of_mem _ trivial⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (by
        obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
        change Ideal.Quotient.factor (lm_le_std Q m T) (Ideal.Quotient.mk _ (T.obj.i c) * show GB (l := l) T.obj m from x) =
          Ideal.Quotient.mk _ (T.obj.i c) * Ideal.Quotient.factor (lm_le_std Q m T) (show GB (l := l) T.obj m from x)
        rw [map_mul]
        rfl) }
  nat φ x := by
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) _ m from x)
    refine Subtype.ext ?_
    change Ideal.Quotient.factor (lm_le_std Q m _) (gφ φ.hom m (show GB (l := l) _ m from x)) = _
    rw [← hy]
    rfl

end CrystallineSemistableComparison.Pb.Diso
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ChartGrConst
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.DH

def LocCmpq : Prop := ∀ {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R C'}
    {c : IdF Φ'.A} (m : QMor Φ Φ' c) (Q : Poly Φ) (Q' : Poly Φ') {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d)
    (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e) (b : ℤ → IdF Φ'.A) (h : ∀ r T, c.S T ≤ (b r).S T) (r : ℤ)
    (hQ : Q.Crit (fun _ => IdF.bot _) 0) (hQ' : ∀ r' ≤ r, Q'.Crit b r'),
    (∀ r', r - d ≤ r' → r' ≤ r → Function.Bijective fun x : Φ.A.obj E.D => (m.o (b r') (h r')).τ E'.D ((Φ.A.map e).hom x)) →
    ∀ j, Function.Bijective ((m.o (b r) (h r)).pull j)

def Zar2 : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 : Set X.Opens) (Q' : ObjectProperty (Thick (nlFun γ p X q κ))) (h : St Q₀ 𝒱 ≤ Q') (h' : Q' ≤ St Q₀ {sSup 𝒱})
    (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T') (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j)

def PolyAll : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (h : Q₀ = ⊤ ∨ Q₀ = FlatT)
    (𝒱 : Set X.Opens), ∃ Q : Poly (sP (St Q₀ 𝒱)), ∀ r : ℤ, Q.Crit (sFil _) r ∧ Q.Crit (fun _ => IdF.bot _) r ∧
      ∀ c : R, Q.Crit (fun r => stdI _ (some r) c) r ∧ Q.Crit (fun _ => stdI _ none c) r ∧ Q.Crit (fun _ => IdF.span _ c) r

def ChartAlg : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ)
    (hb : TFBase γ l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)
    (hκ : ∀ a, κ a = Ideal.Quotient.mk I (algebraMap O R a)) {V : X.Opens} {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∃ (c' : Chart γ 0 q κ V d) (e : R ⊗[O] Γ(X, V) ≃+* c'.D.B), TF l s c'.D ∧ (∀ r, e (r ⊗ₜ 1) = c'.D.i r) ∧
      (∀ i, e (1 ⊗ₜ c.t i) = c'.t i) ∧ ∀ f, ev c'.D c'.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))

def ChartGood : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d), c.Good

def ChartGrConst : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q)

def IsFilS : Prop := ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q)

def ChartP : Prop := ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i)

end CrystallineSemistableComparison.Pb.DH
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso

noncomputable section

namespace GlobalTheory.CompanionTheory.DisoHm

section Lift
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'}

def liftM (m : CH.Mor F F' σ) {P : ObjectProperty C} (hP : ∀ T, P (m.G.obj T)) : CH.Mor (P.ι ⋙ F) F' σ where
  G := P.lift m.G hP
  τ := m.τ
  nat φ x := m.nat φ x
end Lift

section Scal
variable {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def thPc : PDF Λ (Thick L) where
  A := B.OA L c
  J := ⟨fun T => T.J, fun φ _ hx => φ.hle hx⟩
  dp {T} k x := T.δ.dpow k x
  dp_zero {T} _ hx := T.δ.dpow_zero hx
  dp_one {T} _ hx := T.δ.dpow_one hx
  dp_zero_right {T} _ hk := T.δ.dpow_eval_zero hk
  dp_add {T} k _ _ hx hy := T.δ.dpow_add hx hy
  dp_map φ k x hx := (φ.dp.2 x hx).symm

variable {L}

abbrev sPc (Q : ObjectProperty (Thick L)) : PDF Λ Q.FullSubcategory := (thPc L c).res Q.ι

def polyC {Q : ObjectProperty (Thick L)} (P : Poly (sP Q)) : Poly (sPc c Q) where
  P := P.P
  j := P.j
  X := P.X
  X_mem := P.X_mem
  univ := P.univ
  span := P.span

def frameC {Q : ObjectProperty (Thick L)} {d : ℕ} (E : Frame (sP Q) d) : Frame (sPc c Q) d where
  D := E.D
  ne := E.ne
  τ := E.τ
  mem := E.mem
  add := E.add
  nat := E.nat
  bij := E.bij

theorem polyC_crit {Q : ObjectProperty (Thick L)} (P : Poly (sP Q)) (r : ℤ)
    (h : P.Crit (fun _ => IdF.bot _) r) : (polyC c P).Crit (fun _ => IdF.bot _) r := h

end Scal

section G
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lm_eq_span (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (T : Q.FullSubcategory) :
    lm (l := l) T.obj m = (IdF.span (sP Q).A ((l : O) ^ m)).S T := by
  change Ideal.span {(l : T.obj.B) ^ m} = Ideal.span {T.obj.i ((l : O) ^ m)}
  rw [map_pow, map_natCast]

def gρ (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (T : Q.FullSubcategory) :
    (sPc (Ideal.Quotient.mk _) P).A.obj ((P.lift (GF h Q m hQ) hP).obj T) →ₐ[O]
      (sP Q).A.obj T ⧸ (IdF.span (sP Q).A ((l : O) ^ m)).S T :=
  { Ideal.Quotient.factor (lm_eq_span Q m T).le with
    commutes' := fun a => rfl }

theorem gρ_inj (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (T : Q.FullSubcategory) :
    Function.Injective (gρ h Q m hQ P hP T) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
  have e : Ideal.Quotient.mk ((IdF.span (sP Q).A ((l : O) ^ m)).S T) (show T.obj.B from a) = Ideal.Quotient.mk _ (show T.obj.B from b) := hxy
  exact Ideal.Quotient.eq.2 ((lm_eq_span Q m T).ge (Ideal.Quotient.eq.1 e))

def gQ (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) :
    QMor (sPc (Ideal.Quotient.mk _) P) (sP Q) (IdF.span (sP Q).A ((l : O) ^ m)) where
  G := P.lift (GF h Q m hQ) hP
  ρ := gρ h Q m hQ P hP
  inj := gρ_inj h Q m hQ P hP
  nat {T T'} φ x y hxy := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from x)
    have e : Ideal.Quotient.mk ((IdF.span (sP Q).A ((l : O) ^ m)).S T) (show T.obj.B from a) = Ideal.Quotient.mk _ y := hxy
    have e' := (IdF.span (sP Q).A ((l : O) ^ m)).map_mem φ (Ideal.Quotient.eq.1 e)
    rw [map_sub] at e'
    exact Ideal.Quotient.eq.2 e'
  dp T k x y hx hy hxy := by
    have hT := hQ _ T.property
    have e : x = Ideal.Quotient.mk (lm (l := l) T.obj m) (show T.obj.B from y) := gρ_inj h Q m hQ P hP T hxy
    subst e
    have hy' : (show T.obj.B from y) ∈ T.obj.J := hy
    have := (GD_spec T.obj m hT).2 k (show T.obj.B from y) (T.obj.δ.dpow k y) (Ideal.mem_sup_left hy')
      (T.obj.δ.factorial_mul_dpow_eq_pow hy')
    exact congrArg (gρ h Q m hQ P hP T) this

def gP (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) :
    CH.Mor (P.ι ⋙ OMm h q m) (sq (IdF.top (sP Q).A) (stdI Q none ((l : O) ^ m))) (RingHom.id O) :=
  liftM (gMor h Q m hQ) hP

end G

section Gen
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem IdF.ext' {a b : IdF A} (h : ∀ T, a.S T = b.S T) : a = b := by
  cases a
  cases b
  congr
  exact funext h

theorem idM_bij {R' : Type} [CommRing R'] {σ : R →+* R'} {F : C ⥤ ModuleCat.{0} R} {F' : C ⥤ ModuleCat.{0} R'}
    (τ : ∀ T, F.obj T →ₛₗ[σ] F'.obj T)
    (nat : ∀ {T T' : C} (φ : T ⟶ T') (x : F.obj T), τ T' ((F.map φ).hom x) = (F'.map φ).hom (τ T x))
    (h : ∀ T, Function.Bijective (τ T)) (j : ℕ) :
    Function.Bijective ((⟨𝟭 C, τ, nat⟩ : CH.Mor F F' σ).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij _ (fun n => ⟨fun x y hxy => ?_, fun y => ?_⟩) j
  · funext s
    refine (h _).1 ?_
    have := congrFun hxy s
    exact this
  · exact ⟨fun s => Function.surjInv (h _).2 (y s), funext fun s => Function.surjInv_eq (h _).2 (y s)⟩

theorem sqLe_bij {a b a' b' : IdF A} (ha : ∀ T, a.S T = a'.S T) (hb : ∀ T, b.S T = b'.S T) (j : ℕ) :
    Function.Bijective ((sqLe (a := a) (b := b) (a' := a') (b' := b') (fun T => (ha T).le) (fun T => (hb T).le)).pull j) := by
  obtain rfl : a = a' := IdF.ext' ha
  obtain rfl : b = b' := IdF.ext' hb
  refine idM_bij (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ
    (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).nat (fun T => ?_) j
  have e : (sqLe (a := a) (b := b) (a' := a) (b' := b) (fun T => le_rfl) (fun T => le_rfl)).τ T = LinearMap.id := by
    ext ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [e]
  exact Function.bijective_id
end Gen

section Lk
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem gQ_o (h : OL l O) (Q : ObjectProperty (Thick (smFun X q))) (m : ℕ) (hQ : ∀ T, Q T → Good (l := l) T m)
    (P : ObjectProperty (Thick (Lm h q m))) (hP : ∀ T, P ((GF h Q m hQ).obj T)) (b : IdF (sP Q).A)
    (hb : ∀ T, (IdF.span (sP Q).A ((l : O) ^ m)).S T ≤ b.S T)
    (hb' : ∀ T, (stdI Q none ((l : O) ^ m)).S T ≤ b.S T) (j : ℕ) (x : CH.H (P.ι ⋙ OMm h q m) j) :
    ((gQ h Q m hQ P hP).o b hb).pull j x =
      (sqLe (a := IdF.top (sP Q).A) (a' := IdF.top (sP Q).A) (fun _ => le_rfl) hb').pull j ((gP h Q m hQ P hP).pull j x) := by
  refine (CrystallineSemistableComparison.P.prism (σ := RingHom.id O) ((gQ h Q m hQ P hP).o b hb)
    ((gP h Q m hQ P hP).comp (sqLe (a := IdF.top (sP Q).A) (a' := IdF.top (sP Q).A) (fun _ => le_rfl) hb')) (𝟙 _)
    (fun T y => ?_) j x).trans ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id O) _ _ j x).1)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show GB (l := l) T.obj m from y)
  rfl

end Lk
end GlobalTheory.CompanionTheory.DisoHm

namespace GlobalTheory.CompanionTheory.DisoHm
section Cover
variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R}

def smulM (m : CH.Mor F F' (RingHom.id R)) (n : R) : CH.Mor F F' (RingHom.id R) where
  G := m.G
  τ T := n • m.τ T
  nat φ x := by
    change n • m.τ _ _ = (F'.map φ).hom (n • m.τ _ x)
    rw [m.nat, map_smul]

theorem smulM_pull (m : CH.Mor F F' (RingHom.id R)) (n : R) (j : ℕ) (x : CH.H F j) :
    (smulM m n).pull j x = n • m.pull j x := by
  obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
  rfl

theorem tens_iff {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') :
    Tens R (N := fun _ : Unit => R) (M := fun _ => M) (M' := M') (fun _ n x => n • f x) ↔ Function.Bijective f := by
  let e : (∀ _ : Unit, R ⊗[R] M) ≃+ M :=
    (AddEquiv.piUnique (fun _ : Unit => R ⊗[R] M)).trans (TensorProduct.lid R M).toAddEquiv
  have he : ∀ n x, e (Pi.single () (n ⊗ₜ x)) = n • x := fun n x => by simp [e]
  constructor
  · rintro ⟨g, hg⟩
    have : ∀ x, f x = g (e.symm x) := fun x => by
      have h2 : g (Pi.single () ((1 : R) ⊗ₜ x)) = f x := (hg () 1 x).trans (one_smul _ _)
      have h3 : e.symm x = Pi.single () ((1 : R) ⊗ₜ x) := by
        refine (AddEquiv.symm_apply_eq e).2 ?_
        rw [he, one_smul]
      rw [h3, h2]
    have e2 : (f : M → M') = (e.symm.trans g) := funext this
    rw [e2]
    exact (e.symm.trans g).bijective
  · intro hf
    refine ⟨e.trans (AddEquiv.ofBijective f.toAddMonoidHom hf), fun _ n x => ?_⟩
    change f (e _) = _
    rw [he, map_smul]

theorem cover_bij (m : CH.Mor F F' (RingHom.id R)) {A : Type} [Fintype A] (U : A → ObjectProperty C)
    (U' : A → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hU' : ∀ α, Cosieve (U' α)) (hc : ∀ T, ∃ α, U α T)
    (hc' : ∀ T, ∃ α, U' α T) (h : ∀ α T, U' α T → U α (m.G.obj T))
    (H : ∀ S : Finset A, S.Nonempty → ∀ j, Function.Bijective
      ((morU m (U := capS U S) (U' := capS U' S) fun T hT α hα => h α T (hT α hα)).pull j)) (j : ℕ) :
    Function.Bijective (m.pull j) := by
  have key := GlobalTheory.CompanionTheory.CosieveBC.base_change_of_cover (σ := RingHom.id R) m.G (ι := Unit) (fun _ => R) (fun _ => F) F'
    (fun _ n T => (smulM m n).τ T) (fun _ n _ _ φ x => (smulM m n).nat φ x)
    (fun _ n n' T x => by simp [smulM, add_smul]) (fun _ r n T x => by simp [smulM, mul_smul])
    U U' hU hU' hc hc' h (fun S hS j => ?_) j
  · obtain ⟨g, hg⟩ := key
    exact (tens_iff (m.pull j)).1 ⟨g, fun i n x => (hg i n x).trans (smulM_pull m n j x)⟩
  · obtain ⟨g, hg⟩ := (tens_iff ((morU m (U := capS U S) (U' := capS U' S) fun T hT α hα => h α T (hT α hα)).pull j)).2 (H S hS j)
    refine ⟨g, fun i n x => (hg i n x).trans ?_⟩
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
end Cover
end GlobalTheory.CompanionTheory.DisoHm

namespace GlobalTheory.CompanionTheory.DisoHm
section Ch
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem pt_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) :
    pt (GObj h T m hT) = Spec.map (CommRingCat.ofHom (thG (l := l) T m)) ≫ pt T := rfl

theorem inU_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) {V : X.Opens} (hV : InU V T) :
    InU V (GObj h T m hT) := by
  unfold InU
  rw [pt_G]
  intro x _
  exact hV (show (Spec.map (CommRingCat.ofHom (thG (l := l) T m))) x ∈ ⊤ from trivial)

theorem ev_G (h : OL l O) (T : Thick (smFun X q)) (m : ℕ) (hT : Good (l := l) T m) {V : X.Opens} (hV : InU V T)
    (hV' : InU V (GObj h T m hT)) (f : Γ(X, V)) :
    ev (GObj h T m hT) hV' f = thG (l := l) T m (ev T hV f) :=
  GlobalTheory.LogCris.evalAt_map _ (pt T) hV hV' f

theorem ev_hom {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {κ : O →+* R ⧸ I} {V : X.Opens}
    {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : InU V T) (h' : InU V T') (f : Γ(X, V)) :
    ev T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X)
      (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ V), GlobalTheory.Cris.evalAt y V hh f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
    intro y hy hh
    subst hy
    exact GlobalTheory.LogCris.evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) h hh f
  exact key _ (Site.pt_hom φ) h'

theorem exists_sig (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hg : cL.Good)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d)
    (ht : ∀ i, ev cO.D cO.inV (c.t i) = Ideal.Quotient.mk _ (cO.t i))
    (hT : Good (l := l) cO.D m) :
    ∃ σ : cL.D ⟶ GObj h cO.D m hT, ∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i) := by
  have hV := inU_G h cO.D m hT cO.inV
  obtain ⟨σ₀⟩ := hg.1 _ hV
  have hy : ∀ i, ((show (GObj h cO.D m hT).B from Ideal.Quotient.mk (lm (l := l) cO.D m) (cO.t i)) - σ₀.φ (cL.t i)) ∈
      (GObj h cO.D m hT).J := by
    intro i
    refine Ideal.Quotient.eq.1 ?_
    have a1 := ev_G h cO.D m hT cO.inV hV (c.t i)
    have a2 := ev_hom σ₀ cL.inV hV (c.t i)
    rw [ht i] at a1
    rw [hcL i] at a2
    exact a1.symm.trans a2
  obtain ⟨σ, h1, -⟩ := hg.2 _ σ₀ _ hy
  exact ⟨σ, fun i => by simpa using h1 i⟩

end Ch
end GlobalTheory.CompanionTheory.DisoHm
