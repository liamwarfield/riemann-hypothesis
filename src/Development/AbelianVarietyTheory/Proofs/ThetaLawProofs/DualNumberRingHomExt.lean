module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem dualNumber_ringHom_ext {R S : Type} [CommRing R] [CommRing S] {F G : DualNumber R →+* S}
    (h : ∀ a, F (algebraMap R _ a) = G (algebraMap R _ a)) (he : F DualNumber.eps = G DualNumber.eps) : F = G := by
  refine RingHom.ext fun z => ?_
  have e : z = algebraMap R _ z.fst + algebraMap R _ z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add (f := _), map_add (f := _), map_mul, map_mul, h, h, he]

section Sec

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem appLE_eq_iff_stalk (w : LB.Iso L' (L.pull F)) (s : L.Sec) (s' : L'.Sec) :
    (∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ L.U (j PUnit.unit)),
      (F.appLE _ _ hle).hom (s.f (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i)) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun y hy => mem_pull.1 hy.1
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit _ y _ hy _).symm

end Sec

theorem keyPB_cancel : ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (x : KeyIn R) (x' : KeyIn R')
    (x'' : KeyIn R'') (f : R →+* R') (f' : R' →+* R''), KeyPB x' x f → KeyPB x'' x (f'.comp f) → KeyPB x'' x' f' := by
  intro R R' R'' _ _ _ x x' x'' f f' ⟨φ, he, w, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩
    ⟨φ'', he'', w'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', he', w', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyCancel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.EtBaseChange

section Val
variable {T T' : Type} [CommRing T] [CommRing T'] {X Y : Scheme.{0}}

def valH (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) : Γ(X, U) →+* T :=
  (w.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom).hom

theorem valT_eq (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) : valT w U a = valH w U h a :=
  dif_pos h

theorem valT_res (w : Sp T ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ w ⁻¹ᵁ V) (a : Γ(X, U)) :
    valT w V (resG X hle a) = valT w U a := by
  have h' : ⊤ ≤ w ⁻¹ᵁ U := fun p hp => hle (h hp)
  rw [valT_eq w V h, valT_eq w U h']
  have e := congrArg (fun q => q.hom a) (w.map_appLE h (homOfLE hle).op)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom e

theorem valT_appLE (w : Sp T ⟶ Y) (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hle : V ≤ φ ⁻¹ᵁ U) (h : ⊤ ≤ w ⁻¹ᵁ V)
    (a : Γ(X, U)) : valT w V ((φ.appLE U V hle).hom a) = valT (w ≫ φ) U a := by
  have h' : ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U := fun p hp => hle (h hp)
  rw [valT_eq w V h, valT_eq _ U h']
  have e := congrArg (fun q => q.hom a) (Scheme.Hom.appLE_comp_appLE w φ U V ⊤ hle h)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom e

theorem valT_spMap (F : T →+* T') (w : Sp T ⟶ X) {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) :
    valT (spMap F ≫ w) U a = F (valT w U a) := by
  have h' : ⊤ ≤ (spMap F ≫ w) ⁻¹ᵁ U := fun p _ => h (show spMap F p ∈ ⊤ from trivial)
  rw [valT_eq w U h, valT_eq _ U h']
  have e := congrArg (fun q => q.hom a) (Scheme.Hom.appLE_comp_appLE (spMap F) w U ⊤ ⊤ h (fun _ _ => trivial))
  have e2 := congrArg (fun q => q.hom ((w.appLE U ⊤ h).hom a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom F))
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of T')).hom.hom e).symm.trans (Eq.trans ?_ e2)
  have e3 : (spMap F).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap F).appTop := Scheme.Hom.appLE_eq_app _
  simp only [e3]
  rfl

theorem fst_surjective (R : Type) [CommRing R] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  intro p
  have hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have h : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker (TrivSqZeroExt.fstHom R R R).toRingHom : Set (DualNumber R)) := by
    intro a ha
    have ha' : a.fst = 0 := ha
    refine (PrimeSpectrum.isPrime p).mem_of_pow_mem 2 ?_
    have : a ^ 2 = 0 := by
      ext <;> simp [sq, ha']
    rw [this]; exact Ideal.zero_mem _
  rw [← range_comap_of_surjective _ _ hs] at h
  exact h

theorem snd_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h₂ : F DualNumber.eps = DualNumber.eps)
    (a : DualNumber R) : (F a).snd = f a.snd := by
  have : a = algebraMap R _ a.fst + algebraMap R _ a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [this, map_add (f := _), map_mul, h₁, h₁, h₂]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem snd_pow_mul {R : Type} [CommRing R] (a b : DualNumber R) (n : ℕ) (hb : b.fst = 0) :
    (a ^ n * b).snd = a.fst ^ n * b.snd := by
  simp [hb]

end Val

section Dual
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem fst_comp_translate (z : 𝟙_ (Over (Sp R)) ⟶ G) (v : epsR R ⟶ G) (hv : IsTangent v) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ((toUnit (epsR R) ≫ z) * v).left = z.left := by
  let r : 𝟙_ (Over (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    show spMap _ ≫ spMap _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1)
  have h1 : r ≫ v = 1 := by
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
    rw [e₁]
    exact Over.OverMorphism.ext hv
  have h2 : r ≫ toUnit (epsR R) ≫ z = z := by
    rw [← Category.assoc, toUnit_unique (r ≫ toUnit (epsR R)) (𝟙 _), Category.id_comp]
  have h3 : r ≫ ((toUnit (epsR R) ≫ z) * v) = z := by
    rw [MonObj.comp_mul, h1, h2, _root_.mul_one]
  exact congrArg CommaMorphism.left h3

theorem translate_le (z : 𝟙_ (Over (Sp R)) ⟶ G) (v : epsR R ⟶ G) (hv : IsTangent v) {U : G.left.Opens}
    (h : ⊤ ≤ z.left ⁻¹ᵁ U) : ⊤ ≤ ((toUnit (epsR R) ≫ z) * v).left ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := fst_surjective R p
  have := h (show q ∈ ⊤ from trivial)
  rw [← fst_comp_translate z v hv] at this
  exact this

theorem fst_valT_translate (z : 𝟙_ (Over (Sp R)) ⟶ G) (v : epsR R ⟶ G) (hv : IsTangent v) {U : G.left.Opens}
    (h : ⊤ ≤ z.left ⁻¹ᵁ U) (a : Γ(G.left, U)) :
    (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z) * v).left U a).fst = valT (T := R) z.left U a := by
  have := valT_spMap (TrivSqZeroExt.fstHom R R R).toRingHom ((toUnit (epsR R) ≫ z) * v).left
    (translate_le z v hv h) a
  rw [fst_comp_translate z v hv] at this
  exact this.symm

theorem translate_comp {R' : Type} [CommRing R'] {G' : Over (Sp R')} [GrpObj G'] {f : R →+* R'}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) (F : DualNumber R →+* DualNumber R')
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a))
    (z : 𝟙_ (Over (Sp R)) ⟶ G) (z' : 𝟙_ (Over (Sp R')) ⟶ G') (hz : z'.left ≫ φ = spMap f ≫ z.left)
    (v : epsR R ⟶ G) (v' : epsR R' ⟶ G') (hv : v'.left ≫ φ = spMap F ≫ v.left) :
    ((toUnit (epsR R') ≫ z') * v').left ≫ φ = spMap F ≫ ((toUnit (epsR R) ≫ z) * v).left := by
  have hd : spMap F ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
    have : F.comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := RingHom.ext h₁
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  let D : Over.mk ((epsR R').hom ≫ spMap f) ⟶ epsR R := Over.homMk (spMap F) hd
  have e : (D ≫ toUnit (epsR R) ≫ z).left = (toUnit (epsR R') ≫ z').left ≫ φ := by
    show spMap F ≫ (epsR R).hom ≫ z.left = ((epsR R').hom ≫ z'.left) ≫ φ
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ z.left) hd).trans ((Category.assoc _ _ _).trans
      ((congrArg ((epsR R').hom ≫ ·) hz.symm).trans (Category.assoc _ _ _).symm)))
  rw [← h.2 (epsR R') _ _ (D ≫ toUnit (epsR R) ≫ z) (D ≫ v) e hv.symm, ← MonObj.comp_mul]
  rfl

end Dual

section Via
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}

theorem le_inf_pull {T : Type} [CommRing T] (p : Sp T ⟶ x'.P.A.left) (c : x.P.L.ι) (c' : x'.P.L.ι)
    (h : ⊤ ≤ (p ≫ φ) ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ p ⁻¹ᵁ x'.P.L.U c') :
    ⊤ ≤ p ⁻¹ᵁ ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') :=
  fun _ hy => ⟨mem_pull.2 (h hy), h' hy⟩

theorem valT_via {T : Type} [CommRing T] {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s)
    (p : Sp T ⟶ x'.P.A.left) (c : x.P.L.ι) (c' : x'.P.L.ι)
    (h : ⊤ ≤ (p ≫ φ) ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ p ⁻¹ᵁ x'.P.L.U c') :
    valT (p ≫ φ) (x.P.L.U c) (s.f c) =
      valT p ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val ^ l *
        valT p (x'.P.L.U c') (s'.f c') := by
  have hle : (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' ≤ φ ⁻¹ᵁ x.P.L.U c := fun y hy => mem_pull.1 hy.1
  have hp := le_inf_pull p c c' h h'
  have e := congrArg (valT p ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c')) (hs (fun _ => c) c' hle)
  refine (valT_appLE p φ hle hp _).symm.trans (e.trans ?_)
  refine (valT_eq p _ hp _).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
  · exact (map_pow _ _ _).trans (congrArg (· ^ l) (valT_eq p _ hp _).symm)
  · exact (valT_eq p _ hp _).symm.trans (valT_res p _ hp _)

theorem mem_nonzeroLocus_via {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (hy : φ y ∈ Out.nonzeroLocus s) : y ∈ Out.nonzeroLocus s' := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨i, hi⟩ := exists_chart x'.P.isLB y
  have hle : (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have h1 : y ∈ x'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    have := Scheme.basicOpen_appLE φ _ (x.P.L.U k) hle (s.f k)
    refine this.ge ⟨⟨mem_pull.2 (x.P.A.left.basicOpen_le _ hk), hi⟩, hk⟩
  replace h1 := (Scheme.basicOpen_mul _ _ _).le ((congrArg x'.P.A.left.basicOpen e).le h1)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  exact ((Scheme.basicOpen_res _ _ _).le h1.2).2

end Via

end GlobalTheory.KeyKa.EtBaseChange

namespace GlobalTheory.KeyKa
open EtBaseChange

theorem etZ_baseChange : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → EtZ x s z ch → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → R'ˣ), EtZ x' s' z' ch' ∧ (∀ a, jac x' s' (z' a) (ch' a) * (u a : R') ^ (x.P.g * n) = f (jac x s (z a) (ch a))) ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := R') (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : R') ^ l = f (valT (T := R) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  intro R R' _ _ _ _ x x' f φ w n d hg s s' z ch ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ hs ⟨hz₁, hz₂, hz₃, hz₄, hz₅⟩
  have hw : ∀ a, (spMap f ≫ (z a).left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f := fun a =>
    (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w (z a))).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  let z' : Fin d → Pt x' := fun a => Over.homMk (hp.1.lift (spMap f ≫ (z a).left) (𝟙 _) (hw a)) (hp.1.lift_snd _ _ _)
  have hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left := fun a => hp.1.lift_fst _ _ _
  have hch : ∀ a, ∃ i, ⊤ ≤ (z' a).left ⁻¹ᵁ x'.P.L.U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB ((z' a).left (IsLocalRing.closedPoint R'))
    exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map (z' a).left.continuous).mem_open
      (x'.P.L.U i).isOpen hi⟩
  choose ch' hch' using hch
  have hφ : ∀ a, ⊤ ≤ ((z' a).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun a p _ => by
    rw [hz' a]
    exact hz₁ a (show spMap f p ∈ ⊤ from trivial)
  have hW := fun a => le_inf_pull (T := R') (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
  let u : Fin d → R'ˣ := fun a => Units.map (valH (T := R') (z' a).left _ (hW a)).toMonoidHom (w.s (fun _ => ch a, ch' a))
  have hu : ∀ a, valT (T := R') (z' a).left ((x.P.L.pull φ).U (fun _ => ch a) ⊓ x'.P.L.U (ch' a))
      (w.s (fun _ => ch a, ch' a)).val = u a := fun a => valT_eq _ _ (hW a) _
  have hval : ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg →
      valT (T := R') (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : R') ^ l =
        f (valT (T := R) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := fun l sg sg' a h => by
    have e := valT_via (T := R') h (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
    rw [hu] at e
    refine (_root_.mul_comm _ _).trans (e.symm.trans ?_)
    exact (congrArg (fun q => valT (T := R') q (x.P.L.U (ch a)) (sg.f (ch a))) (hz' a)).trans
      (valT_spMap f (z a).left (hz₁ a) _)
  have hzero : ∀ a i, valT (T := R') (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by
    have e := hval n _ _ a (hs i)
    rw [hz₂, map_zero] at e
    exact ((u a).isUnit.pow n).mul_left_eq_zero.1 e
  have hjac : ∀ a, jac x' s' (z' a) (ch' a) * (u a : R') ^ (x.P.g * n) = f (jac x s (z a) (ch a)) := fun a => by
    have ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z a) * x.v (k.cast hg)).left
        (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a)))) = (u a : R') ^ n * TrivSqZeroExt.snd (valT (T := DualNumber R')
          ((toUnit (epsR R') ≫ z' a) * x'.v k).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a))) := fun i k => by
      have c := translate_comp hp F hF₁ (z a) (z' a) (hz' a) (x.v (k.cast hg)) (x'.v k) (hv k)
      have l₁ := translate_le (z a) (x.v (k.cast hg)) (x.basis.1 _) (hz₁ a)
      have l₂ := translate_le (z' a) (x'.v k) (x'.basis.1 _) (hch' a)
      have l₃ : ⊤ ≤ (((toUnit (epsR R') ≫ z' a) * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun p _ => by
        rw [c]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber R') (hs i) _ (ch a) (ch' a) l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber R') q (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a))) c).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hch' a) _).trans (hzero a i))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hW a) _).trans (hu a))
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x'.P.g) := hg.symm.trans (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u a : R') ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm
  refine ⟨z', ch', u, ⟨hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩, hjac, hval⟩
  · exact isUnit_of_mul_isUnit_left (hjac a ▸ (hz₃ a).map f)
  · refine hz₄ a a' h (spMap f p) ?_
    have e₁ := congrArg (fun q => q p) (hz' a)
    have e₂ := congrArg (fun q => q p) (hz' a')
    exact e₁.symm.trans ((congrArg φ e).trans e₂)
  · obtain ⟨a, p, hp'⟩ := hz₅ (φ y) fun i h => hy (i.cast hg.symm) (mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)
    have sq : IsPullback (spMap f) (z' a).left (z a).left φ := by
      refine IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm
      have e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _ := Over.w (z' a)
      have e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _ := Over.w (z a)
      rw [e₁, e₂]
      exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp R')) (f := 𝟙 (Sp R)) (g := spMap f) ⟨by simp⟩
    obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq p y hp'
    exact ⟨a, q, hq⟩

end GlobalTheory.KeyKa
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyVia

variable {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X}

def Via (w : LB.Iso L' (L.pull φ)) (l : ℕ) (a' : ∀ i, Γ(Y, L'.U i)) (a : ∀ j, Γ(X, L.U j)) : Prop :=
  ∀ (j : (L.pull φ).ι) (i : L'.ι) (h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
    (φ.appLE _ _ h).hom (a (j PUnit.unit)) =
      (show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l * resG _ inf_le_right (a' i)

theorem chart_le (j : (L.pull φ).ι) : (L.pull φ).U j ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) :=
  LB.wchart_le L (fun _ => φ) j PUnit.unit

theorem Via.unique (hL : L.IsLB) {w : LB.Iso L' (L.pull φ)} {l : ℕ} {a' b' : ∀ i, Γ(Y, L'.U i)}
    {a : ∀ j, Γ(X, L.U j)} (ha : Via w l a' a) (hb : Via w l b' a) : a' = b' := by
  funext i
  apply TopCat.Presheaf.section_ext Y.sheaf (L'.U i) (a' i) (b' i)
  intro y hy
  have hc := (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)).cover
  have hyc : y ∈ ⨆ j, (L.pull φ).U j := by rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hyc
  have h : (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit) := inf_le_left.trans (chart_le j)
  have e := (ha j i h).symm.trans (hb j i h)
  have hu : IsUnit ((show Γ(Y, (L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) ^ l) :=
    (Units.isUnit (w.s (j, i))).pow l
  have e' := hu.mul_left_cancel e
  have hm : y ∈ (L.pull φ).U j ⊓ L'.U i := ⟨hj, hy⟩
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right) y hm,
      ← TopCat.Presheaf.germ_res_apply _ (homOfLE inf_le_right) y hm]
  exact congrArg (fun v => (Y.presheaf.germ _ y hm).hom v) e'

def pwIso {A B : LB Y} (w : LB.Iso A B) (t : ℤ) : LB.Iso (pw A t) (pw B t) := ⟨fun p => w.s p ^ t⟩

theorem pwIso_isGen {A B : LB Y} {w : LB.Iso A B} (hw : w.IsGen) (t : ℤ) : (pwIso w t).IsGen := by
  intro p q
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem res_appLE {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.appLE_map h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

theorem appLE_res {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a := by
  have e := congrArg (fun q => q.hom a) (φ.map_appLE h (homOfLE h').op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using e

theorem pull_g (j j' : (L.pull φ).ι) (h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit))) :
    (L.pull φ).g j j' = Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit)) := by
  dsimp only [LB.pull, LB.LinComb]
  rw [Fintype.prod_unique]
  exact (zpow_one (Units.map (φ.appLE _ _ h).hom.toMonoidHom (L.g (j PUnit.unit) (j' PUnit.unit))))

def pullSec (φ : Y ⟶ X) {t : ℤ} (s : LB.Sec (pw L t)) : LB.Sec (pw (L.pull φ) t) where
  f j := (φ.appLE _ _ (chart_le j)).hom (s.f (j PUnit.unit))
  compat j j' := by
    have h : (L.pull φ).U j ⊓ (L.pull φ).U j' ≤ φ ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
      fun _ hy => ⟨chart_le j hy.1, chart_le j' hy.2⟩
    have e := (congrArg (φ.appLE _ _ h).hom (s.compat (j PUnit.unit) (j' PUnit.unit))).trans (map_mul _ _ _)
    refine (res_appLE _ _ _).trans ((appLE_res h _ _).symm.trans (e.trans (congrArg₂ (· * ·) ?_
      ((appLE_res h _ _).trans (res_appLE _ _ _).symm))))
    exact (congrArg Units.val ((congrArg (· ^ t) (pull_g j j' h)).trans (map_zpow _ _ t).symm)).symm

theorem exists_via (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) (l : ℕ)
    (s : LB.Sec (pw L (l : ℤ))) : ∃ s' : LB.Sec (pw L' (l : ℤ)), Via w l s'.f s.f := by
  have isLB_pw {Z : Scheme.{0}} {H : LB Z} (hH : H.IsLB) (t : ℤ) : (pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have e := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at e
      exact e
    · intro i j k
      have e := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at e
      exact e
  have hu := pwIso_isGen hw (l : ℤ)
  have hA := isLB_pw hL' (l : ℤ)
  have hB := isLB_pw (DVR.linComb_isLB L hL (fun _ : PUnit => φ) (fun _ => 1)) (l : ℤ)
  refine ⟨DVR.secOfIso (pullSec φ s) hu hA hB, fun j i h => ?_⟩
  have hV : (L.pull φ).U j ⊓ L'.U i ≤ (pw L' (l : ℤ)).U i ⊓ (pw (L.pull φ) (l : ℤ)).U j := fun _ hy => ⟨hy.2, hy.1⟩
  have h₁ := congrArg (DVR.rs hV) (DVR.secOfIso_spec (pullSec φ s) hu hA hB i j)
  have h₂ := ((DVR.rs_rs _ _ _).symm.trans h₁).trans (DVR.isoCand_rs (pwIso w l) (pullSec φ s) i j hV)
  let u : Γ(Y, (L.pull φ).U j ⊓ L'.U i)ˣ := w.s (j, i)
  have h₃ : res (hV.trans (DVR.divLe i j)) ((pwIso w (l : ℤ)).s (j, i)) = u ^ l :=
    (Units.ext (rs_self le_rfl (u ^ (l : ℤ)).val)).trans (zpow_natCast u l)
  have h₄ : resG Y (inf_le_right : (L.pull φ).U j ⊓ L'.U i ≤ L'.U i) ((DVR.secOfIso (pullSec φ s) hu hA hB).f i) =
      ((u ^ l)⁻¹).val * (φ.appLE _ _ h).hom (s.f (j PUnit.unit)) :=
    h₂.trans (congrArg₂ (· * ·) (congrArg (fun v => (v⁻¹).val) h₃) (res_appLE _ _ _))
  exact ((congrArg₂ (· * ·) (Units.val_pow_eq_pow_val u l).symm h₄).trans (Units.mul_inv_cancel_left _ _)).symm

theorem appLE_cst {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (cst p U r) = cst p' V (f r) := by
  refine (appLE_res h le_top _).trans ?_
  have e₁ : p.appTop ≫ φ.appTop = (spMap f).appTop ≫ p'.appTop := by
    rw [← Scheme.Hom.comp_appTop, hφ, Scheme.Hom.comp_appTop]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  have e₃ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ φ.appTop =
      CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ p'.appTop := by
    rw [e₁, ← Category.assoc, ← e₂, Category.assoc]
  exact congrArg (fun q => rs Y (le_top : V ≤ ⊤) (q.hom r)) e₃

theorem Via.comb {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (p : X ⟶ Sp R) (p' : Y ⟶ Sp R')
    (hφ : φ ≫ p = p' ≫ spMap f) {w : LB.Iso L' (L.pull φ)} {l N : ℕ} {b' : Fin N → ∀ i, Γ(Y, L'.U i)}
    {b : Fin N → ∀ j, Γ(X, L.U j)} (hb : ∀ k, Via w l (b' k) (b k)) (c : Fin N → R) :
    Via w l (fun i => ∑ k, AbLaw.cst p' _ (f (c k)) * b' k i) (fun j => ∑ k, AbLaw.cst p _ (c k) * b k j) := by
  intro j i h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, hb k j i h, appLE_cst f p p' hφ, rs_cst, mul_left_comm]

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R'), (KeyPB x' x f ↔ ∃ φ w, KeyVia x' x f φ w) ∧ ∀ φ w, KeyVia x' x f φ w → (∀ (l : ℕ) (s : RR x l), ∃! s' : RR x' l, SecVia x' x φ w s' s) ∧ (∀ z : Pt x, ∃! z' : Pt x', z'.left ≫ φ = spMap f ≫ z.left) ∧ ∀ (l N : ℕ) (b : Fin N → RR x l) (b' : Fin N → RR x' l) (s : RR x l) (s' : RR x' l) (c : Fin N → R), (∀ k, SecVia x' x φ w (b' k) (b k)) → SecVia x' x φ w s' s → Coords x b c s.f → Coords x' b' (fun k => f (c k)) s'.f := by
  intro R R' _ _ x x' f
  refine ⟨⟨fun ⟨φ, he, w, hg, F, H⟩ => ⟨φ, w, he, hg, F, H⟩, fun ⟨φ, w, he, hg, F, H⟩ => ⟨φ, he, w, hg, F, H⟩⟩, ?_⟩
  rintro φ w ⟨he, hg, F, ⟨hP, -⟩, hw, -⟩
  refine ⟨fun l s => ?_, fun z => ?_, fun l N b b' s s' c hb hs hc => ?_⟩
  · obtain ⟨s', hs'⟩ := exists_via x.P.isLB x'.P.isLB hw l s
    refine ⟨s', hs', fun t ht => ?_⟩
    have e : t.f = s'.f := Via.unique (w := w) (l := l) x.P.isLB ht hs'
    obtain ⟨tf, _⟩ := t
    obtain ⟨sf, _⟩ := s'
    obtain rfl : tf = sf := e
    rfl
  · have hz : z.left ≫ x.P.A.hom = 𝟙 (Sp R) := Over.w z
    have hc : (spMap f ≫ z.left) ≫ x.P.A.hom = 𝟙 (Sp R') ≫ spMap f := by
      rw [Category.assoc, hz, Category.comp_id, Category.id_comp]
    refine ⟨Over.homMk (hP.lift _ _ hc) (hP.lift_snd _ _ hc), hP.lift_fst _ _ hc, fun t ht => ?_⟩
    ext1
    exact hP.hom_ext (ht.trans (hP.lift_fst _ _ hc).symm) ((Over.w t).trans (hP.lift_snd _ _ hc).symm)
  · have H := Via.comb (w := w) (l := l) (b' := fun k => (b' k).f) (b := fun k => (b k).f) f x.P.A.hom x'.P.A.hom hP.w hb c
    have e : s.f = fun j => ∑ k, cst x.P.A.hom (x.P.L.U j) (c k) * (show Γ(x.P.A.left, x.P.L.U j) from (b k).f j) :=
      funext hc
    have hs' : Via w l s'.f s.f := hs
    have hs'' := (congrArg (Via w l s'.f) e).mp hs'
    have e' := Via.unique x.P.isLB hs'' H
    exact fun i => congrFun e' i

end GlobalTheory.KeyVia
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteTypeSubringAdjoin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

theorem _root_.GlobalTheory.KeyTf.exists_finiteType_subring_adjoin :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (F : Finset S), Algebra.FiniteType ℤ R₀ →
      ∃ R₁ : Subring S, R₀ ≤ R₁ ∧ (F : Set S) ⊆ R₁ ∧ Algebra.FiniteType ℤ R₁ := by
  intro S _ R₀ F hR₀
  classical
  obtain ⟨s, hs⟩ := hR₀.out
  let T : Finset S := s.image (Subtype.val) ∪ F
  refine ⟨(Algebra.adjoin ℤ (T : Set S)).toSubring, ?_, ?_, ?_⟩
  · intro x hx
    have hmem : (⟨x, hx⟩ : R₀) ∈ Algebra.adjoin ℤ (s : Set R₀) := hs ▸ Algebra.mem_top
    have h2 : x ∈ (Algebra.adjoin ℤ (s : Set R₀)).map R₀.subtype.toIntAlgHom :=
      Subalgebra.mem_map.2 ⟨_, hmem, rfl⟩
    rw [← Algebra.adjoin_image] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)
  · intro x hx
    exact Algebra.subset_adjoin (Finset.mem_union_right _ hx)
  · exact (Subalgebra.fg_iff_finiteType _).1 ⟨T, rfl⟩

end GlobalTheory.KeyTf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsPullbackOfFpqcLeft
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.isGrpPullback_of_fpqc (S S' S'' : Scheme.{0}) (a : S' ⟶ S) (π : S'' ⟶ S') (G : Over S) [GrpObj G]
    (G' : Over S') [GrpObj G'] (G'' : Over S'') [GrpObj G''] (φ : G''.left ⟶ G'.left) (ψ : G'.left ⟶ G.left)
    (hf : Flat π) (hs : Surjective π) (hq : QuasiCompact π) (h₁ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G' π φ)
    (h₂ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G (π ≫ a) (φ ≫ ψ)) (w : ψ ≫ G.hom = G'.hom ≫ a) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G a ψ := by
  refine ⟨?_, ?_⟩
  · let c : G'.left ⟶ pullback G.hom a := pullback.lift ψ G'.hom w
    have hc₁ : c ≫ pullback.fst G.hom a = ψ := pullback.lift_fst _ _ _
    have hc₂ : c ≫ pullback.snd G.hom a = G'.hom := pullback.lift_snd _ _ _
    have hlow : IsPullback (φ ≫ c) G''.hom (pullback.snd G.hom a) π :=
      (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback G.hom a)
        (by rw [Category.assoc, hc₂, h₁.1.w])).1 (by rw [Category.assoc, hc₁]; exact h₂.1)
    have hcov : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (φ ≫ c) :=
      ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hlow.flip hs,
        MorphismProperty.of_isPullback (P := @Flat) hlow.flip hf⟩,
        MorphismProperty.of_isPullback (P := @QuasiCompact) hlow.flip hq⟩
    have hsq : IsPullback (𝟙 G''.left) φ (φ ≫ c) c :=
      ((IsPullback.paste_vert_iff (h₁₁ := φ) (v₁₁ := 𝟙 _) (v₁₂ := c) hlow (by simp)).1
        (by rw [Category.id_comp, hc₂]; exact h₁.1)).flip
    have hc : IsIso c :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms _)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq hcov (inferInstanceAs (IsIso (𝟙 G''.left)))
    exact IsPullback.of_iso (IsPullback.of_hasPullback G.hom a) (asIso c).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp [IsIso.eq_inv_comp, hc₁]) (by simp [IsIso.eq_inv_comp, hc₂])
      (by simp) (by simp)
  · intro T x y x₀ y₀ hx hy
    haveI := hf
    haveI := hs
    let p : pullback T.hom π ⟶ T.left := pullback.fst T.hom π
    haveI : Epi p := Flat.epi_of_flat_of_surjective _
    let T'' : Over S'' := Over.mk (pullback.snd T.hom π)
    let q : Over.mk (T''.hom ≫ π) ⟶ T := Over.homMk p (by simp [p, T'', pullback.condition])
    let q₀ : Over.mk (T''.hom ≫ π ≫ a) ⟶ Over.mk (T.hom ≫ a) :=
      Over.homMk p (by simp [p, T'', pullback.condition_assoc])
    let x'' : T'' ⟶ G'' := Over.homMk (h₁.1.lift (p ≫ x.left) T''.hom
      (by simp [p, T'', pullback.condition])) (by simp [T''])
    let y'' : T'' ⟶ G'' := Over.homMk (h₁.1.lift (p ≫ y.left) T''.hom
      (by simp [p, T'', pullback.condition])) (by simp [T''])
    have hx'' : x''.left ≫ φ = p ≫ x.left := by simp [x'']
    have hy'' : y''.left ≫ φ = p ≫ y.left := by simp [y'']
    have k₁ := h₁.2 T'' x'' y'' (q ≫ x) (q ≫ y) (by simp [q, hx'']) (by simp [q, hy''])
    have k₂ := h₂.2 T'' x'' y'' (q₀ ≫ x₀) (q₀ ≫ y₀)
      (by simp only [Over.comp_left, Over.homMk_left, q₀]; rw [hx, reassoc_of% hx''])
      (by simp only [Over.comp_left, Over.homMk_left, q₀]; rw [hy, reassoc_of% hy''])
    rw [← cancel_epi p]
    calc p ≫ (x₀ * y₀).left = (q₀ ≫ (x₀ * y₀)).left := by simp [q₀]
      _ = ((q₀ ≫ x₀) * (q₀ ≫ y₀)).left := by rw [comp_mul]
      _ = (x'' * y'').left ≫ φ ≫ ψ := k₂
      _ = ((q ≫ x) * (q ≫ y)).left ≫ ψ := by rw [k₁, Category.assoc]
      _ = (q ≫ (x * y)).left ≫ ψ := by rw [comp_mul]
      _ = p ≫ (x * y).left ≫ ψ := by simp [q]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisingUnitSimilitudeOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisingUnitSimilitudeOrigin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.SimilUnit

section Rep

variable {X Y Y' : Scheme.{0}} (L : LB X)

def IsVal (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ y J, Good L y J → val t (𝟙 Y) y J = v y J

variable {L} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
  {v v' : ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ}

theorem IsVal.pull {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (r : Y ⟶ Y') :
    IsVal L (fun _ _ h => ∏ k, h (r ≫ φ k) ^ ε k) (fun y J => val t r y J) :=
  ⟨K, inferInstance, _, ε, LB.pullGen L φ ε t r, DVR.pullGen_isGen _ _ _ _ ht _, fun _ _ _ => rfl,
    fun y J hJ => by rw [val_pull hJ, Category.id_comp]⟩

theorem IsVal.one : IsVal L (Y := Y) (fun _ _ _ => 1) (fun _ _ => 1) :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L, fun i j => by
    refine (map_one _).trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _), fun _ _ _ => Fintype.prod_empty _, fun _ _ _ => val_one _⟩

theorem IsVal.mul (a : IsVal L F v) (b : IsVal L F' v') :
    IsVal L (fun U _ h => F U h * F' U h) (fun y J => v y J * v' y J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := b
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => ?_, fun y J hJ => ?_⟩
  · exact (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (hF U h) (hF' U h))
  · rw [val_mul hJ, hv y J hJ, hv' y J hJ]

theorem IsVal.inv (a : IsVal L F v) : IsVal L (fun U _ h => (F U h)⁻¹) (fun y J => (v y J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht,
    fun U _ h => ?_, fun y J hJ => ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · rw [val_inv, hv y J hJ]

theorem IsVal.pow (a : IsVal L F v) (n : ℕ) : IsVal L (fun U _ h => F U h ^ n) (fun y J => v y J ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using IsVal.one
  | succ n ih => simpa only [pow_succ] using ih.mul a

theorem IsVal.zpow (a : IsVal L F v) (n : ℤ) : IsVal L (fun U _ h => F U h ^ n) (fun y J => v y J ^ n) := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [zpow_natCast] using a.pow k
  · simpa only [zpow_neg, zpow_natCast] using (a.pow k).inv

theorem IsVal.prod {I : Type} {G : I → ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
    {u : I → ∀ y : Y, ((Y ⟶ X) → L.ι) → (Y.presheaf.stalk y)ˣ} (a : ∀ i, IsVal L (G i) (u i)) (s : Finset I) :
    IsVal L (fun U _ h => ∏ i ∈ s, G i U h) (fun y J => ∏ i ∈ s, u i y J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using IsVal.one
  | insert d s hd ih => simpa only [Finset.prod_insert hd] using (a d).mul ih

theorem IsVal.exists_unit (hL : L.IsLB) (a : IsVal L F v)
    (h1 : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), F U h = 1) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ y J, Good L y J → (v y J).val = gs (𝟙 Y) y ⊤ u.val := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := a
  obtain ⟨t', -, hv'⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ h => ((hF U h).trans (h1 U h)).trans (Fintype.prod_empty _).symm) t ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t'.s PEmpty.elim), fun y J hJ => ?_⟩
  rw [← hv y J hJ, ← hv' _ _ y J hJ, val_of t' _ y J PEmpty.elim (fun k => k.elim)]
  exact (congrArg Units.val (gm_res _ y le trivial _)).symm.trans (gs_unit _ y ⊤ trivial _).symm

end Rep

theorem pow_eq_one_of_similitude {A I : Type} [CommGroup A] [Fintype I] [DecidableEq I] (m : ℕ) (hm : m ≠ 0)
    (al : Matrix I I ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix I I ℤ)) (ξ : I → A)
    (hk : ∀ c, ∏ r, ξ r ^ al r c = 1) (r : I) : ξ r ^ m = 1 := by
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
  have hd : al.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hal
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
    exact pow_ne_zero _ hm' this.symm
  have h2 : al * al.transpose = (m : ℤ) • (1 : Matrix I I ℤ) := by
    have e : (al * al.transpose) * al = ((m : ℤ) • (1 : Matrix I I ℤ)) * al := by
      rw [Matrix.mul_assoc, hal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have e' := congrArg (· * al.adjugate) e
    simp only [Matrix.mul_assoc (_ : Matrix I I ℤ) al al.adjugate, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e'
    exact smul_right_injective _ hd e'
  have e : ∏ c, (∏ r', ξ r' ^ al r' c) ^ al r c = ξ r ^ m := by
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    have : ∀ r', ∏ c, ξ r' ^ (al r' c * al r c) = ξ r' ^ (if r' = r then (m : ℤ) else 0) := fun r' => by
      have := congrFun (congrFun h2 r') r
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        mul_ite, _root_.mul_one, mul_zero] at this
      rw [← this]
      exact (map_prod (zpowersHom A (ξ r')) (fun c => Multiplicative.ofAdd (al r' c * al r c)) Finset.univ).symm
    simp only [this, pow_ite, zpow_zero, Finset.prod_ite_eq', Finset.mem_univ, if_true, zpow_natCast]
  rw [← e]
  simp only [hk, one_zpow, Finset.prod_const_one]

theorem exists_normalising_unit : ∀ (R : Type) [CommRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x) (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2])) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), m ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ c, (List.ofFn fun r : Fin 4 => ξ r ^ al r c).prod = 1) → mu.IsGen → w.IsGen → ∃ rho : Rˣ, ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → (val w (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ r).left p J).val = gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ rho) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val := by
  intro R _ x m al ξ mu w hm hal hk hmu hw
  haveI := x.P.isAb.comm
  have hξ : ∀ r, ξ r ^ m = 1 := pow_eq_one_of_similitude m hm al hal ξ fun c => by
    simpa only [List.prod_ofFn] using hk c
  have e₁ : ∀ c, eSec (Out.powObj x.P.A 4) ≫ (Out.powPr x.P.A c).left = eSec x.P.A := fun c =>
    congrArg CommaMorphism.left (IsMonHom.one_hom (Out.powPr x.P.A c))
  have e₂ : ∀ r, eSec (Out.powObj x.P.A 4) ≫ (alMap x al r (ξ r)).left = (ξ r).left := fun r => by
    have h1 : ∀ c, η[Out.powObj x.P.A 4] ≫ Out.powPr x.P.A c = 1 := fun c => by
      rw [IsMonHom.one_hom, Hom.one_def, toUnit_unit, Category.id_comp]
    have : η[Out.powObj x.P.A 4] ≫ alMap x al r (ξ r) = ξ r := by
      simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul, GrpObj.comp_zpow,
        MonObj.comp_one, h1, one_zpow, _root_.one_mul]
      rw [← Category.assoc, toUnit_unique (η[_] ≫ toUnit _) (𝟙 _), Category.id_comp]
    exact congrArg CommaMorphism.left this
  have e₃ : ∀ r, (ξ r).left ≫ ((𝟙 x.P.A) ^ m).left = eSec x.P.A := fun r => by
    have : ξ r ≫ (𝟙 x.P.A) ^ m = η[x.P.A] := by
      rw [MonObj.comp_pow, Category.comp_id, hξ, Hom.one_def, toUnit_unit, Category.id_comp]
    exact congrArg CommaMorphism.left this
  obtain ⟨u, hu⟩ := ((((IsVal.pull hw (eSec (Out.powObj x.P.A 4))).pow (m ^ 2)).mul
    (IsVal.prod (fun r => IsVal.pull hmu (ξ r).left) Finset.univ)).mul
    ((IsVal.pull x.rig_gen (𝟙 _)).zpow (4 - 4 * (m : ℤ) ^ 3)).inv).exists_unit x.P.isLB (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, e₁, e₂, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, e₃, Category.comp_id, Category.id_comp, Fintype.prod_unique, zpow_one,
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_unique, Finset.prod_zpow]
      generalize h (eSec x.P.A) = a
      generalize (∏ r, h (ξ r).left) = b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one]
      module)
  let E := RingEquiv.ofBijective _ (cst_bijective (𝟙 (Sp R)) (W := ⊤) rfl)
  refine ⟨Units.map E.symm.toMonoidHom u, fun p J hJ => ?_⟩
  have e : cst (𝟙 (Sp R)) ⊤ (Units.map E.symm.toMonoidHom u : Rˣ) = u.val := E.apply_symm_apply u.val
  rw [e]
  have := hu p J hJ
  rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul] at this
  exact this

end GlobalTheory.SimilUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisingUnitSimilitudeOriginStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exists_normalising_unit_similitude_origin : ∀ (R : Type) [CommRing R] (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x) (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2])) (w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ))))), m ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ c, (List.ofFn fun r : Fin 4 => ξ r ^ al r c).prod = 1) → mu.IsGen → w.IsGen → ∃ rho : Rˣ, ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → (val w (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ r).left p J).val = gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ rho) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val := by
  first | exact @GlobalTheory.SimilUnit.exists_normalising_unit | exact GlobalTheory.SimilUnit.exists_normalising_unit | (intros; apply GlobalTheory.SimilUnit.exists_normalising_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IndepOnEmpty
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.RelBasis

variable {X Y T : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

def comb (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) (c : Fin N → Γ(T, W)) (y : Y)
    (i : L.ι) : Y.presheaf.stalk y :=
  ∑ k, gs p₁ y W (c k) * gs p₂ y (L.U i) ((b k).f i)

def IndepOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ c : Fin N → Γ(T, W), (∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → comb b p₁ p₂ W c y i = 0) → c = 0

def SpanOn (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens) : Prop :=
  ∀ σ : ∀ i : L.ι, Γ(Y, p₁ ⁻¹ᵁ W ⊓ p₂ ⁻¹ᵁ L.U i),
    (∀ (y : Y) (i i' : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i → p₂ y ∈ L.U i' →
      gs (𝟙 Y) y _ (σ i) = (gm p₂ y (L.U i ⊓ L.U i') (L.g i i') ^ t).val * gs (𝟙 Y) y _ (σ i')) →
    ∃ c : Fin N → Γ(T, W), ∀ (y : Y) (i : L.ι), p₁ y ∈ W → p₂ y ∈ L.U i →
      gs (𝟙 Y) y _ (σ i) = comb b p₁ p₂ W c y i

def BoxSpan (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) : Prop :=
  ∀ (K : Type) [Fintype K] (φ : K → (T ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim (fun k => p₁ ≫ φ k) (fun _ => p₂)) (Sum.elim ε (fun _ => t)))),
    ∃ a : Fin N → LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s r z J = ∑ k, sval (a k) (r ≫ p₁) z J * gs (r ≫ p₂) z (L.U (J (r ≫ p₂))) ((b k).f (J (r ≫ p₂)))

theorem gs_comp {Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ f) z U a = (r.stalkMap z).hom (gs f (r z) U a) := by
  rw [← gs_pull r f z U h, gs_eq f (r z) U h, gs_eq r z (f ⁻¹ᵁ U) h]
  exact (Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _).symm

def gsHom (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom

theorem gs_eq_gsHom (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = gsHom f y U h a := gs_eq f y U h a

theorem comb_comp {Z : Scheme.{0}} (b : Fin N → LB.Sec (pw L t)) (r : Z ⟶ Y) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (c : Fin N → Γ(T, W)) (z : Z) (i : L.ι) (h₁ : p₁ (r z) ∈ W) (h₂ : p₂ (r z) ∈ L.U i) :
    comb b (r ≫ p₁) (r ≫ p₂) W c z i = (r.stalkMap z).hom (comb b p₁ p₂ W c (r z) i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb, comb, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, gs_comp r p₁ z W h₁]
  exact congrArg _ (gs_comp r p₂ z (L.U i) h₂ _)

end GlobalTheory.RelBasis
end
end
