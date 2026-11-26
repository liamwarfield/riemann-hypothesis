module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFiltrationSectionCombination
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.SecJet GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.SecJet.Orders

section Alg
open MvPolynomial

variable {R : Type} [CommRing R]

end Alg

section Val

variable {A : Type} [CommRing A] {X : Scheme.{0}}

def vh (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valR_eq (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR x U f = vh x U h f := by
  rw [valR, dite_eq_left h]; rfl

theorem vh_congr {x y : Sp A ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) :
    vh x U h = vh y U h' := by subst e; rfl

theorem vh_spMap {B : Type} [CommRing B] (ψ : A →+* B) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) (f : Γ(X, U)) : vh (spMap ψ ≫ x) U h' f = ψ (vh x U h f) := by
  have h1 : (spMap ψ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap ψ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have h3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom f)) h2
  simp only [vh, h1, RingHom.comp_apply, CommRingCat.hom_comp]
  exact h3

theorem vh_res (x : Sp A ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    vh x V h' (resG X hVU f) = vh x U h f := by
  have h1 : X.presheaf.map (homOfLE hVU).op ≫ x.appLE V ⊤ h' = x.appLE U ⊤ h := Scheme.Hom.map_appLE _ _ _
  simp only [vh, ← h1, RingHom.comp_apply, CommRingCat.hom_comp]

theorem vh_const {R : Type} [CommRing R] (ψ : R →+* A) (p : X ⟶ Sp R) (x : Sp A ⟶ X) (hx : x ≫ p = spMap ψ)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) : vh x U h (Geo.Tor.constFn p U a) = ψ a := by
  have h1 : p.appLE ⊤ U le_top ≫ x.appLE U ⊤ h = (spMap ψ).appTop := by
    refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ?_
    rw [← hx, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have h3 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h2
  have h4 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  simp only [vh, Geo.Tor.constFn, RingHom.comp_apply]
  erw [h4, h3]
  simp

theorem eq_of_vh {x y : Sp A ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (e : vh x U h = vh y U h') : x = y := by
  have e' : x.appLE U ⊤ h = y.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of A)).hom]
    exact CommRingCat.hom_ext e
  have hT : IsAffineOpen (⊤ : (Sp A).Opens) := isAffineOpen_top _
  have a1 := IsAffineOpen.SpecMap_appLE_fromSpec x hU hT h
  have a2 := IsAffineOpen.SpecMap_appLE_fromSpec y hU hT h'
  rw [e', a2] at a1
  haveI : IsIso hT.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  exact ((cancel_epi _).1 a1).symm

theorem vh_ne_zero [Nontrivial A] (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U))
    (hf : ⊤ ≤ x ⁻¹ᵁ X.basicOpen f) : vh x U h f ≠ 0 := by
  intro h0
  have h1 : (x.appLE U ⊤ h).hom f = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    rw [map_zero]; exact h0
  have h2 := Scheme.basicOpen_appLE x ⊤ U h f
  erw [h1] at h2
  rw [Scheme.basicOpen_zero, top_inf_eq] at h2
  obtain ⟨p⟩ : Nonempty (Sp A) := inferInstanceAs (Nonempty (PrimeSpectrum A))
  have := hf (show p ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← h2] at this
  exact this

theorem top_le_of_nil {B : Type} [CommRing B] (ψ : A →+* B) (hs : Function.Surjective ψ)
    (hn : ∀ z, ψ z = 0 → IsNilpotent z) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) :
    ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have : p ∈ Set.range (PrimeSpectrum.comap ψ) := by
    rw [range_comap_of_surjective _ ψ hs]
    refine (PrimeSpectrum.mem_zeroLocus _ _).2 ?_
    intro z hz
    obtain ⟨n, hn⟩ := hn z hz
    exact (show PrimeSpectrum A from p).isPrime.mem_of_pow_mem n (by rw [hn]; exact Ideal.zero_mem _)
  obtain ⟨q, rfl⟩ := this
  exact h (show (show Sp B from q) ∈ (⊤ : (Sp B).Opens) from trivial)

end Val

section Grp

variable {R : Type} [CommRing R]

theorem epsScale_zero : epsScale R 0 = toUnit _ ≫ TanComb.zeroPt := by
  apply Over.OverMorphism.ext
  show spMap (epsScaleR (0 : R)) = spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

variable {G : Over (Sp R)} [GrpObj G]

theorem epsScale_zero_comp {y : epsR R ⟶ G} (hy : IsTangent y) : epsScale R 0 ≫ y = 1 := by
  rw [epsScale_zero, Category.assoc, (TanComb.isTangent_iff y).1 hy, MonObj.comp_one]

def orig (G : Over (Sp R)) [GrpObj G] : Sp R ⟶ G.left := eSec G

theorem top_le_tangent {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U) :
    ⊤ ≤ (show Sp (DualNumber R) ⟶ G.left from y.left) ⁻¹ᵁ U := by
  refine top_le_of_nil (TrivSqZeroExt.fstHom R R R).toRingHom (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) ?_ _ U ?_
  · intro z hz
    have hz' : z.fst = 0 := hz
    refine ⟨2, ?_⟩
    ext <;> simp [sq, hz']
  · have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (show Sp (DualNumber R) ⟶ G.left from y.left) = orig G := hy
    rw [this]; exact he

theorem fst_vh_tangent {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U)
    (f : Γ(G.left, U)) : (vh (A := DualNumber R) y.left U (top_le_tangent hy he) f).fst = vh (orig G) U he f := by
  have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (show Sp (DualNumber R) ⟶ G.left from y.left) = orig G := hy
  rw [← vh_congr this U (by rw [this]; exact he) he, vh_spMap _ _ _ (top_le_tangent hy he)]
  rfl

theorem isTangent_one : IsTangent (1 : epsR R ⟶ G) := by
  rw [TanComb.isTangent_iff, MonObj.comp_one]

end Grp

section Sec

theorem vh_sec_ne_zero {K : Type} [Field K] {X : Scheme.{0}} {H : LB X} (s : H.Sec) (x : Sp K ⟶ X) (l : H.ι)
    (hl : ⊤ ≤ x ⁻¹ᵁ H.U l) (hs : ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s) : vh x (H.U l) hl (s.f l) ≠ 0 := by
  haveI : Unique (Sp K) := inferInstanceAs (Unique (PrimeSpectrum K))
  have h1 : x default ∈ Out.nonzeroLocus s := hs (show (default : Sp K) ∈ (⊤ : (Sp K).Opens) from trivial)
  rw [Out.nonzeroLocus, TopologicalSpace.Opens.mem_iSup] at h1
  obtain ⟨k, hk⟩ := h1
  have hk' : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (s.f k) := by
    intro p _
    rw [Subsingleton.elim p default]; exact hk
  have hkU : ⊤ ≤ x ⁻¹ᵁ H.U k := hk'.trans (x.preimage_mono (X.basicOpen_le _))
  have hkl : ⊤ ≤ x ⁻¹ᵁ (H.U k ⊓ H.U l) := fun p hp => ⟨hkU hp, hl hp⟩
  have h2 := vh_ne_zero x _ hkU _ hk'
  have h3 := congrArg (vh x _ hkl) (s.compat k l)
  rw [map_mul] at h3
  erw [vh_res x _ hkU hkl, vh_res x _ hl hkl] at h3
  intro h0
  rw [h0, mul_zero] at h3
  exact h2 h3

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G]

theorem exists_sep {H : LB G.left} {J : Type} (s : J → H.Sec) (hs : GlobalTheory.ZH.ImmBy G.hom H s Set.univ)
    {y : epsR K ⟶ G} (hy : IsTangent y) (hy1 : y ≠ 1) (l : H.ι) (hl : ⊤ ≤ orig G ⁻¹ᵁ H.U l) :
    ∃ s₀ s₁ : H.Sec, vh (orig G) _ hl (s₀.f l) ≠ 0 ∧ vh (orig G) _ hl (s₁.f l) = 0 ∧
      (vh (A := DualNumber K) y.left _ (top_le_tangent hy hl) (s₁.f l)).snd ≠ 0 := by
  haveI : Unique (Sp K) := inferInstanceAs (Unique (PrimeSpectrum K))
  obtain ⟨hc, hs⟩ := hs
  have h1 : orig G default ∈ ⨆ i ∈ (Set.univ : Set J), Out.nonzeroLocus (s i) := by rw [hc]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at h1
  obtain ⟨i, -, hi⟩ := h1
  obtain ⟨haff, r, hr, hgen⟩ := hs i trivial
  have hV : ⊤ ≤ orig G ⁻¹ᵁ Out.nonzeroLocus (s i) := by
    intro p _
    rw [Subsingleton.elim p default]; exact hi
  have h0 := vh_sec_ne_zero (s i) (orig G) l hl hV
  have hj : ∃ j, (vh (A := DualNumber K) y.left _ (top_le_tangent hy hV) (r j)).snd ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hy1
    apply Over.OverMorphism.ext
    refine eq_of_vh (A := DualNumber K) haff (top_le_tangent hy hV) (top_le_tangent isTangent_one hV) ?_
    refine RingHom.eq_of_eqOn_set_dense hgen ?_
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact (vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w y) _ _ a).trans
        (vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w (1 : epsR K ⟶ G)) _ _ a).symm
    · apply TrivSqZeroExt.ext
      · exact (fst_vh_tangent hy hV _).trans (fst_vh_tangent isTangent_one hV _).symm
      · refine (hn j).trans ?_
        have := vh_spMap (algebraMap K (DualNumber K)) (orig G) _ hV (top_le_tangent isTangent_one hV) (r j)
        erw [this]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨j, hj⟩ := hj
  have key : vh (A := DualNumber K) y.left _ (top_le_tangent hy hl)
      ((secComb G.hom ![1, -vh (orig G) _ hV (r j)] ![s j, s i]).f l) =
      (vh (A := DualNumber K) y.left _ (top_le_tangent hy hV) (r j) - algebraMap K _ (vh (orig G) _ hV (r j))) *
        vh (A := DualNumber K) y.left _ (top_le_tangent hy hl) ((s i).f l) := by
    have hW : ⊤ ≤ (show Sp (DualNumber K) ⟶ G.left from y.left) ⁻¹ᵁ (Out.nonzeroLocus (s i) ⊓ H.U l) :=
      fun p hp => ⟨top_le_tangent hy hV hp, top_le_tangent hy hl hp⟩
    have h3 := congrArg (vh _ _ hW) (hr j l)
    rw [map_mul, vh_res _ _ (top_le_tangent hy hl) hW, vh_res _ _ (top_le_tangent hy hl) hW,
      vh_res _ _ (top_le_tangent hy hV) hW] at h3
    simp only [secComb, Fin.sum_univ_two, map_add (f := _), map_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w y),
      vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w y)]
    erw [h3]
    simp only [map_one, map_neg]
    ring
  have hf : (vh (A := DualNumber K) y.left _ (top_le_tangent hy hV) (r j) -
      algebraMap K _ (vh (orig G) _ hV (r j))).fst = 0 := by
    rw [TrivSqZeroExt.fst_sub, fst_vh_tangent hy hV]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨s i, secComb G.hom ![1, -vh (orig G) _ hV (r j)] ![s j, s i], h0, ?_, ?_⟩
  · rw [← fst_vh_tangent hy hl, key, TrivSqZeroExt.fst_mul, hf, zero_mul]
  · rw [key, TrivSqZeroExt.snd_mul, hf, fst_vh_tangent hy hl, zero_smul, zero_add, TrivSqZeroExt.snd_sub]
    simpa [TrivSqZeroExt.algebraMap_eq_inl, h0] using hj

theorem tanComb_ne_one {m : ℕ} {v : Fin m → (epsR K ⟶ G)} (hv : IsLieBasis v) {x : Fin m → K} (hx : x ≠ 0) :
    tanComb x v ≠ 1 := by
  intro h
  have h0 : tanComb 0 v = 1 := by
    apply List.prod_eq_one
    intro w hw
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hw
    exact epsScale_zero_comp (hv.1 a)
  obtain ⟨c, -, hc⟩ := hv.2 1 isTangent_one
  exact hx ((hc x (h ▸ isLieComb_tanComb x v)).trans (hc 0 (h0 ▸ isLieComb_tanComb 0 v)).symm)

end Sec

end GlobalTheory.SecJet.Orders

namespace GlobalTheory.SecJet


end GlobalTheory.SecJet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanThetaTranslatesTorsionEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateThetaPullbackNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusOfIsTwistPull
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackNonvanishingOfPulledSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackNonvanishingOfPulledSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistNZ

theorem mem_nz_iff {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι)
    {x : Y} (hk : x ∈ H.U k) : x ∈ nonzeroLocus s ↔ x ∈ Y.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg Y.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, Y.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, Y.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem twistPull_nonzero : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := by
  intro S A _ L hL T ψ m hm a b α s s' H p hp
  have hcov : ∀ y : A.left, ∃ i, y ∈ L.U i := fun y => by
    have : y ∈ (⨆ i, L.U i : A.left.Opens) := by rw [hL.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  obtain ⟨i0, h0⟩ := hcov ((snd T A).left.base p)
  obtain ⟨i1, h1⟩ := hcov (m.left.base p)
  let j : Fin 2 → L.ι := ![i0, i1]
  have e₀ : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  have hpj : p ∈ LB.wchart L ![(snd T A).left, m.left] j := by
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · exact h0
    · exact h1

  have hψ : ψ.left.base p ∈ (LPow A L b T).U (fun _ => j 1) := by
    refine Set.mem_iInter.2 fun _ => ?_
    show ((snd T A).left.base (ψ.left.base p)) ∈ (L.U i1 : Set A.left)
    have : (ψ.left ≫ (snd T A).left).base p = m.left.base p := by rw [e₀]
    rw [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [this]; exact h1
  have h2 : ψ.left.base p ∈ (T ⊗ A).left.basicOpen (s.f (fun _ => j 1)) :=
    (mem_nz_iff s _ hψ).1 hp
  have h3 : p ∈ (T ⊗ A).left.basicOpen ((ψ.left.app _).hom (s.f (fun _ => j 1))) := by
    rw [← Scheme.preimage_basicOpen]; exact h2
  have e := congrArg (T ⊗ A).left.basicOpen (H j)
  dsimp only at e
  erw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (α.s j).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hp4 := e.ge ⟨hpj, hpj, h3⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, hp4.2⟩

end GlobalTheory.TwistNZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackNonvanishingOfPulledSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPullback_nonvanishing_of_pulledSection : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := by
  first | exact @GlobalTheory.TwistNZ.twistPull_nonzero | exact GlobalTheory.TwistNZ.twistPull_nonzero | (intros; apply GlobalTheory.TwistNZ.twistPull_nonzero <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TranslateSection

theorem translT_inv_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A) :
    translT A z⁻¹ ≫ translT A z = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, translPt, Category.assoc, lift_snd, lift_fst, Category.id_comp, comp_lift_assoc, lift_fst_assoc]
    change (fst T A ≫ z) * ((fst T A ≫ z⁻¹) * snd T A) = snd T A
    have e : fst T A ≫ z⁻¹ = (fst T A ≫ z)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one])
    rw [e, mul_inv_cancel_left]

theorem translT_surjective : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A), Function.Surjective (translT A z).left.base := by
  intro S A _ T z y
  refine ⟨(translT A z⁻¹).left.base y, ?_⟩
  have h := congrArg (fun f : T ⊗ A ⟶ T ⊗ A => f.left y) (translT_inv_comp A z)
  simpa [Scheme.Hom.comp_apply] using h

theorem mulT_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (m : ℕ) :
    mulT A (baseOver S) m = (λ_ A).hom ≫ mulA A m ≫ (λ_ A).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv, CartesianMonoidalCategory.leftUnitor_hom, mulT]
  refine (lift_snd _ _).trans ?_
  rw [mulA, MonObj.comp_pow, Category.comp_id]
  rfl

theorem mulT_surjective : ∀ {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (m : ℕ), 1 ≤ m → Function.Surjective (mulT P.A (baseOver S) m).left.base := by
  intro S _ P m hm y
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨-, -, hs, -⟩ := hLaw.mulN S P m hm
  obtain ⟨b, hb⟩ := hs.surj ((λ_ P.A).hom.left y)
  refine ⟨(λ_ P.A).inv.left b, ?_⟩
  have h1 := congrArg (fun f : baseOver S ⊗ P.A ⟶ baseOver S ⊗ P.A => f.left ((λ_ P.A).inv.left b)) (mulT_eq P.A m)
  have h2 := congrArg (fun f : baseOver S ⊗ P.A ⟶ baseOver S ⊗ P.A => f.left y) (λ_ P.A).hom_inv_id
  have h3 := congrArg (fun f : P.A ⟶ P.A => f.left b) (λ_ P.A).inv_hom_id
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.id_left] at h1 h2 h3
  have h2' : (λ_ P.A).inv.left ((λ_ P.A).hom.left y) = y := h2
  have h3' : (λ_ P.A).hom.left ((λ_ P.A).inv.left b) = b := h3
  rw [h1, h3', hb, h2']

theorem mem_nonzeroLocus_of_isTwistPull : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := GlobalTheory.T.twistedPullback_nonvanishing_of_pulledSection

end GlobalTheory.MBLow.TranslateSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateThetaPullbackNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.TransNZ

open GlobalTheory.MBLow.TranslateSection GlobalTheory.MBLow.TrSec

theorem eq_projectionPullbackSection_of_inverseImage {S : Scheme.{0}} (P : PolAV S) (s : P.L.Sec)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S))) (h : IsPolAVSectionInverseImage P (baseOver S) s th) :
    th = thSec P s := by
  have key : ∀ j : Fin 1 → P.L.ι, th.f j = (thSec P s).f j := by
    intro j
    have hj : j = fun _ => j 0 := funext fun k => by rw [Subsingleton.elim k 0]
    rw [hj, h (j 0) (chart_le P _), projectionPullbackSectionBaseProduct_isInverseImage P s (j 0) (chart_le P _)]
  cases th; cases hth : thSec P s
  simp only [hth] at key
  congr
  exact funext key

end GlobalTheory.TransNZ


open GlobalTheory.MBLow.TranslateSection GlobalTheory.MBLow.TrSec in
theorem GlobalTheory.TransNZ.exists_ne : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    ∃ i, (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)) ≠ 0 := by
  intro K _ _ _ x m hm hm3 I pt hpt th hth U t hUt
  have hm1 : 1 ≤ m := by omega
  obtain ⟨i₀, -⟩ := hpt 1 (one_pow _)
  obtain ⟨-, α, s₁, hα, -, hs₁, ht⟩ := hUt i₀
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨a, -, ha⟩ := x.th_ne p₀
  have e := GlobalTheory.TransNZ.eq_projectionPullbackSection_of_inverseImage x.P x.th th hth
  have hp₁ := nonzero_thSec x.P x.th a ha
  rw [← e] at hp₁
  obtain ⟨q, hq⟩ := mulT_surjective x.P m hm1 ((λ_ x.P.A).inv.left.base a)
  have hq' := mem_nonzeroLocus_of_isTwistPull x.P.isLB _ _ _ _ _ α th s₁ hs₁ q (hq ▸ hp₁)
  obtain ⟨r, hr⟩ := translT_surjective x.P.A (U i₀).pt q
  have hr' := mem_nonzeroLocus_of_isTwistPull x.P.isLB _ _ _ _ _ (U i₀).φ s₁ (t i₀) ht r (hr ▸ hq')
  refine ⟨i₀, fun h0 => ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hr'
  have hz : (t i₀).f k = 0 := (GlobalTheory.UU.SecMod.eq_zero_iff_coord _).1 h0 k
  rw [hz, Scheme.basicOpen_zero] at hk
  exact hk
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateThetaPullbackNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translate_thetaPullback_ne_zero : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    ∃ i, (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)) ≠ 0 := by
  first | exact @GlobalTheory.TransNZ.exists_ne | exact GlobalTheory.TransNZ.exists_ne | (intros; apply GlobalTheory.TransNZ.exists_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfTwistedPullbacksSameBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfTwistedPullbacksSameBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TwistRatio

theorem exists_smul_of_isTwistPull : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) (m : ℕ), 1 ≤ m →
    ∀ (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
      (α α' : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp K)) P.A).left, (snd (baseOver (Sp K)) P.A ^ m).left]
        ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (s₁ s₁' : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), α.IsGen → α'.IsGen →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α' th s₁' →
    ∃ c : K, (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁' : EA P (𝟙 (Sp K)) (m ^ 2)) = c • SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁ := by
  intro K _ _ _ P m hm th α α' s₁ s₁' hα hα' h h'
  have hG := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨a, ha⟩ := H1.exists_const P.L P.isLB (fst (baseOver (Sp K)) P.A).left
    (BoxTheta.surj_fst hG P.isAb _)
    (LB.mulGen P.L _ _ _ _ α' (LB.invGen P.L _ _ α))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα' (DVR.invGen_isGen _ _ _ _ hα)) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 a
  refine ⟨c, DVR.SecOps.sec_ext fun j => ?_⟩
  refine sec_ext_val P.isLB (fun y J hJ => ?_) j
  have e1 := VVRank.sv_of_isTwistPull P.A h' (𝟙 _) y hJ
  have e0 := VVRank.sv_of_isTwistPull P.A h (𝟙 _) y hJ
  have ev := ha _ (𝟙 _) y J hJ
  rw [val_mul hJ, val_inv] at ev
  have es := SecMod.value_smul hJ (𝟙 _) c (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁)
  refine e1.trans (Eq.trans ?_ es.symm)
  have eg : gs (𝟙 _) y ⊤ (scal (fst (baseOver (Sp K)) P.A).left c) =
      gs (𝟙 _ ≫ (fst (baseOver (Sp K)) P.A).left) y ⊤
        ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv) c) :=
    gs_pull _ _ y ⊤ trivial _
  have eu : (val α' (𝟙 _) y J).val =
      (val α' (𝟙 _) y J * (val α (𝟙 _) y J)⁻¹).val * (val α (𝟙 _) y J).val := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  change _ = _ * VVRank.sv P.A s₁ (𝟙 _) y J
  rw [e0, eg, ← ev, eu, _root_.mul_assoc]

end GlobalTheory.TwistRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfTwistedPullbacksSameBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_of_twistedPullbacks_sameBundle : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) (m : ℕ), 1 ≤ m →
    ∀ (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
      (α α' : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp K)) P.A).left, (snd (baseOver (Sp K)) P.A ^ m).left]
        ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (s₁ s₁' : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), α.IsGen → α'.IsGen →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α' th s₁' →
    ∃ c : K, (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁' : EA P (𝟙 (Sp K)) (m ^ 2)) = c • SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁ := by
  first | exact @GlobalTheory.TwistRatio.exists_smul_of_isTwistPull | exact GlobalTheory.TwistRatio.exists_smul_of_isTwistPull | (intros; apply GlobalTheory.TwistRatio.exists_smul_of_isTwistPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanThetaTranslatesTorsionEqTop
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TSpan

noncomputable def actL {K : Type} [Field K] (P : PolAV (Sp K)) (k : ℕ)
    (ρ : ThetaGrp P.A P.L (k : ℤ) (baseOver (Sp K)) → (SecM P.A P.L (k : ℤ) (baseOver (Sp K)) ≃ₗ[Γ((baseOver (Sp K)).left, ⊤)] SecM P.A P.L (k : ℤ) (baseOver (Sp K))))
    (θ : ThetaGrp P.A P.L (k : ℤ) (baseOver (Sp K))) : EA P (𝟙 (Sp K)) k →ₗ[K] EA P (𝟙 (Sp K)) k where
  toFun w := SecMod.mk _ (SecM.toSec P.A (ρ θ (SecM.ofSec P.A w.sec)))
  map_add' a b := by
    show SecMod.mk _ (SecM.toSec P.A (ρ θ (SecM.ofSec P.A a.sec + SecM.ofSec P.A b.sec))) = _
    rw [map_add (f := _)]; rfl
  map_smul' c w := by
    show SecMod.mk _ (SecM.toSec P.A (ρ θ ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv c • SecM.ofSec P.A w.sec))) = _
    rw [map_smul]; rfl

theorem span_eq_top : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    Submodule.span K (Set.range fun i =>
      (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2))) = ⊤ := by
  intro K _ _ _ x m hm hm3 I pt hpt th hth U t hUt
  haveI : IsLocallyNoetherian (Sp K) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
  haveI := x.P.isAb.comm
  have hm0 : m ≠ 0 := by omega
  have hN : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero 2 hm0)
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero 2 hm0)
  obtain ⟨-, hirr⟩ := GlobalTheory.ThetaIrred.main GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 (Sp K) x.P K (𝟙 _) (m ^ 2) hN
  obtain ⟨ρ, hact, -, hrat, hmul⟩ := GlobalTheory.thetaGrp_acts_linearly GlobalTheory.allSixLaws.1.globalFns (Sp K) x.P ((m ^ 2 : ℕ) : ℤ)
    (baseOver (Sp K))
  let f := actL x.P (m ^ 2) ρ
  have hf : ∀ θ (a b : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), IsActOf x.P.A x.P.L _ θ a b →
      f θ (SecMod.mk _ a) = SecMod.mk _ b := fun θ a b h => by
    show SecMod.mk _ (SecM.toSec x.P.A (ρ θ (SecM.ofSec x.P.A a))) = _
    rw [(hact θ a b).1 h]; rfl
  have hf' : ∀ θ (a : LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
      IsActOf x.P.A x.P.L _ θ a (f θ (SecMod.mk _ a)).sec := fun θ a => (hact θ _ _).2 rfl

  have hker : ∀ θ : ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)), θ.pt ^ (m ^ 2) = 1 := fun θ =>
    (GlobalTheory.allSixLaws.1.kerPow (Sp K) x.P (m ^ 2) hN1 _ θ.pt).1 fun _ =>
      ⟨⊤, trivial, GlobalTheory.exists_isGen_pull _ θ.φ θ.isGen _⟩
  let Wsp := Submodule.span K (Set.range fun i =>
    (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)))
  refine (hirr Wsp fun θ hθ v v' hvv' hv => ?_).resolve_left fun h => ?_
  · have e0 : f θ v = v' := hf θ v.sec v'.sec hvv'
    rw [← e0]
    refine (Submodule.span_le.2 ?_ : Wsp ≤ Wsp.comap (f θ)) hv
    rintro _ ⟨i, rfl⟩
    obtain ⟨-, α, s₁, hα, -, htw, ha⟩ := hUt i
    obtain ⟨θ₂, hp₂, hv₂⟩ := hmul θ (U i)
    obtain ⟨k, hk⟩ := hpt (θ.pt * pt i) (by rw [mul_pow, hθ, ← (hUt i).1.pt_eq, hker, _root_.mul_one])
    obtain ⟨-, α', s₁', hα', -, htw', ha'⟩ := hUt k
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_smul_of_twistedPullbacks_sameBundle K x.P m (by omega) th α' α s₁' s₁ hα' hα htw' htw
    obtain ⟨d, hd⟩ := hrat (U k) θ₂ (by rw [hp₂, (hUt k).1.pt_eq, (hUt i).1.pt_eq, hk])
    have e : f θ (SecMod.mk _ (t i)) = f θ₂ (SecMod.mk _ s₁) := by
      rw [← hf _ _ _ ha]
      show SecMod.mk _ (SecM.toSec x.P.A (ρ θ _)) = SecMod.mk _ (SecM.toSec x.P.A (ρ θ₂ _))
      rw [hv₂]; rfl
    have e₂ : f θ₂ (SecMod.mk _ s₁) =
        ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (d : Γ((baseOver (Sp K)).left, ⊤))) • f (U k) (SecMod.mk _ s₁) := by
      show SecMod.mk _ (SecM.toSec x.P.A (ρ θ₂ _)) = _
      rw [hd]
      have e3 : (d : Γ((baseOver (Sp K)).left, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
          ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (d : Γ((baseOver (Sp K)).left, ⊤))) := by
        simp [Iso.commRingCatIsoToRingEquiv]
      conv_lhs => rw [e3]
      rfl
    show f θ (SecMod.mk _ (t i)) ∈ Wsp
    rw [e, e₂, hc, map_smul, hf _ _ _ ha']
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · obtain ⟨i, hi⟩ := GlobalTheory.T.exists_translate_thetaPullback_ne_zero K x m hm hm3 I pt hpt th hth U t hUt
    exact hi ((Submodule.eq_bot_iff _).1 h _ (Submodule.subset_span ⟨i, rfl⟩))

end GlobalTheory.TSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanThetaTranslatesTorsionEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_thetaTranslates_torsion_eq_top : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    Submodule.span K (Set.range fun i =>
      (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2))) = ⊤ := by
  first | exact @GlobalTheory.TSpan.span_eq_top | exact GlobalTheory.TSpan.span_eq_top | (intros; apply GlobalTheory.TSpan.span_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLineBundlePowSeparateFirstJetsOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLineBundlePowSeparateFirstJetsOrigin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.MBLow.JetSep

theorem sep : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (N : ℕ), 4 ≤ N → ∀ (i₀ : x.P.L.ι),
    ⊤ ≤ (𝟙 (Sp K) ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U i₀ → ∀ (j₀ : Fin g) (a : K) (c : Fin g → K),
    (∀ s : LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))),
      a * (valR (epsLift (x.v (j₀.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).fst +
        ∑ j, c j * (valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).snd = 0) →
    a = 0 ∧ c = 0 := by
  intro K _ x g hg N hN i₀ hi₀ j₀ a c H
  subst hg
  have := x.P.isAb.comm
  have k₀ : ⊤ ≤ eSec x.P.A ⁻¹ᵁ x.P.L.U i₀ := by simpa using hi₀
  let U' : x.P.A.left.Opens := (lbPow x.P.L N).U fun _ => i₀
  have hU' : ⊤ ≤ eSec x.P.A ⁻¹ᵁ U' :=
    (GlobalTheory.ThetaFn.le_wchart_unique x.P.L (K := PUnit) (eSec x.P.A) (𝟙 _) (fun _ => i₀)).2 (by simpa using k₀)
  let pb : (lbPow x.P.L N).Sec → LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))) := fun s =>
    GlobalTheory.ThetaFn.pullPow x.P.L (K := PUnit) (K' := Fin 1) (snd (baseOver (Sp K)) x.P.A).left
      (Category.comp_id _) (N : ℤ) s
  have hval : ∀ (s : (lbPow x.P.L N).Sec) (w : epsR K ⟶ x.P.A), IsTangent w →
      valR (epsLift w) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀) ((pb s).f fun _ => i₀) =
        valR w.left U' (s.f fun _ => i₀) := by
    intro s w hw
    have h1 : ⊤ ≤ epsLift w ⁻¹ᵁ ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀) := by
      refine (GlobalTheory.ThetaFn.le_wchart_unique x.P.L (K := Fin 1) (epsLift w) _ (fun _ => i₀)).2 ?_
      rw [JetUniq.epsLift_snd]
      exact JetUniq.tan_le hw k₀
    refine (GlobalTheory.HolHom.valR_appLE _ _ _ _ _ _ h1).trans ?_
    rw [JetUniq.epsLift_snd]
    rfl
  have Hs : ∀ s : (lbPow x.P.L N).Sec, a * valR (eSec x.P.A) U' (s.f fun _ => i₀) +
      (valR (tanComb c x.v).left U' (s.f fun _ => i₀)).snd = 0 := by
    intro s
    have e := H (pb s)
    simp only [Fin.cast_eq_self] at e
    rw [hval s _ (x.basis.1 j₀), JetUniq.fst_valR (x.basis.1 j₀) hU'] at e
    rw [JetUniq.snd_valR x.basis.1 (isLieComb_tanComb c x.v) hU']
    refine Eq.trans ?_ e
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hval s _ (x.basis.1 j)]
  obtain ⟨M, sec, hsec⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow GlobalTheory.allSixLaws.1.ample K x.P N hN
  have key : ∀ d : Fin x.P.g → K, d ≠ 0 → ∃ s₀ s₁ : (lbPow x.P.L N).Sec,
      valR (eSec x.P.A) U' (s₀.f fun _ => i₀) ≠ 0 ∧ valR (eSec x.P.A) U' (s₁.f fun _ => i₀) = 0 ∧
      (valR (tanComb d x.v).left U' (s₁.f fun _ => i₀)).snd ≠ 0 := by
    intro d hd
    have hy := isTangent_tanComb K x.P.A _ x.v d x.basis.1
    obtain ⟨s₀, s₁, h0, h1, h2⟩ := Orders.exists_sep sec hsec hy (Orders.tanComb_ne_one x.basis hd) (fun _ => i₀) hU'
    refine ⟨s₀, s₁, ?_, ?_, ?_⟩
    · rwa [Orders.valR_eq _ _ hU']
    · rwa [Orders.valR_eq _ _ hU']
    · rwa [Orders.valR_eq _ _ (Orders.top_le_tangent hy hU')]
  have hc : c = 0 := by
    by_contra hc
    obtain ⟨-, s₁, -, h1, h2⟩ := key c hc
    have e := Hs s₁
    rw [h1, mul_zero, zero_add] at e
    exact h2 e
  refine ⟨?_, hc⟩
  have hd : (Pi.single j₀ 1 : Fin x.P.g → K) ≠ 0 := fun h => by simpa using congrFun h j₀
  obtain ⟨s₀, -, h0, -, -⟩ := key _ hd
  have e := Hs s₀
  subst hc
  rw [JetUniq.snd_valR x.basis.1 (isLieComb_tanComb 0 x.v) hU'] at e
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] at e
  exact (mul_eq_zero.1 e).resolve_right h0

end GlobalTheory.MBLow.JetSep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsLineBundlePowSeparateFirstJetsOriginStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_lineBundlePow_separate_firstJets_origin : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (N : ℕ), 4 ≤ N → ∀ (i₀ : x.P.L.ι),
    ⊤ ≤ (𝟙 (Sp K) ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U i₀ → ∀ (j₀ : Fin g) (a : K) (c : Fin g → K),
    (∀ s : LB.Sec (LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))),
      a * (valR (epsLift (x.v (j₀.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).fst +
        ∑ j, c j * (valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L (N : ℤ) (baseOver (Sp K))).U fun _ => i₀)
          (s.f fun _ => i₀)).snd = 0) →
    a = 0 ∧ c = 0 := by
  first | exact @GlobalTheory.MBLow.JetSep.sep | exact GlobalTheory.MBLow.JetSep.sep | (intros; apply GlobalTheory.MBLow.JetSep.sep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionValueAbelianPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionValueAbelianPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.SecValLin
open GlobalTheory.SecJet.Orders

theorem valR_add' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valR x U (f + g) = valR x U f + valR x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valR_eq x U h, valR_eq x U h, valR_eq x U h, map_add (f := _)]
  · simp only [valR, dif_neg h, add_zero]

theorem valR_scal_mul {R A : Type} [CommRing R] [CommRing A] {X : Scheme.{0}} (ψ : R →+* A) (p : X ⟶ Sp R)
    (x : Sp A ⟶ X) (hx : x ≫ p = spMap ψ) (U : X.Opens) (c : R) (f : Γ(X, U)) :
    valR x U (resTop U (scal p c) * f) = ψ c * valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valR_eq x U h, valR_eq x U h, map_mul]
    have e : resTop U (scal p c) = Geo.Tor.constFn p U c := rfl
    rw [e, vh_const ψ p x hx U h c]
  · simp only [valR, dif_neg h, mul_zero]

theorem exists_linear_valR_sec : ∀ (K : Type) [Field K] (x : KeyIn K) (N : ℕ) (i : Fin 1 → x.P.L.ι) (B : Type) [CommRing B] [Algebra K B]
    (y : Sp B ⟶ (baseOver (Sp K) ⊗ x.P.A).left),
    y ≫ (fst (baseOver (Sp K)) x.P.A).left = spMap (algebraMap K B) →
    ∃ f : EA x.P (𝟙 (Sp K)) N →ₗ[K] B, ∀ s : EA x.P (𝟙 (Sp K)) N,
      f s = valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i) := by
  intro K _ x N i B _ _ y hy
  refine ⟨⟨⟨fun s => valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i),
    fun s t => valR_add' y _ _ _⟩, fun c s => ?_⟩, fun s => rfl⟩
  show valR y _ (resTop _ (scal _ c) * s.sec.f i) = _
  rw [valR_scal_mul (algebraMap K B) _ y hy, RingHom.id_apply, Algebra.smul_def]

end GlobalTheory.SecValLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionValueAbelianPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_sectionValue_abelianPower : ∀ (K : Type) [Field K] (x : KeyIn K) (N : ℕ) (i : Fin 1 → x.P.L.ι) (B : Type) [CommRing B] [Algebra K B]
    (y : Sp B ⟶ (baseOver (Sp K) ⊗ x.P.A).left),
    y ≫ (fst (baseOver (Sp K)) x.P.A).left = spMap (algebraMap K B) →
    ∃ f : EA x.P (𝟙 (Sp K)) N →ₗ[K] B, ∀ s : EA x.P (𝟙 (Sp K)) N,
      f s = valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i) := by
  first | exact @GlobalTheory.SecValLin.exists_linear_valR_sec | exact GlobalTheory.SecValLin.exists_linear_valR_sec | (intros; apply GlobalTheory.SecValLin.exists_linear_valR_sec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFirstJetsLinearIndependent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.MBLow.TRank

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) → ∀ ϑ J, ThJet x hg m pt ϑ J → ∀ (c₀ : K) (c : Fin g → K), (∀ i, c₀ * ϑ i + ∑ j, c j * J i j = 0) → c₀ = 0 ∧ c = 0 := by
  intro K _ _ _ x g hg m hm hm3 I pt hpt ϑ J hTJ c₀ c hrel
  obtain ⟨th, hth, U, t, i₀, c', hUt, hi₀, hval⟩ := hTJ
  have hg1 : 1 ≤ g := hg ▸ x.g_pos
  let j₀ : Fin g := ⟨0, hg1⟩
  have hy : ∀ j : Fin g, epsLift (x.v (j.cast hg.symm)) ≫ (fst (baseOver (Sp K)) x.P.A).left =
      spMap (algebraMap K (DualNumber K)) := fun j => by
    rw [epsLift, ← Over.comp_left, lift_fst]; rfl
  choose f hf using fun j : Fin g => GlobalTheory.T.exists_linear_sectionValue_abelianPower K x (m ^ 2) (fun _ => i₀) (DualNumber K) _ (hy j)
  set a := c₀ - ∑ j, c j * c' j with ha
  let Φ : EA x.P (𝟙 (Sp K)) (m ^ 2) →ₗ[K] K :=
    a • ((TrivSqZeroExt.fstHom K K K).toLinearMap ∘ₗ f j₀) + ∑ j, c j • (TrivSqZeroExt.sndHom K K ∘ₗ f j)
  have hΦ : ∀ s, Φ s = a * (f j₀ s).fst + ∑ j, c j * (f j s).snd := fun s => by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
    rfl
  have hft : ∀ j i, f j (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) =
      valR (epsLift (x.v (j.cast hg.symm))) ((LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K))).U fun _ => i₀)
        ((t i).f fun _ => i₀) := fun j i => hf j _
  have hΦt : ∀ i, Φ (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i)) = 0 := fun i => by
    rw [hΦ]
    simp only [hft, hval]
    set r := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val ^ (m ^ 2)
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add, mul_zero, zero_mul]
    have e1 : ∑ j, c j * (r * (J i j + c' j * ϑ i)) = r * ∑ j, c j * J i j + r * ϑ i * ∑ j, c j * c' j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, ha]
    linear_combination r * hrel i
  have hspan := GlobalTheory.T.span_thetaTranslates_torsion_eq_top K x m hm hm3 I pt hpt th hth U t hUt
  have hΦ0 : Φ = 0 := LinearMap.ext_on_range hspan fun i => by rw [hΦt i, LinearMap.zero_apply]
  have hsep := GlobalTheory.T.sections_lineBundlePow_separate_firstJets_origin K x g hg (m ^ 2) (by nlinarith) i₀ hi₀ j₀ a c fun s => by
    have h := congrArg (fun F => F (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left s)) hΦ0
    simp only [LinearMap.zero_apply, hΦ] at h
    rw [hf j₀, Finset.sum_congr rfl fun j _ => by rw [hf j]] at h
    exact h
  obtain ⟨h1, h2⟩ := hsep
  refine ⟨?_, h2⟩
  subst h2
  simpa [ha] using h1

end GlobalTheory.MBLow.TRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFirstJetsLinearIndependentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_firstJets_linearIndependent : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → 3 ≤ m → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) → ∀ ϑ J, ThJet x hg m pt ϑ J → ∀ (c₀ : K) (c : Fin g → K), (∀ i, c₀ * ϑ i + ∑ j, c j * J i j = 0) → c₀ = 0 ∧ c = 0 := by
  first | exact @GlobalTheory.MBLow.TRank.main | exact GlobalTheory.MBLow.TRank.main | (intros; apply GlobalTheory.MBLow.TRank.main <;> assumption)
end
