module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedTrans
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPeriodRingSeparation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalProperty

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyVectorBundleRank
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle

theorem exists_base {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (B : Type) [CommRing B] [Algebra R B] :
    ∃ (A' : Over (Sp B)) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R B)) := by
  have h := isGrpPullback_pullback A (spMap (algebraMap R B))
  obtain ⟨h1, h2⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ _ _ _ g h hA hg
  exact ⟨_, inferInstance, _, h1, h2, h.1⟩

theorem vb_of_bijective {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F) n) : VB R (H1 F') n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1, Module.Projective.of_equiv E1, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

theorem vb_of_bijective' {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
    {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R} (m : CoefMap (RingHom.id R) F F')
    (h1 : Function.Bijective m.pull1) {n : ℕ} (h : VB R (H1 F') n) : VB R (H1 F) n := by
  let E1 : H1 F ≃ₗ[R] H1 F' := LinearEquiv.ofBijective m.pull1 h1
  obtain ⟨hf, hp, hr⟩ := h
  refine ⟨Module.Finite.equiv E1.symm, Module.Projective.of_equiv E1.symm, fun p => ?_⟩
  rw [Module.rankAtStalk_eq_of_equiv E1]
  exact hr p

theorem finrank_of_vb {k M : Type} [Field k] [AddCommGroup M] [Module k M] {n : ℕ} (h : VB k M n) :
    Module.finrank k M = n := by
  obtain ⟨hf, -, hr⟩ := h
  have e := hr ⊥
  rwa [Module.rankAtStalk_eq_finrank_of_free] at e

theorem first_cohomology_vector_bundle_rank : DescentSt → LowSt → SysBCSt → PerfSt → SteinSt → H1StructureFieldDim → SmallLiftSt → PerfVBSt → H1StructureBundle := by
  intro hD hL hB hP hS hK hT hV R _ A _ g hA hg
  have : IsProper A.hom := hA.proper
  have : IsSeparated A.hom := inferInstance
  have : Smooth A.hom := hg.smooth
  obtain ⟨P, iP, fP, S, hPerf⟩ := hP R A.left A.hom inferInstance inferInstance
  have low : ∀ {R₀ : Type} [CommRing R₀] (A₀ : Over (Sp R₀)) [GrpObj A₀], IsAbelianScheme A₀ →
      ∀ (S₀ : Sys A₀.left P), Function.Bijective (resSys A₀.hom S₀).pull1 ∧
        (Stein (OAff A₀.hom) ↔ Stein (OSys A₀.hom S₀)) := fun {R₀} _ A₀ _ h₀ S₀ => by
    have : IsProper A₀.hom := h₀.proper
    obtain ⟨b1, -, st⟩ := hL R₀ _ _ (OAff A₀.hom) (OSys A₀.hom S₀) (resSys A₀.hom S₀)
      (hD R₀ A₀.left A₀.hom inferInstance P S₀)
    exact ⟨b1, st⟩
  refine vb_of_bijective' (resSys A.hom S) (low A hA S).1 (hV R P (OSys A.hom S) g hPerf ?_ ?_ ?_)
  · intro R' _ _
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg R'
    obtain ⟨S', m, -⟩ := hB R R' A.left A'.left A.hom A'.hom φ h inferInstance P S
    exact ⟨OSys A'.hom S', m, (low A' hA' S').2.1 (hS R' A' g hA' hg')⟩
  · intro k _ _
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg k
    obtain ⟨S', m, -⟩ := hB R k A.left A'.left A.hom A'.hom φ h inferInstance P S
    exact ⟨OSys A'.hom S', m, finrank_of_vb
      (vb_of_bijective _ (low A' hA' S').1 (hK k A' g hA' hg' (Field.toIsField k)))⟩
  · intro B _ _ _ t ht
    obtain ⟨A', _, φ, hA', hg', h⟩ := exists_base A hA hg B
    obtain ⟨S', m, -⟩ := hB R B A.left A'.left A.hom A'.hom φ h inferInstance P S
    obtain ⟨A'', _, φ', hA'', hg'', h'⟩ := exists_base A' hA' hg' (B ⧸ Ideal.span {t})
    have : IsProper A'.hom := hA'.proper
    obtain ⟨S'', m', hm'⟩ := hB B (B ⧸ Ideal.span {t}) A'.left A''.left A'.hom A''.hom φ' h' inferInstance P S'
    refine ⟨OSys A'.hom S', m, OSys A''.hom S'', m', fun y => ?_⟩
    have b2 := (low A'' hA'' S'').1
    obtain ⟨d, rfl⟩ := b2.2 y
    obtain ⟨c, hc⟩ := hT B A' g hA' hg' t ht A''.left A''.hom φ' h' d
    refine ⟨(resSys A'.hom S').pull1 c, ?_⟩
    obtain ⟨d', hd'⟩ := b2.2 (m'.coef.pull1 ((resSys A'.hom S').pull1 c))
    have e := (existsUnique_isPullO h'.w c).unique hc (hm' c d' hd'.symm)
    rw [e, hd']

end GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuot
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerAct

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d}

def val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : T.1.A :=
  PAlg.Hom.f φ.1 (𝒯.c k 0).val

theorem val_comp (𝒯 : Tower κ s) {T T' : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (ψ : T ⟶ T') (k : Fin d) :
    val 𝒯 (φ ≫ ψ) k = PAlg.Hom.f ψ.1 (val 𝒯 φ k) := rfl

theorem sharp_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    T.1.sharp (val 𝒯 φ k) = mapU φ.1 (𝒯.g (s.T k)) := by
  rw [val, ← mapU_sharp]
  exact congrArg (mapU φ.1) (𝒯.c_sharp k)

def valU (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : (T.1.A)ˣ :=
  Units.map (PAlg.Hom.f φ.1).toMonoidHom (𝒯.c k 0)

theorem valU_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    ((valU 𝒯 φ k : (T.1.A)ˣ) : T.1.A) = val 𝒯 φ k := rfl

theorem hom_ext (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T)
    (h : ∀ k, val 𝒯 φ k = val 𝒯 ψ k) : φ = ψ := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, -, hχ⟩ := huniq (fun k => val 𝒯 φ k) hu
  exact (hχ φ (fun k => rfl)).trans (hχ ψ (fun k => (h k).symm)).symm

theorem sharp_mem (ε : Eps l) {T : (F.pt κ).Elements} (x : (epsU ε (F.pt κ)).U T) :
    T.1.sharp ((x.1 : (T.1.A)ˣ) : T.1.A) = 1 := by
  have hx : Units.map T.1.sharp x.1 = 1 := x.2
  exact congrArg Units.val hx

theorem exists_act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) :
    ∃ ψ : 𝒯.obj ⟶ T, ∀ k, val 𝒯 ψ k = ((a k).1 : T.1.A) * val 𝒯 φ k := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (((a k).1 : T.1.A) * val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [map_mul, sharp_mem ε (a k), one_mul, sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, hχ, -⟩ := huniq _ hu
  exact ⟨χ, fun k => hχ k⟩

def act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) : 𝒯.obj ⟶ T :=
  (exists_act 𝒯 ε a φ).choose

theorem act_val (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    val 𝒯 (act 𝒯 ε a φ) k = ((a k).1 : T.1.A) * val 𝒯 φ k :=
  (exists_act 𝒯 ε a φ).choose_spec k

theorem exists_quot (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T) :
    ∃ a : Fin d → (epsU ε (F.pt κ)).U T, ∀ k, ((a k).1 : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k := by
  obtain ⟨g, -, hg, -⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hs : ∀ (χ : 𝒯.obj ⟶ T) k, T.1.sharp (val 𝒯 χ k) = g (s.T k) := fun χ k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg χ) _
  refine ⟨fun k => ⟨valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹, ?_⟩, fun k => ?_⟩
  · show Units.map T.1.sharp (valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, valU_val, valU_val, hs ψ k, hs φ k]
  · show ((valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹ : (T.1.A)ˣ) : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k
    rw [← valU_val 𝒯 φ k, ← Units.val_mul, inv_mul_cancel_right, valU_val]

theorem act_unique (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a b : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (h : act 𝒯 ε a φ = act 𝒯 ε b φ) : a = b := by
  funext k
  have h1 := act_val 𝒯 ε a φ k
  rw [h, act_val, ← valU_val 𝒯 φ k] at h1
  apply Subtype.ext
  apply Units.ext
  exact ((valU 𝒯 φ k).isUnit.mul_left_inj).1 h1.symm

theorem tower_act : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (ε : Eps l), ∃ A : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj, ∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d), PAlg.Hom.f (A.act a φ).1 (𝒯.c k 0).val = ((a k).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c k 0).val := by
  intro l _ O _ F κ d s 𝒯 ε
  refine ⟨{ act := fun a φ => act 𝒯 ε a φ
            act_one := fun c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val]
              exact one_mul _
            act_mul := fun a b c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val, act_val, act_val, ← mul_assoc]
              rfl
            act_comp := fun a c φ => hom_ext 𝒯 _ _ fun k => by
              rw [val_comp, act_val, act_val, val_comp, map_mul]
              rfl
            ne := fun t => by
              obtain ⟨g, -, -, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 ((jE (F.pt κ)).obj t)
              choose u hu using fun k => PAlg.IsTest.sharp_surjective t.1.property (g (s.T k))
              obtain ⟨χ, -, -⟩ := huniq u hu
              exact ⟨χ⟩
            trans := fun t c c' => by
              obtain ⟨a, ha⟩ := exists_quot 𝒯 ε c c'
              have hac : act 𝒯 ε a c = c' := hom_ext 𝒯 _ _ fun k => by rw [act_val, ha]
              exact ⟨a, hac, fun b hb => act_unique 𝒯 ε b a c (hb.trans hac.symm)⟩ }, ?_⟩
  intro T a φ k
  exact act_val 𝒯 ε a φ k

end GlobalTheory.CompanionTheory.TowerAct
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrToContInjective
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContLine

variable {l : ℕ} [Fact l.Prime]

theorem toCont_ev (A : PAlg l) (z : ℤ_[l]) : A.toCont ℤ_[l] ≫ A.evCont z = 𝟙 A :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem shift_ev (A : PAlg l) (z : ℤ_[l]) : contShift A ≫ A.evCont z = A.evCont (z + 1) :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem toCont_shift (A : PAlg l) : A.toCont ℤ_[l] ≫ contShift A = A.toCont ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem toCont_contMap {A B : PAlg l} (φ : A ⟶ B) :
    A.toCont ℤ_[l] ≫ contMap φ ℤ_[l] = φ ≫ B.toCont ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_id (A : PAlg l) : contMap (𝟙 A) ℤ_[l] = 𝟙 (A.cont ℤ_[l]) :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_comp {A B C : PAlg l} (φ : A ⟶ B) (ψ : B ⟶ C) :
    contMap (φ ≫ ψ) ℤ_[l] = contMap φ ℤ_[l] ≫ contMap ψ ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_shift {A B : PAlg l} (φ : A ⟶ B) :
    contMap φ ℤ_[l] ≫ contShift B = contShift A ≫ contMap φ ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

def Xi (P : PAlg l ⥤ Type) : P.Elements ⥤ P.Elements where
  obj T := P.elementsMk (T.obj.cont ℤ_[l]) (P.map (T.obj.toCont ℤ_[l]) T.val)
  map {T T'} φ := Functor.Elements.homMk (contMap φ.hom ℤ_[l]) (by
    rw [← Functor.map_comp_apply, toCont_contMap, Functor.map_comp_apply, φ.map_val])
  map_id T := Functor.Elements.hom_ext (contMap_id T.obj)
  map_comp φ ψ := Functor.Elements.hom_ext (contMap_comp φ.hom ψ.hom)

def iota (P : PAlg l ⥤ Type) : 𝟭 P.Elements ⟶ Xi P where
  app T := Functor.Elements.homMk (T.obj.toCont ℤ_[l]) rfl
  naturality T T' φ := Functor.Elements.hom_ext (toCont_contMap φ.hom).symm

def gam (P : PAlg l ⥤ Type) : Xi P ⟶ Xi P where
  app T := Functor.Elements.homMk (contShift T.obj) (by
    change P.map (contShift T.obj) (P.map (T.obj.toCont ℤ_[l]) T.val) =
      P.map (T.obj.toCont ℤ_[l]) T.val
    rw [← Functor.map_comp_apply, toCont_shift])
  naturality T T' φ := Functor.Elements.hom_ext (contMap_shift φ.hom)

def eta₀ (ε : Eps l) : (((base l).cont ℤ_[l]).A)ˣ := (GlobalTheory.T.continuous_algebra_universal_property ε).choose

theorem eta₀_sharp (ε : Eps l) : ((base l).cont ℤ_[l]).sharp (eta₀ ε) = 1 :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.1

theorem eta₀_shift (ε : Eps l) :
    PAlg.Hom.f (contShift (base l)) (eta₀ ε) = ((base l).cont ℤ_[l]).s (ε.e 0) * eta₀ ε :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.2.1

theorem eta₀_univ (ε : Eps l) (A t : PAlg l) (ht : t.IsTest) (φ : A ⟶ t) (u : (t.A)ˣ) (hu : t.sharp u = 1) :
    ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧
      PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε)) = u :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.2.2 A t ht φ u hu

def eta (ε : Eps l) (A : PAlg l) : ((A.cont ℤ_[l]).A)ˣ :=
  Units.map (PAlg.Hom.f (contMap A.fromBase ℤ_[l])).toMonoidHom (eta₀ ε)

theorem eta_val (ε : Eps l) (A : PAlg l) :
    ((eta ε A : ((A.cont ℤ_[l]).A)ˣ) : (A.cont ℤ_[l]).A) = PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε) := rfl

theorem eta_sharp (ε : Eps l) (A : PAlg l) : (A.cont ℤ_[l]).sharp (eta ε A) = 1 := by
  rw [eta_val, ← mapU_sharp, eta₀_sharp, map_one]

theorem eta_map (ε : Eps l) {A B : PAlg l} (φ : A ⟶ B) :
    PAlg.Hom.f (contMap φ ℤ_[l]) (eta ε A) = eta ε B := by
  rw [eta_val, eta_val, ← fromBase_comp A φ, contMap_comp]
  rfl

theorem eta_shift (ε : Eps l) (A : PAlg l) :
    PAlg.Hom.f (contShift A) (eta ε A) = (A.cont ℤ_[l]).s (ε.e 0) * eta ε A := by
  have h : PAlg.Hom.f (contShift A) (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε)) =
      PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (PAlg.Hom.f (contShift (base l)) (eta₀ ε)) :=
    congrArg (fun f => PAlg.Hom.f f (eta₀ ε)) (contMap_shift A.fromBase).symm ▸ rfl
  rw [eta_val, h, eta₀_shift, map_mul]
  exact congrArg (· * _) (RingHom.congr_fun (Hom.comm (contMap A.fromBase ℤ_[l])) (ε.e 0 : Ob l))

def line (ε : Eps l) (P : PAlg l ⥤ Type) : Line (jE P) (epsU ε P) where
  Ξ := Xi P
  i := iota P
  η T := ⟨eta ε T.obj, MonoidHom.mem_ker.2 (Units.ext (eta_sharp ε T.obj))⟩
  map_η φ := Subtype.ext (Units.ext (eta_map ε φ.hom))
  γ := gam P
  iγ := NatTrans.ext (funext fun T => Functor.Elements.hom_ext (toCont_shift T.obj))
  γη T := Subtype.ext (Units.ext (eta_shift ε T.obj))
  univ T t φ a := by
    have ha : t.obj.obj.sharp (a.1).1 = 1 := congrArg Units.val (MonoidHom.mem_ker.1 a.2)
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := eta₀_univ ε T.obj t.obj.obj t.obj.property φ.hom a.1 ha
    have hψ : P.map ψ (P.map (T.obj.toCont ℤ_[l]) T.val) = t.val := by
      rw [← Functor.map_comp_apply, h1]
      exact φ.map_val
    refine ⟨Functor.Elements.homMk ψ hψ, ⟨Functor.Elements.hom_ext h1, Subtype.ext (Units.ext h2)⟩, ?_⟩
    rintro ⟨ψ', h'⟩ ⟨e1, e2⟩
    refine Functor.Elements.hom_ext (hu ψ' ⟨congrArg Functor.Elements.Hom.hom e1, ?_⟩)
    exact congrArg (fun x => (x.1).1) e2

theorem acr_ev_const (A : PAlg l) (n : ℕ) (z : ℤ_[l]) (a : A.Acr n) :
    mapAcr (A.evCont z) n (mapAcr (A.toCont ℤ_[l]) n a) = a := by
  rw [← mapAcr_comp, toCont_ev, mapAcr_id]

theorem acr_ev_shift (A : PAlg l) (n : ℕ) (z : ℤ_[l]) (x : (A.cont ℤ_[l]).Acr n) :
    mapAcr (A.evCont z) n (mapAcr (contShift A) n x) = mapAcr (A.evCont (z + 1)) n x := by
  rw [← mapAcr_comp, shift_ev]

theorem acr_toCont_injective (A : PAlg l) (n : ℕ) : Function.Injective (mapAcr (A.toCont ℤ_[l]) n) :=
  Function.LeftInverse.injective (g := mapAcr (A.evCont 0) n) (acr_ev_const A n 0)

theorem map_mem_map {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : A.Acr n}
    (hx : x ∈ 𝔞.map (mapAcr A.fromBase n)) : mapAcr f n x ∈ 𝔞.map (mapAcr B.fromBase n) := by
  have h : 𝔞.map (mapAcr A.fromBase n) ≤ (𝔞.map (mapAcr B.fromBase n)).comap (mapAcr f n) :=
    Ideal.map_le_iff_le_comap.2 fun a ha => by
      rw [Ideal.mem_comap, Ideal.mem_comap, mapAcr_fromBase]
      exact Ideal.mem_map_of_mem _ ha
  exact h hx

theorem fixed_const (A : PAlg l) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : (A.cont ℤ_[l]).Acr n}
    (hx : x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n)) (hg : mapAcr (contShift A) n x = x) :
    ∃ m ∈ 𝔞.map (mapAcr A.fromBase n), mapAcr (A.toCont ℤ_[l]) n m = x := by
  obtain ⟨hlc, hinj, -⟩ := GlobalTheory.T.continuous_functions_period_ring_separation A n
  have hper : ∀ z, mapAcr (A.evCont z) n x = mapAcr (A.evCont 0) n x :=
    GlobalTheory.CompanionTheory.PadicShift.eq_of_shift_invariant l _ (hlc x) fun z => by
      rw [← acr_ev_shift, hg]
  refine ⟨mapAcr (A.evCont 0) n x, map_mem_map _ n 𝔞 hx, ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun z => ?_
  rw [map_sub, acr_ev_const, hper z, sub_self]

theorem shift_surj (A : PAlg l) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : (A.cont ℤ_[l]).Acr n}
    (hx : x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n)) :
    ∃ y ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n), mapAcr (contShift A) n y - y = x := by
  obtain ⟨hlc, hinj, hex⟩ := GlobalTheory.T.continuous_functions_period_ring_separation A n
  let f : ℤ_[l] → ↥(𝔞.map (mapAcr A.fromBase n)) := fun z =>
    ⟨mapAcr (A.evCont z) n x, map_mem_map _ n 𝔞 hx⟩
  have hf : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun z => ?_
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hlc x) z] with w hw
    exact Subtype.ext hw
  have hN : ∀ a : ↥(𝔞.map (mapAcr A.fromBase n)), l ^ n • a = 0 := fun a => Subtype.ext (by
    change l ^ n • (a.1 : A.Acr n) = 0
    rw [nsmul_eq_mul, Nat.cast_pow, A.pow_l_acr n, zero_mul])
  obtain ⟨y, hy, hd⟩ := GlobalTheory.CompanionTheory.PadicShift.exists_primitive l n hN f hf
  obtain ⟨w, hw, hwz⟩ := hex 𝔞 (fun z => (y z).1) (hy.comp _) fun z => (y z).2
  refine ⟨w, hw, ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun z => ?_
  rw [map_sub, map_sub, acr_ev_shift, hwz, hwz, sub_eq_zero]
  exact congrArg Subtype.val (hd z)

theorem facyc_of {R : Type} [CommRing R] {C : Type*} [Category C] {G : C ⥤ ModuleCat.{0} R} (Φ : Flt G) {T T' : C}
    (i : T ⟶ T') (g : T' ⟶ T') (h1 : Function.Injective (G.map i).hom)
    (h2 : ∀ r, ∀ x ∈ (Φ.S r).S T', (G.map g).hom x = x → ∃ m, m ∈ (Φ.S r).S T ∧ (G.map i).hom m = x)
    (h3 : ∀ r, ∀ x ∈ (Φ.S r).S T', ∃ y, y ∈ (Φ.S r).S T' ∧ (G.map g).hom y - y = x) : Φ.FAcyc i g := by
  refine ⟨h1, fun r x hx hg => ?_, fun r x hx => ?_⟩
  · obtain ⟨m, hm, hmx⟩ := h2 r x hx hg
    exact ⟨_, Φ.mul r T m hm, by rw [map_smul, hmx]⟩
  · obtain ⟨y, hy, hyx⟩ := h3 r x hx
    exact ⟨_, Φ.mul r T' y hy, by rw [map_smul, ← smul_sub, hyx]⟩

section Main

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)

theorem mem_step (r : ℕ) (T : (F.pt κ).Elements) (x : T.1.Acr n) :
    x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S T ↔
      x ∈ (fil (DD k (base l) n) (ρ r)).map (mapAcr T.1.fromBase n) := by
  rw [← (GlobalTheory.T.period_ring_base_change_from_universal T.1 n).2.2.2.2.1 k (ρ r)]
  rfl

theorem step_fixed (T : (F.pt κ).Elements) (r : ℕ) (x : (T.1.cont ℤ_[l]).Acr n)
    (hx : x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T))
    (hg : mapAcr (contShift T.1) n x = x) :
    ∃ m : T.1.Acr n, m ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S T ∧
      mapAcr (T.1.toCont ℤ_[l]) n m = x := by
  obtain ⟨m, hm, hmx⟩ := fixed_const T.1 n _ ((mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) x).1 hx) hg
  exact ⟨m, (mem_step F κ ε k n ρ hρ r T m).2 hm, hmx⟩

theorem step_surj (T : (F.pt κ).Elements) (r : ℕ) (x : (T.1.cont ℤ_[l]).Acr n)
    (hx : x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T)) :
    ∃ y : (T.1.cont ℤ_[l]).Acr n, y ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T) ∧
      mapAcr (contShift T.1) n y - y = x := by
  obtain ⟨y, hy, hyx⟩ := shift_surj T.1 n _ ((mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) x).1 hx)
  exact ⟨y, (mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) y).2 hy, hyx⟩

theorem facyc (T : (F.pt κ).Elements) :
    ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc ((line ε (F.pt κ)).i.app T) ((line ε (F.pt κ)).γ.app T) :=
  facyc_of _ _ _ (acr_toCont_injective T.1 n) (fun r x hx hg => step_fixed F κ ε k n ρ hρ T r x hx hg)
    (fun r x hx => step_surj F κ ε k n ρ hρ T r x hx)

end Main

theorem exists_line : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), ∃ L : Line (jE (F.pt κ)) (epsU ε (F.pt κ)), ∀ T, ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc (L.i.app T) (L.γ.app T) :=
  fun F κ ε k n ρ hρ => ⟨line ε (F.pt κ), facyc F κ ε k n ρ hρ⟩

end GlobalTheory.CompanionTheory.ContLine
end
end
