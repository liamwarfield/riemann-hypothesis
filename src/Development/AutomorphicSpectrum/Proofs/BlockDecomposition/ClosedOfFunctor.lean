module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem eq_zero_of_pow_mul {R : Type} [CommRing R] (s : Set R) (hs : Ideal.span s = ⊤) (b : R)
    (h : ∀ a ∈ s, ∃ n : ℕ, a ^ n * b = 0) : b = 0 := by
  let K : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R b)
  have hK : K.radical = ⊤ := by
    rw [eq_top_iff, ← hs, Ideal.span_le]
    intro a ha
    obtain ⟨n, hn⟩ := h a ha
    exact ⟨n, by simpa [K, LinearMap.mem_ker] using hn⟩
  have h1 : (1 : R) ∈ K := by
    rw [Ideal.radical_eq_top.1 hK]; trivial
  simpa [K, LinearMap.mem_ker] using h1

theorem exists_pow_mul_of_away {R : Type} [CommRing R] (a x : R)
    (h : algebraMap R (Localization.Away a) x = 0) : ∃ n : ℕ, a ^ n * x = 0 := by
  obtain ⟨⟨_, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) (Localization.Away a) x).1 h
  exact ⟨n, hm⟩

theorem isUnit_away {R : Type} [CommRing R] (a : R) : IsUnit (algebraMap R (Localization.Away a) a) :=
  IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a

theorem exists_ideal_of_local {R : Type} [CommRing R] (Q : ∀ (R' : Type) [CommRing R'], (R →+* R') → Prop)
    (stab : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (g : R →+* R') (h : R' →+* R''), Q R' g → Q R'' (h.comp g))
    (loc : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (s : Set R'), Ideal.span s = ⊤ →
      (∀ a ∈ s, Q (Localization.Away a) ((algebraMap R' _).comp g)) → Q R' g)
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤) (I : R → Ideal R)
    (hI : ∀ f ∈ s, ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g f) → (Q R' g ↔ I f ≤ RingHom.ker g)) :
    ∃ J : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Q R' g ↔ J ≤ RingHom.ker g := by
  classical
  let B : R → Type := fun f => Localization.Away (Ideal.Quotient.mk (I f) f)
  let b : ∀ f, R →+* B f := fun f => (algebraMap (R ⧸ I f) (B f)).comp (Ideal.Quotient.mk (I f))
  have bu : ∀ f, IsUnit (b f f) := fun f => isUnit_away _
  have bI : ∀ f, I f ≤ RingHom.ker (b f) := fun f x hx => by
    simp [b, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  have bQ : ∀ f ∈ s, Q (B f) (b f) := fun f hf => (hI f hf _ _ (bu f)).2 (bI f)

  have fac : ∀ f ∈ s, ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Q R' g → IsUnit (g f) →
      ∃ h : B f →+* R', h.comp (b f) = g := fun f hf R' _ g hq hu => by
    have hle := (hI f hf R' g hu).1 hq
    let g₁ : R ⧸ I f →+* R' := Ideal.Quotient.lift (I f) g fun x hx => hle hx
    have hu' : IsUnit (g₁ (Ideal.Quotient.mk (I f) f)) := by
      rw [show g₁ (Ideal.Quotient.mk (I f) f) = g f from Ideal.Quotient.lift_mk _ _ _]; exact hu
    refine ⟨IsLocalization.Away.lift (S := B f) (Ideal.Quotient.mk (I f) f) hu', ?_⟩
    ext x
    change IsLocalization.Away.lift (S := B f) (Ideal.Quotient.mk (I f) f) hu' (algebraMap (R ⧸ I f) (B f) (Ideal.Quotient.mk (I f) x)) = g x
    rw [IsLocalization.Away.lift_eq]
    exact Ideal.Quotient.lift_mk _ _ _

  refine ⟨⨅ f ∈ s, RingHom.ker (b f), fun R' _ g => ⟨fun hq a ha => ?_, fun hJ => ?_⟩⟩
  · have ha' : ∀ f ∈ s, b f a = 0 := fun f hf => by
      have := (Submodule.mem_iInf _).1 ha f
      exact (Submodule.mem_iInf _).1 this hf
    refine eq_zero_of_pow_mul (g '' (s : Set R)) ?_ (g a) ?_
    · rw [← Ideal.map_span, hs, Ideal.map_top]
    · rintro _ ⟨f, hf, rfl⟩
      let L := Localization.Away (g f)
      obtain ⟨h, hh⟩ := fac f hf L ((algebraMap R' L).comp g) (stab _ _ _ _ hq)
        (isUnit_away _)
      apply exists_pow_mul_of_away
      have := congrArg (fun q => q a) hh
      simpa [ha' f hf] using this.symm
  · set J : Ideal R := ⨅ f ∈ s, RingHom.ker (b f) with hJdef
    suffices H : Q (R ⧸ J) (Ideal.Quotient.mk J) by
      have := stab _ _ _ (Ideal.Quotient.lift J g fun x hx => hJ hx) H
      have e : (Ideal.Quotient.lift J g fun x hx => hJ hx).comp (Ideal.Quotient.mk J) = g := by
        exact RingHom.ext fun x => Ideal.Quotient.lift_mk J g fun x hx => hJ hx
      rwa [e] at this
    refine loc _ _ (Ideal.Quotient.mk J '' (s : Set R)) (by rw [← Ideal.map_span, hs]; exact Ideal.map_top _) ?_
    rintro _ ⟨f, hf, rfl⟩
    refine (hI f hf _ ((algebraMap (R ⧸ J) (Localization.Away (Ideal.Quotient.mk J f))).comp (Ideal.Quotient.mk J))
      (isUnit_away (Ideal.Quotient.mk J f))).2 fun x hx => ?_
    have key : ∀ f' ∈ s, ∃ n : ℕ, b f' f ^ n * b f' x = 0 := fun f' hf' => by
      let L := Localization.Away (b f' f)
      have h1 := (hI f hf L ((algebraMap (B f') L).comp (b f')) (isUnit_away _)).1
        (stab _ _ _ _ (bQ f' hf'))
      exact exists_pow_mul_of_away _ _ (h1 hx)
    choose! n hn using key
    have hmem : Ideal.Quotient.mk J f ^ (s.sup n) * Ideal.Quotient.mk J x = 0 := by
      rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      refine (Submodule.mem_iInf _).2 fun f' => (Submodule.mem_iInf _).2 fun hf' => ?_
      have hle : n f' ≤ s.sup n := Finset.le_sup hf'
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [RingHom.mem_ker, map_mul, map_pow, hd, pow_add, mul_comm (b f' f ^ n f'), _root_.mul_assoc, hn f' hf', mul_zero]
    have hu : IsUnit (algebraMap (R ⧸ J) (Localization.Away (Ideal.Quotient.mk J f)) (Ideal.Quotient.mk J f ^ (s.sup n))) := by
      rw [map_pow]; exact (isUnit_away _).pow _
    have := congrArg (algebraMap (R ⧸ J) (Localization.Away (Ideal.Quotient.mk J f))) hmem
    rw [map_mul, map_zero] at this
    exact (hu.mul_right_eq_zero).1 this

end GlobalTheory.CompanionTheory.TrivLoc

namespace GlobalTheory.CompanionTheory.TrivLoc

variable {S : Scheme.{0}} {A Y : Over S}

def IsTrivAt (N : LB (A ⊗ Y).left) {T : Over S} (y : T ⟶ Y) : Prop :=
  Triv (ev N (fst A T) (snd A T ≫ y))

theorem IsTrivAt.comp {N : LB (A ⊗ Y).left} {T T' : Over S} {y : T ⟶ Y} (h : IsTrivAt N y) (u : T' ⟶ T) :
    IsTrivAt N (u ≫ y) := by
  have e : lift (fst A T') (snd A T' ≫ u ≫ y) = lift (fst A T') (snd A T' ≫ u) ≫ lift (fst A T) (snd A T ≫ y) := by
    ext <;> simp
  unfold IsTrivAt ev at *
  rw [e, Over.comp_left]
  exact GlobalTheory.Biadditive.triv_pull_comp h _

def Locus (N : LB (A ⊗ Y).left) {T : Scheme.{0}} (t : T ⟶ Y.left) : Prop :=
  IsTrivAt N (Over.homMk t rfl : Over.mk (t ≫ Y.hom) ⟶ Y)

theorem locus_left_iff {N : LB (A ⊗ Y).left} {T : Over S} (y : T ⟶ Y) : Locus N y.left ↔ IsTrivAt N y := by
  have w : y.left ≫ Y.hom = T.hom := Over.w y
  let u : T ⟶ Over.mk (y.left ≫ Y.hom) := Over.homMk (𝟙 _) (by simp [w])
  let v : Over.mk (y.left ≫ Y.hom) ⟶ T := Over.homMk (𝟙 _) (by simp [w])
  constructor
  · intro h
    have := IsTrivAt.comp h u
    have e : u ≫ (Over.homMk y.left rfl : Over.mk (y.left ≫ Y.hom) ⟶ Y) = y := by
      ext; simp [u]
    rwa [e] at this
  · intro h
    have := IsTrivAt.comp h v
    have e : v ≫ y = (Over.homMk y.left rfl : Over.mk (y.left ≫ Y.hom) ⟶ Y) := by
      ext; simp [v]
    unfold Locus
    rwa [e] at this

theorem Locus.comp {N : LB (A ⊗ Y).left} {T T' : Scheme.{0}} {t : T ⟶ Y.left} (h : Locus N t) (u : T' ⟶ T) :
    Locus N (u ≫ t) := by
  let v : Over.mk ((u ≫ t) ≫ Y.hom) ⟶ Over.mk (t ≫ Y.hom) := Over.homMk u (by simp)
  have := IsTrivAt.comp h v
  have e : v ≫ (Over.homMk t rfl : Over.mk (t ≫ Y.hom) ⟶ Y) = (Over.homMk (u ≫ t) rfl : Over.mk ((u ≫ t) ≫ Y.hom) ⟶ Y) := by
    ext; simp [v]
  unfold Locus
  rwa [e] at this

end GlobalTheory.CompanionTheory.TrivLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusLocalToGlobal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusLocalToGlobal
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem locus_of_locally : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → ∀ (T : Scheme.{0}) (t : T ⟶ Y.left),
    (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ Locus N (W.ι ≫ t)) → Locus N t := by
  intro S A Y _ hA N hN h0 T t hloc
  let T₀ : Over S := Over.mk (t ≫ Y.hom)
  let y : T₀ ⟶ Y := Over.homMk t rfl
  let M : LB (A ⊗ T₀).left := ev N (fst A T₀) (snd A T₀ ≫ y)
  have hM : M.IsLB := pull_isLB hN _
  have key : ∀ (Z : Over S) (u : Z ⟶ A ⊗ T₀), evc hN (u ≫ fst A T₀) (u ≫ snd A T₀ ≫ y) = 0 →
      Triv (M.pull u.left) := by
    intro Z u h
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM]
    have e := pull_evc hN u (fst A T₀) (snd A T₀ ≫ y)
    rw [h] at e
    exact e
  show Triv M
  refine GlobalTheory.CompanionTheory.Ar.Approx.triv_of_section_of_locally_triv (A ⊗ T₀).left T (snd A T₀).left
    (lift (1 : T₀ ⟶ A) (𝟙 T₀)).left ?_ ?_ M hM ?_ ?_
  · rw [← Over.comp_left, lift_snd]; rfl
  · intro U
    exact GlobalTheory.CompanionTheory.Ar.Approx.isIso_app_of_isAbelianScheme T ((Over.pullback T₀.hom).obj A)
      (CubeGen.isAb_baseChange hA T₀.hom) U
  · refine key T₀ _ ?_
    rw [lift_fst, lift_snd_assoc, Category.id_comp]
    have e := congrArg (CechPic.pull y.left) ((triv_ev_iff hN _ _).1 h0)
    rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e
  · intro x
    obtain ⟨W, hx, hW⟩ := hloc x
    refine ⟨W, hx, ?_⟩
    let p := (snd A T₀).left
    let W₀ : Over S := Over.mk ((W.ι ≫ t) ≫ Y.hom)
    let y' : W₀ ⟶ Y := Over.homMk (W.ι ≫ t) rfl
    let Z : Over S := Over.mk ((p ⁻¹ᵁ W).ι ≫ (A ⊗ T₀).hom)
    let u : Z ⟶ A ⊗ T₀ := Over.homMk (p ⁻¹ᵁ W).ι rfl
    have hr : Set.range ((p ⁻¹ᵁ W).ι ≫ p) ⊆ Set.range W.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact z.2
    let l : Z.left ⟶ W₀.left := IsOpenImmersion.lift W.ι ((p ⁻¹ᵁ W).ι ≫ p) hr
    have hl : l ≫ W.ι = (p ⁻¹ᵁ W).ι ≫ p := IsOpenImmersion.lift_fac _ _ _
    have wz : l ≫ W₀.hom = Z.hom := by
      have hs : p ≫ t ≫ Y.hom = (A ⊗ T₀).hom := Over.w (snd A T₀)
      show l ≫ (W.ι ≫ t) ≫ Y.hom = (p ⁻¹ᵁ W).ι ≫ (A ⊗ T₀).hom
      rw [← hs, ← Category.assoc (p ⁻¹ᵁ W).ι, ← hl]
      simp only [Category.assoc]
    let w : Z ⟶ W₀ := Over.homMk l wz
    have hwy : w ≫ y' = u ≫ snd A T₀ ≫ y := by
      apply Over.OverMorphism.ext
      show l ≫ W.ι ≫ t = (p ⁻¹ᵁ W).ι ≫ p ≫ t
      rw [← Category.assoc, hl, Category.assoc]
    refine key Z u ?_
    have e := pull_evc hN (lift (u ≫ fst A T₀) w) (fst A W₀) (snd A W₀ ≫ y')
    rw [(triv_ev_iff hN _ _).1 hW, map_zero, lift_fst, lift_snd_assoc, hwy] at e
    exact e.symm

end GlobalTheory.CompanionTheory.TrivLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusLocalToGlobalStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_locus_local_to_global : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → ∀ (T : Scheme.{0}) (t : T ⟶ Y.left),
    (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ Locus N (W.ι ≫ t)) → Locus N t := by
  first | exact @GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally | exact GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally | (intros; apply GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalPropertyAffineIdealCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalPropertyAffineIdealCriterion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.TrivLoc.Rep

theorem exists_basicOpen_le {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (r : Γ(Y, V)) (y : Y) (hyU : y ∈ U) (hyr : y ∈ Y.basicOpen r) :
    ∃ f : Γ(Y, U), y ∈ Y.basicOpen f ∧ Y.basicOpen f ≤ Y.basicOpen r := by
  obtain ⟨f, g, e, hy⟩ := exists_basicOpen_le_affine_inter hU (hV.basicOpen r) y ⟨hyU, hyr⟩
  exact ⟨f, hy, e ▸ Y.basicOpen_le g⟩

theorem isUnit_res_of_le {Y : Scheme.{0}} {V W : Y.Opens} (r : Γ(Y, V)) (hle : W ≤ Y.basicOpen r)
    (hWV : W ≤ V) : IsUnit ((Y.presheaf.map (homOfLE hWV).op).hom r) := by
  have h := Y.toRingedSpace.isUnit_res_basicOpen r
  have e : (Y.presheaf.map (homOfLE hWV).op).hom r =
      (Y.presheaf.map (homOfLE hle).op).hom
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom r) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  rw [e]
  exact h.map (Y.presheaf.map (homOfLE hle).op).hom

theorem exists_ideal_on_basicOpen {Y : Scheme.{0}} (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (f : Γ(Y, U)) (r : Γ(Y, V))
    (I : Ideal Γ(Y, V)) (hle : Y.basicOpen f ≤ Y.basicOpen r)
    (hI : ∀ (R' : Type) [CommRing R'] (g : Γ(Y, V) →+* R'), IsUnit (g r) →
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) ↔ I ≤ RingHom.ker g)) :
    ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g f) →
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g) := by
  have hWV : Y.basicOpen f ≤ V := hle.trans (Y.basicOpen_le r)
  let resV : Γ(Y, V) →+* Γ(Y, Y.basicOpen f) := (Y.presheaf.map (homOfLE hWV).op).hom
  let I₂ : Ideal Γ(Y, Y.basicOpen f) := I.map resV
  haveI := hU.isLocalization_basicOpen f
  refine ⟨I₂.comap (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f)), fun R' _ g hu => ?_⟩
  let h' : Γ(Y, Y.basicOpen f) →+* R' := IsLocalization.Away.lift f hu
  have hcomp : h'.comp (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f)) = g := IsLocalization.Away.lift_comp f hu
  have hW := hU.basicOpen f
  have hg : CommRingCat.ofHom g =
      Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op ≫ CommRingCat.ofHom h' := by
    rw [← hcomp]; rfl
  have hg' : CommRingCat.ofHom (h'.comp resV) =
      Y.presheaf.map (homOfLE hWV).op ≫ CommRingCat.ofHom h' := rfl
  have e : Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom (h'.comp resV)) ≫ hV.fromSpec := by
    rw [hg, hg', Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      hU.map_fromSpec hW, hV.map_fromSpec hW]
  have hunit : IsUnit ((h'.comp resV) r) := (isUnit_res_of_le r hle hWV).map h'
  rw [e, hI R' _ hunit]
  constructor
  · intro h x hx
    have hx' : algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) x ∈ I₂ := hx
    have h2 : I₂ ≤ RingHom.ker h' := by
      rw [show I₂ = I.map resV from rfl, Ideal.map_le_iff_le_comap]
      intro z hz
      exact h hz
    have := h2 hx'
    rw [RingHom.mem_ker] at this ⊢
    rw [← hcomp]
    exact this
  · intro h z hz
    have h2 : I₂ ≤ RingHom.ker h' := by
      rw [← IsLocalization.map_under (Submonoid.powers f) Γ(Y, Y.basicOpen f) I₂, Ideal.map_le_iff_le_comap]
      intro x hx
      have := h hx
      rw [RingHom.mem_ker] at this
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [← hcomp] at this
      exact this
    exact h2 (Ideal.mem_map_of_mem resV hz)

theorem local_on_affine {Y : Scheme.{0}} (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    (stab : ∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t))
    (loc : ∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t)
    {U : Y.Opens} (hU : IsAffineOpen U) (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R') (s : Set R')
    (hs : Ideal.span s = ⊤)
    (hQ : ∀ a ∈ s, P (Spec (CommRingCat.of (Localization.Away a)))
      (Spec.map (CommRingCat.ofHom ((algebraMap R' (Localization.Away a)).comp g)) ≫ hU.fromSpec)) :
    P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) := by
  refine loc _ _ fun x => ?_
  let x' : PrimeSpectrum R' := x
  have hx : ∃ a ∈ s, a ∉ x'.asIdeal := by
    by_contra hcon
    push Not at hcon
    have : Ideal.span s ≤ x'.asIdeal := Ideal.span_le.2 hcon
    rw [hs] at this
    exact x'.2.ne_top (top_le_iff.1 this)
  obtain ⟨a, ha, hax⟩ := hx
  let j : Spec (CommRingCat.of (Localization.Away a)) ⟶ Spec (CommRingCat.of R') :=
    Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away a)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization a
  refine ⟨j.opensRange, ?_, ?_⟩
  · have h := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    have hx' : x' ∈ Set.range (PrimeSpectrum.comap (algebraMap R' (Localization.Away a))) := by
      rw [h]; exact hax
    obtain ⟨z, hz⟩ := hx'
    exact ⟨z, hz⟩
  · have h0 := hQ a ha
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] at h0
    have h1 := stab _ _ j.isoOpensRange.inv _ h0
    rwa [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp] at h1

theorem exists_ideal_on_affine : ∀ (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop),
    (∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t) →
    (∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)) (I : Ideal Γ(Y, U)), y ∈ Y.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g r) →
        (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g)) →
    ∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g) := by
  intro Y P stab loc hloc U hU
  let Q : ∀ (R' : Type) [CommRing R'], (Γ(Y, U) →+* R') → Prop := fun R' _ g =>
    P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec)
  let S : Set Γ(Y, U) := {f | ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
    IsUnit (g f) → (Q R' g ↔ J ≤ RingHom.ker g)}
  have hS : Ideal.span S = ⊤ := by
    refine hU.self_le_iSup_basicOpen_iff.1 fun y hy => ?_
    obtain ⟨V, hV, r, I, hyr, hI⟩ := hloc y
    obtain ⟨f, hyf, hle⟩ := exists_basicOpen_le hU hV r y hy hyr
    have hf : f ∈ S := exists_ideal_on_basicOpen P hU hV f r I hle hI
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hyf⟩
  obtain ⟨s, hsS, hs⟩ := (Ideal.span_eq_top_iff_finite S).1 hS
  have hS' : ∀ f, f ∈ S → ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
    IsUnit (g f) → (Q R' g ↔ J ≤ RingHom.ker g) := fun _ h => h
  choose! I hI using hS'
  refine exists_ideal_of_local Q ?_ ?_ s hs I fun f hf => hI f (hsS hf)
  · intro R' R'' _ _ g h hq
    have := stab _ _ (Spec.map (CommRingCat.ofHom h)) _ hq
    change P _ _
    rwa [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at this
  · intro R' _ g s hs hQ
    exact local_on_affine P stab loc hU R' g s hs hQ

end GlobalTheory.CompanionTheory.TrivLoc.Rep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalPropertyAffineIdealCriterionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_property_affine_ideal_criterion : ∀ (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop),
    (∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t) →
    (∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)) (I : Ideal Γ(Y, U)), y ∈ Y.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g r) →
        (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g)) →
    ∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g) := by
  first | exact @GlobalTheory.CompanionTheory.TrivLoc.Rep.exists_ideal_on_affine | exact GlobalTheory.CompanionTheory.TrivLoc.Rep.exists_ideal_on_affine | (intros; apply GlobalTheory.CompanionTheory.TrivLoc.Rep.exists_ideal_on_affine <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineIdealLocusCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineIdealLocusCriterion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc.Glue

theorem ideal_eq_of_le_ker_iff {A : Type} [CommRing A] {I J : Ideal A}
    (h : ∀ (R : Type) [CommRing R] (g : A →+* R), I ≤ RingHom.ker g ↔ J ≤ RingHom.ker g) :
    I = J := by
  apply le_antisymm
  · have := (h (A ⧸ J) (Ideal.Quotient.mk J)).2 (by rw [Ideal.mk_ker])
    rwa [Ideal.mk_ker] at this
  · have := (h (A ⧸ I) (Ideal.Quotient.mk I)).1 (by rw [Ideal.mk_ker])
    rwa [Ideal.mk_ker] at this

theorem eq_zero_of_affine_restrict {T : Scheme.{0}} {V : T.Opens} (s : Γ(T, V))
    (h : ∀ (W : T.Opens) (_ : IsAffineOpen W) (e : W ≤ V),
      (T.presheaf.map (homOfLE e).op).hom s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext T.sheaf V s 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
  have hz := h W hW hWV
  have h1 := TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hWV) x hxW s
  refine h1.symm.trans ?_
  erw [hz, map_zero, map_zero]

theorem exists_closed_subscheme (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    (stab : ∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t))
    (loc : ∀ (T : Scheme.{0}) (t : T ⟶ Y),
      (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t)
    (rep : ∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U),
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔
        J ≤ RingHom.ker g)) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ Y), IsClosedImmersion i ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  choose J hJ using rep
  have hJ' : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (R : CommRingCat.{0}) (g : Γ(Y, U) ⟶ R),
      P (Spec R) (Spec.map g ≫ hU.fromSpec) ↔ J U hU ≤ RingHom.ker g.hom :=
    fun U hU R g => hJ U hU R g.hom
  let I : Y.IdealSheafData :=
    { ideal := fun U => J U.1 U.2
      map_ideal_basicOpen := by
        intro U f
        refine ideal_eq_of_le_ker_iff fun R _ g => ?_
        rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
        refine (hJ U.1 U.2 R _).symm.trans (Iff.trans ?_ (hJ _ (Y.affineBasicOpen f).2 R g))
        have e := U.2.map_fromSpec (Y.affineBasicOpen f).2 (homOfLE (Y.basicOpen_le f)).op
        rw [← e, ← Category.assoc, ← Spec.map_comp]
        rfl }
  have key : ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ I ≤ t.ker := by
    intro T t
    have hW : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : T.Opens) (hW : IsAffineOpen W)
        (e : W ≤ t ⁻¹ᵁ U), P (Spec Γ(T, W)) (hW.fromSpec ≫ t) ↔
          J U hU ≤ RingHom.ker (t.appLE U W e).hom := by
      intro U hU W hW e
      rw [← hJ' U hU, IsAffineOpen.SpecMap_appLE_fromSpec t hU hW e]
    constructor
    · intro hP
      refine Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_
      change (t.app U.1).hom a = 0
      refine eq_zero_of_affine_restrict _ fun W hWa e => ?_
      exact (hW U.1 U.2 W hWa e).1 (stab _ _ _ _ hP) ha
    · intro hI
      refine loc T t fun x => ?_
      obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
        (U := (⊤ : Y.Opens)) (x := t x) trivial
      obtain ⟨W, hWa, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
        (U := t ⁻¹ᵁ U) (x := x) hxU
      have e : W ≤ t ⁻¹ᵁ U := hWU
      have hk : J U hU ≤ RingHom.ker (t.appLE U W e).hom := fun a ha => by
        have h0 : (t.app U).hom a = 0 := t.ideal_ker_le ⟨U, hU⟩ (hI ⟨U, hU⟩ ha)
        change (T.presheaf.map (homOfLE e).op).hom ((t.app U).hom a) = 0
        rw [h0, map_zero]
      have hp := stab _ _ hWa.isoSpec.hom _ ((hW U hU W hWa e).2 hk)
      have e2 : hWa.isoSpec.hom ≫ hWa.fromSpec = W.ι := by
        rw [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, e2] at hp
      exact ⟨W, hxW, hp⟩
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun T t => (key T t).trans ⟨fun h => ?_, ?_⟩⟩
  · exact ⟨IsClosedImmersion.lift I.subschemeι t (by rwa [I.ker_subschemeι]),
      IsClosedImmersion.lift_fac _ _ _⟩
  · rintro ⟨z, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)

end GlobalTheory.CompanionTheory.TrivLoc.Glue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineIdealLocusCriterionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_ideal_locus_criterion : ∀ (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop),
    (∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t)) →
    (∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t) →
    (∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U), ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ J ≤ RingHom.ker g)) →
    ∃ (Z : Scheme.{0}) (i : Z ⟶ Y), IsClosedImmersion i ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  first | exact @GlobalTheory.CompanionTheory.TrivLoc.Glue.exists_closed_subscheme | exact GlobalTheory.CompanionTheory.TrivLoc.Glue.exists_closed_subscheme | (intros; apply GlobalTheory.CompanionTheory.TrivLoc.Glue.exists_closed_subscheme <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricallyIntegralGlobalFunctionsConstant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricallyIntegralGlobalFunctionsConstant
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem triv_of_isEmpty {Y : Scheme.{0}} [IsEmpty Y] (L : LB Y) : Triv L := by
  have hs : ∀ U : Y.Opens, Subsingleton Γ(Y, U) := fun U => by
    have hU : U = ⊥ := by
      ext y
      exact (IsEmpty.false y).elim
    subst hU
    infer_instance
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have := hs (L.U i ⊓ L.U j)
  exact Subsingleton.elim _ _

theorem exists_ideal_near : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB →
    Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → Surjective f →
    (∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)),
      IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom) →
    ∀ p : PrimeSpectrum R, ∃ (r : R) (I : Ideal R), r ∉ p.asIdeal ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
        (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) →
        (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  intro R _ X f M hM hP hQ hprop hgi hsurj hbij p
  have hW := GlobalTheory.TrivLocus.isClosed_trivLocus R X f M hM hP hQ hprop hgi
  by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X)
      (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)}
  · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, hpb, ht⟩ := hp
    obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R X f M hM hP inferInstance hsurj K g₀ X₀ π₀ f₀ hpb
      (hbij K g₀ X₀ π₀ f₀ hpb) ht
    refine ⟨r, I, fun hrp => hr ?_, H⟩
    rw [← hk] at hrp
    exact hrp
  · obtain ⟨_, ⟨r, rfl⟩, hpr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ _ from hp) hW.isOpen_compl
    refine ⟨r, ⊤, hpr, fun R' _ g X' π f' h hu => ?_⟩
    rcases subsingleton_or_nontrivial R' with hR' | hR'
    · have hE : IsEmpty (Spec (CommRingCat.of R')) := inferInstanceAs (IsEmpty (PrimeSpectrum R'))
      have hX' : IsEmpty X' := ⟨fun x => hE.false (f' x)⟩
      exact ⟨fun _ x _ => Subsingleton.elim _ _, fun _ => triv_of_isEmpty _⟩
    · refine ⟨fun ht => ?_, fun hle => ?_⟩
      · exfalso
        obtain ⟨m, hm⟩ := Ideal.exists_maximal R'
        let _ : Field (R' ⧸ m) := Ideal.Quotient.field m
        let q : R' →+* R' ⧸ m := Ideal.Quotient.mk m
        have hpb : IsPullback (pullback.fst f' (Spec.map (CommRingCat.ofHom q)) ≫ π)
            (pullback.snd f' (Spec.map (CommRingCat.ofHom q))) f
            (Spec.map (CommRingCat.ofHom (q.comp g))) := by
          have e : Spec.map (CommRingCat.ofHom (q.comp g)) =
              Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom g) := by
            rw [← Spec.map_comp, CommRingCat.ofHom_comp]
          rw [e]
          exact (IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom q))).paste_horiz h
        have hprime : (RingHom.ker (q.comp g)).IsPrime := RingHom.ker_isPrime _
        refine hsub (show (⟨RingHom.ker (q.comp g), hprime⟩ : PrimeSpectrum R) ∈ _ from ?_)
          ⟨R' ⧸ m, inferInstance, q.comp g, _, _, _, rfl, hpb, GlobalTheory.Biadditive.triv_pull_comp ht _⟩
        intro hr
        exact (hu.map q).ne_zero hr
      · have h1 : g 1 = 0 := hle (Submodule.mem_top (x := (1 : R)))
        rw [map_one] at h1
        exact absurd h1 one_ne_zero

end GlobalTheory.CompanionTheory.TrivLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricallyIntegralGlobalFunctionsConstantStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometrically_integral_global_functions_constant : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB →
    Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → Surjective f →
    (∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)),
      IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom) →
    ∀ p : PrimeSpectrum R, ∃ (r : R) (I : Ideal R), r ∉ p.asIdeal ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
        (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) →
        (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  first | exact @GlobalTheory.CompanionTheory.TrivLoc.exists_ideal_near | exact GlobalTheory.CompanionTheory.TrivLoc.exists_ideal_near | (intros; apply GlobalTheory.CompanionTheory.TrivLoc.exists_ideal_near <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperIntegralPerfectFamilyExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperIntegralPerfectFamilyExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem isPullback_lift_snd {S : Scheme.{0}} (A X Y : Over S) (q : X ⟶ Y) :
    IsPullback (lift (fst A X) (snd A X ≫ q)).left (snd A X).left (snd A Y).left q.left := by
  have hX : IsPullback (fst A X).left (snd A X).left A.hom X.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom X.hom
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom Y.hom
  have e₁ : (lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left = (fst A X).left := by
    rw [← Over.comp_left, lift_fst]
  have e₂ : (lift (fst A X) (snd A X ≫ q)).left ≫ (snd A Y).left = (snd A X).left ≫ q.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hout : IsPullback ((lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left) (snd A X).left
      A.hom (q.left ≫ Y.hom) := by
    rw [e₁, Over.w q]
    exact hX
  exact IsPullback.of_right hout e₂ hY

theorem triv_pull_iso {P Q X : Scheme.{0}} {L : LB X} (e : P ≅ Q) (a : Q ⟶ X) :
    Triv (L.pull (e.hom ≫ a)) ↔ Triv (L.pull a) := by
  constructor
  · intro h
    have := GlobalTheory.Biadditive.triv_pull_comp h e.inv
    rwa [Iso.inv_hom_id_assoc] at this
  · intro h
    exact GlobalTheory.Biadditive.triv_pull_comp h e.hom

theorem triv_pull_iff_locus {S : Scheme.{0}} {A Y T₀ : Over S} (N : LB (A ⊗ Y).left) (v : T₀ ⟶ Y)
    {W X' : Scheme.{0}} (t : W ⟶ T₀.left) (π : X' ⟶ (A ⊗ T₀).left) (f' : X' ⟶ W)
    (h : IsPullback π f' (snd A T₀).left t) :
    Triv ((ev N (fst A T₀) (snd A T₀ ≫ v)).pull π) ↔ Locus N (t ≫ v.left) := by
  let T' : Over S := Over.mk ((t ≫ v.left) ≫ Y.hom)
  let u : T' ⟶ T₀ := Over.homMk t (by simp [T'])
  let w : T' ⟶ Y := Over.homMk (t ≫ v.left) rfl
  have huv : u ≫ v = w := by ext; simp [u, w]
  have hp : IsPullback (lift (fst A T') (snd A T' ≫ u)).left (snd A T').left (snd A T₀).left t :=
    isPullback_lift_snd A T' T₀ u
  let e : X' ≅ (A ⊗ T').left := h.isoIsPullback _ _ hp
  have he : e.hom ≫ (lift (fst A T') (snd A T' ≫ u)).left = π := h.isoIsPullback_hom_fst _ _ hp
  have hc : (lift (fst A T') (snd A T' ≫ u)).left ≫ (lift (fst A T₀) (snd A T₀ ≫ v)).left =
      (lift (fst A T') (snd A T' ≫ w)).left := by
    rw [← Over.comp_left, ← huv]
    congr 1
    ext <;> simp
  have h1 : Triv ((ev N (fst A T₀) (snd A T₀ ≫ v)).pull π) ↔
      Triv (N.pull (π ≫ (lift (fst A T₀) (snd A T₀ ≫ v)).left)) :=
    GlobalTheory.AbLaw.CubeGen.triv_pull_iff N (fun _ : PUnit => (lift (fst A T₀) (snd A T₀ ≫ v)).left) (fun _ => 1) π
  rw [h1, ← he, Category.assoc, hc, triv_pull_iso]
  rfl

theorem family_props {R : Type} [CommRing R] [IsNoetherianRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsProper f] [GeometricallyConnected f] (s : Spec (CommRingCat.of R) ⟶ W) (hs : s ≫ f = 𝟙 _)
    {M : LB W} (hM : M.IsLB) :
    Nonempty (Perf f M) ∧ Nonempty (Perf f (pw M (-1))) ∧ GeometricallyIntegral f ∧ Surjective f := by
  refine ⟨GlobalTheory.ProperFinite.nonempty_perf_of_isProper (R := R) f hM,
    GlobalTheory.ProperFinite.nonempty_perf_of_isProper (R := R) f (isLB_pw hM _),
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance, ?_⟩
  have : Surjective (s ≫ f) := by rw [hs]; infer_instance
  exact Surjective.of_comp s f

theorem exists_chart_family : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (j : Spec (CommRingCat.of R) ⟶ Y.left),
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB ∧ Nonempty (Perf f M) ∧
      Nonempty (Perf f (pw M (-1))) ∧ IsProper f ∧ GeometricallyIntegral f ∧ Surjective f ∧
      (∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)),
        IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom) ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
        (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
        (Triv (M.pull π) ↔ Locus N (Spec.map (CommRingCat.ofHom g) ≫ j)) := by
  intro S A Y _ hA N hN R _ _ j
  have hB : IsAbelianScheme ((Over.pullback (j ≫ Y.hom)).obj A) := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA (j ≫ Y.hom)
  let T₀ : Over S := Over.mk (j ≫ Y.hom)
  let v : T₀ ⟶ Y := Over.homMk j rfl
  let f : (A ⊗ T₀).left ⟶ Spec (CommRingCat.of R) := (snd A T₀).left
  let M : LB (A ⊗ T₀).left := ev N (fst A T₀) (snd A T₀ ≫ v)
  have hM : M.IsLB := pull_isLB hN _
  have sm : Smooth f := hB.smooth
  have pr : IsProper f := hB.proper
  have gc : GeometricallyConnected f := hB.geomConnected
  let s : Spec (CommRingCat.of R) ⟶ (A ⊗ T₀).left := (η[(Over.pullback (j ≫ Y.hom)).obj A]).left
  have hs : s ≫ f = 𝟙 _ := Over.w (η[(Over.pullback (j ≫ Y.hom)).obj A])
  obtain ⟨p₁, p₂, p₃, p₄⟩ := family_props f s hs hM
  refine ⟨(A ⊗ T₀).left, f, M, hM, p₁, p₂, pr, p₃, p₄, ?_, ?_⟩
  · intro K _ g₀ X₀ π₀ f₀ h
    exact GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.globalFns_holds _ hB h
  · intro R' _ g X' π f' h
    exact triv_pull_iff_locus N v _ π f' h

end GlobalTheory.CompanionTheory.TrivLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperIntegralPerfectFamilyExistsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_integral_perfect_family_exists : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (j : Spec (CommRingCat.of R) ⟶ Y.left),
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB ∧ Nonempty (Perf f M) ∧
      Nonempty (Perf f (pw M (-1))) ∧ IsProper f ∧ GeometricallyIntegral f ∧ Surjective f ∧
      (∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)),
        IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom) ∧
      ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
        (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
        (Triv (M.pull π) ↔ Locus N (Spec.map (CommRingCat.ofHom g) ≫ j)) := by
  first | exact @GlobalTheory.CompanionTheory.TrivLoc.exists_chart_family | exact GlobalTheory.CompanionTheory.TrivLoc.exists_chart_family | (intros; apply GlobalTheory.CompanionTheory.TrivLoc.exists_chart_family <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc

theorem closed_of_functor (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    (stab : ∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t))
    (loc : ∀ (T : Scheme.{0}) (t : T ⟶ Y), (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t)
    (near : ∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (r : Γ(Y, U)) (I : Ideal Γ(Y, U)), y ∈ Y.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'), IsUnit (g r) →
        (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g)) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ Y), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ ∃ z : T ⟶ Z, z ≫ i = t :=
  GlobalTheory.T.affine_ideal_locus_criterion Y P stab loc (GlobalTheory.T.local_property_affine_ideal_criterion Y P stab loc near)

theorem locus_near {S : Scheme.{0}} {A Y : Over S} [GrpObj A] (hA : IsAbelianScheme A) [IsLocallyNoetherian Y.left]
    {N : LB (A ⊗ Y).left} (hN : N.IsLB) (y : Y.left) :
    ∃ (U : Y.left.Opens) (hU : IsAffineOpen U) (r : Γ(Y.left, U)) (I : Ideal Γ(Y.left, U)), y ∈ Y.left.basicOpen r ∧
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y.left, U) →+* R'), IsUnit (g r) →
        (Locus N (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔ I ≤ RingHom.ker g) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ := Y.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  obtain ⟨p, hp⟩ := hU.range_fromSpec.ge hy
  have : IsNoetherianRing Γ(Y.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨X, f, M, hM, h₁, h₂, h₃, h₄, h₅, h₆, H⟩ := GlobalTheory.T.proper_integral_perfect_family_exists S A Y hA N hN Γ(Y.left, U) hU.fromSpec
  obtain ⟨r, I, hr, H'⟩ := GlobalTheory.T.geometrically_integral_global_functions_constant _ X f M hM h₁ h₂ h₃ h₄ h₅ h₆ p
  refine ⟨U, hU, r, I, ?_, fun R' _ g hg => ?_⟩
  · rw [← hU.fromSpec_image_basicOpen]
    exact ⟨p, hr, hp⟩
  · have hq := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))
    exact (H R' g _ _ _ hq).symm.trans (H' R' g _ _ _ hq hg)

theorem trivLocus : TrivLocus := by
  intro S A Y _ hA hY N hN h1
  obtain ⟨Z, i, hi, H⟩ := closed_of_functor Y.left (fun T t => Locus N t)
    (fun T T' h t ht => ht.comp h) (fun T t h => GlobalTheory.T.trivial_locus_local_to_global S A Y hA N hN h1 T t h) (locus_near hA hN)
  refine ⟨Over.mk (i ≫ Y.hom), Over.homMk i rfl, hi, fun T y => ?_⟩
  refine (locus_left_iff y).symm.trans ((H _ y.left).trans ⟨?_, ?_⟩)
  · rintro ⟨z, hz⟩
    exact ⟨Over.homMk z (by simp [reassoc_of% hz]), by ext; simpa using hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z.left, by simpa using congrArg (fun q => q.left) hz⟩

end GlobalTheory.CompanionTheory.TrivLoc
