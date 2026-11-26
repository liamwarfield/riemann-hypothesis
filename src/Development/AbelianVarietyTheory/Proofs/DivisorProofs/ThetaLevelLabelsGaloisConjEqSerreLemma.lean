module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsIffPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def LabTors {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (k : ℕ)
    (x : QkPt D (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)) : Prop :=
  (∀ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ k = 1 → ∃ p, x p = y) ∧ (∀ p, x p ^ k = 1) ∧
    (∀ p p', x p = x p' ↔ QkPt.Equiv D (Kb R) p p') ∧
    (∀ p p' p'', QkAdd p p' p'' → x p'' = x p * x p') ∧
    ∀ p p' (z : (Kb R)ˣ), WeilQkIs D (Kb R) k p p' z ↔ WeilIs A.A A.L k (x p) (x p') (unitOn z)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsOneTraitWeilPairingBijection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsOneTraitWeilPairingBijection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LabTorsTrait

open GlobalTheory.ArcPull GlobalTheory.Mum.Recog

theorem labTors_of_oneTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A),
    OneTrait D.toPre A lab → ∀ k : ℕ, 1 ≤ k → LabTors D.toPre A k (lab k) := by
  intro R _ _ _ hR D A lab hT k hk
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, iφ, _, hG, ha, c, H⟩ := hT
  have := hR.2
  have : CharZero W := (RingHom.charZero_iff iφ).1 inferInstance
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB' := D'.tau_bimult
  have c' : Compat φ (Kb W) := c
  obtain ⟨f', hf'⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws W (maximalIdeal W) bW D' A' G' hG U' (Kb W) k hk
  obtain ⟨ε, hε, iε, oε, wε⟩ := exists_ptHom ha c' em
  have e : ∀ p, f' (tr hD c' em hB' p) = ε (lab k p) := fun p => by
    obtain ⟨p₁, h₁, h₂, h₃⟩ := (lies_iff hD c' em hB' p (tr hD c' em hB' p)).2 rfl
    exact ((hf'.1 _ _).1 (H k hk p p₁ _ _ h₁ h₂ h₃ ((hε _ _).1 rfl))).symm
  have pw : ∀ x : TFK (R := R) (Kb R) ⟶ A.A, ε x ^ k = 1 ↔ x ^ k = 1 := fun x => by
    rw [← map_pow, ← map_one ε, iε.eq_iff]
  have hp : ∀ p, lab k p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U'.ext
    rw [← pw, ← e]
    exact (((hf'.1 _ _).2 rfl) w hw).1
  refine ⟨fun y hy => ?_, hp, fun p q => ?_, fun p q r h => ?_, fun p q z => ?_⟩
  · obtain ⟨p', hp'⟩ := hf'.2.1 (ε y) ((pw y).2 hy)
    obtain ⟨p, rfl⟩ := (tr_bij hD c' em hB' hk).2 p'
    exact ⟨p, iε (by rw [← e, hp'])⟩
  · rw [← iε.eq_iff, ← e, ← e, hf'.2.2.1, tr_equiv]
  · apply iε
    rw [map_mul, ← e, ← e, ← e]
    exact hf'.2.2.2.1 _ _ _ ((tr_add hD c' em hB' p q r).2 h)
  · rw [← tr_weil hD c' em hB' hk p q z, wε k _ _ (hp p) (hp q) z, ← e, ← e]
    exact hf'.2.2.2.2 _ _ (Units.map em.toRingHom.toMonoidHom z)

end GlobalTheory.Mum.LabTorsTrait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsOneTraitWeilPairingBijectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ k : ℕ, 1 ≤ k → LabTors D.toPre A k (lab k) := by
  first | exact @GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait | exact GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait | (intros; apply GlobalTheory.Mum.LabTorsTrait.labTors_of_oneTrait <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionLabelingGaloisConjugateAlgClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsFinExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LabExt

open GlobalTheory.ArcPull GlobalTheory.TorusExt

theorem qkExt_refl {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C]
    [Algebra (FractionRing R) C] {k : ℕ} (p : QkPt D C k) : QkExt (RingHom.id C) p p := by
  have e : spMap (RingHom.id C) = 𝟙 _ := Spec.map_id _
  refine ⟨rfl, by rw [e, Category.id_comp], fun χ => ?_⟩
  rw [e]
  exact corr_of_val D.P.isLB fun y J hJ =>
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val (p.g.s χ) r y J) (Category.id_comp _))).symm

section Lab

variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] {ρ : R →+* R₁}
  {D : DegPre R} {D₁ : DegPre R₁} [Algebra (FractionRing R) (Kb R₁)]

variable {A : PolAV (Sp (FractionRing R))} {A₁ : PolAV (Sp (FractionRing R₁))}

end Lab

end GlobalTheory.LabExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionLabelingGaloisConjugateAlgClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalConjLabels

variable {R : Type} [CommRing R] [IsDomain R]

theorem spMap_jFK (f : Kb R →ₐ[FractionRing R] Kb R) :
    spMap f.toRingHom ≫ jFK (R := R) (Kb R) = jFK (R := R) (Kb R) := by
  rw [spMap, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) f.comp_algebraMap

def tauHom (f : Kb R →ₐ[FractionRing R] Kb R) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap f.toRingHom) (spMap_jFK f)

theorem tauHom_left (f : Kb R →ₐ[FractionRing R] Kb R) : (tauHom f).left = spMap f.toRingHom := rfl

theorem tauHom_comp_eq_id (f g : Kb R →ₐ[FractionRing R] Kb R) (h : ∀ a, f (g a) = a) :
    tauHom f ≫ tauHom g = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.id_left, tauHom_left, tauHom_left, spMap, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have e : f.toRingHom.comp g.toRingHom = RingHom.id _ := RingHom.ext h
  rw [e, CommRingCat.ofHom_id, Spec.map_id]
  rfl

theorem map_unitOn' {k k' : Type} [CommRing k] [CommRing k'] (σ : k →+* k') (u : kˣ) :
    Units.map (spMap σ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map σ.toMonoidHom u) :=
  Units.ext (congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))).symm

end GlobalTheory.Mum.GalConjLabels

namespace GlobalTheory.Mum


open GalConjLabels in
theorem labTors_galConj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) (k : ℕ), 1 ≤ k → ∀ (x x' : QkPt D.toPre (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D.toPre A k x → (∀ p p', QkExt σ.toRingHom p p' → (x' p').left = spMap σ.toRingHom ≫ (x p).left) → LabTors D.toPre A k x' := by
  intro R _ _ _ hR D A σ k hk x x' hx hxx'
  haveI : CharZero R := hR.2
  haveI : IsNoetherianRing R := hR.1.1
  have hB := D.tau_bimult
  have hL := GlobalTheory.allSixLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hbij : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let e := AlgEquiv.ofBijective σ hbij
  let ρ : Kb R →ₐ[FractionRing R] Kb R := e.symm.toAlgHom
  have hσρ : ∀ a, σ (ρ a) = a := fun a => e.apply_symm_apply a
  have hρσ : ∀ a, ρ (σ a) = a := fun a => e.symm_apply_apply a
  have hfσ : σ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    σ.comp_algebraMap
  have hfρ : ρ.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb R) :=
    ρ.comp_algebraMap
  haveI : CharZero (Kb R) :=
    (RingHom.charZero_iff (algebraMap (FractionRing R) (Kb R)).injective).1 inferInstance
  have hk0 : (k : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have rev : ∀ {p p' : QkPt D.toPre (Kb R) k}, QkExt σ.toRingHom p p' → QkExt ρ.toRingHom p' p := by
    intro p p' h
    obtain ⟨q, hq⟩ := GlobalTheory.QkClosure.exists_qkExt ρ.toRingHom hfρ p'
    have h2 := GlobalTheory.LevelField.qkExt_trans h hq
    have eid : ρ.toRingHom.comp σ.toRingHom = RingHom.id _ := RingHom.ext hρσ
    rw [eid] at h2
    have := GlobalTheory.QkClosure.qkExt_unique (RingHom.id (Kb R)) (RingHom.id_comp _) h2 (GlobalTheory.LabExt.qkExt_refl p)
    rwa [this] at hq
  have desc : ∀ p' : QkPt D.toPre (Kb R) k, ∃ p, QkExt σ.toRingHom p p' := fun p' =>
    GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom hfσ hk0 p'
  have hx'eq : ∀ p p', QkExt σ.toRingHom p p' → x' p' = tauHom σ ≫ x p := fun p p' h =>
    Over.OverMorphism.ext (hxx' p p' h)
  have cσρ : tauHom σ ≫ tauHom ρ = 𝟙 _ := tauHom_comp_eq_id σ ρ hσρ
  have cρσ : tauHom ρ ≫ tauHom σ = 𝟙 _ := tauHom_comp_eq_id ρ σ hρσ
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  refine ⟨fun y hy => ?_, fun p' => ?_, fun p' q' => ?_, fun p' q' r' hadd => ?_, fun p' q' z => ?_⟩
  · obtain ⟨p, hp⟩ := h1 (tauHom ρ ≫ y) (by rw [← comp_pow, hy, comp_one])
    obtain ⟨p', hp'⟩ := GlobalTheory.QkClosure.exists_qkExt σ.toRingHom hfσ p
    exact ⟨p', by rw [hx'eq p p' hp', hp, ← Category.assoc, cσρ, Category.id_comp]⟩
  · obtain ⟨p, hp⟩ := desc p'
    rw [hx'eq p p' hp, ← comp_pow, h2, comp_one]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    rw [hx'eq p p' hp, hx'eq q q' hq]
    constructor
    · intro h
      have h' : x p = x q := by
        have := congrArg (tauHom ρ ≫ ·) h
        simpa only [← Category.assoc, cρσ, Category.id_comp] using this
      exact GlobalTheory.TorusExt.equiv_of_qkExt hB σ.toRingHom hfσ hp hq ((h3 p q).1 h')
    · intro h
      rw [(h3 p q).2 (GlobalTheory.TorusExt.equiv_of_qkExt hB ρ.toRingHom hfρ (rev hp) (rev hq) h)]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    obtain ⟨r, hr⟩ := desc r'
    rw [hx'eq p p' hp, hx'eq q q' hq, hx'eq r r' hr,
      h4 p q r (GlobalTheory.TorusExt.qkAdd_of_qkExt hB ρ.toRingHom hfρ (rev hp) (rev hq) (rev hr) hadd), comp_mul]
  · obtain ⟨p, hp⟩ := desc p'
    obtain ⟨q, hq⟩ := desc q'
    let z₀ : (Kb R)ˣ := Units.map ρ.toRingHom.toMonoidHom z
    have hz : Units.map σ.toRingHom.toMonoidHom z₀ = z := Units.ext (hσρ z)
    rw [hx'eq p p' hp, hx'eq q q' hq]
    constructor
    · intro hW
      have w₀ : WeilQkIs D.toPre (Kb R) k p q (z₀ : Kb R) := by
        have := GlobalTheory.ArcOfModel.weilQkIs_qkExt hL.1 hL.2.1 D.psi_even hB ρ.toRingHom hfρ k hk p' q' z hW
        rwa [← (GlobalTheory.TorusExt.qkExt_iff hB ρ.toRingHom hfρ _ _).1 (rev hp),
          ← (GlobalTheory.TorusExt.qkExt_iff hB ρ.toRingHom hfρ _ _).1 (rev hq)] at this
      have := GlobalTheory.CommPairing.weilIs_pull hG A.isAb A.isLB (tauHom σ) ((h5 p q z₀).1 w₀)
      rwa [tauHom_left, map_unitOn', hz] at this
    · intro hW
      have := GlobalTheory.CommPairing.weilIs_pull hG A.isAb A.isLB (tauHom ρ) hW
      rw [tauHom_left, map_unitOn', ← Category.assoc, ← Category.assoc, cρσ, Category.id_comp,
        Category.id_comp] at this
      have w₀ := GlobalTheory.ArcOfModel.weilQkIs_qkExt hL.1 hL.2.1 D.psi_even hB σ.toRingHom hfσ k hk p q _
        ((h5 p q z₀).2 this)
      rw [← (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hfσ _ _).1 hp,
        ← (GlobalTheory.TorusExt.qkExt_iff hB σ.toRingHom hfσ _ _).1 hq] at w₀
      have e' : σ.toRingHom (z₀ : Kb R) = (z : Kb R) := hσρ z
      rwa [e'] at w₀

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionLabelingGaloisConjugateAlgClosureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsionLabeling_galoisConjugate_algClosure : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) (k : ℕ), 1 ≤ k → ∀ (x x' : QkPt D.toPre (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D.toPre A k x → (∀ p p', QkExt σ.toRingHom p p' → (x' p').left = spMap σ.toRingHom ≫ (x p).left) → LabTors D.toPre A k x' := by
  first | exact @GlobalTheory.Mum.labTors_galConj | exact GlobalTheory.Mum.labTors_galConj | (intros; apply GlobalTheory.Mum.labTors_galConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphism
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaConj

def conjHom {R : Type} [CommRing R] [IsDomain R] (σ : Kb R →ₐ[FractionRing R] Kb R) :
    TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact σ.commutes a)

end GlobalTheory.ThetaConj


open GlobalTheory.ThetaConj GlobalTheory.ThetaCoord in
theorem GlobalTheory.isThetaPt_conj : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  intro R _ _ A k σ I x x' v hx H
  have hs : Subsingleton (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Kb R)))
  have hn : Nonempty (TFK (R := R) (Kb R)).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Kb R)))
  let e : Kb R ≃ₐ[FractionRing R] Kb R :=
    AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hi : conjHom σ ≫ conjHom e.symm.toAlgHom = 𝟙 _ := by
    refine Over.OverMorphism.ext ?_
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_id _))
    ext a
    exact e.apply_symm_apply a
  have Q := isThetaPtOver_pull A (isThetaPtOver_of_subsingleton A H) _ _ hi
  have Q' : IsThetaPtOver A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
    convert Q using 2 with a a
    · exact Over.OverMorphism.ext (hx a)
    · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ.toRingHom))
  refine ⟨H.1, H.2.1, fun p => ⟨⊤, trivial, ?_⟩⟩
  let j : TFK (R := R) (Kb R) ⟶ overRes (T := TFK (R := R) (Kb R)) ⊤ :=
    Over.homMk (TFK (R := R) (Kb R)).left.topIso.inv (by
      change _ ≫ Scheme.Opens.ι ⊤ ≫ _ = _
      rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  exact isThetaPtOver_pull A Q' (overResι ⊤) j
    (Over.OverMorphism.ext (TFK (R := R) (Kb R)).left.topIso.hom_inv_id)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointConjAlgClosureAutomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoint_conj_algClosure_automorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (k : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (I : Type) (x x' : I → (TFK (R := R) (Kb R) ⟶ A.A)) (v : I → Kb R), (∀ i, (x' i).left = spMap σ.toRingHom ≫ (x i).left) → IsThetaPt A k x (fun i => GlobalTheory.Ex.fnOf (v i)) → IsThetaPt A k x' (fun i => GlobalTheory.Ex.fnOf (σ (v i))) := by
  first | exact @GlobalTheory.isThetaPt_conj | exact GlobalTheory.isThetaPt_conj | (intros; apply GlobalTheory.isThetaPt_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsTraitCompatibleLevelsMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsTraitCompatibleLevelsMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem GlobalTheory.Mum.lab_level_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A),
    OneTrait D.toPre A lab → ∀ k d : ℕ, 1 ≤ k → 1 ≤ d →
    ∀ (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) (k * d)), q.y = d • p.y → q.g = p.g →
      lab (k * d) q = lab k p := by
  intro R _ _ _ _ D A lab hO k d hk hd p q hy hg
  obtain ⟨W, _, _, _, φ, G', _, _, D', A', U', hD, a, _, em, hW, -, -, hG', ⟨ga, hga, hcart, -⟩, hc, hind⟩ := hO
  have := hW.1
  haveI : CharZero W := hW.2.2
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hG := GlobalTheory.globalFns_holds
  have hL := GlobalTheory.firstFiveLaws
  have hN1 : 1 ≤ k * d := Nat.mul_pos hk hd
  have hem : em.toRingHom.comp (algebraMap (FractionRing R) (Kb R)) = algebraMap (FractionRing R) (Kb W) :=
    RingHom.ext em.commutes
  have hsq : spMap em.toRingHom ≫ jFK (R := R) (Kb R) = (TFK (R := W) (Kb W)).hom ≫ spMap ga := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hem]
    refine congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    simp only [RingHom.comp_apply]
    rw [hga r]
    exact hc r
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hcart (TFK (R := W) (Kb W)) _ hsq
  let s : Over.mk (spMap em.toRingHom ≫ jFK (R := R) (Kb R)) ⟶ TFK (R := R) (Kb R) :=
    Over.homMk (spMap em.toRingHom) rfl
  have hcomp : ∀ {m : ℕ} (r : QkPt D.toPre (Kb R) m), 1 ≤ m →
      QkToAkU U'.toUnifPre (Kb W) m (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem r))
        (e.symm (s ≫ lab m r)) := by
    intro m r hm
    refine hind m hm r _ _ _ ((GlobalTheory.TorusExt.qkExt_iff hB _ hem _ _).2 rfl) rfl
      ((GlobalTheory.ArcPull.eq_pullQk_iff hD hG hc hB hB' _ _).1 rfl).2 ?_
    rw [← he, e.apply_symm_apply]
    rfl
  have h₁ := hcomp p hk
  have h₂ := ((GlobalTheory.LevelCompat.qkToAkU_level hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k d (k * d) hk hd rfl
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem p))
    (GlobalTheory.ArcPull.pullQk hD hG hc hB hB' (GlobalTheory.TorusExt.qkExt hB em.toRingHom hem q)) (e.symm (s ≫ lab (k * d) q))).1
    (by show hD.xe.symm q.y = d • hD.xe.symm p.y; rw [hy, map_nsmul])
    (by
      show GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem q.g) =
        GlobalTheory.ArcPull.pullGt hD hG hc (GlobalTheory.TorusExt.gtExt D.toPre em.toRingHom hem p.g)
      rw [hg])).2 (hcomp q hN1)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL W (maximalIdeal W) hW' D' A' G' hG' U' (Kb W) k hk
  have hx := ((hf _ _).1 h₂).trans ((hf _ _).1 h₁).symm
  have hs : s ≫ lab (k * d) q = s ≫ lab k p := e.symm.injective hx
  have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi (spMap em.toRingHom)).1 (congrArg (fun z => z.left) hs))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsTraitCompatibleLevelsMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabels_trait_compatible_levels_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → ∀ k d : ℕ, 1 ≤ k → 1 ≤ d → ∀ (p : QkPt D.toPre (Kb R) k) (q : QkPt D.toPre (Kb R) (k * d)), q.y = d • p.y → q.g = p.g → lab (k * d) q = lab k p := by
  first | exact @GlobalTheory.Mum.lab_level_mul | exact GlobalTheory.Mum.lab_level_mul | (intros; apply GlobalTheory.Mum.lab_level_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointMulLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointMulLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.QkMul

open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem exists_qk_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k d : ℕ) (p : QkPt D.toPre F k), ∃ q : QkPt D.toPre F (k * d), q.y = d • p.y ∧ q.g = p.g := by
  intro R _ _ _ D F _ _ k d p
  refine ⟨qkMk D.tau_bimult (d • p.y) p.g ?_, rfl, rfl⟩
  rw [mul_nsmul, qk_nsmul D.tau_bimult, map_nsmul]

end GlobalTheory.Mum.QkMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointMulLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPoint_mul_level : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k d : ℕ) (p : QkPt D.toPre F k), ∃ q : QkPt D.toPre F (k * d), q.y = d • p.y ∧ q.g = p.g := by
  first | exact @GlobalTheory.Mum.QkMul.exists_qk_mul | exact GlobalTheory.Mum.QkMul.exists_qk_mul | (intros; apply GlobalTheory.Mum.QkMul.exists_qk_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelingsEqOfThetaPointPairingsOrderN
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelingsEqOfThetaPointPairingsOrderN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LabelRigid

open GlobalTheory.LevelOfPairing

section Abstract

variable {G U : Type} [Group G] [CommGroup U] {W : G → G → U → Prop} {M : ℕ}

theorem eq_of_pairing (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hn : ∀ x : G, x ^ M = 1 → (∀ y, y ^ M = 1 → W x y 1) → x = 1) {a b : G} (ha : a ^ M = 1) (hb : b ^ M = 1)
    (h : ∀ y, y ^ M = 1 → ∃ c, W a y c ∧ W b y c) : a = b := by
  have ha' : a⁻¹ ^ M = 1 := by rw [inv_pow, ha, inv_one]
  refine inv_mul_eq_one.1 (hn _ (by rw [(cm _ _).mul_pow, ha', hb, _root_.mul_one]) fun y hy => ?_)
  obtain ⟨c, h₁, h₂⟩ := h y hy
  obtain ⟨d, hd, -⟩ := hu _ y ha' hy
  have e := hm _ _ _ _ _ hd h₁
  rw [inv_mul_cancel] at e
  exact (hu 1 y (one_pow _) hy).unique e (rel_one hu hm hy) ▸ hm _ _ _ _ _ hd h₂

theorem comb_eq (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hn : ∀ x : G, x ^ M = 1 → (∀ y, y ^ M = 1 → W x y 1) → x = 1) {I : Type} {y₁ y₂ : I → G}
    (t₁ : ∀ p, y₁ p ^ M = 1) (t₂ : ∀ p, y₂ p ^ M = 1) (s₂ : ∀ y, y ^ M = 1 → ∃ p, y₂ p = y)
    (hw : ∀ p q c, W (y₁ p) (y₁ q) c → W (y₂ p) (y₂ q) c) {r : ℕ} (b : Fin r → I) (a : Fin r → ℕ) (p : I)
    (hp : y₁ p = (List.ofFn fun i => y₁ (b i) ^ a i).prod) : y₂ p = (List.ofFn fun i => y₂ (b i) ^ a i).prod := by
  refine eq_of_pairing cm hu hm hn (t₂ p) (prod_pow_eq_one cm _ (fun i => t₂ (b i)) a) fun y hy => ?_
  obtain ⟨q, rfl⟩ := s₂ y hy
  choose c hc using fun i => (hu _ _ (t₁ (b i)) (t₁ q)).exists
  have o₁ := rel_one hu hm (t₁ q)
  have o₂ := rel_one hu hm (t₂ q)
  refine ⟨∏ i, c i ^ a i, hw _ _ _ ?_, rel_prod hm o₂ _ _ fun i => rel_pow hm o₂ (hw _ _ _ (hc i)) _⟩
  rw [hp]
  exact rel_prod hm o₁ _ _ fun i => rel_pow hm o₁ (hc i) _

end Abstract

theorem eq_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) {n j m : ℕ}
    (hn : n.Prime) (ho : Odd n) (hm : m = n ^ j * (n ^ 2) ^ 2) (hb : ((n ^ 2) ^ 2) ^ P.g * P.g.factorial < m)
    {I : Type} {y₁ y₂ : I → (baseOver (Sp K) ⟶ P.A)}
    (t₁ : ∀ p, y₁ p ^ (m ^ 2) = 1) (t₂ : ∀ p, y₂ p ^ (m ^ 2) = 1)
    (s₁ : ∀ y, y ^ (m ^ 2) = 1 → ∃ p, y₁ p = y) (s₂ : ∀ y, y ^ (m ^ 2) = 1 → ∃ p, y₂ p = y)
    (hw : ∀ p q c, WeilIs P.A P.L (m ^ 2 : ℕ) (y₁ p) (y₁ q) c → WeilIs P.A P.L (m ^ 2 : ℕ) (y₂ p) (y₂ q) c)
    (hfix : ∀ p, y₁ p ^ n = 1 → y₂ p = y₁ p) {v : I → Γ((baseOver (Sp K)).left, ⊤)}
    (v₁ : IsThetaPt P m y₁ v) (v₂ : IsThetaPt P m y₂ v) (p : I) : y₂ p = y₁ p := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have cm : ∀ a b : baseOver (Sp K) ⟶ P.A, Commute a b := fun a b => _root_.mul_comm a b
  have hm0 : m ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hK : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
  have : NeZero (m ^ 2) := ⟨hm0⟩
  have : NeZero ((m ^ 2 : ℕ) : K) := ⟨hK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  obtain ⟨lev⟩ := GlobalTheory.nonempty_level_of_isAlgClosed K P (m ^ 2) ζ hK hζ
  obtain ⟨hu, hmul, -⟩ := hL.weil _ P (m ^ 2) (baseOver (Sp K))
  have hnd := hL.weilNondeg K P (m ^ 2) hK
  choose b hb' using fun i => s₁ _ (lev.torsion i)
  have eb : lev.pt = fun i => y₁ (b i) := funext fun i => (hb' i).symm
  have comb : ∀ (a : Fin (2 * P.g) → ℕ) (q : I), y₁ q = linComb lev.pt a → y₂ q = linComb (fun i => y₂ (b i)) a :=
    fun a q h => comb_eq (W := fun a b u => WeilIs P.A P.L (m ^ 2 : ℕ) a b u) cm hu hmul hnd t₁ t₂ s₂ hw b a q
      (by rw [h, eb]; rfl)
  have prim : ∀ {T : Type} [CommRing T] [Nontrivial T] (φ : K →+* T),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ζ) (m ^ 2) := fun φ =>
    hζ.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  obtain ⟨lev', hl'⟩ := GlobalTheory.exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) P (m ^ 2) (unitOn ζ) lev.prim
    (fun F _ s => by
      have : Nontrivial Γ(Spec (CommRingCat.of F), ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)⟩
      rw [← map_natCast (Spec.preimage s).hom]
      exact (map_ne_zero _).2 hK) (fun i => y₂ (b i)) (fun i => t₂ _)
    (fun i k => hw _ _ _ (by rw [hb', hb']; exact lev.pairing i k))
  choose q hq using fun a => s₁ _ (ThetaPtDet.levelPoint_pow lev rfl a)
  have e₁ : (fun a => y₁ (q a)) = GlobalTheory.levelPoint lev rfl := funext hq
  have e₂ : (fun a => y₂ (q a)) = GlobalTheory.levelPoint lev' rfl := funext fun a =>
    (comb _ _ (hq a)).trans (by rw [← hl']; rfl)
  have w₁ := ThetaDescentLevel.isThetaPt_reindex v₁ q
  have w₂ := ThetaDescentLevel.isThetaPt_reindex v₂ q
  rw [e₁] at w₁
  rw [e₂] at w₂
  obtain ⟨φ, ⟨hφ, t, ht⟩, hl⟩ := GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.1 P.g n 2 j _ m hn ho le_rfl rfl hm hb K
    (Nat.cast_ne_zero.2 hn.ne_zero) P P rfl rfl _ lev lev' _ w₁ w₂
  have key : ∀ p, y₁ p ≫ φ.hom = y₂ p := fun p => by
    obtain ⟨d, hd⟩ := lev.span K (𝟙 _) (y₁ p) (t₁ p)
    have hd' : linComb lev.pt (fun i => (d i : ℕ)) = y₁ p :=
      (congrArg (linComb · _) (funext fun i => (Category.id_comp (lev.pt i)).symm)).trans hd
    rw [comb _ _ hd'.symm, ← hd', ThetaPtDet.linComb_comp, ← hl']
    exact congrArg (linComb · _) (funext hl)
  obtain ⟨w, hw'⟩ := LBIso.symm (⟨t, ht⟩ : LBIso _ _)
  have h3 : 3 ≤ n := by
    have := hn.two_le
    obtain ⟨c, rfl⟩ := ho
    omega
  have hid := MatchRigid.aut_eq_id hL P (𝟙 _) h3 (Nat.cast_ne_zero.2 hn.ne_zero) φ w hw' fun x hx => by
    have hd : n ∣ m ^ 2 := by
      rw [hm]
      exact dvd_pow (Dvd.dvd.mul_left (dvd_pow (dvd_pow_self n two_ne_zero) two_ne_zero) _) two_ne_zero
    obtain ⟨c, hc⟩ := hd
    obtain ⟨r, rfl⟩ := s₁ x (by rw [hc, pow_mul]; erw [hx]; exact one_pow _)
    exact (key r).trans (hfix r hx)
  rw [← key, hid, Category.comp_id]

theorem labels_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (n j m : ℕ), n.Prime → Odd n → m = n ^ j * (n ^ 2) ^ 2 → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < m → ∀ (x₁ x₂ : QkPt D (Kb R) (m ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D A (m ^ 2) x₁ → LabTors D A (m ^ 2) x₂ → (∀ p, x₁ p ^ n = 1 → x₂ p = x₁ p) → ∀ v : QkPt D (Kb R) (m ^ 2) → Kb R, IsThetaPt A m x₁ (fun p => GlobalTheory.Ex.fnOf (v p)) → IsThetaPt A m x₂ (fun p => GlobalTheory.Ex.fnOf (v p)) → ∀ p, x₂ p = x₁ p := by
  intro R _ _ _ D A n j m hn ho hm hb x₁ x₂ ⟨s₁, t₁, _, _, w₁⟩ ⟨s₂, t₂, _, _, w₂⟩ hfix v v₁ v₂ p
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  obtain ⟨P, g, hg, hP, hmul, hs⟩ := hL.polBaseChange _ (Sp (Kb R)) (jFK (R := R) (Kb R)) A
  have hp : IsGrpPullback P.A A.A _ g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hmul]
    rfl⟩
  have hl : LBIso P.L (A.L.pull g) := LBIso.symm hs
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp (Kb R))) (jFK (R := R) (Kb R)) (Category.id_comp _).symm
  have hE : ∀ x, x.left = (e.symm x).left ≫ g := fun x =>
    (congrArg (fun z => z.left) (e.apply_symm_apply x).symm).trans (he _)
  have kW : ∀ (s : Sp (Kb R) ⟶ Sp (FractionRing R)) (_ : s = 𝟙 _ ≫ jFK (R := R) (Kb R))
      (x y : baseOver (Sp (Kb R)) ⟶ P.A) (x₀ y₀ : Over.mk s ⟶ A.A) (c : Γ(Sp (Kb R), ⊤)ˣ),
      x₀.left = x.left ≫ g → y₀.left = y.left ≫ g →
      (WeilIs P.A P.L (m ^ 2 : ℕ) x y c ↔ WeilIs A.A A.L (m ^ 2 : ℕ) x₀ y₀ c) := by
    rintro s rfl x y x₀ y₀ c hx hy
    have := P.isAb.comm
    exact weilIs_grpPullback_of_comm' _ _ _ _ _ g _ _ A.isLB P.isLB hp hl (baseOver _) _ x y x₀ y₀ c hx hy
  have kT : ∀ (s : Sp (Kb R) ⟶ Sp (FractionRing R)) (_ : s = 𝟙 _ ≫ jFK (R := R) (Kb R))
      (x : QkPt D (Kb R) (m ^ 2) → (baseOver (Sp (Kb R)) ⟶ P.A)) (x₀ : QkPt D (Kb R) (m ^ 2) → (Over.mk s ⟶ A.A))
      (u : QkPt D (Kb R) (m ^ 2) → Γ(Sp (Kb R), ⊤)), (∀ i, (x₀ i).left = (x i).left ≫ g) →
      (∀ i, x i ^ m ^ 2 = 1) → IsThetaPt A m x₀ u → IsThetaPt P m x u := by
    rintro s rfl x x₀ u hx ht h
    exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp (Kb R))) hp hl hx ht _).2 h
  have tor : ∀ {k : ℕ} (x), x ^ k = 1 → e.symm x ^ k = 1 := fun x h => by rw [← map_pow, h, map_one]
  have tor' : ∀ {k : ℕ} (x), x ^ k = 1 → e x ^ k = 1 := fun x h => by rw [← map_pow, h, map_one]
  refine e.symm.injective (eq_of_isAlgClosed P hn ho hm (by rw [hP]; exact hb) (y₁ := fun p => e.symm (x₁ p))
    (y₂ := fun p => e.symm (x₂ p)) (fun p => tor _ (t₁ p)) (fun p => tor _ (t₂ p))
    (fun y hy => (s₁ _ (tor' y hy)).imp fun q h => (congrArg e.symm h).trans (e.symm_apply_apply y))
    (fun y hy => (s₂ _ (tor' y hy)).imp fun q h => (congrArg e.symm h).trans (e.symm_apply_apply y))
    (fun q q' c h => ?_) (fun q h => congrArg e.symm (hfix q ?_))
    (kT _ (Category.id_comp _).symm _ _ _ (fun i => hE _) (fun i => tor _ (t₁ i)) v₁)
    (kT _ (Category.id_comp _).symm _ _ _ (fun i => hE _) (fun i => tor _ (t₂ i)) v₂) p)
  · obtain ⟨z, rfl⟩ : ∃ z : (Kb R)ˣ, unitOn z = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Kb R))).hom.hom.toMonoidHom c, Units.ext
        ((Scheme.ΓSpecIso (CommRingCat.of (Kb R))).commRingCatIsoToRingEquiv.symm_apply_apply c.val)⟩
    exact (kW _ (Category.id_comp _).symm _ _ _ _ _ (hE _) (hE _)).2 ((w₂ _ _ _).1 ((w₁ _ _ _).2
      ((kW _ (Category.id_comp _).symm _ _ _ _ _ (hE _) (hE _)).1 h)))
  · exact (congrArg (· ^ n) (e.apply_symm_apply _).symm).trans (tor' _ h)

end GlobalTheory.Mum.LabelRigid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelingsEqOfThetaPointPairingsOrderNStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabelings_eq_of_thetaPoint_pairings_order_n : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (n j m : ℕ), n.Prime → Odd n → m = n ^ j * (n ^ 2) ^ 2 → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < m → ∀ (x₁ x₂ : QkPt D (Kb R) (m ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D A (m ^ 2) x₁ → LabTors D A (m ^ 2) x₂ → (∀ p, x₁ p ^ n = 1 → x₂ p = x₁ p) → ∀ v : QkPt D (Kb R) (m ^ 2) → Kb R, IsThetaPt A m x₁ (fun p => GlobalTheory.Ex.fnOf (v p)) → IsThetaPt A m x₂ (fun p => GlobalTheory.Ex.fnOf (v p)) → ∀ p, x₂ p = x₁ p := by
  first | exact @GlobalTheory.Mum.LabelRigid.labels_eq | exact GlobalTheory.Mum.LabelRigid.labels_eq | (intros; apply GlobalTheory.Mum.LabelRigid.labels_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemma
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaLevels

variable {R : Type} [CommRing R] [IsDomain R]

def galPt {A : PolAV (Sp (FractionRing R))} (σ : Kb R →ₐ[FractionRing R] Kb R) (y : TFK (R := R) (Kb R) ⟶ A.A) :
    TFK (R := R) (Kb R) ⟶ A.A :=
  Over.homMk (spMap σ.toRingHom ≫ y.left) (by
    rw [Category.assoc, Over.w y]
    show Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R))) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (Kb R)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) σ.comp_algebraMap)

theorem conj_eq_of_pow_eq_one [IsLocalRing R] (hR : Base R) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A) (hT : OneTrait D.toPre A lab) {n : ℕ} (hn : 1 ≤ n)
    (hnK : (n : Kb R) ≠ 0) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (hQ : ∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p')
    (hA : ∀ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ n = 1 → spMap σ.toRingHom ≫ y.left = y.left)
    {M d : ℕ} (hd : 1 ≤ d) (hM : M = n * d) (x₂ : QkPt D.toPre (Kb R) M → (TFK (R := R) (Kb R) ⟶ A.A))
    (hx₂ : ∀ p p', QkExt σ.toRingHom p p' → (x₂ p').left = spMap σ.toRingHom ≫ (lab M p).left)
    (h₂ : LabTors D.toPre A M x₂) (p' : QkPt D.toPre (Kb R) M) (hp' : lab M p' ^ n = 1) : x₂ p' = lab M p' := by
  subst hM
  have hnd : 1 ≤ n * d := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have T₁ := GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection R hR D A lab hT n hn
  have T₂ := GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection R hR D A lab hT (n * d) hnd
  obtain ⟨r, hr⟩ := T₁.1 _ hp'
  obtain ⟨q, hqy, hqg⟩ := GlobalTheory.T.exists_levelPoint_mul_level R D (Kb R) n d r
  have hq : lab (n * d) q = lab n r := GlobalTheory.T.torsionLabels_trait_compatible_levels_mul R hR D A lab hT n d hn hd r q hqy hqg
  have hqp : QkPt.Equiv D.toPre (Kb R) q p' := (T₂.2.2.1 q p').1 (hq.trans hr)
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom σ.comp_algebraMap hnK r
  obtain ⟨q₀, hq₀y, hq₀g⟩ := GlobalTheory.T.exists_levelPoint_mul_level R D (Kb R) n d r₀
  have hq₀ : QkExt σ.toRingHom q₀ q := by
    obtain ⟨y, g, e⟩ := q
    obtain ⟨y₀, g₀, e₀⟩ := q₀
    dsimp only at hqy hqg hq₀y hq₀g
    subst hqg hq₀g hqy hq₀y
    exact ⟨congrArg (d • ·) hr₀.1, hr₀.2.1, hr₀.2.2⟩
  have e₂ := hx₂ q₀ q hq₀
  rw [GlobalTheory.T.torsionLabels_trait_compatible_levels_mul R hR D A lab hT n d hn hd r₀ q₀ hq₀y hq₀g, (T₁.2.2.1 r₀ r).2 (hQ r₀ r hr₀), hr, hA _ hp'] at e₂
  exact ((h₂.2.2.1 q p').2 hqp).symm.trans (Over.OverMorphism.ext e₂)

end GlobalTheory.Mum.ThetaLevels


open GlobalTheory.Mum.ThetaLevels in
theorem GlobalTheory.Mum.thetaLevels_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, (∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p') ∧ ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left) → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ v : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → Kb R, IsThetaPt A (n ^ i) (lab ((n ^ i) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p') → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left := by
  intro R _ _ _ hR n hn ho hu D A lab hT hG
  have hch : CharZero R := hR.2
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ℕ, ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ j₀ * (n ^ 2) ^ 2 := by
    refine ⟨((n ^ 2) ^ 2) ^ A.g * A.g.factorial, ?_⟩
    have h1 : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ (((n ^ 2) ^ 2) ^ A.g * A.g.factorial) :=
      Nat.lt_pow_self hn.one_lt
    have h2 : 1 ≤ (n ^ 2) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)
    exact lt_of_lt_of_le h1 (Nat.le_mul_of_pos_right _ h2)
  refine ⟨j₀ + 4, fun i hi v hv hc σ p p' hpp' => ?_⟩
  have hmj : n ^ i = n ^ (i - 4) * (n ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hbound : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < (n ^ i) := by
    rw [hmj]
    exact lt_of_lt_of_le hj₀ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn.pos (by omega)))
  have hF : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have hKc : CharZero (Kb R) := charZero_of_injective_algebraMap (algebraMap (FractionRing R) (Kb R)).injective
  have hMK : (((n ^ i) ^ 2 : ℕ) : Kb R) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hn.ne_zero))
  choose pre hpre using fun p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) =>
    GlobalTheory.QkClosure.exists_qkExt_descent σ.toRingHom σ.comp_algebraMap hMK p'
  let x₂ : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A) := fun q => galPt σ (lab ((n ^ i) ^ 2) (pre q))
  have hx₂ : ∀ q q', QkExt σ.toRingHom q q' → (x₂ q').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) q).left := fun q q' h => by
    show spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) (pre q')).left = _
    rw [GlobalTheory.QkClosure.qkExt_inj σ.toRingHom σ.comp_algebraMap (hpre q') h]
  have hM1 : 1 ≤ (n ^ i) ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (pow_ne_zero _ hn.ne_zero))
  have H₁ := GlobalTheory.T.torsion_labels_one_trait_weil_pairing_bijection R hR D A lab hT ((n ^ i) ^ 2) hM1
  have H₂ := GlobalTheory.T.isTorsionLabeling_galoisConjugate_algClosure R hR D A σ ((n ^ i) ^ 2) hM1 (lab ((n ^ i) ^ 2)) x₂ H₁ hx₂
  have Hn : ∀ q, lab ((n ^ i) ^ 2) q ^ n = 1 → x₂ q = lab ((n ^ i) ^ 2) q := fun q hq =>
    conj_eq_of_pow_eq_one hR D A lab hT hn.one_lt.le (Nat.cast_ne_zero.2 hn.ne_zero) σ (hG σ).1 (hG σ).2
      (d := n ^ (2 * i - 1)) (Nat.one_le_pow _ _ hn.pos)
      (by rw [← pow_mul, ← pow_succ']; congr 1; omega) x₂ hx₂ H₂ q hq
  obtain ⟨c, hc'⟩ := hc σ
  have h₁ := GlobalTheory.ThetaDescentLevel.isThetaPt_reindex hv pre
  have h₂ := GlobalTheory.T.thetaPoint_conj_algClosure_automorphism R A (n ^ i) σ _ (fun q => lab ((n ^ i) ^ 2) (pre q)) x₂ (fun q => v (pre q)) (fun q => rfl) h₁
  have h₃ : IsThetaPt A (n ^ i) x₂ (fun q => GlobalTheory.Ex.fnOf (v q)) :=
    GlobalTheory.Ex.ThetaDescent.isThetaPt_unit_mul A (n ^ i) x₂ _ _ (GlobalTheory.Ex.fnOf ((c⁻¹ : (Kb R)ˣ) : Kb R))
      ((Units.isUnit c⁻¹).map _) (fun q => by
        unfold GlobalTheory.Ex.fnOf
        rw [← map_mul, hc' _ _ (hpre q), ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]) h₂
  have key := GlobalTheory.T.torsionLabelings_eq_of_thetaPoint_pairings_order_n R D.toPre A n (i - 4) (n ^ i) hn ho hmj hbound (lab ((n ^ i) ^ 2)) x₂ H₁ H₂ Hn v hv h₃ p'
  rw [← key]
  exact hx₂ p p' hpp'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelLabelsGaloisConjEqSerreLemmaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevelLabels_galoisConj_eq_serreLemma : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), OneTrait D.toPre A lab → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, (∀ p p' : QkPt D.toPre (Kb R) n, QkExt σ.toRingHom p p' → QkPt.Equiv D.toPre (Kb R) p p') ∧ ∀ x : TFK (R := R) (Kb R) ⟶ A.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left) → ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ v : QkPt D.toPre (Kb R) ((n ^ i) ^ 2) → Kb R, IsThetaPt A (n ^ i) (lab ((n ^ i) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) → (∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ c : (Kb R)ˣ, ∀ p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2), QkExt σ.toRingHom p p' → σ (v p) = c * v p') → ∀ (σ : Kb R →ₐ[FractionRing R] Kb R) (p p' : QkPt D.toPre (Kb R) ((n ^ i) ^ 2)), QkExt σ.toRingHom p p' → (lab ((n ^ i) ^ 2) p').left = spMap σ.toRingHom ≫ (lab ((n ^ i) ^ 2) p).left := by
  first | exact @GlobalTheory.Mum.thetaLevels_galois | exact GlobalTheory.Mum.thetaLevels_galois | (intros; apply GlobalTheory.Mum.thetaLevels_galois <;> assumption)
end
