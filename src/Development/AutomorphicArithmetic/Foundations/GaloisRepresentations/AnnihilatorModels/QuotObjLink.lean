module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplitHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OrdGen
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsHeckeCorrespondenceOnIntegralShimuraModel
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsPIsogenyKernelEqSubgroupScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelValueIndependent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagBundleMetricLine
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem existsUnique_of_openImmersion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (M : Model b N) (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (s₀ : Y₀ ⟶ M.X) (s : Y ⟶ M.X) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R) (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A), IsOpenImmersion i → i ≫ s = s₀ → m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → (∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y₀, y ≫ s₀ = x ∧ ∃ (m₀ : ObjMap o₁ o₀ y) (m₂ : ObjMap o₁' o₀' y), m₀.φ ≫ ψ₀.left = ψ₁.left ≫ m₂.φ) → ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y, y ≫ s = x ∧ ∃ (m₀ : ObjMap o₁ o y) (m₂ : ObjMap o₁' o' y), m₀.φ ≫ ψ.left = ψ₁.left ≫ m₂.φ := by
  intro p _ D R _ b N _ _ r w j c M Y₀ Y i s₀ s σ₀ σ o o' o₀ o₀' m m' ψ₀ ψ _ his hsq hfac hU S x o₁ o₁' m₁ ψ₁
    hp hisog htj
  have comp_map {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
      {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
      {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
      ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
    have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
      constructor
      · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
      · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
    have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
      intro c
      rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
    have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
      intro y
      rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
    have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
    have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
    have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
    exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩
  obtain ⟨y₀, ⟨hy₀, m₀, m₂, hsq₀⟩, huniq⟩ := hU S x o₁ o₁' m₁ ψ₁ hp hisog htj
  obtain ⟨a, ha⟩ := comp_map m₀ m
  obtain ⟨b, hb⟩ := comp_map m₂ m'
  refine ⟨y₀ ≫ i, ⟨by rw [Category.assoc, his, hy₀], a, b, ?_⟩, ?_⟩
  · rw [ha, hb]
    rw [Category.assoc, hsq, ← Category.assoc, hsq₀, Category.assoc]
  · rintro y ⟨hy, n₀, n₂, hsqn⟩
    obtain ⟨f₀, rfl⟩ := hfac S y hp
    obtain ⟨k₀, hk₀⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₀ m
    obtain ⟨k₂, hk₂⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ n₂ m'
    have hsqk : k₀.φ ≫ ψ₀.left = ψ₁.left ≫ k₂.φ := by
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, ← hsq, ← Category.assoc, hk₀, hsqn, ← hk₂]
      · rw [Category.assoc, Over.w ψ₀, k₀.cart.1.w, Category.assoc, k₂.cart.1.w, ← Category.assoc, Over.w ψ₁]
    have e := huniq f₀ ⟨by rw [← his, ← Category.assoc]; exact hy, k₀, k₂, hsqk⟩
    rw [e]

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePartialBlockMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem isTj_of_objMap_factor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R) (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A), m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ → (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) → IsTj r w j o₀ o₀' ψ₀ → IsTj r w j o o' ψ := by
  intro p _ D R _ b N r w j Y₀ Y i σ₀ σ o o' o₀ o₀' m m' ψ₀ ψ hψ hfac h k _ _ _ x
  have hpu : IsUnit ((p : ℕ) : Γ(Sp k, ⊤)) := by
    have hk : IsUnit ((p : ℕ) : k) := (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero).isUnit
    have := hk.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨x₀, hx₀⟩ := hfac (Sp k) x hpu
  obtain ⟨e, he, -⟩ := m.exists_ptEquiv (Over.mk x) x₀ hx₀
  obtain ⟨e', he', -⟩ := m'.exists_ptEquiv (Over.mk x) x₀ hx₀
  have hcomp : ∀ g₀ : Over.mk x₀ ⟶ o₀.A, e g₀ ≫ ψ = e' (g₀ ≫ ψ₀) := fun g₀ => by
    ext
    rw [Over.comp_left, he, he', Over.comp_left, Category.assoc, hψ, Category.assoc]
  have hker : ∀ g₀ : Over.mk x₀ ⟶ o₀.A, e g₀ ≫ ψ = 1 ↔ g₀ ≫ ψ₀ = 1 := fun g₀ => by
    rw [hcomp]; exact map_eq_one_iff _ e'.injective
  have hact : ∀ (g₀ : Over.mk x₀ ⟶ o₀.A) (c : D.O), e g₀ ≫ o.act.act c = e (g₀ ≫ o₀.act.act c) := fun g₀ c => by
    ext
    rw [Over.comp_left, he, he, Over.comp_left, Category.assoc, Category.assoc, m.act]
  have hkill : ∀ (v : Ideal (𝓞 D.F)) (g₀ : Over.mk x₀ ⟶ o₀.A), KilledBy o v (e g₀) ↔ KilledBy o₀ v g₀ :=
    fun v g₀ => forall₂_congr fun a _ => by rw [hact]; exact map_eq_one_iff _ e.injective
  obtain ⟨h1, h2⟩ := h k x₀
  refine ⟨fun g hg hu => ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := e.surjective g
    rw [hkill]
    rw [hker] at hg
    obtain ⟨n, hn⟩ := hu
    exact h1 g₀ hg ⟨n, (hkill _ g₀).1 hn⟩
  · rw [← h2]
    exact Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv fun g₀ => by
      change _ ↔ e g₀ ≫ ψ = 1 ∧ KilledBy o w (e g₀)
      rw [hker, hkill]).symm)

end GlobalTheory.UPel.HT.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarQuotientStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.NormCover

theorem isIso_ι_of_eq_top {Z : Scheme.{0}} (V : Z.Opens) (hV : V = ⊤) : IsIso V.ι := by
  rw [← Z.isoOfEq_hom_ι hV, ← Z.topIso_hom]
  infer_instance

theorem isUnit_of_basicOpen_eq_top {Z : Scheme.{0}} (a : Γ(Z, ⊤)) (h : Z.basicOpen a = ⊤) : IsUnit a :=
  Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Z.mem_basicOpen _ x hx).1 (h.ge hx)

theorem preimage_eq_top {X Y₀ : Scheme.{0}} (U : X.Opens) (g : Y₀ ⟶ U) : (g ≫ U.ι) ⁻¹ᵁ U = ⊤ := by
  refine top_unique fun x _ => ?_
  change (g ≫ U.ι) x ∈ U
  rw [Scheme.Hom.comp_apply]
  exact (g x).2

theorem exists_normalization_of_etale {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y₀ : Scheme.{0}} (π : X ⟶ Sp R) [Smooth π] (U : X.Opens) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (g : Y₀ ⟶ U) [IsFinite g] [Etale g] (hchar : ∀ y : Y₀, CharZero (Y₀.residueField y)) :
    ∃ (Y : Scheme.{0}) (s : Y ⟶ X) (i : Y₀ ⟶ Y), IsOpenImmersion i ∧ IsDominant i ∧ i ≫ s = g ≫ U.ι ∧
      IsFinite s ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ Flat (s ≫ π) ∧
      IsLocallyNoetherian Y ∧
      ∀ (S : Scheme.{0}) (f : S ⟶ Y), Set.range (f ≫ s) ⊆ U → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f := by
  let s₀ := g ≫ U.ι
  haveI : QuasiCompact s₀ := inferInstance
  haveI : QuasiSeparated s₀ := inferInstance
  haveI : Smooth (s₀ ≫ π) := inferInstance
  haveI : GlobalTheory.IsNormalScheme Y₀ := GlobalTheory.isNormalScheme_of_smooth (s₀ ≫ π)
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian (s₀ ≫ π)
  haveI : IsReduced Y₀ := inferInstance
  haveI hfin : IsFinite s₀.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_locallyOfFiniteType (o := CommRingCat.of R) s₀ π fun y _ => hchar y
  haveI : GlobalTheory.IsNormalScheme s₀.normalization := GlobalTheory.IsNormalScheme.normalization s₀
  have htop₀ : s₀ ⁻¹ᵁ U = ⊤ := preimage_eq_top U g
  haveI : IsIntegralHom (s₀ ∣_ U) := by
    haveI := isIso_ι_of_eq_top _ htop₀
    have e : s₀ ∣_ U = (s₀ ⁻¹ᵁ U).ι ≫ g := by
      rw [← cancel_mono U.ι, morphismRestrict_ι, Category.assoc]
    rw [e]
    infer_instance
  let W := s₀.fromNormalization ⁻¹ᵁ U
  haveI hiso : IsIso (s₀.toNormalization ∣_ W) := GlobalTheory.isIso_toNormalization_morphismRestrict s₀ U
  have htop : s₀.toNormalization ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun x _ => ?_
    change s₀.fromNormalization (s₀.toNormalization x) ∈ U
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact (g x).2
  haveI := isIso_ι_of_eq_top _ htop
  have hi : s₀.toNormalization = inv (s₀.toNormalization ⁻¹ᵁ W).ι ≫ (s₀.toNormalization ∣_ W) ≫ W.ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  haveI : Flat (s₀.toNormalization ≫ s₀.fromNormalization ≫ π) := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  refine ⟨s₀.normalization, s₀.fromNormalization, s₀.toNormalization, ?_, inferInstance,
    Scheme.Hom.toNormalization_fromNormalization s₀, hfin,
    fun y => ((GlobalTheory.isNormalScheme_iff _).mp inferInstance y).2,
    GlobalTheory.flat_normalization s₀ (s₀.fromNormalization ≫ π),
    LocallyOfFiniteType.isLocallyNoetherian s₀.fromNormalization, ?_⟩
  · rw [hi]
    infer_instance
  · intro S f hf
    have hr : Set.range f ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hf ⟨x, rfl⟩
    refine ⟨IsOpenImmersion.lift W.ι f hr ≫ inv (s₀.toNormalization ∣_ W) ≫ (s₀.toNormalization ⁻¹ᵁ W).ι, ?_⟩
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]

end GlobalTheory.UPel.HT.ES.NormCover

namespace GlobalTheory.UPel.HT.ES.NormCover

theorem exists_finite_normal_model : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (M : Model b N) (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ M.X) (g : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), IsFinite g → Etale g → g ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → ∃ (Y : Scheme.{0}) (s : Y ⟶ M.X) (i : Y₀ ⟶ Y), IsOpenImmersion i ∧ IsDominant i ∧ i ≫ s = s₀ ∧ IsFinite s ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ Flat (s ≫ M.s) ∧ IsLocallyNoetherian Y ∧ (∀ (S : Scheme.{0}) (f : S ⟶ Y), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ f₀ : S ⟶ Y₀, f₀ ≫ i = f) := by
  intro p _ D R _ _ _ _ b N _ M Y₀ s₀ g hgf hge hs
  subst hs
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  have hp : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := by
    apply isUnit_of_basicOpen_eq_top
    have h := preimage_eq_top (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) g
    rw [Scheme.Hom.preimage_basicOpen, map_natCast] at h
    exact h
  have hcop : ∀ m : ℕ, m.Coprime p → IsUnit ((m : ℕ) : Γ(Y₀, ⊤)) := by
    intro m hm
    have := (b.unit m hm).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (g ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι ≫ M.s).appTop).hom
    rwa [map_natCast] at this
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : ℕ) : Γ(Y₀, ⊤)) := by
    intro n hn
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
    push_cast
    exact (hp.pow a).mul (hcop m ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm).symm)
  have hchar : ∀ y : Y₀, CharZero (Y₀.residueField y) := by
    intro y
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra h
    have := (hunit n h).map (Y₀.Γevaluation y).hom
    rw [map_natCast, hn] at this
    exact not_isUnit_zero this
  obtain ⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_normalization_of_etale M.s _ g hchar
  refine ⟨Y, s, i, h1, h2, h3, h4, h5, h6, h7, fun S f hpS => h8 S f ?_⟩
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ (f ≫ s) ⁻¹ᵁ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) := by
    rw [Scheme.Hom.preimage_basicOpen, map_natCast]
    have hpS' : IsUnit ((p : ℕ) : Γ(S, (f ≫ s) ⁻¹ᵁ ⊤)) := hpS
    exact (Scheme.basicOpen_of_isUnit S hpS').ge trivial
  exact hx

end GlobalTheory.UPel.HT.ES.NormCover
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MEsNorm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem UpperTheory.Gal.crystallineComparison.Mod.esNorm_of (hG : UpperTheory.Gal.crystallineComparison.Mod.EsGen) : UpperTheory.Gal.crystallineComparison.Mod.EsNorm := by
  intro p _ D R _ _ _ _ b N h3 hcop hp r w j c hw hu hj hc hm M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, hst₀, hgs, hgt, hfgs, hegs, hfgt, hegt, hiso₀, htj₀, huniv₀⟩ :=
    hG p D R b N h3 hcop hp r w j c hw hu hj hc hm M
  obtain ⟨Y, s, i, hio, hid, hi, hfs, hnorm, hflat, hnoeth, hext⟩ :=
    NormCover.exists_finite_normal_model p D R b N hp M Y₀ s₀ gs hfgs hegs hgs
  obtain ⟨t, hit, ht, hft⟩ := GlobalTheory.ExtT.exists_finite_extension p D R b N h3 hcop hp r w j c hw hu hj hc hm M
    Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst₀ hgs hgt hfgs hegs hfgt hegt hiso₀ htj₀ Y s i hio hid hi hfs hnorm hflat
    hnoeth hext
  have hred : AlgebraicGeometry.IsReduced Y :=
    isReduced_normalModel_of_generic p D R b N hp M Y₀ s₀ gs hgs hegs Y s i hio hi hflat hext
  have hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y) := fun y => by
    have := hnorm y
    let A := Y.presheaf.stalk y
    refine (isDomain_iff_noZeroDivisors_and_nontrivial A).2 ⟨⟨?_⟩, inferInstance⟩
    intro a b hab
    let I : Ideal A := Ideal.span {a}
    let J : Ideal A := I ⊔ I.annihilator
    -- The sum of an ideal and its annihilator is faithful in a reduced ring.
    have : FaithfulSMul A J := Module.annihilator_eq_bot.mp <| by
      change J.annihilator = ⊥
      rw [show J = I ⊔ I.annihilator from rfl, Submodule.annihilator_sup, eq_bot_iff]
      intro z hz
      have hzz : z * z = 0 := Submodule.mem_annihilator.mp hz.2 z hz.1
      have hz0 : z = 0 := IsNilpotent.eq_zero ⟨2, by simpa only [pow_two] using hzz⟩
      simpa using hz0
    obtain ⟨s, hs, hreg⟩ := Ideal.nonempty_inter_nonZeroDivisors_of_faithfulSMul (I := J)
    obtain ⟨u, v, hv, rfl⟩ := Ideal.mem_span_singleton_sup.mp hs
    have hva : v * a = 0 := Submodule.mem_annihilator.mp hv a (Ideal.mem_span_singleton_self a)
    -- The fraction (u * a) / (u * a + v) is integral because it is idempotent.
    let F := FractionRing A
    let d : nonZeroDivisors A := ⟨u * a + v, hreg⟩
    let e : F := IsLocalization.mk' F (u * a) d
    let f := algebraMap A F
    have hf : Function.Injective f := IsFractionRing.injective A F
    have he : e * f (u * a + v) = f (u * a) := IsLocalization.mk'_spec F (u * a) d
    have hu : IsUnit (f (u * a + v)) := IsLocalization.map_units F d
    have hidem : e * e = e := by
      apply hu.mul_right_cancel
      apply hu.mul_right_cancel
      have hmul : f (u * a) * f (u * a + v) = f (u * a) * f (u * a) := by
        rw [← map_mul, ← map_mul, mul_add, mul_assoc u a v, mul_comm a v, hva, mul_zero, add_zero]
      calc e * e * f (u * a + v) * f (u * a + v)
          = (e * f (u * a + v)) * (e * f (u * a + v)) := by ring
        _ = f (u * a) * f (u * a) := by rw [he]
        _ = f (u * a) * f (u * a + v) := hmul.symm
        _ = e * f (u * a + v) * f (u * a + v) := by rw [he]
    have hint : IsIntegral A e := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
      simp [Polynomial.eval₂_sub, pow_two, hidem]
    obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
    have hcc : c * c = c := hf (by rw [map_mul, hc, hidem])
    have hcs : c * (u * a + v) = u * a := hf (by rw [map_mul, hc, he])
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with h | h
    · have hc1 : c = 1 := h.mul_left_cancel (by rw [hcc, _root_.mul_one])
      have hs : u * a + v = u * a := by simpa [hc1] using hcs
      right
      apply (mem_nonZeroDivisors_iff_left.mp hreg) b
      rw [hs, _root_.mul_assoc, hab, mul_zero]
    · have hc0 : c = 0 := h.mul_right_eq_zero.mp (by rw [sub_mul, _root_.one_mul, hcc, sub_self])
      have hua : u * a = 0 := by simpa [hc0] using hcs.symm
      left
      apply (mem_nonZeroDivisors_iff_right.mp hreg) a
      rw [hua, zero_add, mul_comm, hva]
  obtain ⟨o, ⟨ms⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X Y M.s s M.univ
  have hpt := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X Y M.s t M.univ
  rw [ht] at hpt
  obtain ⟨o', ⟨mt⟩⟩ := hpt
  subst hi
  subst hit
  obtain ⟨m, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ ms₀ ms
  obtain ⟨m', -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ mt₀ mt
  obtain ⟨ψ, hiso, hcomm⟩ := PIsogExt.exists_isPIsog_extend p D R b N h3 hcop j c hc Y₀ Y i _ _ hio hid hnoeth
    hnorm hdom o o' o₀ o₀' m m' ψ₀ hiso₀
  refine ⟨Y, s, t, o, o', ms, mt, ψ, ht.symm, hfs, hft, hnorm, hflat, hiso, ?_, ?_⟩
  · exact isTj_of_objMap_factor p D R b N r w j Y₀ Y i _ _ o o' o₀ o₀' m m' ψ₀ ψ hcomm hext htj₀
  · exact existsUnique_of_openImmersion p D R b N h3 hcop r w j c M Y₀ Y i (i ≫ s) s _ _ o o' o₀ o₀' m m'
      ψ₀ ψ hio rfl hcomm hext huniv₀
end

namespace UpperTheory.Gal.crystallineComparison.Mod

theorem esGen_link : EsGen := UpperTheory.Cb.exists_heckeCorrespondence_on_integral_shimuraModel
theorem esNorm_link : EsNorm := esNorm_of esGen_link
theorem ordGen_link : OrdGen := UpperTheory.Gal.Ord.ordGen
theorem quotObj_link : QuotObj := UpperTheory.Cb.exists_pIsogeny_kernel_eq_subgroupScheme
theorem congKS_link : CongKS := congKS_holds esNorm_link esGen_link ordGen_link quotObj_link

end UpperTheory.Gal.crystallineComparison.Mod
