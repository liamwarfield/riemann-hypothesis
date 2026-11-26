module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteDimensionalField
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ImHermFormEqCurveForm
section -- merged from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CurveFormSign
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Maps

variable {S X Y : Scheme.{0}} (C : Over S) (G : Over X) (f : Y ⟶ S) (x : Y ⟶ X)

abbrev MapOver : Type := Over.mk (pullback.snd C.hom f ≫ x) ⟶ G

variable {C G f x}

end Maps

section Clauses

variable {S X Y : Scheme.{0}} {C : Over S} [GrpObj C] {G : Over X} [GrpObj G] {f : Y ⟶ S} {x : Y ⟶ X}

end Clauses

end GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign

namespace GlobalTheory.CMPointCompare

section Dictionary

variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} {B G' : Over Y} [GrpObj C] [GrpObj G] [GrpObj B] [GrpObj G']
  {f : Y ⟶ S} {x : Y ⟶ X} {β : B.left ⟶ C.left} {π : G'.left ⟶ G.left}

variable (hβ : IsGrpPullback B C f β) (hπ : IsGrpPullback G' G x π)

end Dictionary

section Intertwine

variable {S X Y : Scheme.{0}} {C : Over S} {G : Over X} [GrpObj C] [GrpObj G] {f : Y ⟶ S} {x : Y ⟶ X}
  {Φ : MapOver C G f x}

end Intertwine

section General

open GlobalTheory.CM

theorem hom_ext_of_complexPoints {R : Type} [CommRing R] (σ : R →+* ℂ) (hσ : Function.Injective σ)
    {B G : Over (Sp R)} [Smooth B.hom] [IsSeparated G.hom] {a b : B ⟶ G}
    (h : ∀ p : Over.mk (spMap σ) ⟶ B, p ≫ a = p ≫ b) : a = b := by
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom σ) hσ
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback B.hom (spMap σ)) ?_
  have : IsReduced (pullback B.hom (spMap σ)) :=
    isReduced_of_smooth_complex _ (pullback.snd B.hom (spMap σ)) inferInstance
  refine ComplexPoints.hom_ext_of_points (pullback.snd B.hom (spMap σ)) G.hom (by simp) fun x hx => ?_
  have e := congrArg (fun z => z.left) (h (Over.homMk (x ≫ pullback.fst _ _) (by
    show (x ≫ _) ≫ _ = spMap σ
    rw [Category.assoc, pullback.condition, reassoc_of% hx])))
  exact (Category.assoc _ _ _).symm.trans (e.trans (Category.assoc _ _ _))

end General

section Linear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)

end Linear

end GlobalTheory.CMPointCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmExistsOnOfPointCarriesObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CMExistsCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

section Triples

variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem sab_lbIso {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem exists_ptEquiv {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {x' : T ⟶ S'} {x : T ⟶ S} (h : x' ≫ f = x) :
    ∃ p : (Over.mk x' ⟶ t'.G) ≃* (Over.mk x ⟶ t.G), ∀ u, (p u).left = u.left ≫ m.φ :=
  LiePull.exists_pushEquiv m.cart (Over.mk x') x h.symm

theorem pt_ext {f : S' ⟶ S} (m : SABMap t' t f) {T : Scheme.{0}} {u v : T ⟶ t'.G.left} (h₁ : u ≫ m.φ = v ≫ m.φ)
    (h₂ : u ≫ t'.G.hom = v ≫ t'.G.hom) : u = v :=
  m.cart.1.hom_ext h₁ h₂

end Triples

section Extend

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem spMap_int (j : K →+* K') {σ : K →+* ℂ} {σ' : K' →+* ℂ} (h : σ'.comp j = σ) :
    spMap (σ'.comp (algebraMap (𝓞 K') K')) ≫ spMap (RingOfIntegers.mapRingHom j) =
      spMap (σ.comp (algebraMap (𝓞 K) K)) := by
  rw [spMap_comp', ← h]
  rfl

theorem exists_cmObj_extend {ρ : 𝓞 K} {σ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ p q) (j : K →+* K') (σ' : K' →+* ℂ)
    (h : σ'.comp j = σ) :
    ∃ (X' : CMObj H K' (RingOfIntegers.mapRingHom j ρ) σ' p q)
      (a : ∀ b, SABMap (X'.A b).t (X.A b).t (spMap (RingOfIntegers.mapRingHom j)))
      (mb : SABMap X'.B.t X.B.t (spMap (RingOfIntegers.mapRingHom j))),
      X'.hh = X.hh ∧ ∀ i, (X'.φ i).left ≫ mb.φ = (a i.isLeft).φ ≫ (X.φ i).left := by
  set f := RingOfIntegers.mapRingHom j with hf
  have hinj : Function.Injective f := fun a b e => Subtype.ext (j.injective (congrArg Subtype.val e))
  choose A' a _ using fun b => PAT.exists_pullback E H _ _ (spMap f) (X.A b)
  obtain ⟨B', mb, -⟩ := PAT.exists_pullback E H _ _ (spMap f) X.B
  have hmon : ∀ i, IsMonHom (X.φ i) := fun i => (X.lin i).1
  choose φ' hφm hφ using fun i : Fin p ⊕ Fin q => PairingFibre.exists_hom (a i.isLeft).cart mb.cart (X.φ i)
  have hpt := spMap_int j h
  refine ⟨{ split := ((splits_basic E).2.2 K).2.2 K' j X.split |>.1
            ρ_sq := by rw [← map_pow, X.ρ_sq, map_neg, map_natCast]
            A := A', B := B'
            typeP := (hasType_baseChange E H _ _ f _ _ (a true) ρ 1 0).1 hinj X.typeP
            typeM := (hasType_baseChange E H _ _ f _ _ (a false) ρ 0 1).1 hinj X.typeM
            typeB := (hasType_baseChange E H _ _ f _ _ mb ρ p q).1 hinj X.typeB
            hh := X.hh, φ := φ', lin := fun i => ?_, onto := fun y => ?_, weil := fun i => ?_ }, a, mb, rfl, hφ⟩
  · refine ⟨hφm i, fun c => Over.OverMorphism.ext (pt_ext mb ?_ (by rw [Over.w, Over.w]))⟩
    have e := congrArg Over.Hom.left ((X.lin i).2 c)
    simp only [Over.comp_left] at e
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, mb.act, ← Category.assoc,
      (a i.isLeft).act, Category.assoc, e, ← Category.assoc, ← hφ, Category.assoc]
  · obtain ⟨pB, hB⟩ := exists_ptEquiv mb hpt
    choose pA hA using fun b => exists_ptEquiv (a b) hpt
    obtain ⟨x, hx⟩ := X.onto (pB y)
    refine ⟨fun i => (pA i.isLeft).symm (x i), pB.injective ?_⟩
    rw [hx, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    apply Over.OverMorphism.ext
    simp only [Function.comp_apply]
    rw [hB, Over.comp_left, Over.comp_left, Category.assoc]
    erw [hφ]
    rw [← Category.assoc, ← hA, MulEquiv.apply_symm_apply]
  · refine (PairingFibre.weilEq_iff (a i.isLeft).cart (a i.isLeft).cart mb.cart (a i.isLeft).cart X.B.t.PP.isLB
      (X.A i.isLeft).t.PP.isLB B'.t.PP.isLB (A' i.isLeft).t.PP.isLB (sab_lbIso mb) (sab_lbIso (a i.isLeft)) (hφ i) (hφ i)
      ((a i.isLeft).act _) (g₂ := 𝟙 _) (by simp) _).2 ?_
    rw [hpt]
    exact X.weil i

end Extend

section Conclusions

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {Pe : D'.La →+ (Fin g → ℂ)} {hP : IsPeriod D' ty Pe}

variable {Xo} {Z : CMLat hP D.p D.q} {x : Sp ℂ ⟶ Xo.X} {e : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)}
  {K' : Type} [Field K'] [NumberField K'] {κ : KA l →+* K'} {σ' : K' →+* ℂ} {k : IntermediateField ℚ ℂ}

end Conclusions

section ChangeOfExp

variable {D₁ D₂ : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)}

end ChangeOfExp

section Point

end Point

section Tensor

end Tensor

end GlobalTheory.CMExistsCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ValuationEqOrdAndEqZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.OrdVal

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem nonneg_of_isIntegral (u : AddValuation A (WithTop ℤ))
    (hu : ∀ r : O, 0 ≤ u (algebraMap O A r)) {x : A} (hx : IsIntegral O x) : 0 ≤ u x := by
  let v : Valuation A (Multiplicative (WithTop ℤ)ᵒᵈ) := u
  let f : O →+* v.integer := (algebraMap O A).codRestrict v.integer (fun r => hu r)
  have h1 : IsIntegral v.integer x := by
    obtain ⟨p, hp, hz⟩ := hx
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hz
  exact (Valuation.integer.integers v).mem_of_integral h1

def centre (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A)) :
    Ideal ↥(As O A) where
  carrier := {a | 0 < u (a : A)}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have := u.map_add (a : A) b
    exact lt_of_lt_of_le (lt_min ha hb) this
  smul_mem' := fun c a ha => by
    change 0 < u ((c : A) * a)
    rw [u.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (hu c))

theorem centre_isPrime (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A)) :
    (centre u hu).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} h => ?_⟩
  · have : (1 : ↥(As O A)) ∈ centre u hu := h ▸ Submodule.mem_top
    change 0 < u (1 : A) at this
    simp at this
  · change 0 < u ((a : A) * b) at h
    by_contra hn
    rw [not_or] at hn
    have ha : u (a : A) = 0 := le_antisymm (not_lt.1 hn.1) (hu a)
    have hb : u (b : A) = 0 := le_antisymm (not_lt.1 hn.2) (hu b)
    rw [u.map_mul, ha, hb] at h
    simp at h

theorem centre_isMaximal (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A))
    {ϖ : O} (hϖ : Irreducible ϖ) (hpos : 0 < u (algebraMap O A ϖ)) :
    (centre u hu).IsMaximal := by
  haveI := centre_isPrime u hu
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) _ ?_
  have hle : IsLocalRing.maximalIdeal O ≤ (centre u hu).comap (algebraMap O ↥(As O A)) := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
    exact hpos
  have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  change ((centre u hu).comap (algebraMap O ↥(As O A))).IsMaximal
  rw [← this]
  infer_instance

theorem le_of_vL_le (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A))
    (ζ : Pts O A) [IsDVRAt ζ] (hζ : ∀ a : ↥(As O A), a ∉ ζ.asIdeal → u (a : A) = 0)
    {a b : ↥(As O A)} (hab : vL ζ a ≤ vL ζ b) : u (a : A) ≤ u (b : A) := by
  rw [vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
  obtain ⟨z, hz⟩ := hab
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj ζ.asIdeal.primeCompl z
  have h1 : algebraMap _ (Loc ζ) (b * s) = algebraMap _ (Loc ζ) (a * x) := by
    simp only at hs
    rw [map_mul, map_mul, hz, mul_assoc, hs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h1
  have h2 : ((c : ↥(As O A)) : A) * ((b : A) * ((s : ↥(As O A)) : A))
      = ((c : ↥(As O A)) : A) * ((a : A) * (x : A)) := congrArg Subtype.val hc
  have h3 := congrArg u h2
  rw [u.map_mul, u.map_mul, u.map_mul, u.map_mul, hζ _ c.2, hζ _ s.2, zero_add, zero_add,
    add_zero] at h3
  rw [h3]
  exact le_add_of_nonneg_right (hu x)

theorem exists_vL_eq_one (ζ : Pts O A) [IsDVRAt ζ] : ∃ a : ↥(As O A), vL ζ a = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ)
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj ζ.asIdeal.primeCompl π
  refine ⟨x, ?_⟩
  have h0 := (vL_eq_zero_iff ζ s).2 s.2
  rw [vL_eq_addVal] at h0
  simp only at hs
  rw [vL_eq_addVal, ← hs, IsDiscreteValuationRing.addVal_mul, h0,
    IsDiscreteValuationRing.addVal_uniformizer hπ, add_zero]

theorem exists_ord_eq [∀ ζ : Pts O A, IsDVRAt ζ] {ϖ : O} (h : IsUnif A ϖ)
    (u : AddValuation A (WithTop ℤ)) (hO : ∀ r : O, 0 ≤ u (algebraMap O A r))
    (hpos : 0 < u (algebraMap O A ϖ)) (hone : ∃ a, u a = 1) :
    ∃ ζ : Pts O A, ∀ a : A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = u a := by
  have hu : ∀ a : ↥(As O A), 0 ≤ u (a : A) := fun a => nonneg_of_isIntegral u hO a.2
  let ζ : Pts O A := ⟨centre u hu, centre_isMaximal u hu h.irreducible hpos⟩
  have hζ : ∀ a : ↥(As O A), a ∉ ζ.asIdeal → u (a : A) = 0 :=
    fun a ha => le_antisymm (not_lt.1 ha) (hu a)
  obtain ⟨a₀, ha₀⟩ := exists_vL_eq_one ζ
  have hfin : ∀ (b : ↥(As O A)) (m : ℕ), vL ζ b = m → u (b : A) = m • u (a₀ : A) := by
    intro b m hb
    have e : vL ζ (a₀ ^ m) = vL ζ b := by rw [vL_pow, ha₀, hb]; simp
    have := le_antisymm (le_of_vL_le u hu ζ hζ e.ge) (le_of_vL_le u hu ζ hζ e.le)
    rw [this, SubmonoidClass.coe_pow, u.map_pow]
  have htop : ∀ b : ↥(As O A), vL ζ b = ⊤ → u (b : A) = ⊤ := by
    intro b hb
    have := le_of_vL_le u hu ζ hζ (a := 0) (b := b) (by rw [hb]; exact le_top)
    simpa using this
  have hϖ : u (algebraMap O A ϖ) = ep ϖ ζ • u (a₀ : A) :=
    hfin (algebraMap O ↥(As O A) ϖ) _ (coe_ep ζ h).symm
  have hϖfin : u (algebraMap O A ϖ) ≠ ⊤ := by
    obtain ⟨y, hy⟩ := h.isUnit.exists_right_inv
    intro ht
    have := congrArg u hy
    rw [u.map_mul, ht, u.map_one] at this
    simp at this
  have ha₀fin : u (a₀ : A) ≠ ⊤ := by
    intro ht
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ep_pos ζ h).ne'
    rw [hϖ, ht, hk, succ_nsmul] at hϖfin
    simp at hϖfin
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 ha₀fin
  have hq0 : 0 ≤ q := by
    have := hu a₀
    rw [← hq] at this
    exact_mod_cast this
  have key : ∀ x : A, (Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨
      ∃ k : ℤ, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ x = (k : WithTop ℤ) ∧ u x = ((k * q : ℤ) : WithTop ℤ) := by
    intro x
    obtain ⟨n, hn⟩ := h.denom x
    have e1 : u (ϖ ^ n • x) = ((n * (ep ϖ ζ * q) : ℤ) : WithTop ℤ) + u x := by
      rw [Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖ, ← hq, ← WithTop.coe_nsmul,
        ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul]
    rw [ord_eq ζ h hn, ordAt]
    cases hv : vL ζ ⟨ϖ ^ n • x, hn⟩ with
    | top =>
      left
      refine ⟨by simp, ?_⟩
      have := htop _ hv
      change u (ϖ ^ n • x) = ⊤ at this
      rw [e1, WithTop.add_eq_top] at this
      exact this.resolve_left WithTop.coe_ne_top
    | coe m =>
      right
      refine ⟨m + -(n * ep ϖ ζ), by rw [ENat.map_natCast, ← WithTop.coe_add], ?_⟩
      have := hfin _ m hv
      change u (ϖ ^ n • x) = _ at this
      rw [e1, ← hq, ← WithTop.coe_nsmul, nsmul_eq_mul] at this
      have hx : u x ≠ ⊤ := by
        intro ht
        rw [ht, add_top] at this
        exact WithTop.top_ne_coe this
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hx
      rw [← ht, ← WithTop.coe_add, WithTop.coe_inj] at this
      rw [← ht, WithTop.coe_inj]
      linarith
  have hq1 : q = 1 := by
    obtain ⟨a, ha⟩ := hone
    rcases key a with ⟨_, h2⟩ | ⟨k, _, h2⟩
    · rw [ha] at h2
      exact absurd h2 WithTop.one_ne_top
    · rw [ha, ← WithTop.coe_one, WithTop.coe_inj] at h2
      exact Int.eq_one_of_mul_eq_one_left hq0 h2.symm
  refine ⟨ζ, fun a => ?_⟩
  rcases key a with ⟨h1, h2⟩ | ⟨k, h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, hq1, mul_one]

theorem eq_zero_of_ord_eq_top [∀ ζ : Pts O A, IsDVRAt ζ] {ϖ : O} (h : IsUnif A ϖ) (a : A)
    (ha : ∀ ζ : Pts O A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = ⊤) : a = 0 := by
  obtain ⟨n, hn⟩ := h.denom a
  have key : (⟨ϖ ^ n • a, hn⟩ : ↥(As O A)) ∈ (⊥ : Ideal ↥(As O A)) := by
    have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) ⟨ϖ ^ n • a, hn⟩ ∈
        Ideal.map (algebraMap ↥(As O A) (Loc ζ)) ⊥ := by
      intro ζ
      have h1 := ha ζ
      rw [ord_eq ζ h hn, ordAt, WithTop.add_eq_top] at h1
      have h2 : vL ζ ⟨ϖ ^ n • a, hn⟩ = ⊤ := by
        simpa using h1.resolve_right WithTop.coe_ne_top
      rw [(vL_eq_top_iff ζ _).1 h2]
      exact Submodule.zero_mem _
    exact Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩)
  have h2 : ϖ ^ n • a = 0 := congrArg Subtype.val (Ideal.mem_bot.1 key)
  rw [Algebra.smul_def, map_pow] at h2
  exact ((h.isUnit.pow n).mul_right_eq_zero).1 h2

theorem valuation_eq_ord_and_eq_zero :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] [∀ ζ : Pts O A, IsDVRAt ζ] (ϖ : O), IsUnif A ϖ → (∀ u : AddValuation A (WithTop ℤ), (∀ r : O, 0 ≤ u (algebraMap O A r)) → 0 < u (algebraMap O A ϖ) → (∃ a, u a = 1) → ∃ ζ : Pts O A, ∀ a : A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = u a) ∧ ∀ a : A, (∀ ζ : Pts O A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = ⊤) → a = 0 :=
  fun _ _ _ _ _ _ _ _ _ h => ⟨exists_ord_eq h, eq_zero_of_ord_eq_top h⟩

end GlobalTheory.OrdVal
end
