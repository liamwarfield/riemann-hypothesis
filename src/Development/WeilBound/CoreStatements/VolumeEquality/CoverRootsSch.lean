module

public import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
noncomputable section

namespace SheetDecomposition.CovSch

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {X Y : Scheme.{0}} {F : Type} [Field F]

theorem top_le_iff (x : Sp F ⟶ X) (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ centre x ∈ U :=
  ⟨fun h => h (show IsLocalRing.closedPoint F ∈ (⊤ : (Sp F).Opens) from trivial),
    fun h => (Scheme.preimage_eq_top_of_closedPoint_mem x h).ge⟩

def val (x : Sp F ⟶ X) (U : X.Opens) (h : centre x ∈ U) : Γ(X, U) →+* F :=
  (Scheme.stalkClosedPointTo x).hom.comp (X.presheaf.germ U (centre x) h).hom

theorem val_eq (x : Sp F ⟶ X) (U : X.Opens) (h : centre x ∈ U) (s : Γ(X, U)) :
    val x U h s = (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((x.appLE U ⊤ ((top_le_iff x U).2 h)).hom s) := by
  have := congrArg (fun φ => φ.hom s) (Scheme.germ_stalkClosedPointTo x U h)
  exact this

theorem valAt'_eq (p : Sp ℂ ⟶ X) (U : X.Opens) (h : centre p ∈ U) (s : Γ(X, U)) : valAt' p U s = val p U h s := by
  rw [val_eq, valAt', dite_eq_left ((top_le_iff p U).2 h)]
  rfl

theorem val_res (x : Sp F ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : centre x ∈ V) (s : Γ(X, U)) :
    val x V h ((X.presheaf.map (homOfLE hVU).op).hom s) = val x U (hVU h) s := by
  have := X.presheaf.germ_res_apply (homOfLE hVU) (centre x) h s
  exact congrArg (Scheme.stalkClosedPointTo x).hom this

theorem val_comp (x : Sp F ⟶ X) (f : X ⟶ Y) (U : Y.Opens) (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U) (h : centre x ∈ W)
    (h' : centre (x ≫ f) ∈ U) (s : Γ(Y, U)) : val x W h ((f.appLE U W hW).hom s) = val (x ≫ f) U h' s := by
  rw [val_eq, val_eq, ← Scheme.Hom.appLE_comp_appLE x f U W ⊤ hW ((top_le_iff x W).2 h)]
  rfl

theorem val_congr {x x' : Sp F ⟶ X} (e : x = x') (U : X.Opens) (h : centre x ∈ U) (h' : centre x' ∈ U)
    (s : Γ(X, U)) : val x U h s = val x' U h' s := by
  subst e
  rfl

theorem val_spMap {F' : Type} [Field F'] (i : F →+* F') (x : Sp F ⟶ X) (U : X.Opens) (h : centre x ∈ U)
    (h' : centre (spMap i ≫ x) ∈ U) (s : Γ(X, U)) : val (spMap i ≫ x) U h' s = i (val x U h s) := by
  rw [val_eq, val_eq, ← Scheme.Hom.appLE_comp_appLE (spMap i) x U ⊤ ⊤ ((top_le_iff x U).2 h) le_rfl]
  have := congrArg (fun φ => φ.hom ((x.appLE U ⊤ ((top_le_iff x U).2 h)).hom s))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom i))
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  exact this

theorem centre_spMap {F' : Type} [Field F'] (i : F →+* F') (x : Sp F ⟶ X) : centre (spMap i ≫ x) = centre x := by
  have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  show x (spMap i _) = x _
  congr 1
  exact Subsingleton.elim _ _

theorem eq_of_val {U : X.Opens} (hU : IsAffineOpen U) {x x' : Sp F ⟶ X} (h : centre x ∈ U) (h' : centre x' ∈ U)
    (e : ∀ s, val x U h s = val x' U h' s) : x = x' := by
  have e1 : x.appLE U ⊤ ((top_le_iff x U).2 h) = x'.appLE U ⊤ ((top_le_iff x' U).2 h') := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of F)).hom]
    ext s
    have := e s
    rw [val_eq, val_eq] at this
    exact this
  have a := hU.SpecMap_appLE_fromSpec x (isAffineOpen_top _) ((top_le_iff x U).2 h)
  have b := hU.SpecMap_appLE_fromSpec x' (isAffineOpen_top _) ((top_le_iff x' U).2 h')
  rw [e1, b, IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem exists_of_hom {U : X.Opens} (hU : IsAffineOpen U) (χ : Γ(X, U) →+* F) :
    ∃ (x : Sp F ⟶ X) (h : centre x ∈ U), ∀ s, val x U h s = χ s := by
  let x : Sp F ⟶ X := Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec
  have h : centre x ∈ U := by
    have : centre x ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rwa [hU.range_fromSpec] at this
  refine ⟨x, h, fun s => ?_⟩
  rw [val_eq, ← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom χ)) hU.fromSpec U ⊤ ⊤
    hU.fromSpec_preimage_self.ge le_rfl]
  have e1 : hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ ((Spec Γ(X, U)).presheaf.map_id _)).trans (Category.comp_id _)
  rw [e1]
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom s))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ))
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
  refine this.trans ?_
  exact congrArg χ (congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id)

variable {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem genMap_germ' (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U) (hg : centre ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq s) = val ξ U hg s := RegAtRing.genMap_germ q U hq hg s

theorem val_injective (hξ : IsCptGen ξ) (U : X.Opens) (hg : centre ξ ∈ U) (hU : ∀ q ∈ U, genPt ξ ⤳ q) :
    Function.Injective (val ξ U hg) := by
  intro s s' e
  refine TopCat.Presheaf.section_ext X.sheaf U s s' fun q hq => ?_
  apply hξ.inj ⟨q, hU q hq⟩
  exact (genMap_germ' ⟨q, hU q hq⟩ U hq hg s).trans (e.trans (genMap_germ' ⟨q, hU q hq⟩ U hq hg s').symm)

theorem exists_open (hξ : IsCptGen ξ) (T : Set Ω) (hT : T.Finite) (U₁ : X.Opens) (h₁ : centre ξ ∈ U₁) :
    ∃ (U : X.Opens) (h : centre ξ ∈ U), U ≤ U₁ ∧ T ⊆ Set.range (val ξ U h) := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨U₁, h₁, le_rfl, Set.empty_subset _⟩
  | @insert a T _ _ ih =>
    obtain ⟨U, h, hU, hT⟩ := ih
    obtain ⟨g, rfl⟩ := hξ.bij.2 a
    obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq g
    refine ⟨U ⊓ V, ⟨h, hV⟩, inf_le_left.trans hU, Set.insert_subset ⟨_, val_res ξ inf_le_right _ s⟩ ?_⟩
    intro b hb
    obtain ⟨s', rfl⟩ := hT hb
    exact ⟨_, val_res ξ inf_le_left _ s'⟩

variable {z : Sp ℂ ⟶ X}

theorem valAt_sec (hz : genPt ξ ⤳ centre z) (U : X.Opens) (h : centre z ∈ U) (hg : centre ξ ∈ U) (s : Γ(X, U)) :
    ValAt ξ z (val ξ U hg s) (val z U h s) :=
  ⟨hz, X.presheaf.germ U (centre z) h s, genMap_germ' ⟨centre z, hz⟩ U h hg s, rfl⟩

theorem v_mul {a b : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z b t) : ValAt ξ z (a * b) (r * t) := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', rfl, rfl⟩ := hb
  exact ⟨h, s * s', map_mul _ _ _, map_mul _ _ _⟩

theorem v_unique (hξ : IsCptGen ξ) {a : Ω} {r t : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z a t) : r = t := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨_, s', e, rfl⟩ := hb
  rw [hξ.inj _ e]

theorem v_inv {a : Ω} {r : ℂ} (ha : ValAt ξ z a r) (hr : r ≠ 0) : a ≠ 0 ∧ ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  have hs : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.mpr hr)
  obtain ⟨u, rfl⟩ := hs
  exact ⟨(u.isUnit.map (genMap ξ ⟨centre z, h⟩)).ne_zero, h,
    ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)),
    map_units_inv (genMap ξ ⟨centre z, h⟩) u, map_units_inv (Scheme.stalkClosedPointTo z).hom u⟩

theorem exists_frac {U : X.Opens} (hU : IsAffineOpen U) (x : Sp F ⟶ X) (h : centre x ∈ U)
    (g : X.presheaf.stalk (centre x)) : ∃ a b : Γ(X, U), val x U h b ≠ 0 ∧
      g * X.presheaf.germ U (centre x) h b = X.presheaf.germ U (centre x) h a := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U) ⟨centre x, h⟩
  have := hU.isLocalization_stalk ⟨centre x, h⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨centre x, h⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk (centre x)) g
  have hu := IsLocalization.map_units (M := (hU.primeIdealOf ⟨centre x, h⟩).asIdeal.primeCompl)
    (X.presheaf.stalk (centre x)) s
  exact ⟨r, s.1, (hu.map (Scheme.stalkClosedPointTo x).hom).ne_zero, hrs⟩

variable {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω}

theorem coordsAt_of_val (c : ∀ k, J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) {w : (Σ k, J k) → ℂ}
    (hw : ∀ s, ValAt ξ z (y s / y ⟨s.1, c s.1⟩) (w s)) (hw1 : ∀ k, w ⟨k, c k⟩ = 1) : CoordsAt ξ y z w := by
  refine ⟨fun k => ⟨c k, by rw [hw1]; exact isUnit_one⟩, fun k c' hu => ?_⟩
  obtain ⟨h0, hr⟩ := v_inv (hw ⟨k, c'⟩) hu.ne_zero
  have hy' : y ⟨k, c'⟩ ≠ 0 := fun e => h0 (by rw [e, zero_div])
  refine ⟨hy', fun i => ⟨w ⟨k, i⟩ * (w ⟨k, c'⟩)⁻¹, ?_, ?_⟩⟩
  · have h1 := v_mul (hw ⟨k, i⟩) hr
    have h2 : y ⟨k, i⟩ / y ⟨k, c k⟩ * (y ⟨k, c'⟩ / y ⟨k, c k⟩)⁻¹ = y ⟨k, i⟩ / y ⟨k, c'⟩ := by
      have := hy k
      field_simp
    exact h2 ▸ h1
  · rw [inv_mul_cancel_right₀ hu.ne_zero]

theorem val_of_coordsAt (c : ∀ k, J k) {w : (Σ k, J k) → ℂ} (hw : CoordsAt ξ y z w) (hw1 : ∀ k, w ⟨k, c k⟩ = 1)
    (s : Σ k, J k) : ValAt ξ z (y s / y ⟨s.1, c s.1⟩) (w s) := by
  obtain ⟨k, i⟩ := s
  obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (by rw [hw1]; exact isUnit_one)).2 i
  rw [hw1, mul_one] at e
  exact e ▸ hr

end SheetDecomposition.CovSch
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifDefs
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

def VecAt {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R : (Fin n → ℂ) → RiemLat E g Λ) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ) : Prop :=
  ∀ (m : ℕ) (s : Fin m → 𝔐.Li), (∀ a, ∃ v, 𝔐.M.ValAt (z t₀) (s a) v) →
    ∃ x : Fin m → (Fin n → ℂ) → Fin g → ℂ, (∀ a, AnalyticAt ℂ (x a) t₀) ∧ ∀ᶠ t in 𝓝 t₀, ∃ v : Fin m → (epsAt (z t) ⟶ 𝔐.t.G),
      (∀ a, 𝔐.M.ValAt (z t) (s a) (v a)) ∧ FibreLatVec 𝔐.t (z t) (R t) (fun a => x a t) v

structure KUnif (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ) where
  ι : Type
  fin : Finite ι
  Di : ι → Datum H
  sig : ∀ k, (Di k).p = D.p ∧ (Di k).q = D.q
  F : ∀ k, UnivFam E (CMType H) j j' n g (Di k).La
  q_eq : ∀ k, (F k).q = q
  form_eq : ∀ k, (F k).form = (Di k).EF ∨ (F k).form = -(Di k).EF
  σ_eq : ∀ k τ, (F k).σ τ = κ.comp (labelEmb c (sm τ))
  Γ : ∀ k, Subgroup ((Di k).La ≃ₗ[𝓞 E] (Di k).La)
  mem_Γ : ∀ k γ, γ ∈ Γ k ↔ InLevel l (Di k) γ
  arith : ∀ k, (F k).IsArith (Γ k)
  pt : ι → (Fin n → ℂ) → (Sp ℂ ⟶ Y.X)
  hol : ∀ k, IsHolTo (ballDom q) (pt k)
  comp_s_eq_spMap_of_isOver : ∀ k, ∀ t ∈ ballDom q, pt k t ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))
  interior : ∀ k, ∀ t ∈ ballDom q, centre (pt k t) ∈ abLocus Y.t.G
  disj : ∀ k k', ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, pt k t = pt k' t' → k = k'
  fibre : ∀ k, ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, pt k t = pt k t' ↔ (F k).Eqv (Γ k) t t'
  onto : ∀ p : Sp ℂ ⟶ Y.X, centre p ∈ abLocus Y.t.G → p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) →
    ∃ k, ∃ t ∈ ballDom q, pt k t = p
  lat : ∀ k, ∀ t ∈ ballDom q, FibreLat Y.t (pt k t) ((F k).R t)
  vec : ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (k : ι) (V : Set (Fin n → ℂ)) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)), IsOpen V → V ⊆ ballDom q →
    IsHolTo V z → (∀ t ∈ V, z t ≫ 𝔐.f = pt k t) → ∀ t₀ ∈ V, VecAt 𝔐 (F k).R z t₀
  locc : ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y.X)), IsOpen T → IsPreconnected T → IsHolTo T y →
    (∀ b ∈ T, centre (y b) ∈ abLocus Y.t.G) → (∀ b ∈ T, y b ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) →
    ∀ b ∈ T, ∀ b' ∈ T, ∀ k k', ∀ t ∈ ballDom q, ∀ t' ∈ ballDom q, y b = pt k t → y b' = pt k' t' → k = k'

def VecOfPeriods : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (κ : c.F →+* ℂ) (σ : KA l →+* ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (n : ℕ) (V : Set (Fin n → ℂ))
    (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (xF : (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c))
    (R : (Fin n → ℂ) → RiemLat E g (FU.Di i).La) (P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)))
    (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V → IsHolTo V z → IsHolTo V xF → IsHolPeriods (FU.Di i) ty V P →
    (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V) →
    (∀ t ∈ V, (R t).form = (FU.Di i).EF ∧ IsUnit (h t).det ∧ (∀ x, P t x = h t *ᵥ (R t).P x) ∧
      xF t ≫ Y.j = z t ≫ 𝔐.f ∧ xF t ≫ pullback.fst _ _ = FU.u i (P t) ∧ xF t ≫ pullback.snd _ _ = spMap κ) →
    ∀ t₀ ∈ V, VecAt 𝔐 R z t₀

def KUnifConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n g : ℕ)
    (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ),
    Nonempty (KUnif Y sm j j' n g q κ) → Nonempty (KUnif Y sm j j' n g q ((starRingEnd ℂ).comp κ))

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.HolNull
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem null_of_lines {n : ℕ} (Z : Set (Fin n → ℂ)) (hZ : MeasurableSet Z) (p : Fin n → ℂ)
    (h : ∀ x : Fin n → ℂ, ∀ᵐ t : ℝ, p + t • x ∉ Z) : volume Z = 0 := by
  have hm : MeasurableSet {u : (Fin n → ℂ) × ℝ | p + u.2 • u.1 ∉ Z} :=
    (hZ.compl).preimage (f := fun u : (Fin n → ℂ) × ℝ => p + u.2 • u.1) (Continuous.measurable (by fun_prop))
  have h1 : ∀ᵐ t : ℝ, ∀ᵐ x : Fin n → ℂ, p + t • x ∉ Z :=
    (Measure.ae_ae_comm (p := fun (x : Fin n → ℂ) (t : ℝ) => p + t • x ∉ Z) hm).mp (Eventually.of_forall h)
  have h2 : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff]
  obtain ⟨t, ht, ht0⟩ := (h1.and h2).exists
  have h3 : volume ((t • ·) ⁻¹' ((p + ·) ⁻¹' Z)) = 0 := by
    rw [ae_iff] at ht
    simpa [Set.preimage] using ht
  rw [Measure.addHaar_preimage_smul volume ht0, measure_preimage_add, mul_eq_zero] at h3
  refine h3.resolve_left ?_
  rw [ENNReal.ofReal_eq_zero, not_le, abs_pos]
  exact inv_ne_zero (pow_ne_zero _ ht0)

theorem zero_set_null {n : ℕ} (V : Set (Fin n → ℂ)) (hV : IsOpen V) (hc : Convex ℝ V) (f : (Fin n → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f V) (p : Fin n → ℂ) (hp : p ∈ V) (hfp : f p ≠ 0) : volume {x ∈ V | f x = 0} = 0 := by
  have hm : MeasurableSet {x ∈ V | f x = 0} := by
    have : {x ∈ V | f x = 0} = V \ (V ∩ f ⁻¹' {0}ᶜ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      tauto
    rw [this]
    exact hV.measurableSet.diff (hf.continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton).measurableSet
  refine null_of_lines _ hm p fun x => ?_
  set S : Set ℝ := (fun t : ℝ => p + t • x) ⁻¹' V with hS
  have hSo : IsOpen S := hV.preimage (by fun_prop)
  have hSc : Convex ℝ S := by
    intro s hs t ht a b ha hb hab
    have := hc hs ht ha hb hab
    have e : a • (p + s • x) + b • (p + t • x) = p + (a • s + b • t) • x := by
      have : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
      conv_rhs => rw [this]
      simp only [smul_add, add_smul, smul_assoc]
      abel
    rw [e] at this
    exact this
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => f (p + s • x)) ((fun s : ℂ => p + s • x) ⁻¹' V) := by
    refine DifferentiableOn.analyticOnNhd ?_ (hV.preimage (by fun_prop))
    exact hf.comp (by fun_prop) fun s hs => hs
  have hh : AnalyticOnNhd ℝ (fun t : ℝ => f (p + t • x)) S := by
    intro t ht
    have h1 : AnalyticAt ℝ (fun s : ℂ => f (p + s • x)) (Complex.ofRealCLM t) :=
      (hg t (by simpa [hS] using ht)).restrictScalars
    have := h1.comp (Complex.ofRealCLM.analyticAt t)
    simpa [Function.comp_def] using this
  rcases hh.eqOn_zero_or_eventually_ne_zero_of_preconnected hSc.isPreconnected with h0 | h0
  · exact (hfp (by simpa using h0 (x := 0) (by simpa [hS] using hp))).elim
  · have h1 : ∀ᵐ t ∂(volume.restrict S), f (p + t • x) ≠ 0 := ae_restrict_le_codiscreteWithin hSo.measurableSet h0
    rw [ae_restrict_iff' hSo.measurableSet] at h1
    filter_upwards [h1] with t ht hz using ht hz.1 hz.2

theorem top_le_iff_pt {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (q : Sp ℂ) : ⊤ ≤ x ⁻¹ᵁ U ↔ x q ∈ U := by
  refine ⟨fun h => h (x := q) trivial, fun h q' _ => ?_⟩
  have : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) q' q
  rw [this]
  exact h

theorem local_null {X : Scheme.{0}} {n : ℕ} {B : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (U : X.Opens)
    (hy : IsHolTo B y) {b : Fin n → ℂ} (hb : b ∈ B) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ b ∈ V ∧ V ⊆ B ∧
      ((∃ b' ∈ V, ⊤ ≤ y b' ⁻¹ᵁ U) → volume {b' ∈ V | ¬ ⊤ ≤ y b' ⁻¹ᵁ U} = 0) := by
  let q : Sp ℂ := (default : PrimeSpectrum ℂ)
  obtain ⟨W, hW, hbW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y b q) (U := ⊤) trivial
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hy W 0).1 b ⟨hb, (top_le_iff_pt _ _ q).mpr hbW⟩
  refine ⟨Metric.ball b ε, Metric.isOpen_ball, Metric.mem_ball_self hε, fun z hz => (hball hz).1, ?_⟩
  rintro ⟨b', hb', hU⟩
  obtain ⟨f, hfU, hf⟩ := hW.exists_basicOpen_le (V := U) ⟨y b' q, (top_le_iff_pt _ _ q).mp hU⟩
    ((top_le_iff_pt _ _ q).mp (hball hb').2)
  refine measure_mono_null ?_ (zero_set_null (Metric.ball b ε) Metric.isOpen_ball (convex_ball b ε)
    (fun z => valAt' (y z) W f) ((hy W f).2.mono hball) b' hb' ((valAt'_ne_zero_iff _ _ (hball hb').2 f q).mpr hf))
  rintro z ⟨hz, hzU⟩
  refine ⟨hz, ?_⟩
  by_contra hne
  exact hzU ((top_le_iff_pt _ _ q).mpr (hfU ((valAt'_ne_zero_iff _ _ (hball hz).2 f q).mp hne)))

theorem holNull : HolNull := by
  intro X n B y U _ hBc hy ⟨b₀, hb₀, hU₀⟩
  choose! V hVo hVb hVB hV using fun b (hb : b ∈ B) => local_null U hy hb
  set G : Set (Fin n → ℂ) := {b | ⊤ ≤ y b ⁻¹ᵁ U} with hG
  have hsub : B ⊆ interior (closure G) := by
    refine hBc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr fun z hz hz' => hz' (interior_subset hz)) (fun b hb => ?_) ?_ |>.trans le_rfl
    · by_cases hcl : b ∈ closure G
      · left
        refine interior_maximal (t := V b) (fun z hz => ?_) (hVo b hb) (hVb b hb)
        obtain ⟨b', hb'V, hb'G⟩ := mem_closure_iff.mp hcl (V b) (hVo b hb) (hVb b hb)
        have hnull := hV b hb ⟨b', hb'V, hb'G⟩
        by_contra hz'
        have ho : IsOpen (V b ∩ (closure G)ᶜ) := (hVo b hb).inter isClosed_closure.isOpen_compl
        refine (ho.measure_pos volume ⟨z, hz, hz'⟩).ne' (measure_mono_null ?_ hnull)
        exact fun w hw => ⟨hw.1, fun h => hw.2 (subset_closure h)⟩
      · exact Or.inr hcl
    · refine ⟨b₀, hb₀, interior_maximal (t := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}) (fun z hz => subset_closure hz.2) (hy U 0).1 ⟨hb₀, hU₀⟩⟩
  refine measure_null_of_locally_null _ fun b hb => ?_
  obtain ⟨b', hb'V, hb'G⟩ := mem_closure_iff.mp (interior_subset (hsub hb.1)) (V b) (hVo b hb.1) (hVb b hb.1)
  refine ⟨{b' ∈ V b | ¬ ⊤ ≤ y b' ⁻¹ᵁ U}, ?_, hV b hb.1 ⟨b', hb'V, hb'G⟩⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((hVo b hb.1).mem_nhds (hVb b hb.1))] with z hz hz'
    using ⟨hz', hz.2⟩

end SheetDecomposition
end
end
