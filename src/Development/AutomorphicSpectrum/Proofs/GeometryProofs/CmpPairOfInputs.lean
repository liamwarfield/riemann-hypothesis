module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCompactificationInteriorPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptIsoCompare
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HodgeCompactPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFiniteExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptCompare
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JNormal
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LGenflag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsoLineOnEquivalence

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.PairIso
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptFlag
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FlagDataMatchUnderTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem fm_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext a <;> simp [dualMap]

theorem fm_flagStep_map {Ω : Type} [Field Ω] {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (φ : V →ₗ[Ω] V') {r : ℕ} (b : Fin r → V) (k : ℕ) :
    (flagStep Ω b k).map φ = flagStep Ω (fun a => φ (b a)) k := by
  simp only [flagStep, Submodule.map_span, Set.image_image]

theorem fm_over {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {U : Over S'} (v w : U ⟶ t'.G)
    (h : v.left ≫ m.φ = w.left ≫ m.φ) : v = w :=
  Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w v, Over.w w]))
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
  {g : HostAut H} {Φ : Xo.X ⟶ Xo.X} {n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ} {Y : Model Xo c β}
  {Y' : Model Xo c β'} {T T' : Scheme.{0}} {u₁ : T ⟶ Y.t.G.left} {u₂ u₂' : T ⟶ Y'.t.G.left}

theorem fm_pre (a : T' ⟶ T) (h : TwTan n Y Y' u₁ u₂) : TwTan n Y Y' (a ≫ u₁) (a ≫ u₂) := by
  obtain ⟨u, u', h1, h2, h3, h4⟩ := h
  refine ⟨a ≫ u, a ≫ u', ?_, ?_, ?_, ?_⟩ <;> simp only [Category.assoc, h1, h2, h3, h4]

theorem fm_fun (hβ : Mono (spMap β)) (h : TwTan n Y Y' u₁ u₂) (h' : TwTan n Y Y' u₁ u₂') : u₂ = u₂' := by
  obtain ⟨u, u', h1, h2, h3, h4⟩ := h
  obtain ⟨v, v', k1, k2, k3, k4⟩ := h'
  have hmono : Mono (Y.jQ ≫ pullback.fst Y.s (spMap β)) := by
    have : IsOpenImmersion Y.jQ := Y.jQ_open
    infer_instance
  have e1 : ∀ z : T ⟶ Y.oF.t.G.left,
      z ≫ Y.oF.t.G.hom ≫ (Y.jQ ≫ pullback.fst Y.s (spMap β)) = (z ≫ Y.m.φ) ≫ Y.t.G.hom := by
    intro z
    rw [Category.assoc, Y.m.cart.1.w]
  have huv : u = v := by
    apply Y.m.cart.1.hom_ext
    · exact h1.trans k1.symm
    · rw [← cancel_mono (Y.jQ ≫ pullback.fst Y.s (spMap β)), Category.assoc, Category.assoc, e1, e1, h1, k1]
  subst huv
  have e2 : ∀ z : T ⟶ Y'.oF.t.G.left,
      z ≫ Y'.oF.t.G.hom ≫ pullback.fst _ _ = (z ≫ Y'.m0.φ) ≫ Xo.univ.t.G.hom := by
    intro z
    rw [Category.assoc, Y'.m0.cart.1.w]
  have hu' : u' = v' := by
    apply Y'.m0.cart.1.hom_ext
    · exact h3.trans k3.symm
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, e2, e2, h3, k3]
      · rw [Category.assoc, Category.assoc]
        exact h4.trans k4.symm
  rw [← h2, ← k2, hu']
end

theorem flag_data_match_under_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (θ : Fl.Li₀ ≃+ Fl'.Li₀) (φ : A.Li ≃ₗ[Ω] A'.Li), Mono (spMap β) → Mono (spMap β') → A.fn.comp ψ.toRingHom = A'.fn → (∀ w, TwTan n Y Y' ((A.M.pt w).left ≫ A.m.φ) ((A'.M.pt (φ w)).left ≫ A'.m.φ)) → (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) → (∀ e, φ (Fl.j e) = Fl'.j (θ e)) ∧ ∀ s s' (r : ℕ) (b : Fin r → Fl.Li₀) (u : Matrix (Fin r) (Fin r) Ω), (∀ k, flagStep Ω (Fl.b s) k = flagStep Ω (fun a => ∑ q, u q a • Fl.j (b q)) k) → (∀ k, flagStep Ω (Fl'.b s') k = flagStep Ω (fun a => ∑ q, u q a • Fl'.j (θ (b q))) k) → ∀ k, (flagStep Ω (Fl.b s) k).map φ.toLinearMap = flagStep Ω (Fl'.b s') k := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J y A A' Fl Fl' ψ θ φ hβ hβ' hfn hw he
  have hsp : spMap ((dualMap A.fn).comp (dualMap ψ.toRingHom)) =
      spMap (dualMap A.fn) ≫ spMap (dualMap ψ.toRingHom) := by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hj : ∀ e, φ (Fl.j e) = Fl'.j (θ e) := by
    intro e
    apply A'.M.inj
    apply fm_over A'.m
    apply fm_fun hβ (hw (Fl.j e))
    rw [Fl.j_pt e, Fl'.j_pt (θ e), ← hfn, fm_dualMap_comp, hsp, Category.assoc]
    exact fm_pre _ (he e)
  refine ⟨hj, ?_⟩
  intro s s' r b u h1 h2 k
  rw [h1 k, h2 k, fm_flagStep_map]
  congr 1
  funext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, hj]

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagMatch

theorem matched_generic_flags_carried : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (θ : Fl.Li₀ ≃+ Fl'.Li₀) (φ : A.Li ≃ₗ[Ω] A'.Li), Mono (spMap β) → Mono (spMap β') → A.fn.comp ψ.toRingHom = A'.fn → (∀ w, TwTan n Y Y' ((A.M.pt w).left ≫ A.m.φ) ((A'.M.pt (φ w)).left ≫ A'.m.φ)) → (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) → (∀ e, φ (Fl.j e) = Fl'.j (θ e)) ∧ ∀ s s' (r : ℕ) (b : Fin r → Fl.Li₀) (u : Matrix (Fin r) (Fin r) Ω), (∀ k, flagStep Ω (Fl.b s) k = flagStep Ω (fun a => ∑ q, u q a • Fl.j (b q)) k) → (∀ k, flagStep Ω (Fl'.b s') k = flagStep Ω (fun a => ∑ q, u q a • Fl'.j (θ (b q))) k) → ∀ k, (flagStep Ω (Fl.b s) k).map φ.toLinearMap = flagStep Ω (Fl'.b s') k :=
  @PositivityTheory.UnitarySelfGeneration.flag_data_match_under_twist

end GlobalTheory.CompanionTheory.Ar.FlagMatch
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeCptFlagStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_hodge_cpt_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y) (Fl : A.Flag) (Fl' : A'.Flag) (ψ : A'.Ω₀ ≃+* A.Ω₀) (θ : Fl.Li₀ ≃+ Fl'.Li₀) (φ : A.Li ≃ₗ[Ω] A'.Li), Mono (spMap β) → Mono (spMap β') → A.fn.comp ψ.toRingHom = A'.fn → (∀ w, TwTan n Y Y' ((A.M.pt w).left ≫ A.m.φ) ((A'.M.pt (φ w)).left ≫ A'.m.φ)) → (∀ e, TwTan n Y Y' (Fl.M₀.pt e).left (spMap (dualMap ψ.toRingHom) ≫ (Fl'.M₀.pt (θ e)).left)) → (∀ e, φ (Fl.j e) = Fl'.j (θ e)) ∧ ∀ s s' (r : ℕ) (b : Fin r → Fl.Li₀) (u : Matrix (Fin r) (Fin r) Ω), (∀ k, flagStep Ω (Fl.b s) k = flagStep Ω (fun a => ∑ q, u q a • Fl.j (b q)) k) → (∀ k, flagStep Ω (Fl'.b s') k = flagStep Ω (fun a => ∑ q, u q a • Fl'.j (θ (b q))) k) → ∀ k, (flagStep Ω (Fl.b s) k).map φ.toLinearMap = flagStep Ω (Fl'.b s') k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagMatch.matched_generic_flags_carried | exact GlobalTheory.CompanionTheory.Ar.FlagMatch.matched_generic_flags_carried | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagMatch.matched_generic_flags_carried <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TIdeal
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem t_ideal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω Ω' : Type) [Field Ω] [CharZero Ω] [Field Ω'] [CharZero Ω'] (φ : Ω →+* Ω') (y : (Σ k, ι k) → Ω), mCoordIdeal (fun p => φ (y p)) = mCoordIdeal y ∧ (blockFnField (fun p => φ (y p))).toSubfield = (blockFnField y).toSubfield.map φ ∧ (Function.Surjective φ → Birational y → Birational (fun p => φ (y p))) ∧ ∀ (s : MRing ι), aeval (fun p => φ (y p)) s = φ (aeval y s) := by
  intro K _ ι _ Ω Ω' _ _ _ _ φ y
  have key : ∀ (s : MRing ι), aeval (fun p => φ (y p)) s = φ (aeval y s) := by
    intro s
    have h := MvPolynomial.comp_aeval_apply (R := ℤ) y (φ.toIntAlgHom) s
    simpa using h.symm
  have cone : ∀ (s : MRing ι), mConeMap (fun p => φ (y p)) s = MvPolynomial.map φ (mConeMap y s) := by
    intro s
    induction s using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
    | mul_X p n hp => rw [map_mul, map_mul, hp, map_mul]; simp [mConeMap]
  refine ⟨?_, ?_, ?_, key⟩
  · ext s
    simp only [mCoordIdeal, RingHom.mem_ker]
    rw [cone]
    constructor
    · intro hs
      apply MvPolynomial.map_injective φ φ.injective
      rw [hs, map_zero]
    · intro hs
      rw [hs, map_zero]
  · have e := IntermediateField.adjoin_map ℚ {t : Ω | ∃ (p : (k : K) × ι k) (q : (k : K) × ι k), p.fst = q.fst ∧ t = y p / y q} (φ.toRatAlgHom)
    have e2 := congrArg IntermediateField.toSubfield e
    rw [IntermediateField.toSubfield_map] at e2
    have hs : (φ.toRatAlgHom) '' {t : Ω | ∃ (p : (k : K) × ι k) (q : (k : K) × ι k), p.fst = q.fst ∧ t = y p / y q}
        = {t : Ω' | ∃ (p : (k : K) × ι k) (q : (k : K) × ι k), p.fst = q.fst ∧ t = φ (y p) / φ (y q)} := by
      ext t
      constructor
      · rintro ⟨u, ⟨p, q, hpq, rfl⟩, rfl⟩
        exact ⟨p, q, hpq, by simp [map_div₀]⟩
      · rintro ⟨p, q, hpq, rfl⟩
        exact ⟨y p / y q, ⟨p, q, hpq, rfl⟩, by simp [map_div₀]⟩
    rw [hs] at e2
    unfold blockFnField
    exact e2.symm
  · intro hsurj hb s'
    obtain ⟨s, rfl⟩ := hsurj s'
    obtain ⟨d, g, h, hg, hh, hne, heq⟩ := hb s
    refine ⟨d, g, h, hg, hh, ?_, ?_⟩
    · rw [key]
      exact fun h0 => hne (φ.injective (by rw [h0, map_zero]))
    · rw [key, key, heq, map_mul]

end PositivityTheory.UnitarySelfGeneration
end

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PairIsoK

theorem finrank_congr {F₁ F₂ L : Type} [Field F₁] [Field F₂] [Field L] [Algebra F₁ L] [Algebra F₂ L]
    (A : IntermediateField F₁ L) (B : IntermediateField F₂ L) (h : A.toSubfield = B.toSubfield) :
    Module.finrank A L = Module.finrank B L := by
  have e1 : Module.finrank A L = Module.finrank A.toSubfield L := rfl
  have e2 : Module.finrank B L = Module.finrank B.toSubfield L := rfl
  rw [e1, e2, h]

theorem isGenericFlag_transport {Ωa Ωb Ω' E₁ E₂ E' : Type} [Field Ωa] [Field Ωb] [Field Ω'] [Algebra Ωa Ω'] [Algebra Ωb Ω']
    [AddCommGroup E₁] [Module Ωa E₁] [AddCommGroup E₂] [Module Ωb E₂] [AddCommGroup E'] [Module Ω' E']
    (ψ : Ωb ≃+* Ωa) (hψ : ∀ a, algebraMap Ωa Ω' (ψ a) = algebraMap Ωb Ω' a)
    (θ : E₁ ≃+ E₂) (hθ : ∀ (a : Ωb) e, θ (ψ a • e) = a • θ e) (j : E₂ →+ E') {S S' : Type} {r : S → ℕ} {r' : S' → ℕ}
    (p : S ≃ S') (hr : ∀ s, r' (p s) = r s) (V : S → Submodule Ωa E₁) (V' : S' → Submodule Ωb E₂)
    (hV : ∀ s e, e ∈ V s ↔ θ e ∈ V' (p s)) (b' : ∀ s', Fin (r' s') → E') (d : ℕ) (h : IsGenericFlag (Ω' := Ω') j V' b' d) :
    IsGenericFlag (Ω' := Ω') (j.comp θ.toAddMonoidHom) V (fun s k => b' (p s) (Fin.cast (hr s).symm k)) d := by
  obtain rfl : r = fun s => r' (p s) := funext fun s => (hr s).symm
  obtain ⟨c, u, hc, hj, hjc, hb, hu1, hu0, hst, hai, hd, hfr⟩ := h
  have hθ' : ∀ (a : Ωa) e, θ (a • e) = ψ.symm a • θ e := fun a e => by
    have := hθ (ψ.symm a) e
    rwa [ψ.apply_symm_apply] at this
  have hθi : ∀ (a : Ωb) e, θ.symm (a • e) = ψ a • θ.symm e := fun a e => by
    apply θ.injective
    rw [hθ a, θ.apply_symm_apply, θ.apply_symm_apply]
  have hsp : ∀ s, Submodule.span Ωa (Set.range fun k => θ.symm (c (p s) k)) = V s := by
    intro s
    ext e
    rw [hV, ← (hc (p s)).2]
    constructor
    · intro he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [θ.apply_symm_apply]
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [hθ']; exact Submodule.smul_mem _ _ hx
    · intro he
      have : ∀ x ∈ Submodule.span Ωb (Set.range (c (p s))),
          θ.symm x ∈ Submodule.span Ωa (Set.range fun k => θ.symm (c (p s) k)) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, rfl⟩ := hx
          exact Submodule.subset_span ⟨k, rfl⟩
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | smul a x _ hx => rw [hθi]; exact Submodule.smul_mem _ _ hx
      simpa using this _ he
  refine ⟨fun s k => θ.symm (c (p s) k), fun s => u (p s), fun s => ⟨?_, hsp s⟩, ?_, ?_, fun s => hb (p s), fun s => hu1 (p s),
    fun s => hu0 (p s), ?_, ?_, hd, ?_⟩
  · refine (hc (p s)).1.map_of_injective_injective (⇑ψ.symm) θ.symm.toAddMonoidHom
      (fun a h => by simpa using h) (fun m h => by simpa using h) ?_
    intro a m
    show θ.symm (ψ.symm a • m) = a • θ.symm m
    rw [hθi, ψ.apply_symm_apply]
  · intro a e
    show j (θ (a • e)) = _ • j (θ e)
    rw [hθ', hj, ← hψ, ψ.apply_symm_apply]
  · intro s
    simpa using hjc (p s)
  · intro s i
    simpa using hst (p s) i
  · have h1 := hai.comp (fun q : (Σ s, {lk : Fin (r' (p s)) × Fin (r' (p s)) // lk.2 < lk.1}) =>
      (⟨p q.1, q.2⟩ : Σ s', {lk : Fin (r' s') × Fin (r' s') // lk.2 < lk.1})) (by
        rintro ⟨s, a⟩ ⟨s', a'⟩ h
        obtain rfl : s = s' := p.injective (congrArg Sigma.fst h)
        simpa using h)
    exact h1.ringHom_of_comp_eq (f := ψ.toRingHom) (g := RingHom.id Ω') ψ.surjective Function.injective_id
      (RingHom.ext hψ)
  · have hrange : (Set.range fun q : Σ s, Fin (r' (p s)) × Fin (r' (p s)) => u (p q.1) q.2.1 q.2.2) =
        Set.range fun q : Σ s', Fin (r' s') × Fin (r' s') => u q.1 q.2.1 q.2.2 := by
      ext t
      constructor
      · rintro ⟨⟨s, a⟩, rfl⟩
        exact ⟨⟨p s, a⟩, rfl⟩
      · rintro ⟨⟨s', a⟩, rfl⟩
        obtain ⟨s, rfl⟩ := p.surjective s'
        exact ⟨⟨s, a⟩, rfl⟩
    rw [hrange, ← hfr]
    refine finrank_congr _ _ ?_
    rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield]
    congr 2
    ext t
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨ψ.symm a, by rw [← hψ, ψ.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ψ a, hψ a⟩

theorem IsGenericFlag_deg_pos {Ωa Ω' E₁ E' : Type} [Field Ωa] [Field Ω'] [Algebra Ωa Ω'] [AddCommGroup E₁] [Module Ωa E₁]
    [AddCommGroup E'] [Module Ω' E'] {j : E₁ →+ E'} {S : Type} {r : S → ℕ} {V : S → Submodule Ωa E₁}
    {b : ∀ s, Fin (r s) → E'} {d : ℕ} (h : IsGenericFlag (Ω' := Ω') j V b d) : 0 < d := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hd, _⟩ := h
  exact hd

theorem exists_coeff {Ωa Ω' E₁ E' : Type} [Field Ωa] [Field Ω'] [Algebra Ωa Ω'] [AddCommGroup E₁] [Module Ωa E₁]
    [AddCommGroup E'] [Module Ω' E'] {j : E₁ →+ E'} {S : Type} {r : S → ℕ} {V : S → Submodule Ωa E₁}
    {b : ∀ s, Fin (r s) → E'} {d : ℕ} (h : IsGenericFlag (Ω' := Ω') j V b d) (s : S) {n : ℕ} (c : Fin n → E₁)
    (hc : Submodule.span Ωa (Set.range c) = V s) :
    ∃ m : Matrix (Fin n) (Fin (r s)) Ω', ∀ k, b s k = ∑ l, m l k • j (c l) := by
  obtain ⟨c', u, hc', hj, -, -, -, -, hst, -⟩ := h
  have h1 : ∀ l, j (c' s l) ∈ Submodule.span Ω' (Set.range fun l => j (c l)) := by
    intro l
    have hm : c' s l ∈ Submodule.span Ωa (Set.range c) := by
      rw [hc, ← (hc' s).2]
      exact Submodule.subset_span ⟨l, rfl⟩
    have key : ∀ x ∈ Submodule.span Ωa (Set.range c), j x ∈ Submodule.span Ω' (Set.range fun l => j (c l)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨q, rfl⟩ := hx
        exact Submodule.subset_span ⟨q, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [hj]; exact Submodule.smul_mem _ _ hx
    exact key _ hm
  have h2 : ∀ k, b s k ∈ Submodule.span Ω' (Set.range fun l => j (c l)) := by
    intro k
    have hk : b s k ∈ flagStep Ω' (b s) (k + 1) := Submodule.subset_span ⟨k, by simp, rfl⟩
    rw [hst] at hk
    refine (Submodule.span_le.2 ?_ : flagStep Ω' _ _ ≤ _) hk
    rintro _ ⟨a, -, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (h1 l)
  have h3 := fun k => (Submodule.mem_span_range_iff_exists_fun Ω').1 (h2 k)
  choose m hm using h3
  exact ⟨fun l k => m k l, fun k => (hm k).symm⟩

theorem exists_basis {Ωa Ω' E₁ E' : Type} [Field Ωa] [Field Ω'] [Algebra Ωa Ω'] [AddCommGroup E₁] [Module Ωa E₁]
    [AddCommGroup E'] [Module Ω' E'] {j : E₁ →+ E'} {S : Type} {r : S → ℕ} {V : S → Submodule Ωa E₁}
    {b : ∀ s, Fin (r s) → E'} {d : ℕ} (h : IsGenericFlag (Ω' := Ω') j V b d) (s : S) :
    ∃ c : Fin (r s) → E₁, LinearIndependent Ωa c ∧ Submodule.span Ωa (Set.range c) = V s := by
  obtain ⟨c, _, hc, _⟩ := h
  exact ⟨c s, hc s⟩

theorem flagStep_rows {Ω₃ F : Type} [Field Ω₃] [AddCommGroup F] [Module Ω₃ F] {r : ℕ} (f : Fin r → F)
    (m m' : Fin r → Fin r → Ω₃) (h : ∀ i, flagStep Ω₃ (fun k l => m l k : Fin r → Fin r → Ω₃) i =
      flagStep Ω₃ (fun k l => m' l k : Fin r → Fin r → Ω₃) i) (i : ℕ) :
    flagStep Ω₃ (fun k => ∑ l, m l k • f l) i = flagStep Ω₃ (fun k => ∑ l, m' l k • f l) i := by
  have := GlobalTheory.CompanionTheory.Ar.FlagPull.flagStep_map_eq (i := RingHom.id Ω₃)
    (j := (Fintype.linearCombination Ω₃ f).toAddMonoidHom) (fun a e => by simp) h i
  simpa [Fintype.linearCombination_apply] using this

theorem flagStep_cast {Ω₃ F : Type} [Field Ω₃] [AddCommGroup F] [Module Ω₃ F] {r r' : ℕ} (h : r = r') (b : Fin r' → F)
    (i : ℕ) : flagStep Ω₃ (fun a : Fin r => b (Fin.cast h a)) i = flagStep Ω₃ b i := by
  subst h
  rfl

theorem pull_both {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type}
    {J' : K' → Type} [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}
    (A : HodgeCpt Y S y) (Fl : A.Flag) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X)
    (κ : K → K') (v : (Σ k, J k) → (Σ k, J' k))
    (hx : A.ξ ≫ A.f = x ≫ Y.j) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S)
    (hvb : ∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn
      {q | InFibre A.ξ p q} (labelRk D s) ⊤)
    (hall : ∀ q : Z, genPt ξ' ⤳ q) (htie : CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩))
    (hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i) (hb : IsBlockMap κ v)
    (hy : ∀ q, y' (v q) = i (y q)) (hfd : FiniteDimensional i.fieldRange Ω') :
    ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (Fl' : A'.Flag) (ψ' : A.Ω₀ ≃+* A'.Ω₀) (θ' : Fl.Li₀ ≃+ Fl'.Li₀)
      (j : A.Li →+ A'.Li),
      A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧
      (∀ s k, Fl'.b s k = j (Fl.b s k)) ∧ A'.fn.comp ψ'.toRingHom = i.comp A.fn ∧
      (∀ e, (Fl'.M₀.pt (θ' e)).left = spMap (dualMap ψ'.toRingHom) ≫ (Fl.M₀.pt e).left) ∧
      (∀ e, Fl'.j (θ' e) = j (Fl.j e)) ∧
      (∀ xdeg e, Fl.RootLines xdeg e → Fl'.RootLines (fun r => pullDeg κ (xdeg r)) (fun r => i (e r))) ∧
      ∀ r (e₀ : Ω) (L : HermLine J) (L' : HermLine J'), Fl.IsHodgeLine r e₀ L → IsPullHerm κ v L L' →
        Fl'.IsHodgeLine r (i e₀) L' := by
  obtain ⟨A', e, j, m, h1, h2, h3, h4, h5, h6, h7, -, h9⟩ :=
    PositivityTheory.UnitarySelfGeneration.hodge_compact_pullback E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A x Z ξ' h hx hdisc hvb hall htie hnorm hd
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ (e.hom ≫ h) i := by
    show A'.ξ ≫ e.hom ≫ h = _
    rw [← Category.assoc, h1]
    exact hd
  have hf : A'.f = (e.hom ≫ h) ≫ A.f := by rw [h2, Category.assoc]
  obtain ⟨Fl', hb', -, ⟨ψ', θ', q1, -, q3, q4⟩, q5⟩ :=
    GlobalTheory.CompanionTheory.Ar.FlagPull.flag_pull E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A A' (e.hom ≫ h) j m κ v Fl hb hy hdom hf h3
      h4 h6 h7 h9 hfd
  refine ⟨A', e, Fl', ψ', θ', j, h1, h2, h4, h5, h6, hb', q1, q3, q4, q5, fun r e₀ L L' hL hP => ?_⟩
  exact GlobalTheory.T.hodge_cpt_finite_extension E H D l Xo c O β Y S Ω Ω' i K K' J J' y y' A A' (e.hom ≫ h) j m κ v Fl hb hy hdom hf h3 h4 h6 h7 h9
    Fl' hb' r e₀ L L' hL hP

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem twTan_pre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    {g : HostAut H} {Φ : Xo.X ⟶ Xo.X} {n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ} {Y : Model Xo c β}
    {Y' : Model Xo c β'} {T T' : Scheme.{0}} {u₁ : T ⟶ Y.t.G.left} {u₂ : T ⟶ Y'.t.G.left} (w : T' ⟶ T)
    (h : TwTan n Y Y' u₁ u₂) : TwTan n Y Y' (w ≫ u₁) (w ≫ u₂) := by
  obtain ⟨u, u', h1, h2, h3, h4⟩ := h
  refine ⟨w ≫ u, w ≫ u', ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, h1]
  · rw [Category.assoc, h2]
  · rw [Category.assoc, h3, Category.assoc]
  · simp only [Category.assoc, h4]

theorem pair_iso : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' := by
  intro hCmp hTh E _ _ _ H D l Xo c O _ β Y g Φ n π S nn M M' T T' hβ hs hπ himg hR
  obtain ⟨x₀, x₀', ψ, hξ, hξ', hfst, hsnd, hcst, hcst'⟩ := himg
  obtain ⟨π₀, hπ₀, hlab⟩ := GlobalTheory.T.cm_type_host_aut_permutation E H l c g
  have hππ : π₀ = π := Equiv.ext fun τ => Subtype.ext ((hπ₀ τ).trans (hπ τ).symm)
  subst hππ
  obtain ⟨θ, hθs, hθt, hθV⟩ := GlobalTheory.T.twisted_hodge_cpt_compare E H D l Xo c O O β β Y Y g Φ n S M.Ω M'.Ω M.K M'.K M.ι M'.ι M.y M'.y T.A T'.A
    T.Fl T'.Fl ψ x₀ x₀' hβ hβ hξ hξ' hfst hsnd

  letI a₁ : Algebra T.A.Ω₀ M.Ω := T.A.fn.toAlgebra
  letI a₂ : Algebra T.A.Ω₀ M'.Ω := (T'.A.fn.comp ψ.symm.toRingHom).toAlgebra
  letI a₃ : Algebra T'.A.Ω₀ M'.Ω := T'.A.fn.toAlgebra
  have hrl : ∀ s, labelRk D (Sum.map π₀ π₀ s) = labelRk D s := by rintro (τ | τ) <;> rfl
  have g₁ : IsGenericFlag (Ω' := M.Ω) T.Fl.j T.Fl.V₀ T.Fl.b T.Fl.deg := T.Fl.generic
  have g₂ : IsGenericFlag (Ω' := M'.Ω) (T'.Fl.j.comp θ.toAddMonoidHom) T.Fl.V₀
      (fun s k => T'.Fl.b (Equiv.sumCongr π₀ π₀ s) (Fin.cast (hrl s).symm k)) T'.Fl.deg :=
    isGenericFlag_transport ψ (fun a => by
        show T'.A.fn (ψ.symm (ψ a)) = T'.A.fn a
        rw [ψ.symm_apply_apply]) θ (fun a e => hθs a e) T'.Fl.j (Equiv.sumCongr π₀ π₀) hrl T.Fl.V₀ T'.Fl.V₀
      (fun s e => hθV s _ (by simpa [Equiv.sumCongr] using (hlab s)) e) T'.Fl.b T'.Fl.deg T'.Fl.generic
  obtain ⟨Ω₃, fΩ, i₁, i₂, hi, ⟨n₁, n₂, hn₁, hn, hf₁, hf₂⟩, hflag⟩ := PositivityTheory.UnitarySelfGeneration.l_genflag T.A.Ω₀ M.Ω M'.Ω T.Fl.Li₀ T.A.Li T'.A.Li
    T.Fl.j (T'.Fl.j.comp θ.toAddMonoidHom) (CMType H ⊕ CMType H) (labelRk D) T.Fl.V₀ T.Fl.b _ T.Fl.deg T'.Fl.deg g₁ g₂
  have hn₂ : 0 < n₂ := by
    have := Nat.mul_pos hn₁ (IsGenericFlag_deg_pos g₁)
    rw [hn] at this
    exact Nat.pos_of_mul_pos_right this
  haveI : CharZero M.Ω := charZero_of_injective_ringHom T.A.cst.injective
  haveI : CharZero M'.Ω := charZero_of_injective_ringHom T'.A.cst.injective
  haveI : CharZero Ω₃ := charZero_of_injective_ringHom i₁.injective
  have hfd₁ : FiniteDimensional i₁.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by omega)
  have hfd₂ : FiniteDimensional i₂.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by omega)
  obtain ⟨K, hK, ι, hι, κ₁, v₁, κ₂, v₂, y, Z, ξ, h₁, h₂, hb₁, hb₂, hy₁, hy₂, harith, hbir, hall, htie, hnorm, hd₁, hd₂, hr₁, hr₂⟩ :=
    PositivityTheory.UnitarySelfGeneration.j_normal M.K M.ι M'.K M'.ι M.Ω M'.Ω Ω₃ i₁ i₂ M.y M'.y (Top.dimFl (CMType H) (D.p + D.q) + 1) T.A.X T'.A.X T.A.ξ T'.A.ξ
      M.arith M'.arith M.birational M'.birational hfd₁ hfd₂ T.A.all T'.A.all T.A.tie T'.A.tie
  have hx₁ : T.A.ξ ≫ T.A.f = (spMap T.A.fn ≫ x₀) ≫ Y.j := by
    rw [Category.assoc, ← hξ]; exact T.A.fn_over
  have hx₂ : T'.A.ξ ≫ T'.A.f = (spMap T'.A.fn ≫ x₀') ≫ Y.j := by
    rw [Category.assoc, ← hξ']; exact T'.A.fn_over
  obtain ⟨A₁, e₁, Fl₁, ψ₁, θ₁, j₁, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ :=
    pull_both i₁ T.A T.Fl (spMap T.A.fn ≫ x₀) Z ξ h₁ κ₁ v₁ hx₁ T.discr T.ht_vb hall htie hnorm hd₁ hb₁
      (fun q => congrFun hy₁ q) hfd₁
  obtain ⟨A₂, e₂, Fl₂, ψ₂, θ₂, j₂, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ :=
    pull_both i₂ T'.A T'.Fl (spMap T'.A.fn ≫ x₀') Z ξ h₂ κ₂ v₂ hx₂ T'.discr T'.ht_vb hall htie hnorm hd₂ hb₂
      (fun q => congrFun hy₂ q) hfd₂

  have hi' : i₁.comp (T.A.fn.comp ψ.toRingHom) = i₂.comp T'.A.fn := by
    ext a
    have := congrArg (fun f => f (ψ a)) hi
    simpa [a₁, a₂, RingHom.algebraMap_toAlgebra] using this
  have hkey : spMap i₁ ≫ spMap T.A.fn ≫ spMap ψ.toRingHom = spMap i₂ ≫ spMap T'.A.fn := by
    rw [spMap_spMap, spMap_spMap, spMap_spMap, hi']
  have hk3 : ∀ {W : Scheme.{0}} (t : Sp T'.A.Ω₀ ⟶ W), spMap i₂ ≫ spMap T'.A.fn ≫ t =
      spMap i₁ ≫ spMap T.A.fn ≫ spMap ψ.toRingHom ≫ t := by
    intro W t
    rw [← Category.assoc, ← hkey]
    simp only [Category.assoc]
  have hX₁ : A₁.ξ ≫ A₁.f = (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Y.j := by
    have hd : ξ ≫ h₁ = spMap i₁ ≫ T.A.ξ := hd₁
    calc A₁.ξ ≫ A₁.f = (A₁.ξ ≫ e₁.hom) ≫ h₁ ≫ T.A.f := by rw [p2, Category.assoc]
      _ = (ξ ≫ h₁) ≫ T.A.f := by rw [p1, Category.assoc]
      _ = spMap i₁ ≫ T.A.ξ ≫ T.A.f := by rw [hd, Category.assoc]
      _ = _ := by rw [hx₁]; simp only [Category.assoc]
  have hX₂ : A₂.ξ ≫ A₂.f = (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Y.j := by
    have hd : ξ ≫ h₂ = spMap i₂ ≫ T'.A.ξ := hd₂
    calc A₂.ξ ≫ A₂.f = (A₂.ξ ≫ e₂.hom) ≫ h₂ ≫ T'.A.f := by rw [q2, Category.assoc]
      _ = (ξ ≫ h₂) ≫ T'.A.f := by rw [q1, Category.assoc]
      _ = spMap i₂ ≫ T'.A.ξ ≫ T'.A.f := by rw [hd, Category.assoc]
      _ = _ := by rw [hx₂]; simp only [Category.assoc]
  have hfst₃ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.fst _ _ =
      (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.fst _ _ ≫ Φ.hom := by
    simp only [Category.assoc]
    rw [hk3, hfst]
  have hsnd₃ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.snd _ _ =
      (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.snd _ _ := by
    simp only [Category.assoc]
    rw [hk3, hsnd]
  have hc₁ : (spMap i₁ ≫ spMap T.A.fn ≫ x₀) ≫ Limits.pullback.snd _ _ = spMap A₁.cst := by
    rw [p3, ← spMap_spMap, ← hcst]
    simp only [Category.assoc]
  have hc₂ : (spMap i₂ ≫ spMap T'.A.fn ≫ x₀') ≫ Limits.pullback.snd _ _ = spMap A₂.cst := by
    rw [q3, ← spMap_spMap, ← hcst']
    simp only [Category.assoc]
  have hAc : A₁.cst = A₂.cst := spMap_inj (by rw [← hc₁, ← hc₂, hsnd₃])
  have hξe : A₂.ξ ≫ (e₂ ≪≫ e₁.symm).hom = A₁.ξ := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, q1, ← p1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨φ, hφt, -, hφV, hφz⟩ := hCmp E H D l Xo c O O β β Y Y g Φ n S Ω₃ K ι y A₁ A₂ (e₂ ≪≫ e₁.symm) _ _ hβ hβ hs hξe hX₁ hX₂
    hfst₃ hsnd₃ hAc hc₁ (fun p hp => by rw [q4, p4]; exact hR p hp)

  let ψ₃ : A₂.Ω₀ ≃+* A₁.Ω₀ := ψ₂.symm.trans (ψ.trans ψ₁)
  let θ₃ : Fl₁.Li₀ ≃+ Fl₂.Li₀ := θ₁.symm.trans (θ.trans θ₂)
  have hθ₃ : ∀ e, θ₃ (θ₁ e) = θ₂ (θ e) := fun e => by simp [θ₃]
  have hfn : A₁.fn.comp ψ₃.toRingHom = A₂.fn := by
    ext a
    have h1 := congrArg (fun f => f (ψ (ψ₂.symm a))) p7
    have h2 := congrArg (fun f => f (ψ₂.symm a)) hi'
    have h3 := congrArg (fun f => f (ψ₂.symm a)) q7
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at h1 h2 h3
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ψ₃, RingEquiv.trans_apply]
    rw [h1, h2, ← h3]
  have hψc : (dualMap ψ₃.toRingHom).comp (dualMap ψ₂.toRingHom) = (dualMap ψ₁.toRingHom).comp (dualMap ψ.toRingHom) := by
    rw [← GlobalTheory.CompanionTheory.Ar.FlagPull.dualMap_comp, ← GlobalTheory.CompanionTheory.Ar.FlagPull.dualMap_comp]
    congr 1
    ext a
    simp [ψ₃]
  have htw : ∀ e, TwTan n Y Y (Fl₁.M₀.pt e).left (spMap (dualMap ψ₃.toRingHom) ≫ (Fl₂.M₀.pt (θ₃ e)).left) := by
    intro e
    obtain ⟨e₀, rfl⟩ := θ₁.surjective e
    rw [hθ₃, q8, p8, ← Category.assoc, spMap_spMap, hψc, ← spMap_spMap, Category.assoc]
    exact twTan_pre _ (hθt e₀)
  obtain ⟨-, hsteps⟩ := GlobalTheory.T.twisted_hodge_cpt_flag E H D l Xo c O O β β Y Y g Φ n S Ω₃ K ι y A₁ A₂ Fl₁ Fl₂ ψ₃ θ₃ φ hβ hβ hfn hφt htw
  have hst : ∀ s k, (flagStep Ω₃ (Fl₁.b s) k).map (φ : A₁.Li →ₗ[Ω₃] A₂.Li) =
      flagStep Ω₃ (Fl₂.b (Equiv.sumCongr π₀ π₀ s)) k := by
    intro s
    obtain ⟨cc, hcl, hcs⟩ := exists_basis g₁ s
    obtain ⟨m₁, hm₁⟩ := exists_coeff g₁ s cc hcs
    obtain ⟨m₂, hm₂⟩ := exists_coeff g₂ s cc hcs
    have hrow := hflag s cc m₁ m₂ hcl hcs hm₁ hm₂
    refine hsteps s (Equiv.sumCongr π₀ π₀ s) _ (fun q => θ₁ (cc q)) (fun q a => i₁ (m₁ q a)) ?_ ?_
    · intro k
      congr 1
      funext a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [p6, hm₁ a, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [p5.1, p9]
    · intro k
      refine (flagStep_cast (hrl s).symm (Fl₂.b (Equiv.sumCongr π₀ π₀ s)) k).symm.trans ?_
      have e1 : (fun a => Fl₂.b (Equiv.sumCongr π₀ π₀ s) (Fin.cast (hrl s).symm a)) =
          fun a => ∑ q, i₂ (m₂ q a) • Fl₂.j (θ₃ (θ₁ (cc q))) := by
        funext a
        set_option synthInstance.maxHeartbeats 100000 in
          rw [q6, hm₂ a, map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [q5.1, hθ₃, q9]
        rfl
      exact (congrArg (fun f => flagStep Ω₃ f k) e1).trans
        (flagStep_rows (fun q => Fl₂.j (θ₃ (θ₁ (cc q)))) (fun q a => i₂ (m₂ q a)) (fun q a => i₁ (m₁ q a))
          (fun i => (hrow i).symm) k)
  have hemb : ∀ s, A₂.emb (Equiv.sumCongr π₀ π₀ s) = (A₁.emb s).comp g.s.toRingHom := by
    intro s
    show A₂.cst.comp (labelEmb c (Sum.map π₀ π₀ s)) = (A₁.cst.comp (labelEmb c s)).comp g.s.toRingHom
    rw [hlab s, hAc]
    rfl
  have hgram := GlobalTheory.T.hodge_compactification_interior_point hTh E H D l Xo c O β Y S Ω₃ K ι y A₁ Fl₁ hβ
  obtain ⟨b, d, hbm, hbn, hbz⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l Xo c O β Y S Ω₃ K ι y A₁ _ hX₁ hβ
  refine ⟨K, hK, ι, hι, κ₁, v₁, κ₂, v₂, Ω₃, fΩ, inferInstance, y, b, d, hb₁, hb₂, ?_, ?_, harith, hbm, hbn, ?_, ?_, ?_⟩
  · rw [hy₁]
    exact (PositivityTheory.UnitarySelfGeneration.t_ideal M.K M.ι M.Ω Ω₃ i₁ M.y).1
  · rw [hy₂]
    exact (PositivityTheory.UnitarySelfGeneration.t_ideal M'.K M'.ι M'.Ω Ω₃ i₂ M'.y).1
  · rw [hr₁, hf₁]
    exact hn₁.ne'
  · rw [hr₁, hr₂, hf₁, hf₂]
    exact hn
  · intro r L L' hL hL'
    have hdeg : (Fl₁.rootLat (r.1, r.2)).IsDegOn Set.univ y L.a (i₁ (T.e r)) := by
      have := p10 _ _ T.roots r
      rw [hL.1, T.sing_deg]
      exact this
    have hdeg' : (Fl₂.rootLat (π₀ r.1, r.2)).IsDegOn Set.univ y L'.a (i₂ (T'.e (π₀ r.1, r.2))) := by
      have := q10 _ _ T'.roots (π₀ r.1, r.2)
      rw [hL'.1, T'.sing_deg]
      exact this
    have hH := p11 r (T.e r) (T.sing r) L (T.hodge r) hL
    have hH' := q11 (π₀ r.1, r.2) (T'.e (π₀ r.1, r.2)) (T'.sing (π₀ r.1, r.2)) L' (T'.hodge _) hL'
    obtain ⟨f, f', hiso, hdef⟩ := GlobalTheory.T.hodge_cpt_iso_compare E H D l Xo c O O β β Y Y S Ω₃ K ι y A₁ A₂ (e₂ ≪≫ e₁.symm) φ Fl₁ Fl₂ r.1 (π₀ r.1) r.2
      (i₁ (T.e r)) (i₂ (T'.e (π₀ r.1, r.2))) L L' hbir hξe
      (fun q h v => ⟨hφV (.inl r.1) (.inl (π₀ r.1)) (hemb (.inl r.1)) q h v, hφV (.inr r.1) (.inr (π₀ r.1)) (hemb (.inr r.1)) q h v⟩)
      (fun k => ⟨hst (.inl r.1) k, hst (.inr r.1) k⟩) hφz hdeg hdeg' hH hH' hgram
    exact ⟨f, f', hiso, fun w hw => hdef w (hbz w hw.1 hw.2)⟩

end GlobalTheory.CompanionTheory.Ar.PairIsoK

namespace PositivityTheory.UnitarySelfGeneration

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

theorem pair_iso : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' :=
  @GlobalTheory.CompanionTheory.Ar.PairIsoK.pair_iso

end PositivityTheory.UnitarySelfGeneration
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationFibreProductCompatible
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HSamesing
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

theorem same_orbit_log_height_difference {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A B : HermLine ι)
    (hab : B.a = A.a) (w z : (Σ k, ι k) → ℂ) (r : ℝ) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hs : SameOrbit w z)
    (h : Real.log (A.h w) = Real.log (B.h w) + r) :
    0 < A.h z ∧ 0 < B.h z ∧ Real.log (A.h z) = Real.log (B.h z) + r := by
  obtain ⟨c, hc, rfl⟩ := hs
  have hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hw k
    exact ⟨i, fun h0 => hi (by simp [h0])⟩
  have hA := A.pos z hz
  have hB := B.pos z hz
  refine ⟨hA, hB, ?_⟩
  have hC : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [A.smul c z hc, B.smul c z hc, hab, Real.log_mul hC hA.ne', Real.log_mul hC hB.ne'] at h
  linarith

theorem h_samesing_ne {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (hP : P.IsPrime) (f g : MRing ι) (hu : UnitRatio P f g) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P)
    (u v : MRing ι) (huv : u * f - v * g ∈ P) (hu0 : evC z u ≠ 0) : evC z v ≠ 0 := by
  intro hv0
  obtain ⟨hf, -, hW⟩ := hu
  let φ : MRing ι →+* ℂ := (MvPolynomial.eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hφ : ∀ h, φ h = evC z h := fun h => rfl
  have hWp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hPW : P ≤ RingHom.ker φ := fun h hh => (RingHom.mem_ker).2 (by rw [hφ]; exact hz.2 h hh)
  have hrel : IsRelevant (RingHom.ker φ) := by
    intro k
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun h => hi ?_⟩
    have := (RingHom.mem_ker).1 h
    simpa [φ] using this
  obtain ⟨u', v', -, hv', h'⟩ := hW _ hWp hPW hrel
  have hmem : (u * v' - v * u') * f ∈ P := by
    have e : (u * v' - v * u') * f = v' * (u * f - v * g) - v * (u' * f - v' * g) := by ring
    rw [e]
    exact P.sub_mem (P.mul_mem_left _ huv) (P.mul_mem_left _ h')
  have hin : u * v' - v * u' ∈ P := (hP.mem_or_mem hmem).resolve_right hf
  have h0 : φ (u * v' - v * u') = 0 := by rw [hφ]; exact hz.2 _ hin
  rw [map_sub, map_mul, map_mul, hφ v, hv0, zero_mul, sub_zero] at h0
  have hv'' : φ v' ≠ 0 := fun h => hv' (RingHom.mem_ker.2 h)
  exact mul_ne_zero (by rw [hφ]; exact hu0) hv'' h0

theorem h_samesing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (P : Ideal (MRing ι)) (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (D : ℕ) (σ₁ σ₂ : Type) (S₁ : PB.AnSys D σ₁) (S₂ : PB.AnSys D σ₂) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) (A₁ : HermLine ι₁) (A₂ : HermLine ι₂) (A₁' A₂' : HermLine ι), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsPullHerm κ₁ v₁ A₁ A₁' → IsPullHerm κ₂ v₂ A₂ A₂' → (Re₁.ref a₁).a = A₁.a → (Re₂.ref a₂).a = A₂.a → (∀ x, Re₁.π x ∉ ReciprocityTheory.AnForm.P.bdry S₁.s → Real.log (A₁.h (Re₁.R.lift x x)) = Real.log ((Re₁.ref a₁).h (Re₁.R.lift x x)) + S₁.ph a₁ (Re₁.π x)) → (∀ x, Re₂.π x ∉ ReciprocityTheory.AnForm.P.bdry S₂.s → Real.log (A₂.h (Re₂.R.lift x x)) = Real.log ((Re₂.ref a₂).h (Re₂.R.lift x x)) + S₂.ph a₂ (Re₂.π x)) → IsMultiProjPrime P → IsoLineOn P {z | z ∈ mcPts P ∧ evC z β ≠ 0} A₁' A₂' → SameSing Re₁ Re₂ P κ₁ v₁ κ₂ v₂ β a₁ a₂ := by
  intro K _ ι _ K₁ _ ι₁ _ K₂ _ ι₂ _ κ₁ v₁ κ₂ v₂ P P₁ P₂ D σ₁ σ₂ S₁ S₂ Re₁ Re₂ β a₁ a₂ A₁ A₂ A₁' A₂'
    hb₁ hb₂ hp₁ hp₂ ha₁ ha₂ hφ₁ hφ₂ hP hiso
  obtain ⟨f, g, hfg, hdef⟩ := hiso
  refine ⟨f, g, ?_, ?_⟩
  · rw [ha₁, ha₂, ← hp₁.1, ← hp₂.1]
    exact hfg
  · intro z hz hβ x₁ x₂ hs₁ hs₂ hb₁' hb₂' u v huv hu
    have hw₁ := (Re₁.R.mem x₁ x₁ (Re₁.R.mem_U x₁)).1
    have hw₂ := (Re₂.R.mem x₂ x₂ (Re₂.R.mem_U x₂)).1
    obtain ⟨q₁, r₁, e₁⟩ := same_orbit_log_height_difference A₁ (Re₁.ref a₁) ha₁ _ _ _ hw₁ hs₁ (hφ₁ x₁ hb₁')
    obtain ⟨q₂, r₂, e₂⟩ := same_orbit_log_height_difference A₂ (Re₂.ref a₂) ha₂ _ _ _ hw₂ hs₂ (hφ₂ x₂ hb₂')
    have hv := h_samesing_ne P hP.1 f g hfg.2 z hz u v huv hu
    have hd := hdef z ⟨hz, hβ⟩ u v huv hu
    rw [← hp₁.2 z] at q₁ e₁
    rw [← hp₂.2 z] at q₂ e₂
    have hu' : 0 < ‖evC z v‖ / ‖evC z u‖ := div_pos (norm_pos_iff.2 hv) (norm_pos_iff.2 hu)
    rw [Real.log_div (mul_pos hu' q₂).ne' q₁.ne', Real.log_mul hu'.ne' q₂.ne'] at hd
    rw [Real.log_div (mul_pos hu' r₂).ne' r₁.ne', Real.log_mul hu'.ne' r₂.ne']
    linarith

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationFibreProductCompatible
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem sameSing_of_isoLine : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (P : Ideal (MRing ι)) (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (D : ℕ) (σ₁ σ₂ : Type) (S₁ : PB.AnSys D σ₁) (S₂ : PB.AnSys D σ₂) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) (A₁ : HermLine ι₁) (A₂ : HermLine ι₂) (A₁' A₂' : HermLine ι), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsPullHerm κ₁ v₁ A₁ A₁' → IsPullHerm κ₂ v₂ A₂ A₂' → (Re₁.ref a₁).a = A₁.a → (Re₂.ref a₂).a = A₂.a → (∀ x, Re₁.π x ∉ ReciprocityTheory.AnForm.P.bdry S₁.s → Real.log (A₁.h (Re₁.R.lift x x)) = Real.log ((Re₁.ref a₁).h (Re₁.R.lift x x)) + S₁.ph a₁ (Re₁.π x)) → (∀ x, Re₂.π x ∉ ReciprocityTheory.AnForm.P.bdry S₂.s → Real.log (A₂.h (Re₂.R.lift x x)) = Real.log ((Re₂.ref a₂).h (Re₂.R.lift x x)) + S₂.ph a₂ (Re₂.π x)) → IsMultiProjPrime P → IsoLineOn P {z | z ∈ mcPts P ∧ evC z β ≠ 0} A₁' A₂' → SameSing Re₁ Re₂ P κ₁ v₁ κ₂ v₂ β a₁ a₂ :=
  @PositivityTheory.UnitarySelfGeneration.h_samesing

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationFibreProductCompatibleStatement
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_fibre_product_compatible : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (P : Ideal (MRing ι)) (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (D : ℕ) (σ₁ σ₂ : Type) (S₁ : PB.AnSys D σ₁) (S₂ : PB.AnSys D σ₂) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) (A₁ : HermLine ι₁) (A₂ : HermLine ι₂) (A₁' A₂' : HermLine ι), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsPullHerm κ₁ v₁ A₁ A₁' → IsPullHerm κ₂ v₂ A₂ A₂' → (Re₁.ref a₁).a = A₁.a → (Re₂.ref a₂).a = A₂.a → (∀ x, Re₁.π x ∉ ReciprocityTheory.AnForm.P.bdry S₁.s → Real.log (A₁.h (Re₁.R.lift x x)) = Real.log ((Re₁.ref a₁).h (Re₁.R.lift x x)) + S₁.ph a₁ (Re₁.π x)) → (∀ x, Re₂.π x ∉ ReciprocityTheory.AnForm.P.bdry S₂.s → Real.log (A₂.h (Re₂.R.lift x x)) = Real.log ((Re₂.ref a₂).h (Re₂.R.lift x x)) + S₂.ph a₂ (Re₂.π x)) → IsMultiProjPrime P → IsoLineOn P {z | z ∈ mcPts P ∧ evC z β ≠ 0} A₁' A₂' → SameSing Re₁ Re₂ P κ₁ v₁ κ₂ v₂ β a₁ a₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine | exact GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.sameSing_of_isoLine <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelComparisonLimit
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelComparisonLimit
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Root

theorem word_expand (hI : Inputs) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) {σ : Type} [Fintype σ] [DecidableEq σ]
    {d : ℕ} (hd : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar M.P d) (ℓ : σ → HermLine M.ι) (n : Fin d → σ → ℤ) (L : Fin d → HermLine M.ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (hℓ : ∀ a, IsSmoothHerm (ℓ a))
    (ha : ∀ j, (L j).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)).a)
    (hh : ∀ j, ∀ z ∈ mcPts M.P, (L j).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)).h z) :
    II _ _ M.P d L = ∑ u : Fin d → σ, (∏ k, (n k (u k) : ℝ)) * II _ _ M.P d (fun k => ℓ (u k)) := by
  have hc : ∀ j, IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)) := fun j =>
    (GlobalTheory.T.hermitian_combination_smooth_conj _ M.ι σ ℓ (n j)).1 hℓ
  rw [hI.metricLocal _ M.ι (II _ M.ι) (hII.1 _ M.ι) M.P d L (fun j => GlobalTheory.CompanionTheory.Ar.Top.combLine ℓ (n j)) hd hL hc ha hh]
  exact GlobalTheory.T.arith_intersection_multilinear_all II hII _ M.ι M.P d σ ℓ n hd hℓ

theorem cmp_root : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M₁ M₂ : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (σ : Type) [Fintype σ] [DecidableEq σ] (ℓ₁ : ℝ → σ → HermLine M₁.ι) (ℓ₂ : ℝ → σ → HermLine M₂.ι) (n : Ψ × Fin N → σ → ℤ) (s : Ψ × Fin N → Ψ × Fin N) (e₁ e₂ : ℕ), e₁ ≠ 0 → e₁ * M₁.δ = e₂ * M₂.δ → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (ℓ₁ t a) ∧ IsSmoothHerm (ℓ₂ t a)) ∧ (∀ r, (M₁.x t (s r)).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).a ∧ ∀ z ∈ mcPts M₁.P, (M₁.x t (s r)).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).h z) ∧ ∀ r, (M₂.x t r).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).a ∧ ∀ z ∈ mcPts M₂.P, (M₂.x t r).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).h z) → (∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ, Tendsto (fun t => (e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (w j)) - (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (w j))) (𝓝[>] 0) (𝓝 0)) → ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M₁.P _ (fun j => M₁.x t (s (w j))) / M₁.δ - II _ _ M₂.P _ (fun j => M₂.x t (w j)) / M₂.δ) (𝓝[>] 0) (𝓝 0) := by
  intro hI II hII Ψ _ _ N M₁ M₂ σ _ _ ℓ₁ ℓ₂ n s e₁ e₂ he₁ hδ hev hnull w
  have hδ₁ : (M₁.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M₁.δ_pos.ne'
  have hδ₂ : (M₂.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M₂.δ_pos.ne'
  have he₁' : (e₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he₁
  have hδR : (e₁ : ℝ) * M₁.δ = e₂ * M₂.δ := by exact_mod_cast hδ
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ))
    (fun u _ => (hnull u).const_mul (∏ k, (n (w k) (u k) : ℝ)))
  have hdiv := hsum.const_mul (((e₁ : ℝ) * M₁.δ)⁻¹)
  simp only [mul_zero, Finset.sum_const_zero] at hdiv
  refine Tendsto.congr' ?_ hdiv
  filter_upwards [hev] with t ht
  obtain ⟨hsm, h1, h2⟩ := ht
  have E₁ := word_expand hI II hII M₁ M₁.arith (ℓ₁ t) (fun k => n (w k)) (fun j => M₁.x t (s (w j)))
    (fun j => M₁.x_smooth t _) (fun a => (hsm a).1) (fun j => (h1 (w j)).1) (fun j => (h1 (w j)).2)
  have E₂ := word_expand hI II hII M₂ M₂.arith (ℓ₂ t) (fun k => n (w k)) (fun j => M₂.x t (w j))
    (fun j => M₂.x_smooth t _) (fun a => (hsm a).2) (fun j => (h2 (w j)).1) (fun j => (h2 (w j)).2)
  rw [E₁, E₂]
  have hsplit : ∀ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
      (∏ k, (n (w k) (u k) : ℝ)) * ((e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j)) -
        (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) =
      (e₁ : ℝ) * ((∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j))) -
        (e₂ : ℝ) * ((∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) := fun u => by ring
  simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  generalize (∑ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
    (∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₁.P _ (fun j => ℓ₁ t (u j))) = A
  generalize (∑ u : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ,
    (∏ k, (n (w k) (u k) : ℝ)) * II _ _ M₂.P _ (fun j => ℓ₂ t (u j))) = B
  have hB : (e₂ : ℝ) * B / ((e₁ : ℝ) * M₁.δ) = B / M₂.δ := by
    rw [hδR]
    have he₂ : (e₂ : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hδR
      exact mul_ne_zero he₁' hδ₁ hδR
    field_simp
  rw [← hB]
  field_simp

end GlobalTheory.CompanionTheory.Ar.Cmp.Root
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelComparisonLimitStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_comparison_limit : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M₁ M₂ : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (σ : Type) [Fintype σ] [DecidableEq σ] (ℓ₁ : ℝ → σ → HermLine M₁.ι) (ℓ₂ : ℝ → σ → HermLine M₂.ι) (n : Ψ × Fin N → σ → ℤ) (s : Ψ × Fin N → Ψ × Fin N) (e₁ e₂ : ℕ), e₁ ≠ 0 → e₁ * M₁.δ = e₂ * M₂.δ → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (ℓ₁ t a) ∧ IsSmoothHerm (ℓ₂ t a)) ∧ (∀ r, (M₁.x t (s r)).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).a ∧ ∀ z ∈ mcPts M₁.P, (M₁.x t (s r)).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).h z) ∧ ∀ r, (M₂.x t r).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).a ∧ ∀ z ∈ mcPts M₂.P, (M₂.x t r).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).h z) → (∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ, Tendsto (fun t => (e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (w j)) - (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (w j))) (𝓝[>] 0) (𝓝 0)) → ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M₁.P _ (fun j => M₁.x t (s (w j))) / M₁.δ - II _ _ M₂.P _ (fun j => M₂.x t (w j)) / M₂.δ) (𝓝[>] 0) (𝓝 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root | exact GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeTieCompare
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeTieCompare
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.twisted_hodge_tie_compare : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' := by
  first | exact @PositivityTheory.UnitarySelfGeneration.pair_iso | exact PositivityTheory.UnitarySelfGeneration.pair_iso
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedHodgeTieCompareStatement
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_hodge_tie_compare : HodgeComparisonCompatibility → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ) (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'), Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) → IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) → ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (κ : M.K → K) (v : (Σ k, M.ι k) → Σ k, ι k) (κ' : M'.K → K) (v' : (Σ k, M'.ι k) → Σ k, ι k) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, ι k) → Ω) (b : MRing ι) (d : K → ℕ), IsBlockMap κ v ∧ IsBlockMap κ' v' ∧ mCoordIdeal (y ∘ v) = M.P ∧ mCoordIdeal (y ∘ v') = M'.P ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (Top.dimFl (CMType H) (D.p + D.q) + 1) ∧ IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 ∧ IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * T.Fl.deg = IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * T'.Fl.deg ∧ ∀ (r : CMType H × Fin (D.p + D.q)) (L L' : HermLine ι), IsPullHerm κ v (T.sing r) L → IsPullHerm κ' v' (T'.sing (π r.1, r.2)) L' → IsoLineOn (mCoordIdeal y) {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} L L' := by
  first | exact @GlobalTheory.CompanionTheory.Relay.twisted_hodge_tie_compare | exact GlobalTheory.CompanionTheory.Relay.twisted_hodge_tie_compare | (intros; apply GlobalTheory.CompanionTheory.Relay.twisted_hodge_tie_compare <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputs
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

theorem hermLine_ext {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {A B : HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A; cases B; cases ha; cases hh; rfl

theorem combLine_equiv {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (e : J ≃ J) :
    Top.combLine (ℓ ∘ e) (n ∘ e) = Top.combLine ℓ n := by
  apply hermLine_ext
  · simp only [Top.combLine, Function.comp]
    exact Equiv.sum_comp e (fun j => n j • (ℓ j).a)
  · funext z
    simp only [Top.combLine, Function.comp]
    exact Equiv.prod_comp e (fun j => (ℓ j).h z ^ n j)

def relab {Ψ : Type} (π : Ψ ≃ Ψ) (N : ℕ) : Ψ × Fin N ≃ Ψ × Fin N := Equiv.prodCongr π (Equiv.refl _)

end GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

theorem degComb {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (sing ref line : Ψ × Fin N → HermLine ι) (hl : ∀ a, (line a).a = (ref a).a)
    (hr : ∀ a, (ref a).a = (Top.combLine sing (fundOnRoot a)).a) (r : Ψ × Fin N) :
    (Top.combLine line (rootOnFund r)).a = (sing r).a := by
  have hfi := GlobalTheory.T.root_fundamental_weight_duality Ψ N
  simp only [Top.combLine] at hr ⊢
  simp_rw [hl, hr, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, (hfi r _).1, ite_smul, one_smul, zero_smul]
  simp

theorem cmpSt_of_eq (hC : CmpSt) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k)
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : PB.AnSys D σ)
    (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂)
    (h₁ : mCoordIdeal (y ∘ v₁) = P₁) (h₂ : mCoordIdeal (y ∘ v₂) = P₂) (β : MRing ι) (b : K → ℕ)
    (hv₁ : IsBlockMap κ₁ v₁) (hv₂ : IsBlockMap κ₂ v₂) (hy : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1))
    (hβ : IsMultiHomog β b) (hβy : β ∉ mCoordIdeal y) (hA₁ : AlgOver Re₁) (hA₂ : AlgOver Re₂)
    (hS : ∀ a, SameSing Re₁ Re₂ (mCoordIdeal y) κ₁ v₁ κ₂ v₂ β a a) (w : Fin (D + 1) → σ) :
    Tendsto (fun t =>
      (IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) : ℝ) *
          II K₁ ι₁ P₁ (D + 1) (fun j => Re₁.line (w j) t) -
        (IntermediateField.relfinrank (blockFnField (y ∘ v₂)) (blockFnField y) : ℝ) *
          II K₂ ι₂ P₂ (D + 1) (fun j => Re₂.line (w j) t)) (𝓝[>] 0) (𝓝 0) := by
  subst h₁ h₂
  exact hC II hII K ι K₁ ι₁ K₂ ι₂ κ₁ v₁ κ₂ v₂ Ω y D σ S₁ S₂ Re₁ Re₂ β b hv₁ hv₂ hy hβ hβy hA₁ hA₂ hS w

end GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

namespace GlobalTheory.CompanionTheory.Ar.Cmp.PairTop

theorem cmpPair : PB.Inputs → CmpSt → HodgeComparisonCompatibility → ThetaUnifAV → CmpPair := by
  intro hIn hC hT hU II hII E _ _ _ H D l Xo c O _ β Y g Φ hΦ π S n M M' T T' hβ hs hπ hA hR w
  classical
  obtain ⟨K, hK, ι, hι, κ, v, κ', v', Ω, hΩ, hΩ0, y, b, d, hbv, hbv', hP, hP', harith, hmh, hb, hne, hdeg, hiso⟩ :=
    GlobalTheory.T.twisted_hodge_tie_compare hT hU E H D l Xo c O β Y g Φ hΦ π S n M M' T T' hβ hs hπ hA hR
  have hJ := GlobalTheory.T.block_pullback_herm_line M.K M.ι K ι κ v hbv
  have hJ' := GlobalTheory.T.block_pullback_herm_line M'.K M'.ι K ι κ' v' hbv'
  have hmpp : IsMultiProjPrime (mCoordIdeal y) := harith.2.1
  obtain ⟨hc1, -, -, hc4⟩ := GlobalTheory.T.iso_line_on_equivalence K ι (mCoordIdeal y)
    {z | z ∈ mcPts (mCoordIdeal y) ∧ evC z b ≠ 0} hmpp (fun z hz => hz.1)
  let f := relab π (D.p + D.q)
  let Lr : CMType H × Fin (D.p + D.q) → HermLine ι := fun r => (hJ.1 (T.sing r)).exists.choose
  let Lr' : CMType H × Fin (D.p + D.q) → HermLine ι := fun r => (hJ'.1 (T'.sing (f r))).exists.choose
  have hLr : ∀ r, IsPullHerm κ v (T.sing r) (Lr r) := fun r => (hJ.1 (T.sing r)).exists.choose_spec
  have hLr' : ∀ r, IsPullHerm κ' v' (T'.sing (f r)) (Lr' r) := fun r => (hJ'.1 (T'.sing (f r))).exists.choose_spec
  have hfi := GlobalTheory.T.root_fundamental_weight_duality (CMType H) (D.p + D.q)
  have hfun : ∀ a, fundOnRoot (f a) ∘ f = fundOnRoot a := fun a => funext fun r => ((hfi a r).2 π).2
  have hsame : ∀ a, SameSing T.Re (T'.Re.comap f) (mCoordIdeal y) κ v κ' v' b a a := by
    intro a
    have e2 : Top.combLine T'.sing (fundOnRoot (f a)) = Top.combLine (T'.sing ∘ f) (fundOnRoot a) := by
      rw [← hfun a, combLine_equiv]
    refine GlobalTheory.T.realisation_fibre_product_compatible K ι M.K M.ι M'.K M'.ι κ v κ' v' (mCoordIdeal y) M.P M'.P _ _ _ T.Sy (T'.Sy.comap f)
      T.Re (T'.Re.comap f) b a a (Top.combLine T.sing (fundOnRoot a)) (Top.combLine T'.sing (fundOnRoot (f a)))
      (Top.combLine Lr (fundOnRoot a)) (Top.combLine Lr' (fundOnRoot a)) hbv hbv'
      (hc4 _ _ κ v _ _ _ (fundOnRoot a) hbv hLr) ?_ (T.ref_deg a) (T'.ref_deg (f a)) (T.sing_eq a)
      (T'.sing_eq (f a)) hmpp (hc1 _ Lr Lr' (fundOnRoot a) fun r => hiso r _ _ (hLr r) (hLr' r))
    rw [e2]
    exact hc4 _ _ κ' v' _ (T'.sing ∘ f) Lr' (fundOnRoot a) hbv' hLr'
  have hword := cmpSt_of_eq hC II hII K ι M.K M.ι M'.K M'.ι κ v κ' v' Ω y _ _ T.Sy (T'.Sy.comap f) M.P M'.P
    T.Re (T'.Re.comap f) hP hP' b d hbv hbv' harith hmh hb T.alg T'.alg hsame
  have hδ : IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * M.δ =
      IntermediateField.relfinrank (blockFnField (y ∘ v')) (blockFnField y) * M'.δ := by
    rw [T.δ_eq, T'.δ_eq, mul_left_comm, hdeg, mul_left_comm]
  have hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsSmoothHerm (T.Re.line a t) ∧ IsSmoothHerm (T'.Re.line (f a) t) := by
    rw [Filter.eventually_all]
    intro a
    filter_upwards [Ioo_mem_nhdsGT (T.Sy.reg a).1, Ioo_mem_nhdsGT (T'.Sy.reg (f a)).1] with t ht1 ht2
    exact ⟨T.Re.line_smooth a t ht1.1 ht1.2.le, T'.Re.line_smooth _ t ht2.1 ht2.2.le⟩
  have hroot : ∀ r, rootOnFund (f.symm r) = rootOnFund r ∘ f := fun r => funext fun a => by
    have h := ((hfi (f.symm r) a).2 π).1
    rw [← h]
    exact congrArg (fun x => rootOnFund x (f a)) (f.apply_symm_apply r)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (T.Re.line a t) ∧ IsSmoothHerm (T'.Re.line (f a) t)) ∧
      (∀ r, (M.x t (f.symm r)).a = (Top.combLine (fun a => T.Re.line a t) (rootOnFund (f.symm r))).a ∧
        ∀ z ∈ mcPts M.P, (M.x t (f.symm r)).h z = (Top.combLine (fun a => T.Re.line a t) (rootOnFund (f.symm r))).h z) ∧
      ∀ r, (M'.x t r).a = (Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r))).a ∧
        ∀ z ∈ mcPts M'.P, (M'.x t r).h z = (Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r))).h z := by
    filter_upwards [hsm, T.line_eq, T'.line_eq] with t hs1 hl1 hl2
    refine ⟨hs1, fun r => ⟨?_, fun z hz => hl1 _ z hz⟩, fun r => ?_⟩
    · rw [M.x_deg, ← T.sing_deg]
      exact (degComb T.sing T.Re.ref (fun a => T.Re.line a t) (fun a => T.Re.line_deg a t) T.ref_deg _).symm
    · have e : Top.combLine (fun a => T'.Re.line (f a) t) (rootOnFund (f.symm r)) =
          Top.combLine (fun a => T'.Re.line a t) (rootOnFund r) := by
        rw [hroot r]
        exact combLine_equiv (fun a => T'.Re.line a t) (rootOnFund r) f
      rw [e]
      refine ⟨?_, fun z hz => hl2 r z hz⟩
      rw [M'.x_deg, ← T'.sing_deg]
      exact (degComb T'.sing T'.Re.ref (fun a => T'.Re.line a t) (fun a => T'.Re.line_deg a t) T'.ref_deg _).symm
  have hmain := GlobalTheory.T.root_model_comparison_limit hIn II hII (CMType H) (D.p + D.q) M M' (CMType H × Fin (D.p + D.q))
    (fun t a => T.Re.line a t) (fun t a => T'.Re.line (f a) t) (fun r => rootOnFund (f.symm r)) f.symm _ _
    hne hδ hev hword (f ∘ w)
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hmain
  exact hmain

end GlobalTheory.CompanionTheory.Ar.Cmp.PairTop
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputsStatement
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmpPair_of_inputs : PB.Inputs → CmpSt → HodgeComparisonCompatibility → ThetaUnifAV → CmpPair := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair | exact GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair <;> assumption)
end
