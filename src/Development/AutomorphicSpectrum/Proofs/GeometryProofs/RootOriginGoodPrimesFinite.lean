module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimes

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonRight
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbGen

theorem flagStep_comp {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e) {r : ℕ}
    (b b' : Fin r → V) (k : ℕ) (h : flagStep Ω b k = flagStep Ω b' k) :
    flagStep Ω' (fun a => j (b a)) k = flagStep Ω' (fun a => j (b' a)) k := by
  have key : ∀ c c' : Fin r → V, flagStep Ω c k ≤ flagStep Ω c' k →
      flagStep Ω' (fun a => j (c a)) k ≤ flagStep Ω' (fun a => j (c' a)) k := by
    intro c c' hle
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have hmem : c a ∈ flagStep Ω c' k := hle (Submodule.subset_span ⟨a, ha, rfl⟩)
    show j (c a) ∈ _
    refine Submodule.span_induction (p := fun v _ => j v ∈ flagStep Ω' (fun a => j (c' a)) k) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨d, hd, rfl⟩
      exact Submodule.subset_span ⟨d, hd, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
    · intro t x _ hx
      rw [hj]
      exact Submodule.smul_mem _ _ hx
  exact le_antisymm (key _ _ h.le) (key _ _ h.ge)

theorem span_image_span {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e)
    (R : Subring Ω) (R' : Subring Ω') (hR : ∀ a ∈ R, i a ∈ R') {r : ℕ} (b : Fin r → V) :
    Submodule.span R' (j '' (Submodule.span R (Set.range b) : Set V)) =
      Submodule.span R' (Set.range fun a => j (b a)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine Submodule.span_induction
      (p := fun v _ => j v ∈ Submodule.span R' (Set.range fun a => j (b a))) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨d, rfl⟩
      exact Submodule.subset_span ⟨d, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
    · intro t x _ hx
      have h1 : j (t • x) = (⟨i t, hR t t.2⟩ : R') • j x := hj (t : Ω) x
      rw [h1]
      exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨b a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩

theorem discr_inv_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    (F : Type) [Field F] [NumberField F] (h : ∀ n : ℕ, 0 < n → unitAt ξ p (n : Ω)) :
    (((NumberField.discr F : ℤ) : Ω))⁻¹ ∈ regAt ξ p := by
  have hn0 : 0 < (NumberField.discr F).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero F)
  obtain ⟨-, -, hu⟩ := h _ hn0
  rcases Int.natAbs_eq (NumberField.discr F) with e | e
  · rw [e]; simpa using hu
  · rw [e]
    simpa using (regAt ξ p).neg_mem hu


set_option maxHeartbeats 1000000 in
theorem isFlagVBOn_genFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → B.M.lat = A.M.lat.pull B.ξ h jA → ∀ q ∈ genFib B.ξ, ∀ s, (B.V s).IsFlagVBOn {q} (fun a => jA (Fl.b s a)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hdom hf hcst hext hpt hρ hlat q hq s
  intro q' hq'
  obtain rfl : q' = q := hq'
  haveI : CharZero Ω₁ := charZero_of_injective_ringHom A.cst.injective
  have hgenA := A.tie.gen
  have hgenB := B.tie.gen
  obtain ⟨hsp, hreg, hun⟩ := RegAtDom.regAt_dominates A.X Ω₁ A.ξ B.X Ω B.ξ h i hdom q'
  have hunit : ∀ n : ℕ, 0 < n → unitAt A.ξ ⟨h q'.1, hsp⟩ (n : Ω₁) := fun n hn =>
    hun hgenB _ (natCast_mem _ n) (by simpa using hq n hn)
  have hVA : A.V s ⟨h q'.1, hsp⟩ = A.dR s ⟨h q'.1, hsp⟩ :=
    Lat.patch_of_not S₀ _ _ fun r hr hfib => hfib (hunit r (A.S_prime r hr).pos)
  have hVB : B.V s q' = B.dR s q' :=
    Lat.patch_of_not S _ _ fun r hr hfib => hfib (hq r (B.S_prime r hr).pos)
  have hdisc := discr_inv_mem ⟨h q'.1, hsp⟩ E hunit
  have hint : ∀ a, A.emb s a ∈ regAt A.ξ ⟨h q'.1, hsp⟩ := fun a =>
    GlobalTheory.T.integral_element_regular A.X Ω₁ A.ξ ⟨h q'.1, hsp⟩ hgenA (A.normal.2 (h q'.1)) _
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)
  obtain ⟨U, hU, b, hb, hfr⟩ := Fl.sub s ⟨h q'.1, hsp⟩ trivial
  obtain ⟨hli, hbs⟩ := hfr ⟨h q'.1, hsp⟩ trivial hU
  refine ⟨⊤, trivial, fun a => jA (b a), fun k => flagStep_comp i jA hext.1 _ _ k (hb k), ?_⟩
  intro q'' hq'' _
  rw [show q'' = q' from hq'']
  refine ⟨hext.2 _ b hli, ?_⟩
  have key := GlobalTheory.T.lattice_eigen_field_extension E Ω₁ Ω i A.Li B.Li jA A.ρ B.ρ (A.emb s) _ _ (A.M.lat ⟨h q'.1, hsp⟩) hext
    (fun a e => (hρ a e).symm) hreg
    (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω₁ A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) hint hdisc
  have hem : B.emb s = i.comp (A.emb s) := by
    show B.cst.comp _ = i.comp (A.cst.comp _)
    rw [hcst]; rfl
  have hL : B.M.lat q' = Submodule.span (regAt B.ξ q') (jA '' (A.M.lat ⟨h q'.1, hsp⟩ : Set A.Li)) := by
    rw [hlat]
    show Lat.pull _ _ _ _ _ = _
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨hsp, e, he, rfl⟩
  have hA : A.M.lat ⟨h q'.1, hsp⟩ ⊓ (eigSp A.ρ (A.emb s)).restrictScalars (regAt A.ξ ⟨h q'.1, hsp⟩) =
      Submodule.span (regAt A.ξ ⟨h q'.1, hsp⟩) (Set.range b) := hVA.symm.trans hbs
  rw [hVB]
  show B.M.lat q' ⊓ (eigSp B.ρ (B.emb s)).restrictScalars (regAt B.ξ q') = _
  rw [hL, hem, key, hA]
  exact span_image_span i jA hext.1 _ _ hreg b

end GlobalTheory.CompanionTheory.Ar.VbGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonRightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_comparison_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → B.M.lat = A.M.lat.pull B.ξ h jA → ∀ q ∈ genFib B.ξ, ∀ s, (B.V s).IsFlagVBOn {q} (fun a => jA (Fl.b s a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.VbGen.isFlagVBOn_genFib | exact GlobalTheory.CompanionTheory.Ar.VbGen.isFlagVBOn_genFib | (intros; apply GlobalTheory.CompanionTheory.Ar.VbGen.isFlagVBOn_genFib <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGoodPrimesFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : R →+* S) (b : T →+* R) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  show Spec.map (CommRingCat.ofHom (a.comp b)) = Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have h' : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := h
  have := Spec.map_injective h'
  exact CommRingCat.hom_ext_iff.1 this |> fun e => by simpa using e

theorem spMap_dualMap_id (Ω : Type) [Field Ω] : spMap (dualMap (RingHom.id Ω)) = 𝟙 _ := by
  have : dualMap (RingHom.id Ω) = RingHom.id _ := by
    ext a <;> simp [dualMap]
  rw [this]
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
  simp

theorem cst_ext {F Ω : Type} [Field F] [NumberField F] [Field Ω] {a b : F →+* Ω}
    (h : a.comp (algebraMap (𝓞 F) F) = b.comp (algebraMap (𝓞 F) F)) : a = b :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h

theorem exists_cover : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → o.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i ∧ 𝔐.f = h ≫ o.𝔐.f ∧ 𝔐.cst = i.comp o.𝔐.cst ∧ (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) ∧ (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) ∧ Fl.RootLines xdeg e ∧ 𝔐.OmVB ∧ SmoothGenericFibreM y ∧ ∀ p ∈ S, 𝔐.R p = 4 := by
  intro hG hW E _ _ _ H D l Xo c Y Sys Fx R o S hSp hSd hdeg
  have hRes : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  have : CharZero R.Ω := charZero_of_injective_ringHom o.𝔐.cst.injective
  have hgen₀ := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y o.𝔐.Ω₀ o.𝔐.ξ₀ o.𝔐.gen₀
  have hgen : GlobalTheory.CompanionTheory.Ar.genPt (o.𝔐.ξ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    have e : o.𝔐.ξ ≫ o.𝔐.f = Spec.map (CommRingCat.ofHom o.𝔐.fn) ≫ o.𝔐.ξ₀ := o.𝔐.fn_over
    rw [e, genPt_comp]; exact hgen₀
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := GlobalTheory.T.exists_finite_extension_primes E H D l Xo c Y R.Ω (o.𝔐.ξ ≫ o.𝔐.f) S hgen hSp
  obtain ⟨K₁, _, J₁, _, y₁, bk₁, bx₁, M₁, h₁, hbk₁, hy₁, hdom₁, hnorm₁, hsm₁⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes R.K R.ι R.Ω Ω i R.y o.𝔐.X o.𝔐.ξ hfin o.𝔐.all o.𝔐.tie
  have hξ₁ : M₁.ξ ≫ h₁ ≫ o.𝔐.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
    have e : M₁.ξ ≫ h₁ = Spec.map (CommRingCat.ofHom i) ≫ o.𝔐.ξ := hdom₁
    rw [← Category.assoc, e, Category.assoc]
  have hgen₁ : GlobalTheory.CompanionTheory.Ar.genPt (M₁.ξ ≫ h₁ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    rw [hξ₁]; show GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom i) ≫ _) ∈ _
    rw [genPt_comp]; exact hgen
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω (M₁.ξ ≫ h₁ ≫ o.𝔐.f) hgen₁
  obtain ⟨K₂, _, J₂, _, y₂, bk₂, bx₂, B, g, hbk₂, hy₂, hdom₂, hf₂, hR₂, hfree₂, hiso₂⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l Xo c Y S (fun _ => 4) Ω K₁ J₁ y₁ M₁ (h₁ ≫ o.𝔐.f) y₀ hnorm₁ hy₀ hgen₁ hSp hSd
      (fun _ _ => le_rfl) (fun p hp => by rw [hξ₁]; exact htors p hp) hroot
  have hgB : B.ξ ≫ g = M₁.ξ := by
    have e : B.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hdomB : GlobalTheory.CompanionTheory.Ar.Dominates B.ξ o.𝔐.ξ (g ≫ h₁) i := by
    show B.ξ ≫ g ≫ h₁ = _
    rw [← Category.assoc, hgB]; exact hdom₁
  have hfB : B.f = (g ≫ h₁) ≫ o.𝔐.f := by rw [hf₂, Category.assoc]
  have hBξ : B.ξ ≫ B.f = y₀ ≫ Y.j := by
    rw [hf₂, ← Category.assoc, hgB]; exact hy₀
  have hcst : B.cst = i.comp o.𝔐.cst := by
    have h1 := B.cst_over
    have h2 := o.𝔐.cst_over
    have h3 : B.ξ ≫ B.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
      rw [hf₂, ← Category.assoc, hgB]; exact hξ₁
    have h4 : spMap (B.cst.comp (algebraMap (𝓞 c.F) c.F)) =
        spMap ((i.comp o.𝔐.cst).comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← Category.assoc, h3, RingHom.comp_assoc, spMap_comp', ← h2]
      simp
    have := c.fin
    have : NumberField c.F := {}
    exact cst_ext (spMap_inj h4)
  obtain ⟨jA, hext, hpt, hact, hlat⟩ :=
    GlobalTheory.T.hodge_comp_comparison_left E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 B i (g ≫ h₁) hdomB hfB
  obtain ⟨Li₀, _, _, M₀, j, V₀, hspan, hj, hV, hflag⟩ :=
    GlobalTheory.T.hodge_comp_comparison_middle E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hfin hdomB hfB hcst hext hpt hact
  have hvb := GlobalTheory.T.hodge_comp_comparison_right E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hdomB hfB hcst hext hpt hact hlat
  obtain ⟨K₃, _, J₃, _, y₃, bk₃, bx₃, 𝔐, g', Fl, xdeg, e, hbk₃, hy₃, hdom₃, hf₃, hR₃, hc₃, hfree₃, hFd, hFb, hlines, -, hiso₃⟩ :=
    GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω K₂ J₂ y₂ B y₀ (fun s a => jA (o.Fl.b s a)) Li₀ _ _ M₀ j V₀ _ hBξ hSd hfree₂
      (fun p hp => by rw [hR₂]; exact hroot p hp) hspan hj hV hflag
  have hsm₂ : SmoothGenericFibreM y₂ :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω K₁ J₁ y₁ K₂ J₂ y₂ M₁.X B.X M₁.ξ B.ξ g M₁.all B.all M₁.tie B.tie hdom₂ hsm₁ hiso₂
  have hsm₃ : SmoothGenericFibreM y₃ :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω K₂ J₂ y₂ K₃ J₃ y₃ B.X 𝔐.X B.ξ 𝔐.ξ g' B.all 𝔐.all B.tie 𝔐.tie hdom₃ hsm₂
      (fun q hq => hiso₃ q hq (hvb q hq))
  have hg' : 𝔐.ξ ≫ g' = B.ξ := by
    have e : 𝔐.ξ ≫ g' = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ B.ξ := hdom₃
    rw [e]; simp
  refine ⟨Ω, inferInstance, inferInstance, K₃, inferInstance, J₃, inferInstance, y₃, fun k => bk₃ (bk₂ (bk₁ k)),
    fun k => (bx₁ k).trans ((bx₂ _).trans (bx₃ _)), i, 𝔐, g' ≫ g ≫ h₁, Fl, xdeg, e,
    hbk₃.comp (hbk₂.comp hbk₁), ?_, ?_, ?_, ?_, ?_, ?_, hlines, ?_, hsm₃, ?_⟩
  · intro k a
    simp only [Equiv.trans_apply]
    rw [hy₃, hy₂, hy₁]
  · show 𝔐.ξ ≫ g' ≫ g ≫ h₁ = _
    rw [← Category.assoc, hg']; exact hdomB
  · rw [hf₃, hf₂]; simp
  · rw [hc₃, hcst]
  · intro s a
    rw [hFb, hpt, spMap_dualMap_id, Category.id_comp]
  · rw [hFd, hdeg, _root_.mul_one]
  · intro p hp
    have := hfree₃ p hp
    exact this
  · intro p hp
    rw [hR₃, hR₂]

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGoodPrimesFiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_good_primes_finite : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → o.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i ∧ 𝔐.f = h ≫ o.𝔐.f ∧ 𝔐.cst = i.comp o.𝔐.cst ∧ (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) ∧ (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) ∧ Fl.RootLines xdeg e ∧ 𝔐.OmVB ∧ SmoothGenericFibreM y ∧ ∀ p ∈ S, 𝔐.R p = 4 :=
  @GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_cover
end
