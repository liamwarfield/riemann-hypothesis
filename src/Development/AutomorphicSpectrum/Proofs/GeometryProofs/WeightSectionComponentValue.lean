module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarInt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.AlgebraicApproximationValued
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.IsTanIff
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.TestMem

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.CommonZeroEvaluation.RegularChartNonzeroDenominator
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem ModelDimension.regular_chart_nonzero_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h), ∃ g₀ : C.R, g₀ ≠ 0 ∧ ∀ (A : Subring (Om C.Z)) (hA : ∀ r : C.R, (r : Om C.Z) ∈ A), (g₀ : Om C.Z)⁻¹ ∈ A → ∀ (L : Type) [Field L] (io : c.F →+* L) (ev : A →+* L), letI := io.toAlgebra; ∀ (ψ : C.R →ₐ[c.F] L), (∀ r : C.R, ψ r = ev ⟨r, hA r⟩) → ∀ (z y : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrBor t z y → FinTr.RegAt h C.Z io A ev y := by
  intro E _ _ _ H Dw l Xo c hL h C
  classical
  obtain ⟨q, φ₀, y₀, hy₀⟩ := hL.test _ (genFr h C.Z)
  choose a ha b hb hb0 hab using C.frac
  let x : Fin q.n ⊕ Ix Dw → Om C.Z := fun k => match k with
    | .inl i => φ₀ (Ideal.Quotient.mk q.I (MvPolynomial.X i))
    | .inr k => (((C.t k)⁻¹ : (Om C.Z)ˣ) : Om C.Z)
  let bb : Fin q.n ⊕ Ix Dw → C.R := fun k => ⟨b (x k), hb (x k)⟩
  have hbb : ∀ k, bb k ≠ 0 := fun k h0 => hb0 (x k) (congrArg Subtype.val h0)
  refine ⟨∏ k, bb k, Finset.prod_ne_zero_iff.2 fun k _ => hbb k, fun A hA hg L _ io ev => ?_⟩
  letI := io.toAlgebra
  intro ψ hψ z y t hz hb'
  have hx : ∀ k, x k ∈ A := fun k => by
    have e1 : ((∏ k, bb k : C.R) : Om C.Z) = b (x k) * ((∏ j ∈ Finset.univ.erase k, bb j : C.R) : Om C.Z) := by
      rw [← Finset.mul_prod_erase _ bb (Finset.mem_univ k)]; rfl
    have hne : ((∏ k, bb k : C.R) : Om C.Z) ≠ 0 := fun h0 =>
      Finset.prod_ne_zero_iff.2 (fun k _ => hbb k) (Subtype.ext h0)
    have e2 : x k = a (x k) * ((∏ j ∈ Finset.univ.erase k, bb j : C.R) : Om C.Z) *
        ((∏ k, bb k : C.R) : Om C.Z)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hne, e1, ← mul_assoc, hab]
    rw [e2]
    exact A.mul_mem (A.mul_mem (hA ⟨_, ha _⟩) (hA _)) hg
  have hc : ∀ a : c.F, algebraMap c.F (Om C.Z) a ∈ A := fun a => hA (algebraMap c.F C.R a)
  have hev : ∀ (a : c.F) (h : algebraMap c.F (Om C.Z) a ∈ A), ev ⟨_, h⟩ = io a := fun a h => by
    have := hψ (algebraMap c.F C.R a)
    rw [ψ.commutes] at this
    exact this.symm
  have hφ : ∀ r, φ₀ r ∈ A := ModelDimension.Spread.test_mem q φ₀ A hc (fun i => hx (.inl i))
  let ψq := ModelDimension.Spread.evAlg φ₀ A hφ ev hev
  obtain ⟨zq, hzq⟩ := hL.bc _ _ ψq y₀
  obtain ⟨t', ht'⟩ := ModelDimension.Spread.spec_bor φ₀ C.R.val hy₀ C.gen C.bor A hφ hA (fun k => hx (.inr k)) ev ψq ψ
    (fun _ => rfl) hψ hzq hz
  exact ⟨fun a => ⟨hc a, hev a _⟩, q, φ₀, ψq, y₀, zq, _, hy₀, hzq, fun r => ⟨hφ r, rfl⟩,
    (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c L).2.1 _ _ _ _ _ ht' hb'⟩
end

section -- merged from Development.WeilBound.CoreStatements.CommonZeroEvaluation.IntegralFrameOverCdvr
section -- merged from Development.WeilBound.CoreStatements.CommonZeroEvaluation.DualMapRComp
noncomputable section

namespace ModelDimension.Near

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem chart_inj {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {B : Type} [CommRing B] {f g : Γ(X, U) →+* B}
    (h : spMap f ≫ hU.fromSpec = spMap g ≫ hU.fromSpec) : f = g :=
  spMap_inj ((cancel_mono hU.fromSpec).1 h)

theorem dualMapR_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMapR (g.comp f) = (dualMapR g).comp (dualMapR f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMapR]

theorem exists_spread {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {S K : Type} [CommRing S] [Field K]
    (x : Sp S ⟶ X) (ψ : S →+* K) (f : Γ(X, U) →+* K) (hf : spMap ψ ≫ x = spMap f ≫ hU.fromSpec) :
    ∃ h : S, ψ h ≠ 0 ∧ ∃ fh : Γ(X, U) →+* Localization.Away h,
      spMap (algebraMap S (Localization.Away h)) ≫ x = spMap fh ≫ hU.fromSpec := by
  let p : PrimeSpectrum S := PrimeSpectrum.comap ψ (IsLocalRing.closedPoint K)
  let W : TopologicalSpace.Opens (PrimeSpectrum S) := x ⁻¹ᵁ U
  have hp : p ∈ (W : Set (PrimeSpectrum S)) := by
    have e : x p = hU.fromSpec (spMap f (IsLocalRing.closedPoint K)) := by
      have := congrArg (fun q : Sp K ⟶ X => q (IsLocalRing.closedPoint K)) hf
      exact this
    show x p ∈ (U : Set X)
    rw [e, ← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨_, ⟨h, rfl⟩, h1, h2⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp
    W.isOpen
  refine ⟨h, fun h0 => h1 ?_, ?_⟩
  · show ψ h ∈ (IsLocalRing.closedPoint K).asIdeal
    rw [h0]
    exact zero_mem _
  have hr : Set.range (spMap (algebraMap S (Localization.Away h)) ≫ x) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨q, rfl⟩
    refine h2 (a := PrimeSpectrum.comap (algebraMap S (Localization.Away h)) q) fun hq => ?_
    exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hq (IsLocalization.Away.algebraMap_isUnit h))
  let g := IsOpenImmersion.lift hU.fromSpec _ hr
  have hg : g ≫ hU.fromSpec = _ := IsOpenImmersion.lift_fac _ _ _
  have e : spMap (Spec.preimage g).hom = g := Spec.map_preimage g
  exact ⟨(Spec.preimage g).hom, by rw [e]; exact hg.symm⟩

theorem fin_gen {O A : Type} [CommRing O] [CommRing A] {α : O →+* A} (h : α.FiniteType) :
    ∃ s : Finset A, ∀ Q : Subring A, (∀ o, α o ∈ Q) → (∀ a ∈ s, a ∈ Q) → ∀ a, a ∈ Q := by
  letI := α.toAlgebra
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := O) (A := A) (self := h)
  refine ⟨s, fun Q h1 h2 a => ?_⟩
  have ha : a ∈ Algebra.adjoin O (s : Set A) := hs ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact h2 a ha
  | algebraMap o => exact h1 o
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

end ModelDimension.Near
end
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

open AlgebraicGeometry CategoryTheory ModelDimension.Near

set_option maxHeartbeats 1000000 in
theorem ModelDimension.integral_frame_over_cdvr : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → T.FinRes → ∀ y : IntFr Xo c T io, letI := io.toAlgebra; ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ : S →ₐ[c.F] T.Fr) (z₀ : FrPt Xo c T.Fr) (t₀ : Ix Dw → T.Frˣ), FrMap ψ w z₀ → FrBor t₀ z₀ y.1 → ∃ (F : Finset S) (n : ℕ), ∀ ψ' : S →ₐ[c.F] T.Fr, (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) → ∀ z' : FrPt Xo c T.Fr, FrMap ψ' w z' → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ letI := io'.toAlgebra; ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z'' : FrPt Xo c T'.Fr) (t' : Ix Dw → T'.Frˣ), FrMap φ z' z'' ∧ FrBor t' z'' y'.1 ∧ (∀ x : T.Fr, x ≠ 0 → vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), vV T'.V ((t' (some ⟨τ, i⟩) : T'.Frˣ) : T'.Fr) * (e₀ : ℤ) = (e' : ℤ) * vV T.V ((t₀ (some ⟨τ, i⟩) : T.Frˣ) : T.Fr) := by
  intro hG E _ _ _ H Dw l Xo c hI Y la T io e₀ ho hfin y
  letI := io.toAlgebra
  intro S _ _ w ψ z₀ t₀ hz₀ hb₀
  classical
  have hExt : GlobalTheory.Published.SemiAbelianHomExtension := hG.2.2.1
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨b, hb⟩ := GlobalTheory.Reg.GenInt.exists_factor (algebraMap T.V T.Fr) hinj (io.comp (algebraMap (𝓞 c.F) c.F))
    (fun o => GlobalTheory.Reg.GenInt.int_mem_range io o)
  obtain ⟨yt, -, hyt⟩ := valCrit_proj Y.s Y.proj T.V T.Fr b (Small.ptY Y y.1) (by
    rw [Small.ptY_over, ← Tor.spMap_comp, hb])
  have := Y.t.semi.smooth
  have := projProper _ _ _ Y.proj
  obtain ⟨U, hU, hxU, -, n, v₀, hC⟩ :=
    GlobalTheory.exists_affine_lieBasis_baseChange Y.X Y.t.G (yt (IsLocalRing.closedPoint T.V)) ⊤ trivial
  replace hC : IsChart Y hU v₀ := hC
  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.ModelPoints.existsUnique_chartHom hU T.V yt hxU
  obtain ⟨α, hα, hαf⟩ := GlobalTheory.ModelPoints.exists_chart_finiteType Y.s hU
  obtain ⟨gens, hgens⟩ := fin_gen hαf
  have hy : Small.ptY Y y.1 = Tor.spMap ((algebraMap T.V T.Fr).comp f₀) ≫ hU.fromSpec := by
    rw [← hyt, ← hf₀, Tor.spMap_comp f₀, Category.assoc]
  have hz₀Y : Small.ptY Y z₀ = Tor.spMap ((algebraMap T.V T.Fr).comp f₀) ≫ hU.fromSpec :=
    (ptY_bor Y hb₀).symm.trans hy
  obtain ⟨h, hh, fh, hfh⟩ := exists_spread hU (Small.ptY Y w) ψ.toRingHom _
    ((Small.ptY_map Y hz₀).symm.trans hz₀Y)
  have hg : ∀ τ i, ∃ cv, Crd Y hU v₀ fh cv
      (Tor.spMap (Chart.dualMapR (algebraMap S (Localization.Away h))) ≫ Small.tanY Y w τ i) := fun τ i =>
    (hC.isBas fh).exists (hfh ▸ gt_bc _ (tanY_gt Y w τ i))
  choose cv hcv using hg
  let g : ∀ τ : E →+* ℂ, Matrix (Fin n) (Fin (Dw.mult τ)) (Localization.Away h) :=
    fun τ => Matrix.of fun j i => cv τ i j
  have key : ∀ (ψ' : S →ₐ[c.F] T.Fr) (z' : FrPt Xo c T.Fr), FrMap ψ' w z' → ∀ χ : Localization.Away h →+* T.Fr,
      χ.comp (algebraMap S _) = ψ'.toRingHom → Small.ptY Y z' = Tor.spMap (χ.comp fh) ≫ hU.fromSpec ∧
        ∀ τ i, Crd Y hU v₀ (χ.comp fh) (fun j => ((g τ).map χ) j i) (Small.tanY Y z' τ i) := by
    intro ψ' z' hz' χ hχ
    refine ⟨?_, fun τ i => ?_⟩
    · rw [Small.ptY_map Y hz', ← hχ, Tor.spMap_comp _ χ, Tor.spMap_comp fh χ, Category.assoc, Category.assoc, hfh]
    · have h1 := (hcv τ i).bc χ
      rw [← Category.assoc, ← Tor.spMap_comp, ← dualMapR_comp, hχ] at h1
      rw [Small.tanY_map Y hz']
      exact h1
  let χ₀ : Localization.Away h →+* T.Fr := IsLocalization.Away.lift h (Ne.isUnit hh)
  have hχ₀ : χ₀.comp (algebraMap S _) = ψ.toRingHom := IsLocalization.Away.lift_comp h _
  obtain ⟨k1, k2⟩ := key ψ z₀ hz₀ χ₀ hχ₀
  have hf : χ₀.comp fh = (algebraMap T.V T.Fr).comp f₀ := chart_inj hU (k1.symm.trans hz₀Y)
  choose C hC1 hC2 hC3 using fun τ => hC.crd_bor hb₀ τ
  choose u hu1 hu2 using fun τ => hC.integral hExt y f₀ hy τ
  have e0 : ∀ τ, (g τ).map χ₀ * C τ = (u τ).map (algebraMap T.V T.Fr) := fun τ =>
    hC3 τ _ k1 _ _ (k2 τ) (by rw [hf]; exact hu2 τ)
  have ev1 : ∀ᶠ ψ' in closeF T.V ψ.toRingHom, ∀ s ∈ gens, ModelDimension.Near.ext h χ₀ ψ' (fh s) ∈ (algebraMap T.V T.Fr).range := by
    rw [Filter.eventually_all_finset]
    intro s _
    have h1 := tend_ext (V := T.V) hh hχ₀ (fh s)
    rw [show χ₀ (fh s) = algebraMap T.V T.Fr (f₀ s) from RingHom.congr_fun hf s] at h1
    filter_upwards [h1.cong] with ψ' ⟨b', h2, _⟩
    exact ⟨b', h2⟩
  have ev2 : ∀ᶠ ψ' in closeF T.V ψ.toRingHom, ∀ τ j i, ∃ b' : T.V,
      algebraMap T.V T.Fr b' = ((g τ).map (ModelDimension.Near.ext h χ₀ ψ') * C τ) j i ∧
        b' - u τ j i ∈ IsLocalRing.maximalIdeal T.V := by
    simp only [Filter.eventually_all]
    intro τ j i
    have h1 := Tend.sum Finset.univ fun k => (tend_ext (V := T.V) hh hχ₀ (g τ j k)).mul_const (C τ k i)
    rw [show ∑ k, χ₀ (g τ j k) * C τ k i = algebraMap T.V T.Fr (u τ j i) from congrFun (congrFun (e0 τ) j) i] at h1
    exact h1.cong
  obtain ⟨F, N, hFN⟩ : ∃ (F : Finset S) (N : ℕ), ∀ ψ' : S →+* T.Fr,
      (∀ s ∈ F, ψ' s = ψ.toRingHom s ∨ (N : ℤ) ≤ vV T.V (ψ' s - ψ.toRingHom s)) → _ :=
    (eventually_ne (V := T.V) hh).and (ev1.and ev2)
  refine ⟨F, N, fun ψ' hψ' z' hz' => ?_⟩
  obtain ⟨q1, q2, q3⟩ := hFN ψ'.toRingHom hψ'
  generalize hχ : ModelDimension.Near.ext h χ₀ ψ'.toRingHom = χ at q2 q3
  have hχ' : χ.comp (algebraMap S _) = ψ'.toRingHom := hχ ▸ ext_comp χ₀ q1
  obtain ⟨k3, k4⟩ := key ψ' z' hz' χ hχ'
  have hα' : (χ.comp fh).comp α = (algebraMap T.V T.Fr).comp b := by
    apply spMap_inj
    rw [Tor.spMap_comp, ← hα, ← Category.assoc, ← k3, Small.ptY_over, hb]
  obtain ⟨f', hf'⟩ := GlobalTheory.Reg.GenInt.exists_factor (algebraMap T.V T.Fr) hinj (χ.comp fh)
    (hgens ((algebraMap T.V T.Fr).range.comap (χ.comp fh)) (fun o => ⟨b o, (RingHom.congr_fun hα' o).symm⟩) q2)
  choose W hW1 hW2 using q3
  obtain ⟨T', io', e', y', ho', halg, hrest⟩ := hI la T io e₀ ho hfin z'
  refine ⟨T', io', e', y', ho', halg, ?_⟩
  letI := io'.toAlgebra
  obtain ⟨φ, z'', t', hφ, hz'', hb''⟩ := hrest
  obtain ⟨r, -, her, hr, -⟩ := GlobalTheory.IntegralFrameCheck.nval_map_of_overLa ho ho' φ.toRingHom (fun a => φ.commutes a) hφ
  have hval : ∀ x : T.Fr, vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x := fun x => by
    rw [show vV T'.V (φ x) = _ from hr x, her]
    push_cast
    ring
  refine ⟨φ, z'', t', hz'', hb'', fun x _ => hval x, fun τ i => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.Reg.GenInt.exists_factor (algebraMap T'.V T'.Fr) (IsFractionRing.injective _ _)
    (φ.toRingHom.comp (algebraMap T.V T.Fr)) hφ
  have hF : φ.toRingHom.comp (χ.comp fh) = (algebraMap T'.V T'.Fr).comp (φ₀.comp f') := by
    rw [← hf', ← RingHom.comp_assoc, ← hφ₀, RingHom.comp_assoc]
  have k5 : Small.ptY Y z'' = Tor.spMap (φ.toRingHom.comp (χ.comp fh)) ≫ hU.fromSpec := by
    rw [Small.ptY_map Y hz'', k3, Tor.spMap_comp (χ.comp fh), Category.assoc]
  obtain ⟨C', hC1', hC2', hC3'⟩ := hC.crd_bor hb'' τ
  obtain ⟨u', hu1', hu2'⟩ := hC.integral hExt y' (φ₀.comp f') (by rw [ptY_bor Y hb'', k5, hF]) τ
  have e1 : ((g τ).map χ).map φ.toRingHom * C' = u'.map (algebraMap T'.V T'.Fr) :=
    hC3' _ k5 _ _ (fun i => by rw [Small.tanY_map Y hz'']; exact (k4 τ i).bc φ.toRingHom) (by rw [hF]; exact hu2')
  obtain ⟨B, hB⟩ := exists_left_inv (u' := Matrix.of (W τ)) (hu1 τ) (hW2 τ)
  have e2 : ((g τ).map χ).map φ.toRingHom * (C τ).map φ.toRingHom =
      ((Matrix.of (W τ)).map φ₀).map (algebraMap T'.V T'.Fr) := by
    rw [← Matrix.map_mul]
    ext j k
    rw [Matrix.map_apply, ← hW1]
    exact (RingHom.congr_fun hφ₀ _).symm
  have hB' : B.map φ₀ * (Matrix.of (W τ)).map φ₀ = 1 := by
    rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero _) (map_one _)]
  have e3 := vV_diag_eq (C := (C τ).map φ.toRingHom)
    (fun j k hjk => by rw [Matrix.map_apply, hC1 τ hjk, map_zero]) hC1'
    (fun j => by rw [Matrix.map_apply, hC2]; exact (map_ne_zero _).2 (Units.ne_zero _))
    (fun j => by rw [hC2']; exact Units.ne_zero _) hB' hu1' e2 e1 i
  rw [hC2', Matrix.map_apply, hC2] at e3
  rw [e3]
  exact hval _
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChartNonzeroDenominator
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChartNonzeroDenominator
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.CompanionTheory.Relay.frame_chart_nonzero_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h), ∃ g₀ : C.R, g₀ ≠ 0 ∧ ∀ (A : Subring (Om C.Z)) (hA : ∀ r : C.R, (r : Om C.Z) ∈ A), (g₀ : Om C.Z)⁻¹ ∈ A → ∀ (L : Type) [Field L] (io : c.F →+* L) (ev : A →+* L), letI := io.toAlgebra; ∀ (ψ : C.R →ₐ[c.F] L), (∀ r : C.R, ψ r = ev ⟨r, hA r⟩) → ∀ (z y : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrBor t z y → FinTr.RegAt h C.Z io A ev y := by
  first | exact @ModelDimension.regular_chart_nonzero_denominator | exact ModelDimension.regular_chart_nonzero_denominator
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChartNonzeroDenominatorStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem _root_.GlobalTheory.T.frame_chart_nonzero_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (h : GenFrEx Xo c) (C : GlobalTheory.Reg.FChart h), ∃ g₀ : C.R, g₀ ≠ 0 ∧ ∀ (A : Subring (Om C.Z)) (hA : ∀ r : C.R, (r : Om C.Z) ∈ A), (g₀ : Om C.Z)⁻¹ ∈ A → ∀ (L : Type) [Field L] (io : c.F →+* L) (ev : A →+* L), letI := io.toAlgebra; ∀ (ψ : C.R →ₐ[c.F] L), (∀ r : C.R, ψ r = ev ⟨r, hA r⟩) → ∀ (z y : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ C.y z → FrBor t z y → FinTr.RegAt h C.Z io A ev y := by
  first | exact @GlobalTheory.CompanionTheory.Relay.frame_chart_nonzero_denominator | exact GlobalTheory.CompanionTheory.Relay.frame_chart_nonzero_denominator | (intros; apply GlobalTheory.CompanionTheory.Relay.frame_chart_nonzero_denominator <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameSubalgebraRelay
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameSubalgebraRelay
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → T.FinRes → ∀ y : IntFr Xo c T io, letI := io.toAlgebra; ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ : S →ₐ[c.F] T.Fr) (z₀ : FrPt Xo c T.Fr) (t₀ : Ix Dw → T.Frˣ), FrMap ψ w z₀ → FrBor t₀ z₀ y.1 → ∃ (F : Finset S) (n : ℕ), ∀ ψ' : S →ₐ[c.F] T.Fr, (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) → ∀ z' : FrPt Xo c T.Fr, FrMap ψ' w z' → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ letI := io'.toAlgebra; ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z'' : FrPt Xo c T'.Fr) (t' : Ix Dw → T'.Frˣ), FrMap φ z' z'' ∧ FrBor t' z'' y'.1 ∧ (∀ x : T.Fr, x ≠ 0 → vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), vV T'.V ((t' (some ⟨τ, i⟩) : T'.Frˣ) : T'.Fr) * (e₀ : ℤ) = (e' : ℤ) * vV T.V ((t₀ (some ⟨τ, i⟩) : T.Frˣ) : T.Fr) := by
  first | exact @ModelDimension.integral_frame_over_cdvr | exact ModelDimension.integral_frame_over_cdvr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameSubalgebraRelayStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_subalgebra_relay : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → T.FinRes → ∀ y : IntFr Xo c T io, letI := io.toAlgebra; ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ : S →ₐ[c.F] T.Fr) (z₀ : FrPt Xo c T.Fr) (t₀ : Ix Dw → T.Frˣ), FrMap ψ w z₀ → FrBor t₀ z₀ y.1 → ∃ (F : Finset S) (n : ℕ), ∀ ψ' : S →ₐ[c.F] T.Fr, (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) → ∀ z' : FrPt Xo c T.Fr, FrMap ψ' w z' → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ letI := io'.toAlgebra; ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z'' : FrPt Xo c T'.Fr) (t' : Ix Dw → T'.Frˣ), FrMap φ z' z'' ∧ FrBor t' z'' y'.1 ∧ (∀ x : T.Fr, x ≠ 0 → vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), vV T'.V ((t' (some ⟨τ, i⟩) : T'.Frˣ) : T'.Fr) * (e₀ : ℤ) = (e' : ℤ) * vV T.V ((t₀ (some ⟨τ, i⟩) : T.Frˣ) : T.Fr) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay | exact GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicApproximationCompleteDvr
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicApproximationCompleteDvr
open Formalism.L2.Pj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  first | exact @ModelDimension.algebraic_approximation_valued | exact ModelDimension.algebraic_approximation_valued
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicApproximationCompleteDvrStatement
open Formalism.L2.Pj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_approximation_complete_dvr : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra F R] [Algebra.Smooth F R] (T : CDVR), T.FinRes → ∀ (io : F →+* T.Fr) (ψ : R →+* T.Fr), ψ.comp (algebraMap F R) = io → ∀ (S : Finset R) (n : ℕ) (g : R), g ≠ 0 → ∃ ψ' : R →+* T.Fr, ψ'.comp (algebraMap F R) = io ∧ (∀ x, IsAlgebraic ℤ (ψ' x)) ∧ (∀ s ∈ S, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) ∧ ψ' g ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr | exact GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr | (intros; apply GlobalTheory.CompanionTheory.Relay.algebraic_approximation_complete_dvr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightSectionComponentValue
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx

section Help

theorem exists_loc {R K L : Type} [CommRing R] [IsDomain R] [Field K] [Field L] (i : R →+* K)
    (hi : Function.Injective i) (g : R) (hg : g ≠ 0) (χ : R →+* L) (hχ : χ g ≠ 0) :
    ∃ (A : Subring K) (ev : A →+* L) (hA : ∀ r, i r ∈ A), (i g)⁻¹ ∈ A ∧ (∀ r, ev ⟨i r, hA r⟩ = χ r) ∧
      ∀ x : A, ∃ (a : R) (k : ℕ), ev x * χ g ^ k = χ a := by
  have hig : i g ≠ 0 := (map_ne_zero_iff i hi).2 hg
  let large₂ := Localization.Away g
  let Φ : large₂ →+* K := IsLocalization.Away.lift g (isUnit_iff_ne_zero.2 hig)
  let Ψ : large₂ →+* L := IsLocalization.Away.lift g (isUnit_iff_ne_zero.2 hχ)
  have hΦ : ∀ r, Φ (algebraMap R large₂ r) = i r := fun r => IsLocalization.Away.lift_eq g _ r
  have hΨ : ∀ r, Ψ (algebraMap R large₂ r) = χ r := fun r => IsLocalization.Away.lift_eq g _ r
  have hsurj : ∀ x : large₂, ∃ (a : R) (k : ℕ), x * algebraMap R large₂ g ^ k = algebraMap R large₂ a := by
    intro x
    obtain ⟨⟨a, ⟨s, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) x
    exact ⟨a, k, by simpa using h⟩
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, k, h⟩ := hsurj x
    have h1 := congrArg Φ h
    rw [map_mul, hx, zero_mul, hΦ] at h1
    have ha : a = 0 := hi (by rw [← h1, map_zero])
    have hu : IsUnit (algebraMap R large₂ g ^ k) := (IsLocalization.Away.algebraMap_isUnit g).pow k
    rw [ha, map_zero] at h
    exact (hu.mul_left_eq_zero).1 h
  let e : large₂ ≃+* Φ.range := RingEquiv.ofBijective Φ.rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), Φ.rangeRestrict_surjective⟩
  have hA : ∀ r, i r ∈ Φ.range := fun r => ⟨algebraMap R large₂ r, hΦ r⟩
  have hev : ∀ x : large₂, (Ψ.comp e.symm.toRingHom) (e x) = Ψ x := fun x => by
    simp
  have hev' : ∀ r, (Ψ.comp e.symm.toRingHom) ⟨i r, hA r⟩ = χ r := fun r => by
    have : (⟨i r, hA r⟩ : Φ.range) = e (algebraMap R large₂ r) := Subtype.ext (hΦ r).symm
    rw [this, hev, hΨ]
  refine ⟨Φ.range, Ψ.comp e.symm.toRingHom, hA, ?_, hev', fun x => ?_⟩
  · obtain ⟨v, hv⟩ := IsLocalization.Away.algebraMap_isUnit (x := g) (S := large₂) |>.exists_right_inv
    refine ⟨v, ?_⟩
    have := congrArg Φ hv
    rw [map_mul, hΦ, map_one] at this
    exact eq_inv_of_mul_eq_one_right this
  · obtain ⟨a, k, h⟩ := hsurj (e.symm x)
    refine ⟨a, k, ?_⟩
    have := congrArg Ψ h
    rw [map_mul, map_pow, hΨ, hΨ] at this
    exact this

theorem inv_mem_of_mul {K : Type} [Field K] {A : Subring K} {a b g : K} (ha : a ≠ 0) (hb : b ∈ A) (hg : g⁻¹ ∈ A)
    (hne : g ≠ 0) (h : a * b = g) : a⁻¹ ∈ A := by
  have : a⁻¹ = b * g⁻¹ := by
    rw [← h]
    have hb0 : b ≠ 0 := fun h0 => hne (by rw [← h, h0, mul_zero])
    field_simp
  rw [this]
  exact A.mul_mem hb hg

theorem vV_units_prod {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {I : Type} (s : Finset I) (t : I → Kˣ) (e : I → ℤ) :
    vV V (((∏ i ∈ s, t i ^ e i : Kˣ)) : K) = ∑ i ∈ s, e i * vV V ((t i : Kˣ) : K) := by
  classical
  have hz : ∀ (u : Kˣ) (m : ℤ), vV V (((u ^ m : Kˣ)) : K) = m * vV V (u : K) := by
    intro u m
    simp only [vV]
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow]
    ring_nf
  induction s using Finset.induction_on with
  | empty =>
    have : vV V (1 : K) = 0 := by simp [vV]
    simpa using this
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Units.val_mul,
      vV_mul (Units.ne_zero _) (Units.ne_zero _), hz, ih]

theorem vV_eq_of_close {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {a a' : K} (ha : a ≠ 0) (h : a' = a ∨ vV V a < vV V (a' - a)) : a' ≠ 0 ∧ vV V a' = vV V a := by
  by_cases he : a' = a
  · subst he
    exact ⟨ha, rfl⟩
  have h : vV V a < vV V (a' - a) := h.resolve_left he
  have hneg : ∀ x : K, vV V (-x) = vV V x := fun x => by simp [vV]
  have hd : a' - a ≠ 0 := sub_ne_zero.2 he
  have h0 : a' ≠ 0 := by
    intro h0
    rw [h0, zero_sub, hneg] at h
    exact lt_irrefl _ h
  refine ⟨h0, ?_⟩
  have h1 := min_le_vV_add (V := V) ha hd (by rwa [add_sub_cancel])
  have h2 := min_le_vV_add (V := V) h0 (neg_ne_zero.2 hd) (by rwa [← sub_eq_add_neg, sub_sub_cancel])
  rw [add_sub_cancel] at h1
  rw [← sub_eq_add_neg, sub_sub_cancel, hneg] at h2
  rcases min_le_iff.1 h1 with h1 | h1 <;> rcases min_le_iff.1 h2 with h2 | h2 <;> omega

theorem nval_transfer {T T' : CDVR} {e₀ e' : ℕ} (he₀ : 0 < e₀) (he' : 0 < e') {I : Type} [Fintype I] (ex : I → ℤ)
    (t₀ : I → T.Frˣ) (t' : I → T'.Frˣ)
    (hvt : ∀ i, ex i ≠ 0 → vV T'.V ((t' i : T'.Frˣ) : T'.Fr) * (e₀ : ℤ) = (e' : ℤ) * vV T.V ((t₀ i : T.Frˣ) : T.Fr))
    {a a' : T.Fr} (φ : T.Fr →+* T'.Fr) (hφ : ∀ x : T.Fr, x ≠ 0 → vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x)
    (ha : a ≠ 0) (hclose : a' = a ∨ vV T.V a < vV T.V (a' - a)) :
    nval T'.V e' (((∏ i, t' i ^ ex i : T'.Frˣ) : T'.Fr) * φ a') = nval T.V e₀ (((∏ i, t₀ i ^ ex i : T.Frˣ) : T.Fr) * a) := by
  obtain ⟨ha'0, hva⟩ := vV_eq_of_close ha hclose
  have hsum : (e₀ : ℤ) * vV T'.V (((∏ i, t' i ^ ex i : T'.Frˣ)) : T'.Fr) =
      (e' : ℤ) * vV T.V (((∏ i, t₀ i ^ ex i : T.Frˣ)) : T.Fr) := by
    rw [vV_units_prod, vV_units_prod, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : ex i = 0
    · rw [h0]; simp
    · have := hvt i h0
      linear_combination (ex i) * this
  have hW' := Units.ne_zero (∏ i, t' i ^ ex i : T'.Frˣ)
  have hW := Units.ne_zero (∏ i, t₀ i ^ ex i : T.Frˣ)
  have hφa : φ a' ≠ 0 := (map_ne_zero φ).2 ha'0
  have key : vV T'.V (((∏ i, t' i ^ ex i : T'.Frˣ) : T'.Fr) * φ a') * (e₀ : ℤ) =
      (e' : ℤ) * vV T.V (((∏ i, t₀ i ^ ex i : T.Frˣ) : T.Fr) * a) := by
    rw [vV_mul hW' hφa, vV_mul hW ha, ← hva]
    have := hφ _ ha'0
    linear_combination hsum + this
  rw [nval_of_ne (mul_ne_zero hW' hφa), nval_of_ne (mul_ne_zero hW ha)]
  have he'' : (0 : ℝ) < e' := by exact_mod_cast he'
  have he₀' : (0 : ℝ) < e₀ := by exact_mod_cast he₀
  have keyR : (vV T'.V (((∏ i, t' i ^ ex i : T'.Frˣ) : T'.Fr) * φ a') : ℝ) * e₀ =
      e' * (vV T.V (((∏ i, t₀ i ^ ex i : T.Frˣ) : T.Fr) * a) : ℝ) := by exact_mod_cast key
  congr 1
  rw [div_eq_div_iff he''.ne' he₀'.ne']
  linarith

theorem close_of_le {T : CDVR} {a a' : T.Fr} {n' : ℕ} (hn : (vV T.V a + 1).toNat ≤ n')
    (h : a' = a ∨ (n' : ℤ) ≤ vV T.V (a' - a)) : a' = a ∨ vV T.V a < vV T.V (a' - a) := by
  rcases h with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    have h3 : vV T.V a + 1 ≤ ((vV T.V a + 1).toNat : ℤ) := Int.self_le_toNat _
    have h4 : (((vV T.V a + 1).toNat : ℕ) : ℤ) ≤ (n' : ℤ) := by exact_mod_cast hn
    omega

theorem alg_map {K L : Type} [Field K] [Field L] [iK : Algebra ℤ K] [iL : Algebra ℤ L] (f : K →+* L) {x : K}
    (h : IsAlgebraic ℤ x) : IsAlgebraic ℤ (f x) := by
  obtain rfl : iK = Ring.toIntAlgebra K := Subsingleton.elim _ _
  obtain rfl : iL = Ring.toIntAlgebra L := Subsingleton.elim _ _
  exact h.algHom f.toIntAlgHom

theorem alg_of_loc {L : Type} [Field L] [Algebra ℤ L] {x a g : L} {k : ℕ} (ha : IsAlgebraic ℤ a) (hg : IsAlgebraic ℤ g) (hg0 : g ≠ 0)
    (hx : x * g ^ k = a) : IsAlgebraic ℤ x := by
  have e1 : x = a * (g ^ k)⁻¹ := by
    rw [← hx]
    field_simp
  rw [e1]
  exact ha.mul (hg.pow k).inv

end Help


set_option maxHeartbeats 2000000 in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem approx_main : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0) → ∀ (B' : Finset (Om Z)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Xo c T io, y.IsAlg → (letI := io.toAlgebra; GlobalTheory.AllWt.LiesOn Z y.1) → evI y f ≠ 0 → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io') (A : Subring (Om Z)) (ev : A →+* T'.Fr), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ nval T'.V e' (evI y' f) = nval T.V e₀ (evI y f) ∧ (↑B' : Set (Om Z)) ⊆ A ∧ (∀ b ∈ B', b ≠ 0 → b⁻¹ ∈ A) ∧ (∀ x, IsAlgebraic ℤ (ev x)) ∧ FinTr.RegAt h Z io' A ev y'.1 := by
  intro hG E _ _ _ H Dw l Xo c r U h e hCL Y Z u f hf B' la T io e₀ ho y hy hLies hne
  letI := io.toAlgebra
  classical
  obtain ⟨hL, -, -, hAt⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨C, ψ, z₀, t₀, hm, hb⟩ := hAt h T.Fr y.1
  have hZ : C.Z = Z := by
    have s₀ : Sp T.Fr := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)
    exact comp_eq_of_mem (hLies s₀) (liesOn_chart C hm hb s₀)
  subst hZ
  haveI := C.sm
  obtain ⟨g₀, hg₀, hReg⟩ := GlobalTheory.T.frame_chart_nonzero_denominator E H Dw l Xo c hL h C
  obtain ⟨F, n, hNear⟩ := GlobalTheory.T.integral_frame_subalgebra_relay hG E H Dw l Xo c hCL.intAll Y la T io e₀ ho hy y C.R C.y ψ z₀ t₀ hm hb
  let fS : C.R := evR Xo c f C.y
  have hz₀ : evR Xo c f z₀ = ψ fS := GlobalTheory.Reg.PChartModel.evR_map hL hf.1 ψ hm
  have hy₀ : evI y f = ((∏ i, t₀ i ^ GlobalTheory.AllWt.exOf Dw u 0 i : T.Frˣ) : T.Fr) * ψ fS := by
    rw [← hz₀]
    exact GlobalTheory.FlagTan.evR_frBor hf hb
  have hψf : ψ fS ≠ 0 := fun h0 => hne (by rw [hy₀, h0, mul_zero])
  choose na hna de hde hde0 hfr using C.frac
  let deR : Om C.Z → C.R := fun b => ⟨de b, hde b⟩
  let naR : Om C.Z → C.R := fun b => ⟨na b, hna b⟩
  let g₁ : C.R := ∏ b ∈ B', deR b
  let g₂ : C.R := ∏ b ∈ B'.filter (· ≠ 0), naR b
  let g : C.R := g₀ * g₁ * g₂
  have hde0' : ∀ b, deR b ≠ 0 := fun b hb0 => hde0 b (congrArg Subtype.val hb0)
  have hna0' : ∀ b, b ≠ 0 → naR b ≠ 0 := fun b hb0 h0 => by
    have h1 : na b = 0 := congrArg Subtype.val h0
    have := hfr b
    rw [h1] at this
    exact (mul_ne_zero hb0 (hde0 b)) this
  have hg₁ : g₁ ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hde0' b
  have hg₂ : g₂ ≠ 0 := Finset.prod_ne_zero_iff.2 fun b hb => hna0' b (Finset.mem_filter.1 hb).2
  have hg : g ≠ 0 := mul_ne_zero (mul_ne_zero hg₀ hg₁) hg₂
  let n' : ℕ := max n (vV T.V (ψ fS) + 1).toNat
  obtain ⟨ψ₁, hψ₁c, hψ₁a, hψ₁n, hψ₁g⟩ := GlobalTheory.T.algebraic_approximation_complete_dvr c.F C.R T hy io ψ.toRingHom
    (RingHom.ext fun a => ψ.commutes a) (insert fS F) n' g hg
  let ψ' : C.R →ₐ[c.F] T.Fr := { ψ₁ with commutes' := fun a => RingHom.congr_fun hψ₁c a }
  have hψ' : ∀ x, ψ' x = ψ₁ x := fun _ => rfl
  obtain ⟨z', hz'⟩ := hL.bc _ _ ψ' C.y
  obtain ⟨T', io', e', y', ho', hy', hrest⟩ := hNear ψ' (fun s hs => by
    rcases hψ₁n s (Finset.mem_insert_of_mem hs) with h1 | h1
    · exact Or.inl h1
    · refine Or.inr (le_trans ?_ h1)
      exact_mod_cast le_max_left _ _) z' hz'
  letI := io'.toAlgebra
  obtain ⟨φ, z'', t', hφ, hb', hvφ, hvt⟩ := hrest
  let χ : C.R →+* T'.Fr := φ.toRingHom.comp ψ₁
  have hχg : χ g ≠ 0 := (map_ne_zero φ.toRingHom).2 hψ₁g
  obtain ⟨A, ev, hA, hgA, hevχ, hevx⟩ := exists_loc C.R.val.toRingHom Subtype.val_injective g hg χ hχg
  have hAr : ∀ r : C.R, (r : Om C.Z) ∈ A := hA
  have hgne : ((g : C.R) : Om C.Z) ≠ 0 := fun h0 => hg (Subtype.ext h0)
  have hgA' : ((g : C.R) : Om C.Z)⁻¹ ∈ A := hgA
  have hdvd : ∀ a b : C.R, a ≠ 0 → a * b = g → (a : Om C.Z)⁻¹ ∈ A := fun a b ha hab =>
    inv_mem_of_mul (fun h0 => ha (Subtype.ext h0)) (hAr b) hgA' hgne (congrArg Subtype.val hab)
  have hdeA : ∀ b ∈ B', (de b)⁻¹ ∈ A := fun b hb0 => by
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem deR hb0
    exact hdvd (deR b) (g₀ * w * g₂) (hde0' b) (by
      show deR b * (g₀ * w * g₂) = g₀ * g₁ * g₂
      rw [show g₁ = deR b * w from hw]; ring)
  have hnaA : ∀ b ∈ B', b ≠ 0 → (na b)⁻¹ ∈ A := fun b hb0 hb1 => by
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem naR (show b ∈ B'.filter (· ≠ 0) from Finset.mem_filter.2 ⟨hb0, hb1⟩)
    exact hdvd (naR b) (g₀ * g₁ * w) (hna0' b hb1) (by
      show naR b * (g₀ * g₁ * w) = g₀ * g₁ * g₂
      rw [show g₂ = naR b * w from hw]; ring)
  have hg₀A : ((g₀ : C.R) : Om C.Z)⁻¹ ∈ A := hdvd g₀ (g₁ * g₂) hg₀ (by
    show g₀ * (g₁ * g₂) = g₀ * g₁ * g₂
    ring)
  let ψ₂ : C.R →ₐ[c.F] T'.Fr := φ.comp ψ'
  have hz'' : FrMap ψ₂ C.y z'' := frMap_trans _ _ _ _ φ _ _ _ hz' hφ
  refine ⟨T', io', e', y', A, ev, ho', hy', ?_, ?_, ?_, ?_, ?_⟩
  · have hyv : evI y' f = ((∏ i, t' i ^ GlobalTheory.AllWt.exOf Dw u 0 i : T'.Frˣ) : T'.Fr) * φ (ψ₁ fS) := by
      have h1 : evR Xo c f z'' = ψ₂ fS := GlobalTheory.Reg.PChartModel.evR_map hL hf.1 ψ₂ hz''
      have h2 : evR Xo c f y'.1 = ((∏ i, t' i ^ GlobalTheory.AllWt.exOf Dw u 0 i : T'.Frˣ) : T'.Fr) * evR Xo c f z'' :=
        GlobalTheory.FlagTan.evR_frBor hf hb'
      rw [h1] at h2
      exact h2
    rw [hyv, hy₀]
    refine nval_transfer ho.1 ho'.1 _ t₀ t' (fun i hi => ?_) φ.toRingHom hvφ hψf
      (close_of_le (le_max_right _ _) (hψ₁n fS (Finset.mem_insert_self _ _)))
    rcases i with _ | ⟨τ, i⟩
    · exact absurd (show GlobalTheory.AllWt.exOf Dw u 0 none = 0 by
        show (GlobalTheory.AllWt.wtOf Dw u 0).2 = 0
        rw [GlobalTheory.AllWt.wtOf_snd]; simp) hi
    · exact hvt τ i
  · intro b hb0
    have : b = na b * (de b)⁻¹ := by
      rw [← hfr b]
      field_simp [hde0 b]
    rw [this]
    exact A.mul_mem (hAr (naR b)) (hdeA b hb0)
  · intro b hb0 hb1
    have : b⁻¹ = de b * (na b)⁻¹ := by
      rw [← hfr b]
      have := hde0 b
      field_simp
    rw [this]
    exact A.mul_mem (hAr (deR b)) (hnaA b hb0 hb1)
  · intro x
    obtain ⟨a, k, hx⟩ := hevx x
    have hχa : ∀ a, IsAlgebraic ℤ (χ a) := fun a => alg_map φ.toRingHom (hψ₁a a)
    exact alg_of_loc (hχa a) (hχa g) hχg hx
  · exact hReg A hAr hg₀A T'.Fr io' ev ψ₂ (fun r => (hevχ r).symm) z'' y'.1 t' hz'' hb'

end GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightSectionComponentValueStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_section_component_value : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (f : Rul Xo c), f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0) → ∀ (B' : Finset (Om Z)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Xo c T io, y.IsAlg → (letI := io.toAlgebra; GlobalTheory.AllWt.LiesOn Z y.1) → evI y f ≠ 0 → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io') (A : Subring (Om Z)) (ev : A →+* T'.Fr), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ nval T'.V e' (evI y' f) = nval T.V e₀ (evI y f) ∧ (↑B' : Set (Om Z)) ⊆ A ∧ (∀ b ∈ B', b ≠ 0 → b⁻¹ ∈ A) ∧ (∀ x, IsAlgebraic ℤ (ev x)) ∧ FinTr.RegAt h Z io' A ev y'.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx.approx_main | exact GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx.approx_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.FinTr.Approx.approx_main <;> assumption)
end
