module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev ArcLt (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)

def arcDet (Dw : Datum H) (K₁ : Type) [Field K₁] : MvPolynomial (ArcLt Dw) (LaurentSeries K₁) :=
  ∏ τ : E →+* ℂ, Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)))

abbrev ArcS (Dw : Datum H) (K₁ : Type) [Field K₁] : Type := Localization.Away (arcDet Dw K₁)

def arcX (Dw : Datum H) (K₁ : Type) [Field K₁] (τ : E →+* ℂ) (i k : Fin (Dw.mult τ)) : ArcS Dw K₁ :=
  algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw))

def arcι (Dw : Datum H) (K₁ : Type) [Field K₁] : PowerSeries K₁ →+* ArcS Dw K₁ :=
  (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)).comp
    ((MvPolynomial.C).comp (HahnSeries.ofPowerSeries ℤ K₁))

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsLieImage {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (ν : ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)) (v : epsR (PowerSeries K₁) ⟶ W.t.G) : Prop :=
  ∀ (n : ℕ) (ρ : DualNumber (PowerSeries K₁) →+* DualNumber (PowerSeries K₁ ⧸ Ideal.span {PowerSeries.X} ^ (n + 1)))
    (κ : DualNumber K₁ →+* DualNumber (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1)))
    (vn : Sp (DualNumber (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1))) ⟶
      (ReciprocityTheory.ChartRestriction.G.Out.thickObj (PowerSeries K₁) (Ideal.span {PowerSeries.X}) n W.t.G).left),
    (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ r)) → ρ DualNumber.eps = DualNumber.eps →
    (∀ r, κ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (PowerSeries.C r))) →
    κ DualNumber.eps = DualNumber.eps →
    vn ≫ (ReciprocityTheory.ChartRestriction.G.Out.thickObj (PowerSeries K₁) (Ideal.span {PowerSeries.X}) n W.t.G).hom =
      spMap (algebraMap (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1))
        (DualNumber (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1)))) →
    vn ≫ (ReciprocityTheory.ChartRestriction.G.Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left = spMap ρ ≫ v.left →
    ∀ x, GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn) (LB.pullGen _ _ _ (ν.s x) (spMap κ))

def IsArcPointPowerSeries (Y : Model Xo c β) {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b)
    (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁))
    [Algebra c.F (ArcS Dw K₁)] (yF : FrPt Xo c (ArcS Dw K₁)) : Prop :=
  χ ≫ Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap b ∧
  (∃ z : Sp (ArcS Dw K₁) ⟶ Xo.XF c, z ≫ Y.j = spMap (arcι Dw K₁) ≫ χ ∧ z ≫ pullback.fst _ _ = yF.x) ∧
  ∃ v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries K₁) ⟶ W.t.G),
    (∀ τ k, IsLieImage W (e τ k) (v τ k)) ∧
    ∀ τ i, ∃ vS : Fin (Dw.mult τ) → (Sp (DualNumber (ArcS Dw K₁)) ⟶ Xo.univ.t.G.left),
      (∀ k, ∃ v'' : Sp (DualNumber (ArcS Dw K₁)) ⟶ Y.oF.t.G.left,
        v'' ≫ Y.m.φ = spMap (dualMap (arcι Dw K₁)) ≫ (v τ k).left ≫ W.m.φ ∧ vS k = v'' ≫ Y.m0.toSABMap.φ) ∧
      IsCombAt yF.x vS (fun k => arcX Dw K₁ τ i k) (yF.u τ i)

def SectionOfLineBundleOne {X : Scheme.{0}} {L : LB X} (σ : ReciprocityTheory.ChartRestriction.G.Out.H0 L 1) (θ : LB.Sec L) : Prop :=
  ∀ (j : Fin 1 → L.ι) (h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0)),
    σ.f j = (X.presheaf.map (homOfLE h).op).hom (θ.f (j 0))

def IsArcPt3At (Y : Model Xo c β) {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b)
    (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    [Algebra c.F (ArcS Dw K₁)] (yF : FrPt Xo c (ArcS Dw K₁)) (th : a.D₀.P.L.Sec) : Prop :=
  ∃ (σ : ReciprocityTheory.ChartRestriction.G.Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x)
    (θ' : LB.Sec W.P.U.LG.L) (θ : LB.Sec W.t.PP.L),
    (∃ j, th.f j ≠ 0) ∧ (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 (show _ from σ) fam) ∧
    (∀ (j : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι) (V : W.P.D.toPre.P.A.left.Opens)
      (h₁ : V ≤ LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j)
      (h₂ : V ≤ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀),
      LB.Coh W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j →
      (W.φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (W.w.s (fun _ => j₀, j 1)).val * resG _ h₁ ((fam 0).f j)) ∧
    SectionOfLineBundleOne σ θ' ∧ HEq θ θ' ∧
    ∃ (t' : SAB H (Sp (ArcS Dw K₁))) (m1 : SABMap t' Xo.univ.t yF.x) (m2 : SABMap t' W.t (spMap (arcι Dw K₁)))
      (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (W.t.PP.L.pull m2.φ))
      (σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (W.t.PP.L.pull m2.φ)),
      (∃ g : t'.G.left ⟶ Y.oF.t.G.left, g ≫ Y.m0.toSABMap.φ = m1.φ ∧ g ≫ Y.m.φ = m2.φ ≫ W.m.φ) ∧
      RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧
      ∀ g : t'.G.left ⟶ Gx yF.x, g ≫ (snd (Over.mk yF.x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk yF.x) Xo.univ.t.G).left = t'.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx yF.x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (yF.s.f (fun _ => j PUnit.unit))

def ArcLieBasis {Y : Model Xo c β} {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)) : Prop :=
  ∃ v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries K₁) ⟶ W.t.G),
    (∀ τ k, IsLieImage W (e τ k) (v τ k)) ∧
    ∀ τ : E →+* ℂ,
      let eig : (epsR (PowerSeries K₁) ⟶ W.t.G) → Prop := fun w => ∀ x : 𝓞 E,
        (w ≫ W.t.act.act x).left =
          spMap (epsScaleR (PowerSeries.C (R := K₁) (algebraMap c.F K₁ (embK c τ x)))) ≫ w.left
      (∀ k, IsTangent (v τ k) ∧ eig (v τ k)) ∧
      ∀ w, IsTangent w → eig w → ∃! cf : Fin (Dw.mult τ) → PowerSeries K₁, IsLieComb cf (v τ) w

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfC
noncomputable section

namespace Formalism.L2.Pj.CompSplitPfC

open TensorProduct

variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]

theorem cspC_alg (s : S) : algebraMap S (S ⊗[P] FractionRing P) s = s ⊗ₜ (1 : FractionRing P) := rfl

theorem cspC_inj : Function.Injective (algebraMap S (S ⊗[P] FractionRing P)) := by
  have hf : Function.Injective (Algebra.linearMap P (FractionRing P)) :=
    IsFractionRing.injective P (FractionRing P)
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (Algebra.linearMap P (FractionRing P)) hf
  have key : ∀ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      (LinearMap.lTensor S (Algebra.linearMap P (FractionRing P))) ((TensorProduct.rid P S).symm s) := by
    intro s
    rw [cspC_alg, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
  intro a b h
  rw [key, key] at h
  exact (TensorProduct.rid P S).symm.injective (h2 h)

theorem cspC_artinian : IsArtinianRing (S ⊗[P] FractionRing P) := by
  haveI : Algebra.Etale (FractionRing P) (FractionRing P ⊗[P] S) := inferInstance
  haveI : Module.Finite (FractionRing P) (FractionRing P ⊗[P] S) :=
    Algebra.FormallyUnramified.finite_of_free (FractionRing P) _
  haveI : IsArtinianRing (FractionRing P ⊗[P] S) := IsArtinianRing.of_finite (FractionRing P) _
  exact Function.Surjective.isArtinianRing (f := (Algebra.TensorProduct.comm P (FractionRing P) S))
    (Algebra.TensorProduct.comm P (FractionRing P) S).surjective

theorem cspC_range (y : S ⊗[P] integralClosure P (FractionRing P)) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      Algebra.TensorProduct.map (AlgHom.id P S) (integralClosure P (FractionRing P)).val y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s z =>
    obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := FractionRing P)).mp z.2
    refine ⟨p • s, ?_⟩
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, cspC_alg, ← hp,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨s', hs'⟩ := hb
    exact ⟨s + s', by rw [map_add (f := _), map_add (f := _), hs, hs']⟩

theorem cspC_idem_of {r : S ⊗[P] FractionRing P} (hr : IsIdempotentElem r) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s = r := by
  have hint : IsIntegral S r := by
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1), Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp [mul_sub, hr.eq]
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := S)
    (B := FractionRing P)).2 ⟨r, hint⟩
  obtain ⟨s, hs⟩ := cspC_range y
  refine ⟨s, hs.trans ?_⟩
  exact congrArg Subtype.val hy

variable (P) in
include P in
theorem cspC_minimal_unique {q P1 P2 : Ideal S} [hq : q.IsPrime] (h1 : P1 ∈ minimalPrimes S)
    (h2 : P2 ∈ minimalPrimes S) (hq1 : P1 ≤ q) (hq2 : P2 ≤ q) : P1 = P2 := by
  by_contra hne
  let M := Algebra.algebraMapSubmonoid S (nonZeroDivisors P)
  have hP1 : P1.IsPrime := Ideal.minimalPrimes_isPrime h1
  have hP2 : P2.IsPrime := Ideal.minimalPrimes_isPrime h2
  have hM : ∀ I ∈ minimalPrimes S, Disjoint (M : Set S) I := by
    intro I hI
    refine Set.disjoint_left.2 fun m hm hmI => ?_
    have hnzd : m ∈ nonZeroDivisors S := by
      refine mem_nonZeroDivisors_iff_right.2 fun x hx => cspC_inj (P := P) ?_
      have hu := IsLocalization.map_units (S ⊗[P] FractionRing P) (⟨m, hm⟩ : M)
      have h0 : algebraMap S (S ⊗[P] FractionRing P) x * algebraMap S (S ⊗[P] FractionRing P) m = 0 := by
        rw [← map_mul, hx, map_zero]
      rw [map_zero]
      exact (hu.mul_left_eq_zero).1 h0
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hI) hmI hnzd
  let Q1 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P1
  let Q2 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P2
  have hQ1 : Q1.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P1 hP1 (hM P1 h1)
  have hQ2 : Q2.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P2 hP2 (hM P2 h2)
  have hc1 : Q1.comap (algebraMap S (S ⊗[P] FractionRing P)) = P1 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP1 (hM P1 h1)
  have hc2 : Q2.comap (algebraMap S (S ⊗[P] FractionRing P)) = P2 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP2 (hM P2 h2)
  have hQne : Q1 ≠ Q2 := fun e => hne (by rw [← hc1, ← hc2, e])
  have := cspC_artinian (P := P) (S := S)
  obtain ⟨r, hr2, hrid, hrall⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne Q2
  have hr1 : r ∈ Q1 := hrall Q1 hQ1 hQne
  obtain ⟨s, hs⟩ := cspC_idem_of (P := P) hrid
  have hs1 : s ∈ P1 := by rw [← hc1, Ideal.mem_comap, hs]; exact hr1
  have hs2 : s ∉ P2 := by rw [← hc2, Ideal.mem_comap, hs]; exact hr2
  have hsid : s * s = s := cspC_inj (P := P) (by rw [map_mul, hs, hrid.eq])
  have h0 : (1 - s) * s ∈ P2 := by
    rw [sub_mul, one_mul, hsid, sub_self]
    exact P2.zero_mem
  have h1s : 1 - s ∈ P2 := (hP2.mem_or_mem h0).resolve_right hs2
  have : (1 : S) ∈ q := by
    have := q.add_mem (hq2 h1s) (hq1 hs1)
    rwa [sub_add_cancel] at this
  exact hq.ne_top ((Ideal.eq_top_iff_one _).2 this)

end Formalism.L2.Pj.CompSplitPfC
end
end

noncomputable section

namespace Formalism.L2.Pj.CompSplitPfD

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology

theorem cspD_gen {X : Type} [TopologicalSpace X] [QuasiSober X] {W : Set X} (hW : W ∈ irreducibleComponents X) :
    IsGenericPoint hW.1.genericPoint W := by
  have h1 := hW.1.isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_mem_irreducibleComponents W hW).closure_eq] at h1

theorem cspD_max {X : Type} [TopologicalSpace X] [T0Space X] {W : Set X}
    (hW : W ∈ irreducibleComponents X) {η : X} (hη : IsGenericPoint η W) (z : X) (hz : z ⤳ η) : z = η := by
  have hWc : closure ({η} : Set X) = W := hη
  have h1 : closure ({η} : Set X) ⊆ closure {z} := specializes_iff_closure_subset.mp hz
  have hirr : IsIrreducible (closure ({z} : Set X)) := isIrreducible_singleton.closure
  have h2 : closure ({z} : Set X) ⊆ W := hW.2 hirr (hWc ▸ h1)
  have h3 : closure ({z} : Set X) = closure {η} := le_antisymm (hWc ▸ h2) h1
  exact (inseparable_iff_closure_eq.mpr h3).eq

theorem cspD_disj {X : Type} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    (hloc : ∀ x : X, ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → X), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  rw [Set.disjoint_left]
  intro x hxZ hxZ'
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η Z := ⟨_, cspD_gen hZ⟩
  obtain ⟨η', hη'⟩ : ∃ η', IsGenericPoint η' Z' := ⟨_, cspD_gen hZ'⟩
  have s1 : η ⤳ x := by rw [specializes_iff_mem_closure, hη.def]; exact hxZ
  have s2 : η' ⤳ x := by rw [specializes_iff_mem_closure, hη'.def]; exact hxZ'
  obtain ⟨Y, tY, g, hg, ⟨y, rfl⟩, hY⟩ := hloc x
  have hU : IsOpen (Set.range g) := hg.isOpen_range
  obtain ⟨a, ha⟩ : η ∈ Set.range g := s1.mem_open hU ⟨y, rfl⟩
  obtain ⟨b, hb⟩ : η' ∈ Set.range g := s2.mem_open hU ⟨y, rfl⟩
  have hind := hg.toIsEmbedding.toIsInducing
  have maxa : ∀ a', a' ⤳ a → a' = a := fun a' h => hg.injective (by
    have h' : g a' ⤳ g a := h.map hg.continuous
    rw [ha] at h' ⊢; exact cspD_max hZ hη _ h')
  have maxb : ∀ b', b' ⤳ b → b' = b := fun b' h => hg.injective (by
    have h' : g b' ⤳ g b := h.map hg.continuous
    rw [hb] at h' ⊢; exact cspD_max hZ' hη' _ h')
  have ya : a ⤳ y := hind.specializes_iff.mp (by rw [ha]; exact s1)
  have yb : b ⤳ y := hind.specializes_iff.mp (by rw [hb]; exact s2)
  have hab := hY a b y maxa maxb ya yb
  apply hne
  calc Z = closure {η} := hη.def.symm
    _ = closure {η'} := by rw [← ha, ← hb, hab]
    _ = Z' := hη'.def

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem cspD_smooth (Xo : Moduli Dw l) (c : Coeff l) :
    Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
  first
    | (haveI := Xo.smooth; exact MorphismProperty.pullback_snd _ _ inferInstance)
    | (haveI := Xo.smooth; infer_instance)
    | (haveI := Xo.smooth; haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s; infer_instance)

theorem cspD_local (Xo : Moduli Dw l) (c : Coeff l) (x : Xo.XF c) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → Xo.XF c), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (Xo.XF c).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have hsm := cspD_smooth Xo c
  have h1 := HasRingHomProperty.appLE (P := @Smooth)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp; trivial)
  let ψ : c.F →+* Γ(Xo.XF c, V) :=
    ((pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)).appLE ⊤ V (fun p _ => by simp; trivial)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra c.F Γ(Xo.XF c, V) := ψ.toAlgebra
  have : Algebra.Smooth c.F Γ(Xo.XF c, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := c.F)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) c.F) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) c.F) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

theorem cspD_comp_disj (Xo : Moduli Dw l) (c : Coeff l) (Z Z' : Comp Xo c) (hne : Z ≠ Z') :
    Disjoint (Z : Set (Xo.XF c)) Z' := cspD_disj (cspD_local Xo c) Z Z' Z.2 Z'.2 (fun h => hne (Subtype.ext h))

end Formalism.L2.Pj.CompSplitPfD
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FrameProofs
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Open

variable (Xo : Moduli Dw l) (c : Coeff l)

def BorDesc : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' →
    ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R) (yq : FrPt Xo c q.R),
      FrMap φ yp y → FrMap ψ yq y' →
      ∃ (r : TRing c.F) (α : p.R →ₐ[c.F] r.R) (β : q.R →ₐ[c.F] r.R) (χ : r.R →ₐ[c.F] S)
        (z z' : FrPt Xo c r.R) (t₀ : Ix Dw → (r.R)ˣ),
        χ.comp α = φ ∧ χ.comp β = ψ ∧ FrMap α yp z ∧ FrMap β yq z' ∧ FrBor t₀ z z' ∧
          ∀ i, χ (t₀ i : r.R) = (t i : S)

def IntLatU : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io), letI := io.toAlgebra; y'.1.x = y.1.x →
    (∀ τ : E →+* ℂ, ∃ A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, IsUnit A.det ∧
      ∀ i, IsCombAt y.1.x (y.1.u τ) (fun j => algebraMap T.V T.Fr (A i j)) (y'.1.u τ i)) ∧
    ∀ (a : T.Frˣ) (pm : Gx y'.1.x ⟶ Gx y.1.x),
      pm ≫ (CartesianMonoidalCategory.snd (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.snd (Over.mk y'.1.x) Xo.univ.t.G).left →
      pm ≫ (CartesianMonoidalCategory.fst (Over.mk y.1.x) Xo.univ.t.G).left =
          (CartesianMonoidalCategory.fst (Over.mk y'.1.x) Xo.univ.t.G).left →
      (∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.1.x).U i ≤ pm ⁻¹ᵁ (PPx y.1.x).U i),
        (pm.appLE _ _ h).hom (scal y.1.x (a : T.Fr) i * y.1.s.f i) = y'.1.s.f i) →
      valV T.V (a : T.Fr) = 1

end Open

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem wtField_of (hD : BorDesc Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  have key : ∀ (p q : TRing c.F) (φ : p.R →ₐ[c.F] S) (ψ : q.R →ₐ[c.F] S) (yp : FrPt Xo c p.R)
      (yq : FrPt Xo c q.R), FrMap φ yp y → FrMap ψ yq y' → ψ (f q yq) = wchar (ex Dw a n) t * φ (f p yp) := by
    intro p q φ ψ yp yq hp hq
    obtain ⟨r, α, β, χ, z, z', t₀, hα, hβ, hz, hz', hb₀, ht⟩ := hD S t y y' hb p q φ ψ yp yq hp hq
    rw [← hα, ← hβ, AlgHom.comp_apply, AlgHom.comp_apply, ← hf.1 p r α yp z hz, ← hf.1 q r β yq z' hz',
      hf.2 r t₀ z z' hb₀, map_mul]
    congr 1
    simp only [wchar, map_prod, map_pow, ht]
  unfold evR evalAt
  rw [dite_eq_left hy, dite_eq_left hy']
  exact key _ _ _ _ _ _ hy.choose_spec.choose_spec.choose_spec hy'.choose_spec.choose_spec.choose_spec

theorem valV_algebraMap_unit (T : CDVR) {u : T.V} (hu : IsUnit u) :
    valV T.V (algebraMap T.V T.Fr u) = 1 := by
  unfold valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro h
  exact (IsDiscreteValuationRing.maximalIdeal T.V).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem intDiagUnit_of (hL : IntLatU Xo c) : IntDiagUnit Xo c := by
  intro T io y y' t hb k
  let := io.toAlgebra
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hb
  obtain ⟨hA, hG⟩ := (show IntLatU Xo c from hL) T io y y' hx
  rcases k with _ | ⟨τ, i⟩
  · exact hG (t none) pm h1 h2 h3
  obtain ⟨A, hdet, hAc⟩ := hA τ

  have hrow : ∀ i', ∃ cf : Fin (Dw.mult τ) → T.Fr, cf i' = (t (some ⟨τ, i'⟩) : T.Fr) ∧
      (∀ j, i' < j → cf j = 0) ∧ ∀ j, algebraMap T.V T.Fr (A i' j) = cf j := by
    intro i'
    obtain ⟨cf, hci, hcz, hcomb⟩ := hu τ i'
    have htan : IsTanAt y.1.x (y'.1.u τ i') := hx ▸ y'.1.tan τ i'
    obtain ⟨a0, -, huniq⟩ := y.1.basis τ (y'.1.u τ i') htan (y'.1.eig τ i')
    have e1 := huniq cf hcomb
    have e2 := huniq _ (hAc i')
    exact ⟨cf, hci, hcz, fun j => congrFun (e2.trans e1.symm) j⟩
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hlow : A.IsLowerTriangular := by
    intro i' j hij
    obtain ⟨cf, -, hcz, hA'⟩ := hrow i'
    apply hinj
    rw [hA' j, hcz j hij, map_zero]
  rw [Matrix.det_of_isLowerTriangular A hlow, IsUnit.prod_univ_iff] at hdet
  obtain ⟨cf, hci, -, hA'⟩ := hrow i
  rw [← hci, ← hA' i]
  exact valV_algebraMap_unit T (hdet i)

end Proofs

end Formalism.L2.Pj
end
end
