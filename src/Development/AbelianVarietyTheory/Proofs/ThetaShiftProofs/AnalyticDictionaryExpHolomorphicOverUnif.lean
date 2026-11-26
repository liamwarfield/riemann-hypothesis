module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpHolomorphicOverUnif
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

section Lift

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem gtHol_toUnit_left :
    (show Sp ℂ ⟶ Sp ℂ from (toUnit (Out.TF (R := ℂ) ℂ)).left) = 𝟙 (Sp ℂ) := by
  have h : (show Sp ℂ ⟶ Sp ℂ from (toUnit (Out.TF (R := ℂ) ℂ)).left) =
      Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ := by
    have := Over.w (toUnit (Out.TF (R := ℂ) ℂ))
    exact (Category.comp_id _).symm.trans this
  refine h.trans ((Spec.map_comp _ _).symm.trans ?_)
  refine Eq.trans (congrArg Spec.map ?_) (Spec.map_id _)
  ext x
  exact (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm

theorem gtHol_isLift (D₀ : Out.DegPre ℂ) {g : ℕ} (u : HolUnif D₀.P.A D₀.P.L g) (p : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A)
    (χ : D₀.X) (c z : Fin g → ℂ) (hc : u.ex c = D₀.c χ) (hp : (show Sp ℂ ⟶ _ from p.left) = (u.ex z).left) :
    FrameValue.IsLift u (Out.DegPre.gtφ D₀ ℂ p χ) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] := by
  have e : ∀ w, (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ u.ex w).left) = (u.ex w).left := fun w =>
    (congrArg (fun q : Sp ℂ ⟶ Sp ℂ => q ≫ (u.ex w).left) gtHol_toUnit_left).trans (Category.id_comp _)
  have hp' : p = toUnit _ ≫ u.ex z := Over.OverMorphism.ext (hp.trans (e z).symm)
  have h0 : u.ex 0 = η[D₀.P.A] := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp
  intro k
  refine (Category.id_comp _).trans ?_
  fin_cases k
  · refine Eq.trans ?_ (e (c + z))
    refine congrArg (fun m : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A => m.left) ?_
    rw [u.ex_add, MonObj.comp_mul, hc, ← hp']
    rfl
  · refine Eq.trans ?_ (e c)
    rw [hc]
    rfl
  · exact hp
  · refine Eq.trans ?_ (e 0)
    rw [h0]
    rfl

end Lift

theorem analyticDictionaryExp_holomorphic_over_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a), IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 z).b.left)) ∧ ∀ x j, DifferentiableOn ℂ (fun z => chiVal (Λ.ex0 z) x j) {z | ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j} ∧ ∀ z, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j → chiVal (Λ.ex0 z) x j = eTwoPi (z.1 (Λ.ε.symm x)) * FrameValue.frameProd Λ.u Out.DegPre.gtε ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] j := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ
  have hl : ∀ (z : Λ.A.V) (x : a.D₀.X), FrameValue.IsLift Λ.u (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x)
      (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] := fun z x =>
    gtHol_isLift a.D₀ Λ.u _ x _ _ (by rw [Λ.ct, LinearEquiv.apply_symm_apply]) (Λ.ex0_b z)
  have hv : ∀ x j z, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 z).b x) j →
      chiVal (Λ.ex0 z) x j = eTwoPi (z.1 (Λ.ε.symm x)) * FrameValue.frameProd Λ.u Out.DegPre.gtε
        ![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] j := by
    intro x j z hj
    have h₁ := FrameValue.valAt'_gen a.D₀.P.isLB ((Λ.ex0 z).isGen x) (hl z x) (j := j) hj
    obtain ⟨y, rfl⟩ := Λ.ε.surjective x
    rw [LinearEquiv.symm_apply_apply] at h₁ ⊢
    rw [Λ.arcDict_expZero_section] at h₁
    exact h₁
  refine ⟨fun U f => ?_, fun x j => ⟨?_, hv x j⟩⟩
  · obtain ⟨ho, hd⟩ := Λ.u.hol U f
    simp only [Λ.ex0_b, Set.mem_univ, true_and]
    exact ⟨ho.preimage continuous_snd, hd.comp differentiable_snd.differentiableOn (fun _ h => h)⟩
  · refine DifferentiableOn.congr ?_ (hv x j)
    refine DifferentiableOn.fun_mul ?_ ?_
    · have : Differentiable ℂ (fun z : Λ.A.V => z.1 (Λ.ε.symm x)) :=
        (Λ.A.evalCLM (Λ.ε.symm x)).differentiable.comp differentiable_fst
      exact ((this.const_mul _).cexp).differentiableOn
    · intro z₀ hz₀
      refine DifferentiableAt.differentiableWithinAt ?_
      have hd : ∀ k, Differentiable ℂ fun z : Λ.A.V =>
          (![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] : Fin 4 → Fin Λ.A.gB → ℂ) k := fun k => by
        fin_cases k
        · exact differentiable_snd.const_add _
        · exact differentiable_const _
        · exact differentiable_snd
        · exact differentiable_const _
      have h : ∀ k, DifferentiableAt ℂ (fun z : Λ.A.V => Λ.u.fr (j k)
          ((![Λ.A.ct (Λ.ε.symm x) + z.2, Λ.A.ct (Λ.ε.symm x), z.2, 0] : Fin 4 → Fin Λ.A.gB → ℂ) k) ^
            Out.DegPre.gtε k) z₀ := fun k => by
        have hk := ((hl z₀ x).le_iff j).1 hz₀ k
        refine DifferentiableAt.zpow ?_ (Or.inl (Λ.u.fr_ne _ _ hk))
        exact ((Λ.u.fr_hol (j k)).differentiableAt ((Λ.u.hol _ 0).1.mem_nhds hk)).comp z₀ (hd k z₀)
      exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (h k).hasFDerivAt).differentiableAt

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvLePreimage
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecCoord

theorem germ_le_preimage (Γ : Germs) (w : ℂ) {Z : Scheme.{0}} (x : Sp (Γ.R w) ⟶ Z) (U : Z.Opens)
    (h : ⊤ ≤ (spMap (Γ.ev w).toRingHom ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro q _
  let p : PrimeSpectrum (Γ.R w) := spMap (Γ.ev w).toRingHom (default : PrimeSpectrum ℂ)
  have hp : p ∈ (show Set (PrimeSpectrum (Γ.R w)) from (x ⁻¹ᵁ U).carrier) :=
    h (x := (default : PrimeSpectrum ℂ)) trivial
  have hle : (show PrimeSpectrum (Γ.R w) from q) ≤ p := by
    intro s hs
    by_contra hn
    refine (show PrimeSpectrum (Γ.R w) from q).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hs (Γ.unit w s fun h0 => hn ?_))
    show (Γ.ev w).toRingHom s ∈ (default : PrimeSpectrum ℂ).asIdeal
    rw [show (Γ.ev w).toRingHom s = 0 from h0]
    exact zero_mem _
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open (x ⁻¹ᵁ U).isOpen hp

theorem comp_le_preimage {X Y Z : Scheme.{0}} (g : X ⟶ Y) (x : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (g ≫ x) ⁻¹ᵁ U := fun p _ => h (x := g p) trivial

theorem exists_ev_le_preimage {Z : Scheme.{0}} {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ Z) (U : Z.Opens)
    (hU : ⊤ ≤ (spMap (Conv.halfRing T).val.toRingHom ≫ yT) ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ w : ℂ, T' < w.im → ∀ hw : T < w.im, ⊤ ≤ (spMap (Conv.ev T w hw).toRingHom ≫ yT) ⁻¹ᵁ U := by
  have hfac : spMap (Conv.halfRing T).val.toRingHom ≫ yT =
      spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) := by
    rw [← Category.assoc, ← spMap_comp]
    rfl
  have hU' : ⊤ ≤ (spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ yT) ⁻¹ᵁ U := by
    intro p _
    rw [hfac] at hU
    obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  obtain ⟨T', h, hT'⟩ := Conv.exists_le_preimage_inclusion yT hU'
  refine ⟨T', h, fun w hw' hw => ?_⟩
  have e : (Conv.ev T w hw).toRingHom = (Conv.ev T' w hw').toRingHom.comp
      (Subalgebra.inclusion (Conv.halfRing_mono h) : Conv.halfRing T →+* Conv.halfRing T') :=
    RingHom.ext fun r => Conv.ev_congr hw hw' rfl
  rw [e, spMap_comp, Category.assoc]
  exact comp_le_preimage _ _ _ hT'

theorem spec_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), ∀ (N : ℕ) [NeZero N] (C : Coords Φ N), ∃ T' ≥ Ψ.T, ∃ hT : C.T ≤ T', ∀ w (hw : T' < w.im), ⊤ ≤ Ψ.yw w ⁻¹ᵁ C.U ∧ (∀ hw', ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw')).toRingHom ≫ Ψ.yT) ⁻¹ᵁ C.U) ∧ ∀ i v (x' : Sp ℂ ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme) (j : o.t.PP.L.ι), x' ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.pi w v).left → ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j → valR x' ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) = Conv.ev C.T w (lt_of_le_of_lt hT hw) (C.cf i v) * Ψ.fr w j v ^ N := by
  intro E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ N _ C
  obtain ⟨T₁, hT₁, hU⟩ := exists_ev_le_preimage Ψ.yT C.U (by rw [Ψ.yT_gen]; exact C.mem)
  refine ⟨max T₁ C.T, le_max_of_le_left hT₁, le_max_right _ _, fun w hw => ?_⟩
  have hw1 : T₁ < w.im := (le_max_left _ _).trans_lt hw
  have hwC : C.T < w.im := (le_max_right _ _).trans_lt hw
  have hwT : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw1
  have hy : ⊤ ≤ Ψ.yw w ⁻¹ᵁ C.U := by
    rw [Ψ.yw_eq w hwT]
    exact hU w hw1 hwT
  have hg : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ C.U := by
    apply germ_le_preimage
    have e : (Γ.ev w).toRingHom.comp (Subalgebra.inclusion (Γ.le Ψ.T w hwT)).toRingHom =
        (Conv.ev Ψ.T w hwT).toRingHom := RingHom.ext fun r => Γ.ev_eq Ψ.T w hwT r
    rw [← Category.assoc, ← spMap_comp, e, ← Ψ.yw_eq w hwT]
    exact hy
  refine ⟨hy, fun _ => hg, fun i v x' j hx' hj => ?_⟩
  have hxU : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ (o.t.G.hom ⁻¹ᵁ C.U) := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
    exact hg
  have hxj : ⊤ ≤ (Ψ.xt w hwT v).left ⁻¹ᵁ o.t.PP.L.U j := by
    apply germ_le_preimage
    rw [← Ψ.pi_eq w hwT v]
    exact hj
  obtain ⟨z, hz⟩ : ∃ z : Sp (Γ.R w) ⟶ (o.t.G.hom ⁻¹ᵁ C.U).toScheme,
      z ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Ψ.xt w hwT v).left :=
    ⟨IsOpenImmersion.lift (o.t.G.hom ⁻¹ᵁ C.U).ι (Ψ.xt w hwT v).left (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hxU (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hzj : ⊤ ≤ z ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j) := by
    intro p _
    rw [← hz] at hxj
    exact Set.mem_iInter.2 fun _ => hxj (x := p) trivial
  have ex : x' = spMap (Γ.ev w).toRingHom ≫ z := by
    rw [← cancel_mono (o.t.G.hom ⁻¹ᵁ C.U).ι, hx', Category.assoc, hz, Ψ.pi_eq w hwT v]
  have hgen : (spMap (Γ.R w).val.toRingHom ≫ z) ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι = (Φ.x v).left := by
    rw [Category.assoc, hz, Ψ.xt_gen]
  have hv := C.val i v _ j hgen (by rw [← Ψ.xt_gen w hwT v]; exact comp_le_preimage _ _ _ hxj)
  rw [HolHom.valR_spMap _ _ _ hzj, ← Ψ.τt_gen w hwT v j hxj] at hv
  have hr : valR z ((Out.powOver o.t.G o.t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
      Subalgebra.inclusion (Γ.le C.T w hwC) (C.cf i v) * Ψ.τt w v j ^ N := Subtype.ext hv
  rw [ex, HolHom.valR_spMap _ _ _ hzj, hr, map_mul, map_pow]
  exact congrArg (· * _) (Γ.ev_eq C.T w hwC (C.cf i v))

end GlobalTheory.SpecCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueLiftCoordsLocalSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueLiftCoordsLocalSubring
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LiftPoint

open GlobalTheory.Points GlobalTheory.AmpleSpan GlobalTheory.Specialise

section General

variable {A K : Type} [CommRing A] [CommRing K] {j : A →+* K} {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X}
  {I : Type} {t : I → LB.Sec H}

theorem exists_lift_of_valR_mem (hj : Function.Injective j) {D : X.Opens} (hD : IsAffineOpen D) (x : Sp K ⟶ X)
    (hx : ⊤ ≤ x ⁻¹ᵁ D) (h : ∀ g, valR x D g ∈ j.range) :
    ∃ ξ : Sp A ⟶ X, ⊤ ≤ ξ ⁻¹ᵁ D ∧ spMap j ≫ ξ = x := by
  choose φ hφ using h
  simp only [valR_eq x D hx] at hφ
  let ψ : Γ(X, D) →+* A := ⟨⟨⟨φ, hj (by simp [hφ])⟩, fun a b => hj (by simp [hφ])⟩, hj (by simp [hφ]),
    fun a b => hj (by simp [hφ])⟩
  refine ⟨_, le_preimage_specMap_fromSpec hD (CommRingCat.ofHom ψ), ?_⟩
  rw [← specMap_valMap_fromSpec hD x hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext hφ)

theorem ext_of_spMap_comp [IsAffine Y] (hj : Function.Injective j) {ξ ξ' : Sp A ⟶ Y}
    (h : spMap j ≫ ξ = spMap j ≫ ξ') : ξ = ξ' :=
  ext_of_valR (isAffineOpen_top Y) (le_preimage_top _) (le_preimage_top _) fun g => hj (by
    rw [← valR_spMap_comp j ξ ⊤ (le_preimage_top _), ← valR_spMap_comp j ξ' ⊤ (le_preimage_top _), h])

theorem exists_lift [IsAffine Y] [IsLocalRing A] (ht : EmbedsBy f t) (hj : Function.Injective j) {b : Sp A ⟶ Y}
    {x : Sp K ⟶ X} (hb : x ≫ f = spMap j ≫ b) {c : I → A} (h : HasCoords x t fun l => j (c l)) {m : I}
    (hm : IsUnit (c m)) : ∃ ξ : Sp A ⟶ X, ξ ≫ f = b ∧ spMap j ≫ ξ = x ∧ HasCoords ξ t c := by
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hx := h.le_nonzeroLocus (hm.map j)
  obtain ⟨ξ, hξ, e⟩ := exists_lift_of_valR_mem hj hD x hx fun g => by
    obtain ⟨q, rfl⟩ := hsurj g
    rw [valR_eval₂Hom f x hx]
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C, ← valR_eq, hb, valR_spMap_comp j b ⊤ (le_preimage_top _)]
      exact ⟨_, rfl⟩
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p l hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      refine mul_mem hp ⟨c l * hm.unit⁻¹.val, (hm.map j).mul_right_cancel ?_⟩
      rw [h.valR_ratio hx (hρ l), ← map_mul, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  refine ⟨ξ, ext_of_spMap_comp hj ?_, e, ?_⟩
  · rw [← Category.assoc, e, hb]
  · have e' : (fun l => valR ξ (Out.nonzeroLocus (t m)) (ρ l) * c m) = c := funext fun l => hj (by
      rw [map_mul, ← valR_spMap_comp j ξ _ hξ, e]
      exact h.valR_ratio hx (hρ l))
    rw [← e']
    exact (hasCoords_ratio hξ hρ).mul_unit hm

end General

theorem le_preimage_powOver {S : Scheme.{0}} (G : Over S) (L : LB G.left) (U : S.Opens) (N : ℕ) {A : Type}
    [CommRing A] (x : Sp A ⟶ (G.hom ⁻¹ᵁ U).toScheme) {j : L.ι} (h : ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ (Out.powOver G L U N).U (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

theorem existsUnique_lift : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K] [IsLocalRing K] (f : R →+* K) (y : Sp R ⟶ S) (x : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (cf : Fin n → R) (j : L.ι) (u : Kˣ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → Function.Injective f → ⊤ ≤ y ⁻¹ᵁ U → x ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap f ≫ y → ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → (∀ i, valR x ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * u) → (∃ i, IsUnit (cf i)) → ∃! x' : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme, x' ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ∧ spMap f ≫ x' = x ∧ ∀ j', ⊤ ≤ (x' ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j' → ∃ u' : Rˣ, ∀ i, valR x' ((Out.powOver G L U N).U (fun _ => j')) ((b i).f (fun _ => j')) = cf i * u' := by
  intro S G _ _ L U N n b R K _ _ _ _ f y x cf j u hL hU hb hf hy hxy hj hval ⟨m, hm⟩
  have : IsAffine U := hU
  let y' : Sp R ⟶ U.toScheme := IsOpenImmersion.lift U.ι y (by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨y z, hy trivial⟩, rfl⟩)
  have ey : y' ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
  have key : ∀ ξ : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme,
      ξ ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ↔ ξ ≫ G.hom ∣_ U = y' := fun ξ => by
    rw [← cancel_mono U.ι, ey, Category.assoc, morphismRestrict_ι]
  have hxy' : x ≫ G.hom ∣_ U = spMap f ≫ y' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ey, morphismRestrict_ι, hxy]
  obtain ⟨ξ, h₁, h₂, h₃⟩ := exists_lift hb hf hxy' (c := cf)
    ⟨fun _ => j, le_preimage_powOver G L U N x hj, u, hval⟩ hm
  refine ⟨ξ, ⟨(key ξ).2 h₁, h₂, fun j' hj' => h₃.chart (le_preimage_powOver G L U N ξ hj')⟩, ?_⟩
  rintro ξ' ⟨k₁, -, k₃⟩
  obtain ⟨j', hj'⟩ := exists_le_preimage_of_iSup_eq_top (ξ' ≫ (G.hom ⁻¹ᵁ U).ι) hL.cover
  exact HasCoords.ext hb (((key ξ').1 k₁).trans h₁.symm)
    ⟨fun _ => j', le_preimage_powOver G L U N ξ' hj', k₃ j' hj'⟩ h₃ hm

end GlobalTheory.LiftPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueLiftCoordsLocalSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_lift_coords_localSubring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K] [IsLocalRing K] (f : R →+* K) (y : Sp R ⟶ S) (x : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (cf : Fin n → R) (j : L.ι) (u : Kˣ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → Function.Injective f → ⊤ ≤ y ⁻¹ᵁ U → x ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap f ≫ y → ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → (∀ i, valR x ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * u) → (∃ i, IsUnit (cf i)) → ∃! x' : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme, x' ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ∧ spMap f ≫ x' = x ∧ ∀ j', ⊤ ≤ (x' ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j' → ∃ u' : Rˣ, ∀ i, valR x' ((Out.powOver G L U N).U (fun _ => j')) ((b i).f (fun _ => j')) = cf i * u' := by
  first | exact @GlobalTheory.LiftPoint.existsUnique_lift | exact GlobalTheory.LiftPoint.existsUnique_lift | (intros; apply GlobalTheory.LiftPoint.existsUnique_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoordsDetermineFamily
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.CoordFamily

open Filter Topology GlobalTheory.Specialise GlobalTheory.AmpleSpan GlobalTheory.HolHom

variable {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X} {I : Type} {t : I → LB.Sec H}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {x : V → (Sp ℂ ⟶ X)} {cf : I → V → ℂ}

theorem eq_of_proportional (ht : EmbedsBy f t) {p p' : Sp ℂ ⟶ X} (hf : p ≫ f = p' ≫ f) {c c' : I → ℂ}
    (h : HasCoords p t c) (h' : HasCoords p' t c') {ρ : ℂ} (e : ∀ i, c' i = ρ * c i) : p = p' := by
  obtain ⟨m, hm⟩ := h'.exists_isUnit ht.1
  have hρ : IsUnit ρ := isUnit_of_mul_isUnit_left (e m ▸ hm)
  have h₁ := h.mul_unit hρ
  have e' : (fun l => c l * ρ) = c' := funext fun l => by rw [e, mul_comm]
  rw [e'] at h₁
  exact h₁.ext ht hf h' hm

theorem holAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z) : HolAt x z := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit ht.1
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hne : ∀ᶠ v in 𝓝 z, cf m v ≠ 0 := (hd m).continuousAt.eventually_ne hm.ne_zero
  have hev : ∀ᶠ v in 𝓝 z, ⊤ ≤ x v ⁻¹ᵁ Out.nonzeroLocus (t m) :=
    hne.mono fun v hv => (hc v).le_nonzeroLocus hv.isUnit
  refine holAt_of_affine hD hev.self_of_nhds hev fun g => ?_
  obtain ⟨q, rfl⟩ := hsurj g
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine (differentiableAt_const (valR y ⊤ a)).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [MvPolynomial.eval₂Hom_C, valAt'_eq_valR]
    exact (HolHom.valR_appLE (x v) f ⊤ _ le_top a hv).trans (by rw [hy])
  | add p q hp hq =>
    refine (hp.add hq).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [valAt'_eq_valR, HolHom.valR_eq _ _ hv, map_add (f := _), Pi.add_apply]
  | mul_X p l hp =>
    refine (hp.mul ((hd l).fun_mul ((hd m).fun_inv hm.ne_zero))).congr_of_eventuallyEq
      ((hev.and hne).mono fun v hv => ?_)
    have e := (hc v).valR_ratio hv.1 (hρ l)
    have e' : valR (x v) _ (ρ l) = cf l v * (cf m v)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hv.2]
    simp only [valAt'_eq_valR, map_mul, MvPolynomial.eval₂Hom_X', Pi.mul_apply]
    rw [← e']
    simp only [HolHom.valR_eq _ _ hv.1, map_mul]

theorem hasCoords_deriv (hcov : ⨆ l, Out.nonzeroLocus (t l) = ⊤) (hc : ∀ v, HasCoords (x v) t fun i => cf i v)
    {z w : V} (hx : HolAt x z) (hd : ∀ i, DifferentiableAt ℂ (cf i) z) {ν : Sp (DualNumber ℂ) ⟶ X}
    (hν : IsDerivAt x z w ν) :
    HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w) := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit hcov
  choose ρ hρ using fun l => exists_isRatio (t l) (t m)
  have hz := (hc z).le_nonzeroLocus hm
  have hν' := (le_preimage_dual_iff hν.1 _).2 hz
  have hu : IsUnit (TrivSqZeroExt.inl (cf m z) + TrivSqZeroExt.inr (fderiv ℂ (cf m) z w) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by simpa using hm)
  have h₁ := (hasCoords_ratio hν' hρ).mul_unit hu
  convert h₁ using 2 with l
  have hev : cf l =ᶠ[𝓝 z] fun v => valAt' (x v) _ (ρ l) * cf m v :=
    (hx _ hz).1.mono fun v hv => ((hc v).valR_ratio hv (hρ l)).symm
  have h0 := hev.self_of_nhds
  beta_reduce at h0
  rw [hev.fderiv_eq, h0, fderiv_fun_mul ((hx _ hz).2 _) (hd m)]
  ext
  · simp [fst_valR hν.1 hz]
  · simp [fst_valR hν.1 hz, hν.2 _ hz, mul_comm]

theorem isDerivAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z w : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z)
    {ν : Sp (DualNumber ℂ) ⟶ X} (hb : ν ≫ f = constVec y)
    (hν : HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w)) :
    IsDerivAt x z w ν := by
  have hx := holAt_of_coords ht hy hc hd
  obtain ⟨ν', hν'⟩ := hx.exists_isDerivAt w
  have h1 := hν'.comp f
  have h2 : (fun v => x v ≫ f) = fun _ => y := funext hy
  have h3 : ν' ≫ f = constVec y := (h2 ▸ h1).unique (isDerivAt_const y z w)
  rw [hν.ext_of_isLocalRing ht (hb.trans h3.symm) (hasCoords_deriv ht.1 hc hx hd hν')]
  exact hν'

theorem hasCoords_powOver {S : Scheme.{0}} {G : Over S} {L : LB G.left} (hL : L.IsLB) {U : S.Opens} {N : ℕ}
    {b : I → LB.Sec (Out.powOver G L U N)} {A : Type} [CommRing A] [IsLocalRing A]
    {p : Sp A ⟶ (G.hom ⁻¹ᵁ U).toScheme} {c : I → A}
    (h : ∀ j, ⊤ ≤ (p ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : Aˣ,
      ∀ i, valR p ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = c i * u) : HasCoords p b c := by
  obtain ⟨j, hj⟩ := Points.exists_le_preimage_of_iSup_eq_top (p ≫ (G.hom ⁻¹ᵁ U).ι) hL.cover
  exact ⟨fun _ => j, fun s hs => Set.mem_iInter.2 fun _ => hj hs, h j hj⟩

end GlobalTheory.CoordFamily

namespace GlobalTheory

open Specialise HolHom CoordFamily in
theorem coords_determine_family : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (x : V → (Sp ℂ ⟶ (G.hom ⁻¹ᵁ U).toScheme)) (cf : Fin n → V → ℂ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → (∀ v, x v ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y) → (∀ v j, ⊤ ≤ (x v ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : ℂ, u ≠ 0 ∧ ∀ i, valR (x v) ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = cf i v * u) → (∀ v v' (ρ : ℂ), (∀ i, cf i v' = ρ * cf i v) → x v' = x v) ∧ ((∀ i, Differentiable ℂ (cf i)) → IsHolTo Set.univ (fun v => x v ≫ (G.hom ⁻¹ᵁ U).ι) ∧ ∀ (z₀ : V) (ν : Sp (DualNumber ℂ) ⟶ (G.hom ⁻¹ᵁ U).toScheme), ν ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y → (∀ j, ⊤ ≤ (ν ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : (DualNumber ℂ)ˣ, ∀ i, valR ν ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = (TrivSqZeroExt.inl (cf i 0) + TrivSqZeroExt.inr (fderiv ℂ (cf i) 0 z₀)) * (u : DualNumber ℂ)) → ∀ (W : G.left.Opens) (f : Γ(G.left, W)), spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ ν = x 0 ∧ (⊤ ≤ (x 0 ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (ν ≫ (G.hom ⁻¹ᵁ U).ι) W f) = fderiv ℂ (fun v => valAt' (x v ≫ (G.hom ⁻¹ᵁ U).ι) W f) 0 z₀)) := by
  intro S G _ L U N n b y V _ _ x cf hL _ hb hy hc
  have hc' : ∀ v, HasCoords (x v) b fun i => cf i v := fun v => hasCoords_powOver hL fun j hj => by
    obtain ⟨u, hu, e⟩ := hc v j hj
    exact ⟨Units.mk0 u hu, e⟩
  have hi : (G.hom ∣_ U) ≫ U.ι = (G.hom ⁻¹ᵁ U).ι ≫ G.hom := morphismRestrict_ι _ _
  have hy' : ∀ v, x v ≫ (G.hom ∣_ U) = x 0 ≫ (G.hom ∣_ U) := fun v => by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hi, hy, hy]
  refine ⟨fun v v' ρ e => (eq_of_proportional hb ((hy' v).trans (hy' v').symm) (hc' v) (hc' v') e).symm,
    fun hd => ⟨isHolTo_of_holAt isOpen_univ fun z _ => (holAt_of_coords hb hy' hc' fun i => hd i z).comp _,
      fun z₀ ν hν hνc W f => ?_⟩⟩
  have h := isDerivAt_of_coords (w := z₀) hb hy' hc' (fun i => hd i 0) (ν := ν)
    (by rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Category.assoc, hi, hν, hy])
    (hasCoords_powOver hL hνc)
  exact ⟨h.1, fun hW => (h.comp (G.hom ⁻¹ᵁ U).ι).2 W hW f⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LePreimageOfUnit
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecGroup

section General

variable {S : Scheme.{0}} {G T T' : Over S}

theorem left_mul_of_comp [GrpObj G] (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom) {a b : T ⟶ G} {a' b' : T' ⟶ G}
    (ha : a'.left = r ≫ a.left) (hb : b'.left = r ≫ b.left) : (a' * b').left = r ≫ (a * b).left := by
  have e₁ : a' = Over.homMk r hr ≫ a := Over.OverMorphism.ext ha
  have e₂ : b' = Over.homMk r hr ≫ b := Over.OverMorphism.ext hb
  rw [e₁, e₂, ← MonObj.comp_mul]
  rfl

theorem left_one [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl

theorem map_zero_eq_one {V M : Type} [AddGroup V] [Group M] (x : V → M) (h : ∀ v v', x (v + v') = x v * x v') :
    x 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem ext_of_generic {A K : Type} [CommRing A] [Field K] {j : A →+* K} (hj : Function.Injective j)
    [IsSeparated G.hom] {p : Sp A ⟶ S} {a b : Over.mk p ⟶ G} (h : spMap j ≫ a.left = spMap j ≫ b.left) : a = b := by
  have : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have : IsDomain A := hj.isDomain j
  exact Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp A) G.hom ((Over.w a).trans (Over.w b).symm) (spMap j) h)

theorem le_preimage_of_unit {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have h₀ : spMap ρ (⊥ : PrimeSpectrum K) ∈ x ⁻¹ᵁ U := h (x := (⊥ : PrimeSpectrum K)) trivial
  have hs : (show PrimeSpectrum A from p) ⤳ (show PrimeSpectrum A from spMap ρ (⊥ : PrimeSpectrum K)) := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun s hs => ?_
    change ρ s ∈ (⊥ : Ideal K)
    rw [Ideal.mem_bot]
    by_contra hne
    exact (show PrimeSpectrum A from p).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hs (hρ s hne))
  exact hs.mem_open (x ⁻¹ᵁ U).isOpen h₀

theorem isFrm_map {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hρ : ∀ s, ρ s ≠ 0 → IsUnit s)
    {X : Scheme.{0}} (L : LB X) (x : Sp A ⟶ X) (τ : L.ι → A) (h : IsFrm L x τ) :
    IsFrm L (spMap ρ ≫ x) (fun j => ρ (τ j)) := by
  refine ⟨fun j hj => (h.1 j (le_preimage_of_unit ρ hρ x _ hj)).map ρ, fun j j' hj => ?_⟩
  have hx := le_preimage_of_unit ρ hρ x _ hj
  rw [HolHom.valR_spMap ρ x _ hx, ← map_mul, ← h.2 j j' hx]

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ : GenPts A t y} {Γ : Germs} (Ψ : SpecPts Φ Γ)
  {w : ℂ} (hw : Ψ.T < w.im)

theorem val_base :
    spMap (Γ.R w).val.toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = y := by
  rw [← Category.assoc, spMap_comp_spMap]
  exact Ψ.yT_gen

theorem ev_base :
    spMap (Γ.ev w).toRingHom ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT = Ψ.yw w := by
  rw [← Category.assoc, spMap_comp_spMap, Ψ.yw_eq w hw]
  congr 2
  exact RingHom.ext fun s => Γ.ev_eq Ψ.T w hw s

theorem xt_add (v v' : A.V) : Ψ.xt w hw (v + v') = Ψ.xt w hw v * Ψ.xt w hw v' := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.add]
  exact left_mul_of_comp (T' := Over.mk y) _ (val_base Ψ hw) (Ψ.xt_gen w hw v).symm (Ψ.xt_gen w hw v').symm

theorem xt_act (e : 𝓞 E) (v : A.V) : Ψ.xt w hw (A.actV e v) = Ψ.xt w hw v ≫ t.act.act e := by
  have := t.semi.separated
  refine ext_of_generic (j := (Γ.R w).val.toRingHom) Subtype.val_injective ?_
  rw [Ψ.xt_gen, Φ.lin, Over.comp_left, Over.comp_left, ← Ψ.xt_gen w hw v, Category.assoc]

include hw

theorem pi_add (v v' : A.V) : Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v' := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_add]
  exact (left_mul_of_comp (T' := Over.mk (Ψ.yw w)) _ (ev_base Ψ hw) (Ψ.pi_eq w hw v) (Ψ.pi_eq w hw v')).symm

theorem pi_act (e : 𝓞 E) (v : A.V) : Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ t.act.act e := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ.pi_eq w hw, xt_act, Over.comp_left, Over.comp_left, Ψ.pi_eq w hw, Category.assoc]

theorem pi_frm (v : A.V) : IsFrm t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v) := by
  rw [Ψ.pi_eq w hw]
  exact isFrm_map (Γ.ev w).toRingHom (Γ.unit w) _ _ _ (Ψ.τt_frm w hw v)

theorem pi_rig (j : t.PP.L.ι) (hj : ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ t.PP.L.U j) :
    Ψ.fr w j 0 = valAt' (Ψ.yw w) ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
  rw [Ψ.pi_eq w hw] at hj
  have h₁ : ⊤ ≤ (Ψ.xt w hw 0).left ⁻¹ᵁ t.PP.L.U j := le_preimage_of_unit (Γ.ev w).toRingHom (Γ.unit w) _ _ hj
  have h₂ : ⊤ ≤ (Φ.x 0).left ⁻¹ᵁ t.PP.L.U j := by
    rw [← Ψ.xt_gen w hw 0]
    exact fun p _ => h₁ (x := spMap (Γ.R w).val.toRingHom p) trivial
  have h₃ : ⊤ ≤ (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ⁻¹ᵁ
      (t.PP.L.pull (eSec t.G)).U (fun _ => j) := by
    rw [map_zero_eq_one _ (xt_add Ψ hw), left_one] at h₁
    exact fun p hp => Set.mem_iInter.2 fun _ => h₁ hp
  have h₄ : Ψ.τt w 0 j = valR (spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT)
      ((t.PP.L.pull (eSec t.G)).U (fun _ => j)) (t.PP.rig.s (fun _ => j)).val := by
    refine Subtype.ext ?_
    rw [Ψ.τt_gen w hw 0 j h₁, Φ.rig j h₂]
    exact (congrArg (fun q => valR q _ _) (val_base Ψ hw).symm).trans
      (HolHom.valR_spMap (Γ.R w).val.toRingHom _ _ h₃ _)
  rw [SpecPts.fr, h₄, HolHom.valAt'_eq_valR, ← ev_base Ψ hw]
  exact (HolHom.valR_spMap (Γ.ev w).toRingHom _ _ h₃ _).symm

omit hw

theorem specPts_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), ∀ w : ℂ, Ψ.T < w.im → (∀ v v', Ψ.pi w (v + v') = Ψ.pi w v * Ψ.pi w v') ∧ (∀ (e : 𝓞 E) v, Ψ.pi w (A.actV e v) = Ψ.pi w v ≫ o.t.act.act e) ∧ (∀ v, IsFrm o.t.PP.L (Ψ.pi w v).left (fun j => Ψ.fr w j v)) ∧ ∀ j, ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ o.t.PP.L.U j → Ψ.fr w j 0 = valAt' (Ψ.yw w) ((o.t.PP.L.pull (eSec o.t.G)).U (fun _ => j)) (o.t.PP.rig.s (fun _ => j)).val :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ψ _ hw =>
    ⟨pi_add Ψ hw, pi_act Ψ hw, pi_frm Ψ hw, pi_rig Ψ hw⟩

end GlobalTheory.SpecGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaCharOffNeZeroDifferentiableQuasiPeriodic
noncomputable section

open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaBlock

variable {g : ℕ} {S : Finset (Fin g)}

def offEquiv (S : Finset (Fin g)) : {n : Fin g → ℤ // ∀ k ∈ S, n k = 0} ≃ ({k // k ∉ S} → ℤ) where
  toFun n i := n.1 i
  invFun l := ⟨fun k => if h : k ∈ S then 0 else l ⟨k, h⟩, fun k hk => dif_pos hk⟩
  left_inv n := by
    refine Subtype.ext (funext fun k => ?_)
    by_cases h : k ∈ S
    · simp [h, n.2 k h]
    · simp [h]
  right_inv l := by
    funext i
    simp [i.2]

private theorem submatrix_mem_siegelH_of_posDef_im (S : Finset (Fin g)) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    τ.submatrix (Subtype.val : {k // k ∉ S} → Fin g) Subtype.val ∈ _root_.ReciprocityTheory.PTheta.SiegelH {k // k ∉ S} := by
  unfold _root_.ReciprocityTheory.PTheta.SiegelH
  exact ⟨hs.submatrix _, hp.submatrix Subtype.val_injective⟩

private theorem ofReal_re_eq_self_of_eq_zero_or_half {c : ℂ} (h : c = 0 ∨ c = 1 / 2) :
    ((c.re : ℝ) : ℂ) = c := by
  rcases h with rfl | rfl
  · simp
  · apply Complex.ext <;> simp

private theorem dotProduct_eq_restrict_of_vanishing (S : Finset (Fin g)) {v : Fin g → ℂ}
    (hv : ∀ k ∈ S, v k = 0) (w : Fin g → ℂ) :
    v ⬝ᵥ w = (fun i : {k // k ∉ S} => v i) ⬝ᵥ (fun i : {k // k ∉ S} => w i) := by
  unfold dotProduct
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => k ∉ S)]
  have h0 : ∑ i : {k // ¬ k ∉ S}, v i * w i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hv i (not_not.1 i.2), zero_mul]
  rw [h0, add_zero]

private theorem mulVec_restrict_eq_submatrix_mulVec_of_vanishing (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    {v : Fin g → ℂ} (hv : ∀ k ∈ S, v k = 0) :
    (fun i : {k // k ∉ S} => (τ *ᵥ v) i) =
      τ.submatrix Subtype.val Subtype.val *ᵥ (fun i : {k // k ∉ S} => v i) := by
  funext i
  simp only [mulVec, submatrix_apply]
  rw [dotProduct_comm, dotProduct_eq_restrict_of_vanishing S hv, dotProduct_comm]

private theorem thetaCharOff_eq_theta_submatrix (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    (c₁ c₂ : Fin g → ℂ) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hS : ∀ k ∈ S, c₁ k = 0) (z : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z = _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff _root_.ReciprocityTheory.PTheta.theta _root_.ReciprocityTheory.PTheta.thetaTerm _root_.ReciprocityTheory.PTheta.eC _root_.ReciprocityTheory.PTheta.shiftVec _root_.ReciprocityTheory.PTheta.ofRealVec
  rw [← (_root_.GlobalTheory.ThetaBlock.offEquiv S).tsum_eq]
  congr 1
  funext n
  have hv : ∀ k ∈ S, ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) k = 0 := fun k hk => by
    simp [n.2 k hk, hS k hk]
  have hw : (fun i : {k // k ∉ S} =>
      (((_root_.GlobalTheory.ThetaBlock.offEquiv S n) i : ℤ) : ℂ) + (((c₁ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) i := by
    funext i
    rw [ofReal_re_eq_self_of_eq_zero_or_half (h₁ i)]
    rfl
  have hz : (fun i : {k // k ∉ S} => z i) + (fun i : {k // k ∉ S} => (((c₂ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => (z + c₂) i := by
    funext i
    simp [ofReal_re_eq_self_of_eq_zero_or_half (h₂ i)]
  rw [hw, hz, dotProduct_eq_restrict_of_vanishing S hv (τ *ᵥ _), mulVec_restrict_eq_submatrix_mulVec_of_vanishing S τ hv,
    dotProduct_eq_restrict_of_vanishing S hv (z + c₂)]
  congr 1
  ring

theorem _root_.GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic (g : ℕ) (S : Finset (Fin g))
    (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2)
    (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) (hS : ∀ k ∈ S, c₁ k = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂) ∧
      ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z,
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
          a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) *
            _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z := by
  have hτ := submatrix_mem_siegelH_of_posDef_im S hs hp
  have hfun : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ = fun z => _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) :=
    funext (thetaCharOff_eq_theta_submatrix S τ c₁ c₂ h₁ h₂ hS)
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    obtain ⟨w, hw⟩ := Function.ne_iff.1
      (_root_.GlobalTheory.theta_ne_zero hτ (fun i : {k // k ∉ S} => (c₁ i).re)
        (fun i : {k // k ∉ S} => (c₂ i).re))
    apply hw
    have h := congrFun h0 (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩)
    rw [hfun] at h
    have hr : (fun i : {k // k ∉ S} => (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩) i.1) = w := by
      funext i
      simp [i.2]
    simp only [Pi.zero_apply] at h
    rwa [hr] at h
  · rw [hfun]
    exact (_root_.GlobalTheory.differentiable_theta hτ _ _).comp (by fun_prop)
  · intro m n hn
    set N : Fin g → ℂ := fun i => (n i : ℂ) with hN
    set M : Fin g → ℂ := fun i => (m i : ℂ) with hM
    have hsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ τ *ᵥ y = y ⬝ᵥ τ *ᵥ x := by
      intro x y
      rw [dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]
    refine ⟨Complex.exp (2 * Real.pi * Complex.I * (c₁ ⬝ᵥ M) -
      Real.pi * Complex.I * (N ⬝ᵥ τ *ᵥ N) - 2 * Real.pi * Complex.I * (N ⬝ᵥ c₂)),
      Complex.exp_ne_zero _, fun z => ?_⟩
    let e : {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} ≃ {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} :=
      { toFun := fun p => ⟨p.1 - n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        invFun := fun p => ⟨p.1 + n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        left_inv := fun p => by ext; simp
        right_inv := fun p => by ext; simp }
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff
    rw [← e.tsum_eq, ← tsum_mul_left]
    congr 1
    funext p
    have hQ : (fun i => (((e p).1 i : ℤ) : ℂ)) = (fun i => ((p.1 i : ℤ) : ℂ)) - N := by
      funext i
      simp [e, hN]
    rw [hQ, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨∑ i, (p.1 i - n i) * m i, ?_⟩
    have hcast : ((∑ i, (p.1 i - n i) * m i : ℤ) : ℂ) =
        (fun i => ((p.1 i : ℤ) : ℂ)) ⬝ᵥ M - N ⬝ᵥ M := by
      simp [dotProduct, hM, hN, Finset.sum_sub_distrib, sub_mul]
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, mulVec_add,
      mulVec_sub]
    linear_combination (Real.pi * Complex.I) * hsym (fun i => ((p.1 i : ℤ) : ℂ)) N +
      (Real.pi * Complex.I) * hsym c₁ N - (2 * Real.pi * Complex.I) * hcast

end GlobalTheory.ThetaBlock
end
end
