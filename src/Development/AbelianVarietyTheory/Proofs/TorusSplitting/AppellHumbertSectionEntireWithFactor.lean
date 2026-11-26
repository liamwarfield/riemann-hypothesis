module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem isHolTo_snd_slice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {e : W → (Sp ℂ ⟶ X)}
    (he : IsHolTo ((Set.univ : Set V) ×ˢ (Set.univ : Set W)) (fun bz => e bz.2)) : IsHolTo Set.univ e := by
  intro U f
  have h := he U f
  have hd : Differentiable ℂ (fun z : W => ((0 : V), z)) := (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have hs : {b ∈ (Set.univ : Set W) | ⊤ ≤ e b ⁻¹ᵁ U} = (fun z : W => ((0 : V), z)) ⁻¹'
        {b ∈ (Set.univ : Set V) ×ˢ (Set.univ : Set W) | ⊤ ≤ e b.2 ⁻¹ᵁ U} :=
      Set.ext fun z => ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩
    rw [hs]
    exact h.1.preimage hd.continuous
  · exact h.2.comp (f := fun z : W => ((0 : V), z)) hd.differentiableOn
      (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)

theorem isHolTo_ex_of_isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty Pm) :
    IsHolTo Set.univ (fun z => (Fu.ex i Pm z).left) := by
  exact isHolTo_snd_slice (e := fun z => (Fu.ex i Pm z).left)
    (Fu.hol i 0 Set.univ (fun _ => Pm) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2

theorem isFnOf_entire_factor :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → ∀ (s : LB.Sec (PPx (Fu.u i Pm))) (θ : (Fin g → ℂ) → ℂ), IsFnOf Fu i Pm fr (Fu.u i Pm) s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Pm a) = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) + Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * θ z := by
  intro E _ _ _ H Dw l Xo σ g ty Fu i Pm Hm χl fr hP hF s θ hθ
  obtain ⟨-, -, -, hdf, hne, -, -, hfac⟩ := hF
  let pt : (Fin g → ℂ) → (Sp ℂ ⟶ Gx (Fu.u i Pm)) := fun z =>
    (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left
  have h1 : ∀ z, pt z ≫ gxFst (Fu.u i Pm) = (Fu.ex i Pm z).left := fun z => by
    have : (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ snd _ _).left = (Fu.ex i Pm z).left := by
      rw [Out.ptSecT, lift_snd]
    exact this
  have h2 : ∀ z, pt z ≫ gxSnd (Fu.u i Pm) = 𝟙 (Sp ℂ) := fun z => by
    have : (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ fst _ _).left = 𝟙 (Sp ℂ) := by
      rw [Out.ptSecT, lift_fst]; rfl
    exact this
  have hex := isHolTo_ex_of_isPeriod Fu i Pm hP
  have hpt : IsHolTo Set.univ pt := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback (p := gxSnd (Fu.u i Pm)) (q := gxFst (Fu.u i Pm))
      (IsPullback.of_hasPullback (Fu.u i Pm) Xo.univ.t.G.hom) ?_ ?_
    · simp only [h2]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
    · simp only [h1]
      exact hex
  have hch : ∀ z, ∃ j, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    have hm : (Fu.ex i Pm z).left (default : PrimeSpectrum ℂ) ∈ ⨆ j, Xo.univ.t.PP.L.U j := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  have hU : ∀ j z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ pt z ⁻¹ᵁ (PPx (Fu.u i Pm)).U (fun _ => j) := fun j z h y hy => by
    have h3 := h hy
    rw [← h1] at h3
    exact Set.mem_iInter.2 fun _ => h3
  refine ⟨fun z₀ => ?_, fun a z => ?_⟩
  · obtain ⟨j, hj⟩ := hch z₀
    have ho : IsOpen {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      have h0 := (hex (Xo.univ.t.PP.L.U j) 0).1
      simp only [Set.mem_univ, true_and] at h0
      exact h0
    have hv : DifferentiableOn ℂ (fun z => valAt' (pt z) ((PPx (Fu.u i Pm)).U fun _ => j) (s.f fun _ => j))
        {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} :=
      (hpt _ (s.f (fun _ => j))).2.mono (fun z hz => ⟨trivial, hU j z hz⟩)
    have hq : DifferentiableOn ℂ θ {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      refine (hv.mul ((hdf j).inv (fun z hz => hne j z hz))).congr fun z hz => ?_
      rw [Pi.mul_apply, Pi.inv_apply, hθ j z (pt z) (h1 z) (h2 z) hz, mul_inv_cancel_right₀ (hne j z hz)]
    exact hq.differentiableAt (ho.mem_nhds hj)
  · obtain ⟨j, hj⟩ := hch z
    have he : Fu.ex i Pm (z + Pm a) = Fu.ex i Pm z := by
      rw [Fu.ex_add i Pm hP, (Fu.ex_ker i Pm hP (Pm a)).2 ⟨a, rfl⟩, _root_.mul_one]
    have e1 := hθ j z (pt z) (h1 z) (h2 z) hj
    have e2 := hθ j (z + Pm a) (pt z) (by rw [he]; exact h1 z) (h2 z) (by rw [he]; exact hj)
    have e3 := (hfac a j z).2 hj
    have n2 := hne j (z + Pm a) (by rw [he]; exact hj)
    apply mul_right_cancel₀ n2
    rw [← e2, e1, e3]
    ring

end GlobalTheory.EtaAn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appellHumbert_section_entire_with_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → ∀ (s : LB.Sec (PPx (Fu.u i Pm))) (θ : (Fin g → ℂ) → ℂ), IsFnOf Fu i Pm fr (Fu.u i Pm) s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Pm a) = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) + Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * θ z := by
  first | exact @GlobalTheory.EtaAn.isFnOf_entire_factor | exact GlobalTheory.EtaAn.isFnOf_entire_factor | (intros; apply GlobalTheory.EtaAn.isFnOf_entire_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.PeriodTorusIsTorusAtFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.PeriodTorusIsTorusAtFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodTorus

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x : Frame X.Ψ r)

theorem perFr_add (v w : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X x (v + w) τ i = Formalism.L2.PjFree.perFr X x v τ i + Formalism.L2.PjFree.perFr X x w τ i := by
  have h : ∀ ρ : E →+* ℂ, Data.emb ρ (v + w) = Data.emb ρ v + Data.emb ρ w := fun ρ => by
    ext a; simp [Data.emb]
  unfold Formalism.L2.PjFree.perFr
  simp only [h]
  split_ifs
  · simp [Matrix.mulVec_add]
  · simp
  · simp [hermC, mul_add, Finset.sum_add_distrib]
  · simp
  · simp

theorem perFr_smul (α : E) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X x (α • v) τ i = τ α * Formalism.L2.PjFree.perFr X x v τ i := by
  have h : ∀ ρ : E →+* ℂ, Data.emb ρ (α • v) = ρ α • Data.emb ρ v := fun ρ => by
    ext a; simp [Data.emb]
  unfold Formalism.L2.PjFree.perFr
  simp only [h]
  split_ifs
  · simp [Matrix.mulVec_smul]
  · simp
  · simp only [hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : starRingEnd ℂ (conjEmb τ α) = τ α := by simp [conjEmb]
    rw [this]; ring
  · simp
  · simp

theorem norm_sq_eq_Hf {J : Type} [Fintype J] (v : EuclideanSpace ℂ J) : ‖v‖ ^ 2 = (I2.Hf v v).re := by
  rw [EuclideanSpace.norm_sq_eq, I2.Hf, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end

theorem isTorusAt_of_isTorusOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ) (T : I2.PT E) (ψ : (Fin Uw.g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → IsTorusOf (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) (Uw.Pm k x) Hm T ψ → I2.IsTorusAt (U.X k) x.1 T ∧ T.r = r ∧ (∀ th, T.ph th = I2.phiFD (U.X k) th x.1) ∧ ∀ m, (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ τ, T.dim τ ≤ m := by
  intro E _ _ _ H Dw l Xo c σ r U hG hU Uw k x Hm T ψ hR hT
  obtain ⟨hr, hdim, hH, hL, hact, -⟩ := hT
  obtain ⟨hmaj, -, -⟩ := GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k x Hm hG hU hR
  let P : (Fin r → E) →+ (Fin Uw.g → ℂ) := AddMonoidHom.mk'
    (fun v j => perFr (U.X k) x.1 v (relab c σ (Uw.e j).1) (Uw.e j).2)
    (fun v w => funext fun j => perFr_add _ _ _ _ _ _)
  have hP : ∀ a, P (Uw.φ k a : Fin r → E) = Uw.Pm k x a := fun a => funext fun j => (Uw.Pm_eq k x a j).symm
  have hΛ : ∀ v ∈ (U.X k).Λ, ∃ a, (Uw.φ k a : Fin r → E) = v := fun v hv =>
    ⟨(Uw.φ k).symm ⟨v, hv⟩, by simp⟩
  have hAt : I2.IsTorusAt (U.X k) x.1 T := by
    refine ⟨ψ.toLinearMap.toAddMonoidHom.comp P, -1, Or.inr rfl, fun y => ?_, fun α v => ?_, fun v hv => ?_,
      fun u hu v hv => ?_⟩
    · rw [hL]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, (Uw.φ k a).2, congrArg ψ (hP a)⟩
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨a, rfl⟩ := hΛ v hv
        exact ⟨a, congrArg ψ (hP a).symm⟩
    · change ψ (P ((α : E) • v)) = I2.act α (ψ (P v))
      rw [← hact]
      exact congrArg ψ (funext fun j => perFr_smul _ _ _ _ _ _)
    · obtain ⟨a, rfl⟩ := hΛ v hv
      change ‖ψ (P _)‖ ^ 2 = _
      rw [hP, norm_sq_eq_Hf, hH, hmaj]
    · obtain ⟨a, rfl⟩ := hΛ u hu
      obtain ⟨b, rfl⟩ := hΛ v hv
      change (I2.Hf (ψ (P _)) (ψ (P _))).im = _
      have h := congrArg (fun t : ℚ => (t : ℝ)) (Uw.iso k a b)
      simp only [neg_mul, map_neg, Rat.cast_neg, Rat.cast_intCast] at h
      rw [hP, hP, hH, hR.2.2, h]
      ring
  obtain ⟨hp, hq⟩ := Uw.F.sig (Uw.ik k)
  refine ⟨hAt, by rw [hr, hp, hq, hU.1], (I2.TorusAtPf.torusAtLa1_holds E r _ x.1 x.2 T hAt).2, fun m hm => ?_⟩
  obtain ⟨-, hty⟩ := hU.2.1 k
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (U.X k).Ψ := by
    obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h0 : τ0 ∈ (U.X k).Ψ
    · exact ⟨_, h0⟩
    · by_contra hn
      exact h0 (((U.X k).cmType τ0).2 fun h' => hn ⟨_, h'⟩)
  have h1 : T.dim τ = Dw.p := by
    rw [hdim]; unfold Datum.mult; rw [if_pos ((hty τ).1 hτ), hp]
  have h2 := T.dim_conj τ
  rcases hm with hm | hm
  · exact ⟨τ, by omega⟩
  · exact ⟨ComplexEmbedding.conjugate τ, by omega⟩

end GlobalTheory.PeriodTorus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.PeriodTorusIsTorusAtFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodTorus_isTorusAt_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (Uw : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (Hm : Matrix (Fin Uw.g) (Fin Uw.g) ℂ) (T : I2.PT E) (ψ : (Fin Uw.g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim), IsRiem Uw.F (Uw.ik k) (Uw.Pm k x) Hm → IsTorusOf (Uw.F.Di (Uw.ik k)) (fun j => relab c σ (Uw.e j).1) (Uw.Pm k x) Hm T ψ → I2.IsTorusAt (U.X k) x.1 T ∧ T.r = r ∧ (∀ th, T.ph th = I2.phiFD (U.X k) th x.1) ∧ ∀ m, (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ τ, T.dim τ ≤ m := by
  first | exact @GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf | exact GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf | (intros; apply GlobalTheory.PeriodTorus.isTorusAt_of_isTorusOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2Norm
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2Norm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn.ThetaTorus

open MeasureTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.EtaAn.ThetaTorus.setAverage_equiv {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
    [BorelSpace W]
    (m₁ : Measure V) [m₁.IsAddHaarMeasure] (m₂ : Measure W) [m₂.IsAddHaarMeasure]
    (e : V ≃L[ℝ] W) (s : Set W) (f : W → ℝ) :
    ⨍ w in s, f w ∂m₂ = ⨍ v in e ⁻¹' s, f (e v) ∂m₁ := by
  set ν : Measure W := Measure.map e m₁
  have hc := Measure.isAddLeftInvariant_eq_smul m₂ ν
  set c := m₂.addHaarScalarFactor ν
  have hpos : (0 : ℝ) < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure m₂ ν
  let e' : V ≃ᵐ W := e.toHomeomorph.toMeasurableEquiv
  have hν : ν = Measure.map e' m₁ := rfl
  have hint : ∫ w in s, f w ∂ν = ∫ v in e ⁻¹' s, f (e v) ∂m₁ := by
    rw [hν]; exact setIntegral_map_equiv e' f s
  have hmeas : ν.real s = m₁.real (e ⁻¹' s) := by
    rw [hν, measureReal_def, measureReal_def, e'.map_apply]; rfl
  rw [setAverage_eq, setAverage_eq, hc, Measure.restrict_smul, integral_smul_nnreal_measure, hint,
    measureReal_nnreal_smul_apply, hmeas, NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel₀ hpos.ne', _root_.one_mul]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.EtaAn.ThetaTorus.Hf_add_re {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (v + w) (v + w)).re = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf v v).re + 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf v w).re + (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf w w).re := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf
  simp only [PiLp.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib, Complex.add_re,
    Complex.re_sum]
  have hsym : ∀ i, (w.ofLp i * (starRingEnd ℂ) (v.ofLp i)).re
      = (v.ofLp i * (starRingEnd ℂ) (w.ofLp i)).re := by
    intro i
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp only [hsym]
  ring

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.EtaAn.ThetaTorus.theta_section_l2_torus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (T : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), _root_.GlobalTheory.EtaAn.IsTorusOf D ty Pm Hm T ψ → Differentiable ℂ θ → (∀ a z, θ (z + Pm a) = (((Int.negOnePow (D.EF a (H.w0 • a)) : ℤˣ) : ℤ) : ℂ) * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (Pm a) + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pm a) (Pm a)) * θ z) → MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume → (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 ∧ T.l2 1 (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => θ (ψ.symm (v 0))) = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re)) / (MeasureTheory.volume Fd).toReal ∧ ∀ z, Real.sqrt (T.ptN2 1 (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ z)) = ‖θ z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) := by
  intro E _ _ _ H D g ty Pm Hm T ψ θ Fd hT hθ hper hFd
  unfold _root_.GlobalTheory.EtaAn.IsTorusOf at hT
  obtain ⟨-, -, hψ, hL, -, heps⟩ := hT
  have hIJ : ∀ v w : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim,
      _root_.ReciprocityTheory.ChartRestriction.G.I2.HC v w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (ψ.symm (v 0)) (ψ.symm (w 0)) := by
    intro v w
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.HC
    rw [Fin.sum_univ_one, ← hψ, ψ.apply_symm_apply, ψ.apply_symm_apply]
  have hpt : ∀ z, T.ptN2 1 (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ z)
      = ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) := by
    intro z
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.ptN2
    rw [hIJ]
    simp only [ψ.symm_apply_apply, Nat.cast_one, _root_.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.Sec
    refine ⟨?_, ?_⟩
    · have hl : Differentiable ℂ (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => ψ.symm (v 0)) :=
        (LinearMap.toContinuousLinearMap
          (ψ.symm : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim →ₗ[ℂ] (Fin g → ℂ))).differentiable.comp (differentiable_apply 0)
      exact hθ.comp hl
    · intro p hp v
      obtain ⟨a, ha⟩ := (hL (p 0)).1 (hp 0)
      have h1 : ψ.symm ((v + p) 0) = ψ.symm (v 0) + Pm a := by
        rw [Pi.add_apply, map_add (f := _), ← ha, ψ.symm_apply_apply]
      simp only [h1, hper, hIJ, Fin.prod_univ_one, ← ha, heps, ψ.symm_apply_apply, Nat.cast_one,
        _root_.one_mul, pow_one]
      ring_nf
  · let ψR : (Fin g → ℂ) ≃L[ℝ] _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim :=
      (ψ.restrictScalars ℝ).toContinuousLinearEquiv
    let e : (Fin g → ℂ) ≃L[ℝ] (Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) :=
      ψR.trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim)).symm
    have he : ∀ z, e z = fun _ => ψ z := fun z => rfl
    haveI : (volume : Measure (Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.l2
    refine (_root_.GlobalTheory.EtaAn.ThetaTorus.setAverage_equiv volume volume e _ _).trans ?_
    simp only [he, hpt]
    have hS : e ⁻¹' T.fd 1 = ψ ⁻¹' ZSpan.fundamentalDomain T.b := by
      ext z
      simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.fd, he]
    rw [hS]
    let emap : Submodule.span ℤ (Set.range T.b) → Pm.range := fun x =>
      ⟨ψ.symm x, by
        obtain ⟨a, ha⟩ := (hL x).1 x.2
        exact ⟨a, by rw [← ha, ψ.symm_apply_apply]⟩⟩
    have hbij : Function.Bijective emap := by
      refine ⟨fun x y h => ?_, fun y => ?_⟩
      · have h' := congrArg (fun u : Pm.range => ψ (u : Fin g → ℂ)) h
        simp only [emap, ψ.apply_symm_apply] at h'
        exact Subtype.ext h'
      · obtain ⟨y, a, rfl⟩ := y
        exact ⟨⟨ψ (Pm a), (hL _).2 ⟨a, rfl⟩⟩, Subtype.ext (by simp [emap])⟩
    haveI : Countable Pm.range := hbij.2.countable
    have hψm : Measurable (ψ : (Fin g → ℂ) → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) := ψR.continuous.measurable
    have hFdS : IsAddFundamentalDomain Pm.range (ψ ⁻¹' ZSpan.fundamentalDomain T.b) volume :=
      (ZSpan.isAddFundamentalDomain T.b (Measure.map ψ volume)).preimage_of_equiv
        (MeasurePreserving.quasiMeasurePreserving ⟨hψm, rfl⟩) hbij
        (fun x z => by
          show ψ ((emap x : Fin g → ℂ) + z) = (x : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) + ψ z
          simp [emap])
    have hinv : ∀ (h : Pm.range) (z : Fin g → ℂ),
        ‖θ (h +ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h +ᵥ z) (h +ᵥ z)).re)
          = ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) := by
      rintro ⟨_, a, rfl⟩ z
      show ‖θ (Pm a + z)‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pm a + z) (Pm a + z)).re)
        = ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re)
      have hexp := _root_.GlobalTheory.EtaAn.ThetaTorus.Hf_add_re (ψ z) (ψ (Pm a))
      rw [← map_add (f := _)] at hexp
      simp only [hψ] at hexp
      have hs : ‖((((Int.negOnePow (D.EF a (H.w0 • a)) : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
        rcases Int.units_eq_one_or (Int.negOnePow (D.EF a (H.w0 • a))) with h | h <;> simp [h]
      have hre : (↑Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (Pm a) + ↑Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pm a) (Pm a)).re
          = Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (Pm a)).re + Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pm a) (Pm a)).re := by
        simp [Complex.add_re, Complex.mul_re]
      rw [add_comm, hper, norm_mul, norm_mul, hs, Complex.norm_exp, hre, hexp, _root_.one_mul,
        mul_pow, mul_comm (Real.exp _ ^ 2), _root_.mul_assoc, sq (Real.exp _), ← Real.exp_add,
        ← Real.exp_add]
      ring_nf
    rw [setAverage_eq, measureReal_def, hFdS.measure_eq hFd, hFdS.setIntegral_eq hFd (f := fun z =>
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re)) hinv,
      smul_eq_mul, div_eq_inv_mul]
  · intro z
    rw [hpt z]
    have hsq : Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re)
        = Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [hsq, ← mul_pow]
    exact Real.sqrt_sq (by positivity)

end GlobalTheory.EtaAn.ThetaTorus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2NormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_torus_l2_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), IsTorusOf D ty Pm Hm T ψ → Differentiable ℂ θ → (∀ a z, θ (z + Pm a) = (((Int.negOnePow (D.EF a (H.w0 • a)) : ℤˣ) : ℤ) : ℂ) * Complex.exp (Real.pi * hermForm Hm z (Pm a) + Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * θ z) → MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume → (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 ∧ T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (MeasureTheory.volume Fd).toReal ∧ ∀ z, Real.sqrt (T.ptN2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ z)) = ‖θ z‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm z z).re) := by
  first | exact @GlobalTheory.EtaAn.ThetaTorus.theta_section_l2_torus | exact GlobalTheory.EtaAn.ThetaTorus.theta_section_l2_torus | (intros; apply GlobalTheory.EtaAn.ThetaTorus.theta_section_l2_torus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.RelabellingGoodEmbeddingIsTypeFn
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.RelabellingGoodEmbeddingIsTypeFn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem relab_isTypeFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, Dw.mult (relab c σ τ) = Dw.mult τ) ∧ ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  intro E _ _ _ H Dw l _ c σ hσ
  obtain ⟨hbij, hrt, -, hty⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  refine ⟨hbij, fun τ => ?_, fun g e => hty Dw g e⟩
  unfold Datum.mult
  exact if_congr (hrt τ) rfl rfl

end GlobalTheory.EtaAn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.RelabellingGoodEmbeddingIsTypeFnStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relabelling_goodEmbedding_isTypeFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, Dw.mult (relab c σ τ) = Dw.mult τ) ∧ ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  first | exact @GlobalTheory.EtaAn.relab_isTypeFn | exact GlobalTheory.EtaAn.relab_isTypeFn | (intros; apply GlobalTheory.EtaAn.relab_isTypeFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.CuspAndSupCLeOfBounded
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoundedCusp

theorem mem_SS_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : FD.Wt X.Ψ r) (τ0 : X.Ψ) (h : X.p0 = 0 ∨ X.p0 = r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) :
    P ∈ X.SS la := by
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  exfalso
  have hiso : X.IsIsoV (X.embV ξ) := fun τ =>
    ⟨by rw [show X.embV ξ τ = Data.emb τ.1 ξ from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  have hmpos := PositiveMinorUnits.mN_pos (MajorantFamilyNorms.hG_of X τ0) X.p0 X.p0_le (mat x τ0) (hx τ0).1
    (MajorantFamilyNorms.hsg_of X hx τ0) (X.embV ξ τ0) (hiso τ0).1 (hiso τ0).2
  have htop := PositiveMinorUnits.mN_top (MajorantFamilyNorms.hG_of X τ0) X.p0 (mat x τ0) (hx τ0).1
    (MajorantFamilyNorms.hsg_of X hx τ0) (X.embV ξ τ0) (hiso τ0).1
  rcases h with h | h
  · rw [h, PositiveMinorUnits.mN_zero] at hmpos
    exact lt_irrefl _ hmpos
  · rw [h, htop] at hmpos
    exact lt_irrefl _ hmpos

end GlobalTheory.BoundedCusp

namespace GlobalTheory

theorem cusp_and_supC_le_of_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (n : ℕ) (f : Rul Xo c) (C : ℝ), 2 ≤ n → Even n → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → f ∈ sec Xo c 0 n → (∀ σ, GoodEmb c σ → ∀ k, ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm (laU (U σ) 0 n k) (rdU (U σ) f k) x ≤ C) → 0 ≤ C → f ∈ cusp Xo c U 0 n ∧ ∀ σ (xi : ℝ), GoodEmb c σ → supC Xo c U xi σ 0 n f ≤ C := by
  intro E _ _ _ H Dw l Xo c r U n f C hn hev hU hf hb hC
  refine ⟨?_, fun σ xi hσ => ?_⟩
  · rw [mem_cusp]
    refine ⟨hf, fun σ hσ => holCusp_mem_holSub _ _ fun j => ?_⟩
    obtain ⟨-, -, -, -, hsec, -⟩ := hU σ hσ
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, hev⟩
    obtain ⟨τ0⟩ : Nonempty ((U σ).X j).Ψ := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : τ ∈ ((U σ).X j).Ψ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, not_not.mp (fun h' => h ((((U σ).X j).cmType τ).mpr h'))⟩⟩
    have hbd : ((U σ).X j).IsBddSec (laU (U σ) 0 n j) (rdU (U σ) f j) :=
      ⟨hsec _ _ hD f hf j, C, hb σ hσ j⟩
    have hle := ((U σ).X j).p0_le
    by_cases h0 : ((U σ).X j).p0 = 0 ∨ ((U σ).X j).p0 = r
    · exact BoundedCusp.mem_SS_of_definite _ _ τ0 h0 _ hbd
    · refine AR.Up.cuspStatement_holds r _ _ τ0 (by omega) (by omega) ?_ ?_ _ hbd
      · intro i i' h1 h2
        unfold laU
        by_cases h3 : ((U σ).X j).p0 ≤ (i : ℕ)
        · rw [if_pos h3, if_pos (by omega)]
          simp
        · rw [if_neg h3, if_neg (by omega)]
          simp
      · intro i i' h1 h2
        unfold laU
        rw [if_neg (by omega), if_pos (by omega)]
        omega
  · have h1 : lieFac Dw xi (0 : (E →+* ℂ) × ℕ → ℕ) = 1 := by simp [lieFac]
    unfold supC supN
    rw [h1, _root_.one_mul]
    refine ENNReal.toReal_le_of_le_ofReal hC ?_
    exact iSup_le fun p => ENNReal.ofReal_le_ofReal (hb σ hσ p.1 p.2 p.2.2)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBorelOrthonormalFlagFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBorelOrthonormalFlagFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem exists_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ (∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1) ∧ X.la1 (rmul x b) = X.la1 x ∧ (∀ th, I2.phiFD X th (rmul x b) = I2.phiFD X th x) ∧ ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P → X.pnorm la P x = ‖P (rmul x b)‖ := by
  intro E _ _ _ r X x hx
  have hb := FrameDegreeData.bOf_mem X hx
  have ho := FrameDegreeData.ortho_bOf X hx
  have hd : ∀ τ i, ‖dmin X.Gm (rmul x (FrameDegreeData.bOf X x)) τ i‖ = 1 := by
    intro τ i
    unfold dmin
    rw [ho τ, FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Complex.norm_real]
    rcases FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j : Fin r) with h | h <;>
      rw [h] <;> simp
  have hl : X.la1 (rmul x (FrameDegreeData.bOf X x)) = X.la1 x := by
    unfold Data.la1
    rw [ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel X hx hb]
  refine ⟨_, hb, OrthogonalFrameDomain.rmul_mem_dom X hx hb, hd, hl, fun th => ?_, fun la P hP => ?_⟩
  · unfold I2.phiFD
    rw [hl]
  · rw [← FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx _ hb]
    unfold Data.pnorm
    simp only [norm_div, hd, div_one, Real.one_rpow, Finset.prod_const_one, _root_.mul_one]

end GlobalTheory.EtaAn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBorelOrthonormalFlagFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_borel_orthonormal_flag_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ (∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1) ∧ X.la1 (rmul x b) = X.la1 x ∧ (∀ th, I2.phiFD X th (rmul x b) = I2.phiFD X th x) ∧ ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P → X.pnorm la P x = ‖P (rmul x b)‖ := by
  first | exact @GlobalTheory.EtaAn.exists_unit_frame | exact GlobalTheory.EtaAn.exists_unit_frame | (intros; apply GlobalTheory.EtaAn.exists_unit_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ArchimedeanBoundTotalConstantSize
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.EtaAn.archimedeanBoundTotalConstant_size : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q m Nc : ℕ) (L : ℝ), 2 ≤ L → 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E → 1 ≤ r → 1 ≤ m → m ≤ r → 1 ≤ q → 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E → Real.log (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E) ≤ 2 * L → Real.log (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E) ≤ 2 * L → Real.log r ≤ L → Real.log q ≤ 70 * L → Real.log Nc ≤ 41 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r * L) ^ 2 → 0 ≤ _root_.GlobalTheory.EtaAn.p16 E r q m 5 (max 1 Nc * 5 ^ (8 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2)) ∧ _root_.GlobalTheory.EtaAn.p16 E r q m 5 (max 1 Nc * 5 ^ (8 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2)) ≤ 200000 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r * L) ^ 2 := by
  intro E _ _ _ r q m Nc L hL hf hr hm hmr hq hrd hlrd hlf hlr hlq hlN
  unfold _root_.GlobalTheory.EtaAn.p16 _root_.GlobalTheory.EtaAn.p3 _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar _root_.ReciprocityTheory.ChartRestriction.G.I2.RR
  push_cast
  set f := _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E with hfdef
  set D := _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E with hDdef
  have hF : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMR : (m : ℝ) ≤ r := by exact_mod_cast hmr
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlM : Real.log m ≤ L := (Real.log_le_log (by positivity) hMR).trans hlr
  have hlFnn : 0 ≤ Real.log f := Real.log_nonneg hF
  have hlRnn : 0 ≤ Real.log r := Real.log_nonneg hR
  have hlMnn : 0 ≤ Real.log m := Real.log_nonneg hM
  have hlQnn : 0 ≤ Real.log q := Real.log_nonneg hQ
  have hlDnn : 0 ≤ Real.log D := Real.log_nonneg hrd
  have heOne := Real.exp_one_gt_d9
  have heTwo : (7.3 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
  have hlTwo : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlFive : Real.log 5 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlSix : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlSeven : Real.log 7 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlTenThousand : Real.log 10000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num), show (10 : ℝ) = 2 * 5 by norm_num, Real.exp_mul]
    have : (7.3 : ℝ) ^ 5 ≤ Real.exp 2 ^ 5 := pow_le_pow_left₀ (by norm_num) heTwo 5
    rw [← Real.rpow_natCast] at this
    norm_num at this ⊢
    linarith
  have hlTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlFiveNonneg : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)

  have hy : (1 : ℝ) ≤ f * r * q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF hR) hQ
  have hsqrt : 1 ≤ √((f : ℝ) * r * q) := Real.one_le_sqrt.mpr hy
  have hlogSqrt : Real.log (1 + 6 * √((f : ℝ) * r * q)) ≤ 2 + 37 * L := by
    calc Real.log (1 + 6 * √((f : ℝ) * r * q)) ≤ Real.log (7 * √((f : ℝ) * r * q)) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 7 + (Real.log f + Real.log r + Real.log q) / 2 := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      _ ≤ 2 + 37 * L := by linarith
  have hlogSqrtNonneg : 0 ≤ Real.log (1 + 6 * √((f : ℝ) * r * q)) :=
    Real.log_nonneg (by have := Real.sqrt_nonneg ((f : ℝ) * r * q); linarith)

  have hg : Real.log (3 * (2 * (f : ℝ) * m)) = Real.log 6 + Real.log f + Real.log m := by
    rw [show 3 * (2 * (f : ℝ) * m) = 6 * f * m by ring, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hlogFact : Real.log (2 * (3 * (2 * (f : ℝ) * m)) ^ (2 * f * m)) =
      Real.log 2 + 2 * f * m * Real.log (3 * (2 * (f : ℝ) * m)) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hgUpper : Real.log (3 * (2 * (f : ℝ) * m)) ≤ 2 + 3 * L := by rw [hg]; linarith
  have hgNonneg : 0 ≤ Real.log (3 * (2 * (f : ℝ) * m)) := by rw [hg]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 6 by norm_num)]

  have hmaxOne : (1 : ℝ) ≤ max 1 (Nc : ℝ) := le_max_left _ _
  have hlogBig : Real.log (max 1 (Nc : ℝ) * 5 ^ (8 * f * r ^ 2)) =
      Real.log (max 1 (Nc : ℝ)) + 8 * f * r ^ 2 * Real.log 5 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hXnn : 0 ≤ 41 * ((f : ℝ) * r * L) ^ 2 := by positivity
  have hlogMax : Real.log (max 1 (Nc : ℝ)) ≤ 41 * ((f : ℝ) * r * L) ^ 2 := by
    rcases le_total (Nc : ℝ) 1 with h | h
    · rw [max_eq_left h, Real.log_one]; exact hXnn
    · rw [max_eq_right h]; exact hlN
  have hlogMaxNonneg : 0 ≤ Real.log (max 1 (Nc : ℝ)) := Real.log_nonneg hmaxOne

  have hlogLast : Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2))
      ≤ 10 + 24 * L := by
    rw [show 5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2) =
        10000 * r * f ^ 3 * m ^ 3 * D ^ 7 by ring]
    have hD : (0 : ℝ) < D := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    linarith
  have hlogLastNonneg : 0 ≤ Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) := by
    apply Real.log_nonneg
    rw [show 5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2) =
        10000 * r * f ^ 3 * m ^ 3 * D ^ 7 by ring]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hR)
        (one_le_pow₀ hF)) (one_le_pow₀ hM)) (one_le_pow₀ hrd)
  rw [hlogFact, hlogBig]

  have hFL : 2 ≤ (f : ℝ) * L := le_trans hL (le_mul_of_one_le_left (by linarith) hF)
  have hFRsq : 4 * ((f : ℝ) * r ^ 2) ≤ ((f : ℝ) * r * L) ^ 2 := by
    have hFLsq : 4 ≤ (f : ℝ) * L ^ 2 := by
      calc (4 : ℝ) = 1 * (2 * 2) := by ring
        _ ≤ f * (L * L) := mul_le_mul hF (mul_le_mul hL hL (by norm_num) (by linarith))
            (by norm_num) (by positivity)
        _ = f * L ^ 2 := by ring
    calc 4 * ((f : ℝ) * r ^ 2) ≤ (f * L ^ 2) * ((f : ℝ) * r ^ 2) :=
          mul_le_mul_of_nonneg_right hFLsq (by positivity)
      _ = ((f : ℝ) * r * L) ^ 2 := by ring
  have hFRsqL : 2 * ((f : ℝ) * r ^ 2 * L) ≤ ((f : ℝ) * r * L) ^ 2 := by
    calc 2 * ((f : ℝ) * r ^ 2 * L) ≤ (f * L) * ((f : ℝ) * r ^ 2 * L) :=
          mul_le_mul_of_nonneg_right hFL (by positivity)
      _ = ((f : ℝ) * r * L) ^ 2 := by ring
  have hRle : (r : ℝ) ≤ f * r ^ 2 := by
    calc (r : ℝ) = 1 * 1 * r := by ring
      _ ≤ f * r * r := mul_le_mul (mul_le_mul hF hR zero_le_one (by positivity)) le_rfl
          (by positivity) (by positivity)
      _ = f * r ^ 2 := by ring
  have hprodSqrt : (r : ℝ) * (f * r * Real.log (1 + 6 * √((f : ℝ) * r * q))) ≤
      r * (f * r * (2 + 37 * L)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogSqrt (by positivity)) (by positivity)
  have hprodFact : (r : ℝ) * (2 * f * m * Real.log (3 * (2 * (f : ℝ) * m))) ≤ r * (2 * f * r * (2 + 3 * L)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc 2 * (f : ℝ) * m * Real.log (3 * (2 * (f : ℝ) * m)) ≤ 2 * f * m * (2 + 3 * L) :=
          mul_le_mul_of_nonneg_left hgUpper (by positivity)
      _ ≤ 2 * f * r * (2 + 3 * L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMR (by positivity)) (by linarith)
  have hprodRFM : (r : ℝ) * (2 * f * m) ≤ 2 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hMR (by positivity : (0 : ℝ) ≤ 2 * f * r)
    linarith
  have hprodLast : (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
      Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) ≤
      625 * (f * r ^ 2) * (10 + 24 * L) := by
    calc (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
          Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2))
        ≤ (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 * (10 + 24 * L) :=
          mul_le_mul_of_nonneg_left hlogLast (by positivity)
      _ ≤ 625 * (f * r ^ 2) * (10 + 24 * L) :=
          mul_le_mul_of_nonneg_right (by linarith [hprodRFM]) (by linarith)
  have hprodFiveA : 8 * (f : ℝ) * r ^ 2 * Real.log 5 ≤ 16 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlFive (by positivity : (0 : ℝ) ≤ f * r ^ 2)
    linarith
  have hprodFiveB : 2 * (f : ℝ) * r ^ 2 * Real.log 5 ≤ 4 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlFive (by positivity : (0 : ℝ) ≤ f * r ^ 2)
    linarith
  have hnnSqrt : 0 ≤ (r : ℝ) * (f * r * Real.log (1 + 6 * √((f : ℝ) * r * q))) := by positivity
  have hnnFact : 0 ≤ (r : ℝ) * (2 * f * m * Real.log (3 * (2 * (f : ℝ) * m))) := by positivity
  have hnnLast : 0 ≤ (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
      Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) := by
    positivity
  have hnnFive : 0 ≤ (f : ℝ) * r ^ 2 * Real.log 5 := by positivity
  have hnnTwo : 0 ≤ (r : ℝ) * Real.log 2 := by positivity
  have hRlogTwo : (r : ℝ) * Real.log 2 ≤ r := mul_le_of_le_one_right (by positivity) hlTwo
  have hrfm_nonneg : 0 ≤ (r : ℝ) * (2 * f * m) := by positivity
  have hRnn : (0 : ℝ) ≤ r := by positivity
  constructor
  · linarith
  · linarith

end GlobalTheory.EtaAn
end
