module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdeg
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCompactificationInteriorPoint
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LeadMinorSmulOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquiv

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArch
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArchC
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArchB
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.RA

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

theorem rpow_of_sq {n d : ℝ} (hn : 0 < n) (h : n ^ 2 = d) (a : ℤ) : d ^ (-(a : ℝ) / 2) = n ^ (-a) := by
  rw [← h, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_intCast]
  congr 1
  push_cast
  ring

theorem move_pnorm (hσ : GoodEmb c σ) (hU : IsUnf U) {k : U.Comp} (x : (U.X k).dom) :
    ∃ (x₀ : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), (U.X k).IsOrtho x₀.1 ∧ FrBor t (U.un k x₀) (U.un k x) ∧
      ∀ a : WZ E, (U.X k).pnorm (laZ U a k) (fun _ => 1) x.1 =
        ∏ s : Σ τ, Fin (Dw.mult τ), ‖toC (t (some s) : CAt σ)‖ ^ (-a (s.1, s.2)) := by
  obtain ⟨x₀, t, ho, hb, hn⟩ := GF.move hσ hU x
  obtain ⟨f, hf, -⟩ := GF.letters hσ hU k
  obtain ⟨hbij, -, hconj, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  refine ⟨x₀, t, ho, hb, fun a => ?_⟩
  unfold Data.pnorm
  rw [norm_one, one_mul, ← Fintype.prod_prod_type']
  refine (Fintype.prod_equiv f _ _ fun s => ?_).symm
  have hpos : 0 < ‖toC (t (some s) : CAt σ)‖ := norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) (t (some s)))
  have hinv : Function.invFun (relab c σ) (relab c σ s.1) = s.1 := Function.leftInverse_invFun hbij.1 _
  rcases hf s with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩
  · have h1 := (hn s (f s).1 (f s).2).1 a2 a3
    have h2 : laZ U a k (f s).1 (f s).2 = a (s.1, s.2) := by
      unfold laZ
      rw [if_pos (by omega), a2, hinv, a3, Nat.add_sub_cancel_left]
    rw [h2]
    exact (rpow_of_sq hpos h1 _).symm
  · have e1 : conjEmb (f s).1.1 = relab c σ s.1 := by
      rw [a2]; exact ComplexEmbedding.involutive_conjugate E _
    have h1 := (hn s (f s).1 (f s).2).2 e1 (by omega)
    have h2 : laZ U a k (f s).1 (f s).2 = -a (s.1, s.2) := by
      unfold laZ
      rw [if_neg (by omega), e1, hinv, a3]
      congr 3
      omega
    rw [h2]
    have h3 := (inv_pow _ 2).trans ((congrArg (·⁻¹) h1).trans (inv_inv _))
    rw [rpow_of_sq (inv_pos.2 hpos) h3, neg_neg, inv_zpow, zpow_neg]

theorem lieFacZ_eq (Dw : Datum H) {x : ℝ} (hx : 0 < x) (a : WZ E) :
    lieFacZ Dw x a = ∏ s : Σ τ, Fin (Dw.mult τ), Real.sqrt (Real.pi * (2 * x)) ^ (-a (s.1, s.2)) := by
  have hp : 0 < Real.pi * (2 * x) := mul_pos Real.pi_pos (by linarith)
  have e : ∀ s : Σ τ, Fin (Dw.mult τ), Real.sqrt (Real.pi * (2 * x)) ^ (-a (s.1, s.2)) =
      Real.exp (-(a (s.1, s.2) : ℝ) / 2 * Real.log (2 * Real.pi * x)) := fun s => by
    rw [← rpow_of_sq (Real.sqrt_pos.2 hp) (Real.sq_sqrt hp.le), Real.rpow_def_of_pos hp, mul_comm]
    congr 3
    ring
  simp only [e]
  rw [← Real.exp_sum, lieFacZ, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_neg_distrib, Fintype.sum_sigma, neg_div]

theorem prod_root {M : Type} [CommMonoid M] (F : (Σ τ, Fin (Dw.mult τ)) → M) :
    ∏ s, F s = ∏ ρ : RootIx Dw, F (FinRd.labelSig Dw (HodgeCpt.rootIdx Dw ρ)) :=
  (Fintype.prod_bijective _ ((FinRd.labelSig_bijective Dw).comp (FinRd.rootIdx_bijective Dw)) _ _ fun _ => rfl).symm

end PositivityTheory.UnitarySelfGeneration.RA
end
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArchA
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.RA

open GlobalTheory.CompanionTheory.Ar.Rec.FinRd GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FrameValue
open GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest (hasVal_unique)

section HV

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω}

theorem aeval_conj (z : (Σ k, ι k) → ℂ) (g : MRing ι) :
    MvPolynomial.aeval (fun p => starRingEnd ℂ (z p)) g = starRingEnd ℂ (MvPolynomial.aeval z g) := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]

theorem hv_conj {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → ℂ} {w : ℂ} (h : Small.HasVal y a s z w) :
    Small.HasVal y a s (fun p => starRingEnd ℂ (z p)) (starRingEnd ℂ w) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, e, ?_, ?_⟩
  · rw [aeval_conj]
    exact (map_ne_zero _).2 hz0
  · rw [aeval_conj, aeval_conj, ez, map_mul]

theorem ptsOver_conj {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (h : z ∈ Small.ptsOver ℂ P) :
    (fun p => starRingEnd ℂ (z p)) ∈ Small.ptsOver ℂ P :=
  ⟨fun k => (h.1 k).imp fun _ hi => (map_ne_zero _).2 hi, fun f hf => by rw [aeval_conj, h.2 f hf, map_zero]⟩

theorem ptsOver_of_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (h : z ∈ mcPts P) : z ∈ Small.ptsOver ℂ P :=
  ⟨h.1, fun f hf => by
    have := h.2 f hf
    rwa [MvPolynomial.eval_map, ← algebraMap_int_eq, ← MvPolynomial.aeval_def] at this⟩

theorem valAt_of_hasVal {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {zC : Spec (CommRingCat.of ℂ) ⟶ X}
    {z : (Σ k, ι k) → ℂ} (hp : z ∈ Small.ptsOver ℂ (mCoordIdeal y)) (hz : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre zC)
    (hc : CoordsAt ξ y zC z) {s : Ω} {w : ℂ} (h : Small.HasVal y 0 s z w) : ValAt ξ zC s w := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hz0, ez⟩ := h
  have hdd : dg = dh := funext fun k => by have := hd k; simp at this; exact this
  subst hdd
  choose cc hcc using hc.1
  have hc' : ∀ k, z ⟨k, cc k⟩ ≠ 0 := fun k => (hcc k).ne_zero
  have hM : (∏ k, y ⟨k, cc k⟩ ^ dg k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc.2 k (cc k) (hcc k)).1
  have hMw : (∏ k, z ⟨k, cc k⟩ ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
  have hfy : MvPolynomial.aeval y f ≠ 0 := fun h0 => hz0 (hp.2 f (by
    show mConeMap y f = 0
    rw [Small.ReadFinTest.mConeMap_form y hf, h0]
    simp))
  have := CxVal.mul (GlobalTheory.CompanionTheory.Ar.PB.valAt_form hc hz hc' hg)
    (CxVal.inv (GlobalTheory.CompanionTheory.Ar.PB.valAt_form hc hz hc' hf) (div_ne_zero hz0 hMw))
  convert this using 1
  · rw [e]; field_simp
  · rw [ez]; field_simp

theorem hv_mono {z : (Σ k, ι k) → ℂ} (hp : z ∈ Small.ptsOver ℂ (mCoordIdeal y)) (ch : ∀ k, ι k)
    (hy : ∀ k, y ⟨k, ch k⟩ ≠ 0) (hz : ∀ k, z ⟨k, ch k⟩ ≠ 0) (d : K → ℤ) :
    Small.HasVal y d (∏ k, y ⟨k, ch k⟩ ^ d k) z (∏ k, z ⟨k, ch k⟩ ^ d k) := by
  classical
  have hsingle : ∀ k, Small.HasVal y (Pi.single k 1) (y ⟨k, ch k⟩) z (z ⟨k, ch k⟩) := fun k =>
    ⟨Pi.single k 1, 0, MvPolynomial.X ⟨k, ch k⟩, 1, TiePrimes.homog_X _, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one,
      fun j => by
        by_cases hj : j = k
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj], by simp, by simp, by simp⟩
  have := hv_prod Finset.univ fun k _ => hv_zpow hp (hsingle k) (hy k) (hz k) (d k)
  convert this using 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

end HV

section Frame

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [AddCommGroup L] [Module Ω L]

theorem isFrameAt_of_tri (V : Lat ξ L) (p : Cpt ξ) {r : ℕ} (b b₀ : Fin r → L) (T : Matrix (Fin r) (Fin r) Ω)
    (hfl : ∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) (hb : V.IsFrameAt b p) (hT : ∀ i, b i = ∑ j, T i j • b₀ j)
    (h1 : ∀ i j, T i j ∈ regAt ξ p) (h2 : ∀ i, T i i ≠ 0 ∧ (T i i)⁻¹ ∈ regAt ξ p) : V.IsFrameAt b₀ p := by
  obtain ⟨hi, htri⟩ := GlobalTheory.T.flag_equal_change_lower_triangular Ω L r b b₀ T hb.1 hfl hT
  refine ⟨hi, hb.2.trans (le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_))⟩
  · rintro _ ⟨i, rfl⟩
    rw [hT]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ (⟨T i j, h1 i j⟩ : regAt ξ p) (Submodule.subset_span ⟨j, rfl⟩)
  · have key : ∀ n : ℕ, ∀ i : Fin r, (i : ℕ) = n → b₀ i ∈ Submodule.span (regAt ξ p) (Set.range b) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i hi'
        have e : b₀ i = (T i i)⁻¹ • (b i - ∑ j ∈ Finset.univ.erase i, T i j • b₀ j) := by
          rw [hT i, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_right, smul_smul,
            inv_mul_cancel₀ (h2 i).1, one_smul]
        rw [e]
        refine Submodule.smul_mem _ (⟨_, (h2 i).2⟩ : regAt ξ p) (Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩)
          (Submodule.sum_mem _ fun j hj => ?_))
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
        · exact Submodule.smul_mem _ (⟨T i j, h1 i j⟩ : regAt ξ p) (ih j (hi' ▸ h) j rfl)
        · rw [htri i j h, zero_smul]
          exact Submodule.zero_mem _
    rintro _ ⟨i, rfl⟩
    exact key i i rfl

end Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem interior_of {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y₁ : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S y₁) (z : Sp ℂ ⟶ 𝔐.X) (v : Sp ℂ ⟶ Xo.XF c) (hv : v ≫ Y.j = z ≫ 𝔐.f) :
    𝔐.Interior z ∧ HodgeMetric.PolarisedAt 𝔐.t z := by
  constructor
  · have hmem : Y.jQ (v (IsLocalRing.closedPoint ℂ)) ∈
        Limits.pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    have e : Limits.pullback.fst Y.s (spMap β) (Y.jQ (v (IsLocalRing.closedPoint ℂ))) = 𝔐.f (GlobalTheory.CompanionTheory.Ar.centre z) := by
      have h2 : (v ≫ Y.jQ ≫ Limits.pullback.fst Y.s (spMap β))
          (IsLocalRing.closedPoint ℂ) = (z ≫ 𝔐.f) (IsLocalRing.closedPoint ℂ) := by
        rw [show v ≫ Y.jQ ≫ Limits.pullback.fst Y.s (spMap β) = z ≫ 𝔐.f from hv]
      simp only [Scheme.Hom.comp_apply] at h2
      exact h2
    have hab : 𝔐.f (GlobalTheory.CompanionTheory.Ar.centre z) ∈ abLocus Y.t.G := e ▸ hmem
    exact (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (GlobalTheory.CompanionTheory.Ar.centre z)).1 hab
  · obtain ⟨t', ⟨m₁⟩⟩ := exists_sab z 𝔐.t
    obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m m₁
    have cancel : ∀ (q : Sp ℂ ⟶ Y.X) (_ : q = v ≫ Y.jQ ≫ Limits.pullback.fst _ _) (_ : SABMap t' Y.t q),
        Nonempty (SABMap t' Y.oF.t v) := by
      intro q hq n; subst hq
      exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
    obtain ⟨m₃⟩ := cancel _ hv.symm n
    obtain ⟨w₂, g₂, -⟩ := m₃.lin
    obtain ⟨am, -⟩ := amplePt _ _ v _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB t'.PP.isLB ⟨w₂, g₂⟩ Y.oF.ample Y.oF.ktriv
    exact ⟨t', m₁, MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper, am⟩

variable {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y SS RM Fx}

set_option maxHeartbeats 400000 in
theorem pt_frame (Fr : Small.GenFrame Or) (F : Type) [Field F] [Algebra c.F F] (zC : Sp F ⟶ Or.𝔐.X) (q : TRing c.F)
    (φ : letI := Small.cstAlg Or; q.R →ₐ[c.F] RM.Ω) (yq : FrPt Xo c q.R)
    (hφ : letI := Small.cstAlg Or; FrMap φ yq Fr.y₀) (ψ : q.R →ₐ[c.F] F) (y : FrPt Xo c F)
    (hψ : FrMap ψ yq y) (hr : ∀ r, ValAt Or.𝔐.ξ zC (φ r) (ψ r)) :
    zC ≫ Or.𝔐.f = Small.ptY Y y ∧ ∀ s i, ∃ v : epsAt zC ⟶ Or.𝔐.t.G, Or.𝔐.M.ValAt zC (Or.Fl.b s i) v ∧
      v.left ≫ Or.𝔐.m.φ = Small.tanY Y y (Small.labelC s) (Small.labelFin Dw s i) := by
  letI := Small.cstAlg Or
  have hgen : GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre zC := Or.𝔐.all _
  let P : Cpt Or.𝔐.ξ := ⟨GlobalTheory.CompanionTheory.Ar.centre zC, hgen⟩
  have hinj : Function.Injective (genMap Or.𝔐.ξ P) := Or.𝔐.tie.gen.inj P
  have hreg : ∀ r, ∃ s', genMap Or.𝔐.ξ P s' = φ.toRingHom r ∧
      (Scheme.stalkClosedPointTo zC).hom s' = ψ.toRingHom r := fun r => by
    obtain ⟨h', s', hs, hs'⟩ := hr r
    exact ⟨s', hs, hs'⟩
  obtain ⟨θ, hθ1, hθ2⟩ := exists_factor _ _ hinj φ.toRingHom ψ.toRingHom hreg
  have hsep : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have he : Or.𝔐.X.fromSpecStalk P.1 ≫ Or.𝔐.f = spMap θ ≫ Small.ptY Y yq := by
    refine pts_eq (genMap Or.𝔐.ξ P) hinj Y.s ?_
    rw [← Category.assoc, ← Category.assoc]
    have e1 : spMap (genMap Or.𝔐.ξ P) ≫ Or.𝔐.X.fromSpecStalk P.1 = Or.𝔐.ξ := LieTangent.spec_genMap _ _
    rw [e1, ← Fr.pt_eq, Small.ptY_map Y hφ, ← hθ1, LieTangent.spec_comp]
  refine ⟨?_, fun s i => ?_⟩
  · have e0 : spMap (Scheme.stalkClosedPointTo zC).hom ≫ Or.𝔐.X.fromSpecStalk P.1 = zC := LieTangent.spec_centre zC
    have e1 : spMap (Scheme.stalkClosedPointTo zC).hom ≫ spMap θ = spMap ψ.toRingHom :=
      (LieTangent.spec_comp _ _).trans (congrArg (fun g => spMap g) hθ2)
    have e2 : Small.ptY Y y = spMap ψ.toRingHom ≫ Small.ptY Y yq := Small.ptY_map Y hψ
    refine (congrArg (· ≫ Or.𝔐.f) e0.symm).trans ((Category.assoc _ _ _).trans ?_)
    exact (congrArg (fun g => _ ≫ g) he).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Small.ptY Y yq) e1).trans e2.symm))
  obtain ⟨v, hvt, hv'⟩ := exists_tan_lift Or.𝔐.m.cart (Or.𝔐.X.fromSpecStalk P.1) θ (Small.ptY Y yq)
    (Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) (Small.tanY_hom Y _ _ _) (tanY_one Y _ _ _) he
  have hext : Or.𝔐.M.Extends P (Or.Fl.b s i) v := by
    refine extends_of Or.𝔐.m.cart _ P _ v hvt ?_
    have e2 := Small.tanY_map Y hφ (Small.labelC s) (Small.labelFin Dw s i)
    have e3 := Fr.tan_eq s i
    have e4 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap (genMap Or.𝔐.ξ P)) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
          Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
      rw [← Category.assoc, spec_dual_comp, hθ1]
    exact e3.symm.trans (e2.trans (e4.trans (congrArg (fun u => _ ≫ u) hv'.symm)))
  obtain ⟨EC, _, _, ⟨MC⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Or.𝔐.X Or.𝔐.t.G F zC
  have hb := LieTangent.isTanAt_base _ (LieTangent.spec_centre zC) hvt
  obtain ⟨w, hw⟩ := MC.onto _ hb
  refine ⟨MC.pt w, (Or.𝔐.M.valAt_iff _ _ _).2 ⟨hgen, v, hext, hw⟩, ?_⟩
  have e5 : (MC.pt w).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo zC).hom) ≫ v.left :=
    congrArg (fun u => u.left) hw
  have e6 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo zC).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫
        Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := by
    have e7 : spMap (GlobalTheory.CompanionTheory.Ar.dualMap (Scheme.stalkClosedPointTo zC).hom) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) =
        spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) := (spec_dual_comp θ _).trans (by rw [hθ2])
    exact (congrArg (fun u => u ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i)) e7.symm).trans
      (Category.assoc _ _ _)
  have e8 : Small.tanY Y y (Small.labelC s) (Small.labelFin Dw s i) =
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψ.toRingHom) ≫ Small.tanY Y yq (Small.labelC s) (Small.labelFin Dw s i) := Small.tanY_map Y hψ _ _
  refine Eq.trans ?_ (e8.trans e6).symm
  rw [e5]
  exact (Category.assoc _ _ _).trans (congrArg (fun u => _ ≫ u) hv')

end PositivityTheory.UnitarySelfGeneration.RA
end
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open AlgebraicGeometry CategoryTheory
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.RA

open GlobalTheory.CompanionTheory.Ar.Rec.FinRd
open GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest (hasVal_unique)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y SS RM Fx}

theorem root_val {Fr : Small.GenFrame Or} {A : Subring RM.Ω} (hG : GoodRing Fr A) {z : (Σ k, RM.ι k) → ℂ}
    (hz : z ∈ Small.ptsOver ℂ (mCoordIdeal RM.y)) (ev : A →+* ℂ)
    (hev : ∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) {zC : Sp ℂ ⟶ Or.𝔐.X}
    (hc : CoordsAt Or.𝔐.ξ RM.y zC z) (hI : Or.𝔐.Interior zC) (ρ : RootIx Dw) {ν : ℝ}
    (hν : Or.𝔐.M.IsGrNorm Or.𝔐.t.PP.L (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1) (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1)
      (HodgeCpt.rootIdx Dw ρ).2 zC 1 ν) :
    (∃ w : ℂ, Small.HasVal RM.y (RM.xdeg ρ) (Or.e ρ)⁻¹ z w ∧
      ‖w‖ = ν ^ HodgeCpt.rootSgn Dw ρ * (Or.sing ρ).h z) ∧
    (Or.sing ρ).h (fun p => starRingEnd ℂ (z p)) = (Or.sing ρ).h z := by
  have hS := Or.hodge ρ zC z hc hI _ _ hν
  obtain ⟨ch, hch⟩ := hS.exists_chart
  obtain ⟨u, hu, eu⟩ := hS.2.2 ch hch
  constructor
  · have hy : ∀ k, RM.y ⟨k, ch k⟩ ≠ 0 := fun k => (hc.2 k (ch k) (IsUnit.mk0 _ (hch k))).1
    have hm := (hG.2.2.1 ρ ch hy).2
    have h1 := hev ⟨_, hm⟩
    have h2 := valAt_of_hasVal hz (Or.𝔐.all _) hc h1
    rw [one_zpow, one_div, Or.sing_deg] at hu
    rw [CxVal.unique h2 hu] at h1
    have h3 := hv_mul h1 (hv_mono hz ch hy hch (RM.xdeg ρ))
    have hM : (∏ k, RM.y ⟨k, ch k⟩ ^ RM.xdeg ρ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
    refine ⟨_, by
      convert h3 using 1
      · rw [zero_add]
      · show _ = (_ * _)⁻¹ * _
        rw [mul_inv, mul_right_comm, inv_mul_cancel₀ hM, one_mul], ?_⟩
    rw [eu, norm_mul, norm_prod, Or.sing_deg]
    simp only [norm_zpow]
  · have hI' : Or.𝔐.Interior (HodgeLine.cj zC) := by
      unfold HodgeCpt.Interior
      rw [HodgeLine.centre_cj]
      exact hI
    have hS' := Or.hodge ρ (HodgeLine.cj zC) _ (HodgeLine.coordsAt_conj hc) hI' _ _
      (HodgeLine.isGrNorm_conj Or.𝔐.t Or.𝔐.M _ hν)
    obtain ⟨u', hu', eu'⟩ := hS'.2.2 ch fun k => (map_ne_zero _).2 (hch k)
    rw [CxVal.unique hu' (HodgeLine.valAt_conj hu)] at eu'
    simp only [Complex.norm_conj, RCLike.norm_conj] at eu'
    exact mul_left_cancel₀ (zpow_pos hν.pos _).ne' (eu'.trans eu.symm)

theorem norm_alg {I : Type} [Fintype I] (T T₀ h K : I → ℝ) (sg ex n : I → ℤ) (hT : ∀ i, 0 < T i)
    (hs : ∀ i, sg i * sg i = 1) (hn : ∀ i, n i = -(sg i * ex i)) :
    (∏ i, T i ^ ex i) * ∏ i, ((K i * (T i * T₀ i)) ^ sg i * h i) ^ n i =
      (∏ i, h i ^ n i) * (∏ i, K i ^ (-ex i)) * ∏ i, T₀ i ^ (-ex i) := by
  simp only [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : sg i * n i = -ex i := by rw [hn]; linear_combination (-ex i) * hs i
  rw [mul_zpow, ← zpow_mul, e, mul_zpow, mul_zpow, zpow_neg (T i)]
  have := (zpow_pos (hT i) (ex i)).ne'
  field_simp

set_option maxHeartbeats 800000 in
theorem core {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c}
    (hL : CompLaws U h e) {x : ℝ} (hx : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x)
    {Fr : Small.GenFrame Or} {Z : Comp Xo c} (Rd : Reading Fr h Z) {A : Subring RM.Ω} (hG : GoodRing Fr A)
    {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {z : (Σ k, RM.ι k) → ℂ}
    (hz : z ∈ Small.ptsOver ℂ (mCoordIdeal RM.y)) (ev : A →+* ℂ)
    (hev : ∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x))
    (hcst : ∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) :
    (∀ ρ, (Or.sing ρ).h (fun p => starRingEnd ℂ (z p)) = (Or.sing ρ).h z) ∧
    ∃ k, Over (U σ) (e Z) k ∧ ∃ y ∈ ((U σ).X k).dom, ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ),
      (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∃ θ : ℂ,
        ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw x a *
          ((U σ).X k).pnorm (laZ (U σ) a k) (fun _ => 1) y ∧
        ∀ f ∈ secZ Xo c a, Small.HasVal RM.y (Top.combLine (RM.line 1) n').a
          (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * rdU (U σ) f k y) := by
  letI := Small.cstAlg Or
  have hU := hL.unf σ hσ
  obtain ⟨zC, ⟨hgen, hc⟩, -⟩ := (GlobalTheory.T.local_ring_points_existsUnique Or.𝔐.X RM.Ω Or.𝔐.ξ RM.K RM.ι RM.y Or.𝔐.tie ℂ).1 z
    (fun k => (hz.1 k).imp fun _ hi => IsUnit.mk0 _ hi) hz.2
  have hva : ∀ a : A, ValAt Or.𝔐.ξ zC (a : RM.Ω) (ev a) := fun a => valAt_of_hasVal hz hgen hc (hev a)
  obtain ⟨q, φ, yq, hφ, hφA⟩ := hG.2.1
  let ψ₀ : q.R →+* ℂ := ev.comp (φ.toRingHom.codRestrict A hφA)
  let ψ : q.R →ₐ[c.F] CAt σ :=
    { (show q.R →+* CAt σ from ψ₀) with
      commutes' := fun a => by
        have h1 := hev ⟨φ (algebraMap c.F q.R a), hφA _⟩
        have h2 : φ (algebraMap c.F q.R a) = Or.𝔐.cst a := φ.commutes a
        have h3 : Small.HasVal RM.y 0 (φ (algebraMap c.F q.R a)) z (σ a) := by rw [h2]; exact hcst a
        exact hasVal_unique hz h1 h3 }
  obtain ⟨y, hψ⟩ := GlobalTheory.FramedBaseChange.bcEx_all E H Dw l Xo c σ q yq ψ
  obtain ⟨hpt, htan⟩ := @pt_frame E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr ℂ _ σ.toAlgebra zC q φ yq hφ ψ y hψ fun r => hva ⟨φ r, hφA r⟩
  obtain ⟨hI, hpol⟩ := interior_of Or.𝔐 zC (Small.ptF (S := CAt σ) y) hpt.symm
  obtain ⟨k, x₁, t, ht⟩ := hU.2.2.1 y
  obtain ⟨x₀, t₀, ho, h0, hpn⟩ := move_pnorm hσ hU x₁
  have hB' := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) ((U σ).un k x₀) ((U σ).un k x₁) y).2.2.1 t₀ t h0 ht
  have hx0 : 0 < x := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hx σ hσ k τ]
    exact norm_pos_iff.2 ((map_ne_zero _).2 ((U σ).X k).ξ0_ne)
  have hnorm : ∀ ρ : RootIx Dw, Or.𝔐.M.IsGrNorm Or.𝔐.t.PP.L (Or.𝔐.V (HodgeCpt.rootIdx Dw ρ).1)
      (Or.Fl.b (HodgeCpt.rootIdx Dw ρ).1) (HodgeCpt.rootIdx Dw ρ).2 zC 1
      (Real.sqrt (Real.pi * (2 * x)) * (‖toC (t (Small.rootFrameIx Dw ρ) : CAt σ)‖ *
        ‖toC (t₀ (Small.rootFrameIx Dw ρ) : CAt σ)‖)) := fun ρ => by
    have hr := ρ.2.2
    obtain ⟨b, T, hfl, hfr, hT, hTA, hTd⟩ := hG.2.2.2 (HodgeCpt.rootIdx Dw ρ).1 ⟨_, hgen⟩
    have hfr' := isFrameAt_of_tri _ _ b _ T hfl hfr hT (fun i j => HodgeLine.mem_of_valAt (hva ⟨_, hTA i j⟩) hgen)
      fun i => ⟨(hTd i).1, HodgeLine.mem_of_valAt (hva ⟨_, (hTd i).2⟩) hgen⟩
    obtain ⟨Γ, hΓ, hP⟩ := HodgeMetric.GramFrame.exists_gramAt_posDef_of_frame Or.𝔐 zC hgen hpol _ _ hfr'
    obtain ⟨z', v, hz', hv, hIP⟩ := GF.transport Or.𝔐 zC y hpt _ (Small.labelFin Dw (HodgeCpt.rootIdx Dw ρ).1) _
      (htan _) Γ hΓ
    have key := GF.gram hσ hU (by omega) x₀ ho y _ hB' _ _ (Small.mult_labelC Dw (HodgeCpt.rootIdx Dw ρ).1) z' hz' v hv
      Γ hIP (HodgeCpt.rootIdx Dw ρ).2
    have hmul : ‖toC ((t * t₀) (Small.rootFrameIx Dw ρ) : CAt σ)‖ =
        ‖toC (t (Small.rootFrameIx Dw ρ) : CAt σ)‖ * ‖toC (t₀ (Small.rootFrameIx Dw ρ) : CAt σ)‖ :=
      norm_mul (toC (t (Small.rootFrameIx Dw ρ) : CAt σ)) (toC (t₀ (Small.rootFrameIx Dw ρ) : CAt σ))
    rw [hx σ hσ] at key
    exact ⟨hgen, _, Γ, fun _ => rfl, hfr', by simp, hΓ, hP, (key.trans (congrArg _ hmul)).symm⟩
  have hroot := fun ρ => root_val hG hz ev hev hc hI ρ (hnorm ρ)
  refine ⟨fun ρ => (hroot ρ).2, ?_⟩
  choose w hw hwn using fun ρ => (hroot ρ).1
  have htpos : ∀ (t : Ix Dw → (CAt σ)ˣ) j, 0 < ‖toC (t j : CAt σ)‖ := fun t j =>
    norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) (t j))
  have hw0 : ∀ ρ, w ρ ≠ 0 := fun ρ => by
    rw [← norm_pos_iff, hwn]
    exact mul_pos (zpow_pos (hnorm ρ).pos _) ((Or.sing ρ).pos z hz.1)
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hsec : ∀ a : WZ E, ∀ f ∈ secZ Xo c a, Small.HasVal RM.y 0 (Fr.rd f) z
      ((∏ j, toC (t j : CAt σ) ^ exZ Dw a j) * rdU (U σ) f k x₁.1) := fun a f hf => by
    have hrd : Fr.rd f = φ (f q yq) := Fr.rd_eq_of_frMap hL.evalWD hf.1 q φ yq hφ
    have hft : Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y := ⟨q, ψ, yq, hψ⟩
    have hy : evR Xo c f y = ψ (f q yq) := by
      unfold evR evalAt
      rw [dif_pos hft]
      exact hL.evalWD f hf.1 (CAt σ) _ q _ ψ _ yq y hft.choose_spec.choose_spec.choose_spec hψ
    have hbor : evR Xo c f y = ((∏ i, t i ^ exZ Dw a i : (CAt σ)ˣ) : CAt σ) * evR Xo c f ((U σ).un k x₁) :=
      evalAt_bor_zpow (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.1 (exZ Dw a) hf.1
        (fun p t y y' hb => by rw [hf.2 p t y y' hb, Units.coe_prod]) (CAt σ) t _ y (hL.unTest σ hσ k x₁) hft ht
    have h1 := hev ⟨φ (f q yq), hφA _⟩
    have h2 : ev ⟨φ (f q yq), hφA _⟩ = (∏ j, toC (t j : CAt σ) ^ exZ Dw a j) * rdU (U σ) f k x₁.1 := by
      refine (show _ = toC (ψ (f q yq)) from rfl).trans ?_
      rw [← hy, hbor]
      have e1 : rdU (U σ) f k x₁.1 = toC (evR Xo c f ((U σ).un k x₁)) := dif_pos x₁.2
      have e2 : toC ((∏ i, t i ^ exZ Dw a i : (CAt σ)ˣ) : CAt σ) = ∏ j, toC (t j : CAt σ) ^ exZ Dw a j :=
        (Units.coe_prod (M := ℂ) (fun i => t i ^ exZ Dw a i) _).trans
          (Finset.prod_congr rfl fun j _ => Units.val_zpow_eq_zpow_val (α := ℂ) (t j) _)
      rw [e1, ← e2]
      rfl
    rw [hrd, ← h2]
    exact h1
  refine ⟨k, ?_, x₁.1, x₁.2, fun a n' hn => ?_⟩
  · obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.T.compactification_comp_equiv E H Dw l Xo c r U h e hL σ hσ
    refine (hκ1 Z k).2 (by_contra fun hne => ?_)
    have he0 : e Z ∈ secZ Xo c 0 := by
      have h1 := hL.e_sec Z
      rw [← secZ_nat] at h1
      exact h1
    have hex : ∀ i, exZ Dw (0 : WZ E) i = 0 := fun i => by cases i <;> rfl
    have hrd : Fr.rd (e Z) = 1 := by
      rw [Rd.rd_eq 0 (e Z) he0, (hL.e_val Z).1, map_one]
      simp [hex]
    have hv := hsec 0 _ he0
    rw [hrd, (hκ2 Z k hne _ x₁.2).1, mul_zero] at hv
    exact zero_ne_one (hasVal_unique hz hv hv_one)
  have hnone : n' none = 0 := by
    have h1 := hn none
    have h2 : RM.coef (towerWt Dw a) 0 none = 0 := by simp [Top.RootModel.coef]
    rw [h2] at h1
    exact_mod_cast h1
  have hsome : ∀ r, n' (some r) = -(HodgeCpt.rootSgn Dw r * exZ Dw a (Small.rootFrameIx Dw r)) := fun r => by
    have h1 := hn (some r)
    have h2 : RM.coef (towerWt Dw a) 0 (some r) = -towerWt Dw a r.1 r.2 := rfl
    rw [h2, towerWt_root] at h1
    exact_mod_cast h1
  have hdeg : (Top.combLine (RM.line 1) n').a = 0 + ∑ r, n' (some r) • RM.xdeg r := by
    show ∑ j, n' j • (RM.line 1 j).a = _
    rw [Fintype.sum_option, hnone, zero_smul]
    refine congrArg _ (Finset.sum_congr rfl fun r _ => ?_)
    show n' (some r) • (RM.x 1 r).a = _
    rw [RM.x_deg]
  have hev' : ∀ r, Or.e r ^ (-n' (some r)) = (Or.e r)⁻¹ ^ n' (some r) := fun r => by
    rw [zpow_neg, inv_zpow]
  have hrt : ∀ r ∈ (Finset.univ : Finset (RootIx Dw)), Small.HasVal RM.y (n' (some r) • RM.xdeg r)
      ((Or.e r)⁻¹ ^ n' (some r)) z (w r ^ n' (some r)) := fun r _ =>
    hv_zpow hz (hw r) (inv_ne_zero (Or.lines r).1) (hw0 r) _
  refine ⟨(∏ j, toC (t j : CAt σ) ^ exZ Dw a j) * ∏ r, w r ^ n' (some r), ?_, fun f hf => ?_⟩
  · rw [norm_mul, norm_prod, norm_prod]
    simp only [norm_zpow, hwn]
    rw [prod_exZ Dw a fun j => ‖toC (t j : CAt σ)‖, hpn, lieFacZ_eq Dw hx0, prod_root, prod_root]
    exact norm_alg _ _ _ _ _ _ _ (fun _ => htpos t _) (rootSgn_mul_self Dw) hsome
  · rw [hdeg, mul_right_comm]
    simp only [hev']
    exact hv_mul (hsec a f hf) (hv_prod Finset.univ hrt)

end PositivityTheory.UnitarySelfGeneration.RA
end
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.UnitarySelfGeneration

theorem y_read_arch : (Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (σ : c.F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal RM.y), (∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) → MvPolynomial.aeval z u ≠ 0 → ∃ k, Over (U (goodOf c σ)) (e Z) k ∧ ∃ y ∈ ((U (goodOf c σ)).X k).dom, ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∃ θ : ℂ, ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw x a * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y ∧ ∀ f ∈ secZ Xo c a, (GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * rdU (U (goodOf c σ)) f k y)) ∧ (¬ GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * starRingEnd ℂ (rdU (U (goodOf c σ)) f k y)))) := by
  intro _ E _ _ _ H Dw l Xo c r U h e hL x hx O _ β Y SS RM Sys Fx Or Fr Z Rd
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective
  obtain ⟨B, hB⟩ := GlobalTheory.T.root_origin_frame_height E H Dw l Xo c O β Y SS RM Sys Fx Or Fr
  obtain ⟨u, hu, hA⟩ := GlobalTheory.T.form_off_specialization_ring RM.K RM.ι RM.Ω RM.y RM.birational B
  refine ⟨u, hu, fun σ z hz hcst hzu => ?_⟩
  have hz' := RA.ptsOver_of_mcPts hz
  by_cases hσ : GoodEmb c σ
  · have eg : goodOf c σ = σ := if_pos hσ
    rw [eg]
    obtain ⟨A, ev, hBA, hQ, hev⟩ := hA ℂ z hz' hzu
    obtain ⟨-, k, hk, y, hy, hh⟩ := RA.core hL hx Rd (hB A hBA hQ) hσ hz' ev hev hcst
    refine ⟨k, hk, y, hy, fun a n' hn => ?_⟩
    obtain ⟨θ, h1, h2⟩ := hh a n' hn
    exact ⟨θ, h1, fun f hf => ⟨fun _ => h2 f hf, fun hn => absurd hσ hn⟩⟩
  · have eg : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    have hg := goodEmb_goodOf c σ
    have hcst' : ∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) (fun p => starRingEnd ℂ (z p)) (goodOf c σ t) := fun t => by
      rw [eg]
      exact RA.hv_conj (hcst t)
    have hz'' := RA.ptsOver_conj hz'
    obtain ⟨A, ev, hBA, hQ, hev⟩ := hA ℂ _ hz'' (by rw [RA.aeval_conj]; exact (map_ne_zero _).2 hzu)
    obtain ⟨hc, k, hk, y, hy, hh⟩ := RA.core hL hx Rd (hB A hBA hQ) hg hz'' ev hev hcst'
    simp only [Complex.conj_conj] at hc
    refine ⟨k, hk, y, hy, fun a n' hn => ?_⟩
    obtain ⟨θ, h1, h2⟩ := hh a n' hn
    refine ⟨starRingEnd ℂ θ, ?_, fun f hf => ⟨fun hn => absurd hn hσ, fun _ => ?_⟩⟩
    · rw [Complex.norm_conj, h1]
      simp only [← hc]
    · have h3 := RA.hv_conj (h2 f hf)
      simp only [Complex.conj_conj, map_mul] at h3
      exact h3

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentNormConstantModels
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.component_norm_constant_models : (Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (σ : c.F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal RM.y), (∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) → MvPolynomial.aeval z u ≠ 0 → ∃ k, Over (U (goodOf c σ)) (e Z) k ∧ ∃ y ∈ ((U (goodOf c σ)).X k).dom, ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∃ θ : ℂ, ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw x a * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y ∧ ∀ f ∈ secZ Xo c a, (GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * rdU (U (goodOf c σ)) f k y)) ∧ (¬ GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * starRingEnd ℂ (rdU (U (goodOf c σ)) f k y)))) := by
  first | exact @PositivityTheory.UnitarySelfGeneration.y_read_arch | exact PositivityTheory.UnitarySelfGeneration.y_read_arch
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentNormConstantModelsStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_norm_constant_models : (Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (σ : c.F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal RM.y), (∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) → MvPolynomial.aeval z u ≠ 0 → ∃ k, Over (U (goodOf c σ)) (e Z) k ∧ ∃ y ∈ ((U (goodOf c σ)).X k).dom, ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∃ θ : ℂ, ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw x a * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y ∧ ∀ f ∈ secZ Xo c a, (GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * rdU (U (goodOf c σ)) f k y)) ∧ (¬ GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * starRingEnd ℂ (rdU (U (goodOf c σ)) f k y)))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.component_norm_constant_models | exact GlobalTheory.CompanionTheory.Relay.component_norm_constant_models | (intros; apply GlobalTheory.CompanionTheory.Relay.component_norm_constant_models <;> assumption)
end
