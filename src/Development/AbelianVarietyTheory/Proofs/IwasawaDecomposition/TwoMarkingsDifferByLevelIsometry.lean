module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicSupportedAtBadPrimePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedInvMulLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometry
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor.TwoMarkings

open GlobalTheory.ShFam.OpenReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {a : CxFr Z σ}

theorem linearIndependent_dirs {i : Fin Fu.n} {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ}
    {y : Sp ℂ ⟶ Xo.XF c} (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hy : y ≫ pullback.fst _ _ = Fu.u i P) (hj : y ≫ Z.jQ = a.1.1)
    {v₀ : Letter Dw → (Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left)}
    (h1 : ∀ z, v₀ z ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (h2 : ∀ z, v₀ z ≫ Z.m.φ = a.2.v z.1 z.2)
    (h3 : ∀ z, IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ z ≫ Z.m0.toSABMap.φ)) :
    LinearIndependent ℂ W := by
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hj]
  have hty : ∀ z j, W z j ≠ 0 → (e j).1 = z.1 := fun z =>
    (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ z.1 (h3 z)).1 fun b =>
      (eig_iff Z.m0.toSABMap (h1 z) b _).2 ((eig_iff Z.m (h1 z) b _).1 (h2 z ▸ a.2.eig z.1 z.2 b))
  obtain ⟨t1, t2, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  obtain ⟨v, hv, -⟩ := t2 0
  obtain ⟨v', k1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
    (by rw [(t1 _ _ hv).1, ← hy, Category.assoc])
  rw [Fintype.linearIndependent_iff]
  rintro cf hc ⟨τ, k⟩
  have hb := a.2.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx k1).2 ((tan_iff Z.m0.toSABMap hy k1).1 (t1 _ _ hv)))
    fun b => (eig_iff Z.m k1 b _).2 ((eig_iff Z.m0.toSABMap k1 b _).1
      ((GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP _ _ τ hv).2 (fun j hj => absurd rfl hj) b))
  have e1 : a.2.v τ = fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hb
  have hcomb : ∀ d : Fin (Dw.mult τ) → ℂ, ∑ k, d k • W ⟨τ, k⟩ = 0 →
      IsCombAtG Z.t (a.1.1 ≫ genι Z) (fun k => v₀ ⟨τ, k⟩ ≫ Z.m.φ) d (v' ≫ Z.m.φ) := fun d hd =>
    (comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) d k1).2 ((comb_iff Z.m0.toSABMap hy (fun k => h1 ⟨τ, k⟩) d k1).1
      ((GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP _ _ _ (fun k => h3 ⟨τ, k⟩) d _).2 (hd ▸ hv)))
  have hτ : ∑ k, cf ⟨τ, k⟩ • W ⟨τ, k⟩ = 0 := by
    funext j
    have hz : ∀ ρ, (e j).1 ≠ ρ → (∑ k, cf ⟨ρ, k⟩ • W ⟨ρ, k⟩) j = 0 := fun ρ hρ => by
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [Pi.smul_apply, by_contra fun h => hρ (hty ⟨ρ, k⟩ j h), smul_zero]
    by_cases h : (e j).1 = τ
    · have := congrFun hc j
      rw [Fintype.sum_sigma, Finset.sum_apply, Finset.sum_eq_single τ (fun ρ _ hρ => hz ρ (h ▸ hρ.symm)) (by simp)] at this
      exact this
    · exact hz τ h
  exact congrFun (hb.unique (hcomb _ hτ) (hcomb 0 (by simp))) k

theorem per_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), (∀ i j Q Q', Per Fu a i Q → Per Fu a j Q' → i = j) ∧ ∀ i Q Q', Per Fu a i Q → Per Fu a i Q' → ∃ gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La, IsIsom (Fu.Di i) gm ∧ IsLev l (Fu.Di i) gm ∧ ∀ v, Q' (gm v) = Q v := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu a
  haveI := Z.jQ_open
  refine ⟨?_, ?_⟩
  · rintro i j Q Q' ⟨P, W, y, hP, hy, hj, -⟩ ⟨P', W', y', hP', hy', hj', -⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    exact Fu.disj i j P P' hP hP' (hy.symm.trans hy')
  · rintro i Q Q' ⟨P, W, y, hP, hy, hj, hv, hQ⟩ ⟨P', W', y', hP', hy', hj', hv', hQ'⟩
    obtain rfl : y = y' := (cancel_mono Z.jQ).1 (hj.trans hj'.symm)
    choose v₀ h1 h2 h3 using hv
    choose v₁ k1 k2 k3 using hv'
    obtain rfl : v₀ = v₁ := funext fun z =>
      Z.m.cart.1.hom_ext ((h2 z).trans (k2 z).symm) ((h1 z).trans (k1 z).symm)
    obtain ⟨gam, h, g1, g2, g3, g4⟩ := (Fu.fibre i P P' hP hP').1 (hy.symm.trans hy')
    have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
      LinearMap.toMatrix'_mulVec _ z
    obtain ⟨-, -, h5⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ Fu i P P' gam
      (LinearMap.toMatrix' h.toLinearMap) hP hP' g1 g2 g3 (fun a => by rw [hm, g4])
    simp only [hm] at h5
    obtain ⟨t1, -, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P' hP'
    have hW : ∀ z, h (W z) = W' z := fun z => (t3 _ (t1 _ _ (k3 z))).unique
      ((GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ Fu i P hP i P' h.toLinearMap hP' h5 _ _).1 (h3 z)) (k3 z)
    refine ⟨gam, g1, g2, fun v => funext fun z => ?_⟩
    refine Fintype.linearIndependent_iffₛ.1 (linearIndependent_dirs hP' hy' hj' k1 k2 k3) _ _ ?_ z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hQ', g4, hQ, map_sum]
    simp only [map_smul, hW]

end GlobalTheory.ShFam.Hor.TwoMarkings
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_markings_differ_by_level_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), (∀ i j Q Q', Per Fu a i Q → Per Fu a j Q' → i = j) ∧ ∀ i Q Q', Per Fu a i Q → Per Fu a i Q' → ∃ gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La, IsIsom (Fu.Di i) gm ∧ IsLev l (Fu.Di i) gm ∧ ∀ v, Q' (gm v) = Q v := by
  first | exact @GlobalTheory.ShFam.Hor.TwoMarkings.per_unique | exact GlobalTheory.ShFam.Hor.TwoMarkings.per_unique | (intros; apply GlobalTheory.ShFam.Hor.TwoMarkings.per_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsLOfCopy
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.DatCopy

namespace GlobalTheory.Mem.R3.LiftCopy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Three

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} {R : RealDat3 a.D A Ks} {F : Face3 a.D A}

theorem holdsL_tr (h : HoldsL R F) : letI := alg b iK; HoldsL (real3 b R) (face3 b F) := by
  let := alg b iK
  constructor
  case heckeR => exact (by with_unfolding_all exact (h.heckeR :))
  case heckeL => exact (by with_unfolding_all exact (h.heckeL :))
  case hecke =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 =>
        (∃ hE, Cx.HeckeIntertwiningDefinite A X hE) ∧ ∃ hW, Cx.HeckeIntertwiningLifts A X hW)
        (toCx3_eq b R F)).mp h.hecke :)
  case gUnit => exact (by with_unfolding_all exact (h.gUnit :))
  case gEquiv =>
    with_unfolding_all
      exact ((congrArg (fun u : Parts R =>
        Cx.GEquiv3 A (cxW R F u) (R.gEx F) ∧
          Cx.LiftGroupEquivariance A (cxW R F u) (R.gWx F))
        (parts_eq b R F)).mp h.gEquiv :)
  case block =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => X.zs.InBlock)
        (toCx3_eq b R F)).mp h.block :)
  case liftTest =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTest X)
        (toCx3_eq b R F)).mp h.liftTest :)
  case liftTestB =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTestB X false)
        (toCx3_eq b R F)).mp h.liftTestB :)
  case liftOnto =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 =>
        ∀ hW, Cx.HeckeIntertwiningLifts A X hW → U2.OntoC A X F.P0 F.ψ0 F.P1 F.ψ1 hW)
        (toCx3_eq b R F)).mp h.liftOnto :)
  case unif => exact (by with_unfolding_all exact (h.unif :))
  case mLat =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => X.MLat false)
        (toCx3_eq b R F)).mp h.mLat :)
  case levW =>
    with_unfolding_all
      exact ((congrArg (fun u : Parts R =>
        Cx.LevelTypeOfLifts A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc)
          (Sp := F.Sp) (Zsc := F.Zsc) (R.gWx F) false F.P0 F.ψ0)
        (parts_eq b R F)).mp h.levW :)
  case thmA =>
    with_unfolding_all
      exact ((congrArg (fun W : type_of% R.Wp3 => ∀ i t,
        Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (W i) fun p => R.lam3 i t p A.A.v0)
        (wp3_apply_eq_sq_mul_sub_sq_mul b R)).mp h.thmA :)
  case sumW =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => X.PartsW false)
        (toCx3_eq b R F)).mp h.sumW :)
  case aux => exact (by with_unfolding_all exact ((realAdelicInertTransport_furtherRows b h.aux) :))
  case ok => exact (by with_unfolding_all exact (h.ok :))
  case sep => exact (by with_unfolding_all exact (h.sep :))

theorem holdsL_back (h : letI := alg b iK; HoldsL (real3 b R) (face3 b F)) : HoldsL R F := by
  have h2 := holdsL_tr (a := b) a (iK := alg b iK) h
  exact (by with_unfolding_all exact ((cast (congrArg (fun R' : RealDat3 a.D A Ks => HoldsL R' F) (twice_eq b R).symm) ((h2))) : _))

end Three

section Dat

variable {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {Tw : Top.TwDat B} {Wt : Set B.places.Pl}
  (s : SameGrp a b) {z : Dat a.st I hX Tw Wt}

theorem holdsL_of_copy (h : HoldsL (DatCopy.copy b s z).R (DatCopy.copy b s z).F) :
    HoldsL z.R z.F :=
  holdsL_back b (iK := z.alg) (by
    with_unfolding_all exact (h :))

end Dat

end GlobalTheory.Mem.R3.LiftCopy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismsNearSameAdelicCongruent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismsNearSameAdelicCongruent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear

theorem entries_le_of_add_mul {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) K) (c : WithZero (Multiplicative ℤ)) (hA : ∀ r s, v (A r s) < 1)
    (h : ∀ r s, v ((D + A * D) r s) ≤ c) (r s : Fin n) : v (D r s) ≤ c := by
  obtain ⟨p, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v (D p.1 p.2)) ⟨(r, s), Finset.mem_univ _⟩
  refine (hmax (r, s) (Finset.mem_univ _)).trans ?_
  by_cases hμ : v (D p.1 p.2) = 0
  · rw [hμ]; exact zero_le'
  have hlt : v ((A * D) p.1 p.2) < v (D p.1 p.2) := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ hμ fun k _ => ?_
    rw [map_mul]
    calc v (A p.1 k) * v (D k p.2) ≤ v (A p.1 k) * v (D p.1 p.2) :=
          mul_le_mul_right (hmax (k, p.2) (Finset.mem_univ _)) _
      _ < 1 * v (D p.1 p.2) := mul_lt_mul_of_pos_right (hA p.1 k) (zero_lt_iff.2 hμ)
      _ = v (D p.1 p.2) := one_mul _
  have e := Valuation.map_add_eq_of_lt_left v hlt
  rw [← e, ← Matrix.add_apply]
  exact h p.1 p.2

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_ratA {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (G : GL (Fin n) E) (r s : Fin n) :
    adAt F P ((GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((G : Matrix (Fin n) (Fin n) E) r s) := by
  exact adAt_inclE F P _

theorem congE_of_near (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (d d' : ℕ) (hd' : 1 ≤ d') (hdd : d' ≤ d)
    (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (G G' : GL (Fin n) E)
    (hG : ∀ w, (G : Matrix (Fin n) (Fin n) E) *ᵥ w = g w) (hG' : ∀ w, (G' : Matrix (Fin n) (Fin n) E) *ᵥ w = g' w)
    (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    (hy : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d : ℤ)))
    (hy' : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G' : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d' : ℤ))) :
    CongE P d' g' g := by
  set φ := adAt F P
  set y := x⁻¹ * GlobalTheory.TwU.ratA F G
  set y' := x⁻¹ * GlobalTheory.TwU.ratA F G'
  set H : GL (Fin n) E := G⁻¹ * G'
  have hyH : y * GlobalTheory.TwU.ratA F H = y' := by
    simp only [y, y', H, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  set Y : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set Y' : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y' : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set R : Matrix (Fin n) (Fin n) (P.adicCompletion E) := ((GlobalTheory.TwU.ratA F H : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  have hYR : Y * R = Y' := by
    simp only [Y, Y', R, ← Matrix.map_mul, ← Units.val_mul, hyH]
  have hdA : ∀ r s, Valued.v ((Y - 1) r s) < 1 := fun r s => by
    refine lt_of_le_of_lt (hy r s) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hsum : ∀ r s, Valued.v (((R - 1) + (Y - 1) * (R - 1)) r s) ≤ WithZero.exp (-(d' : ℤ)) := fun r s => by
    have e : (R - 1) + (Y - 1) * (R - 1) = (Y' - 1) - (Y - 1) := by
      rw [← hYR]; noncomm_ring
    rw [e, Matrix.sub_apply]
    refine Valuation.map_sub_le _ (hy' r s) ((hy r s).trans ?_)
    rw [WithZero.exp_le_exp]; omega
  have hD := entries_le_of_add_mul Valued.v (Y - 1) (R - 1) _ hdA hsum

  have hH : ∀ r s, Valued.v (algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s)) ≤ WithZero.exp (-(d' : ℤ)) := by
    intro r s
    have e : (R - 1) r s = algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
      simp only [R, Matrix.map_apply, φ, adAt_ratA]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← e]; exact hD r s
  intro w hw
  have hHw : g ((H : Matrix (Fin n) (Fin n) E) *ᵥ w) = g' w := by
    rw [← hG, Matrix.mulVec_mulVec, ← Units.val_mul, ← hG']
    simp only [H, mul_inv_cancel_left]
  have e : (((qOf P : ℕ) : E) ^ d')⁻¹ • (g' w - g w) =
      g ((((qOf P : ℕ) : E) ^ d')⁻¹ • (((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w)) := by
    rw [map_smul, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, hHw]
  rw [e]
  refine (hg _).2 ?_
  rw [GlobalTheory.Mem.ColAd.mem_stdAt_val] at hw ⊢
  intro l
  have hs : Valued.v (algebraMap E (P.adicCompletion E) ((((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w) l)) ≤ WithZero.exp (-(d' : ℤ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul, map_mul]
    calc _ ≤ WithZero.exp (-(d' : ℤ)) * 1 := mul_le_mul' (hH l k) (hw k)
      _ = _ := mul_one _
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, map_inv₀, map_inv₀, map_pow, map_pow, map_natCast, hq]
  calc _ ≤ (WithZero.exp (-1 : ℤ) ^ d')⁻¹ * WithZero.exp (-(d' : ℤ)) := mul_le_mul_right hs _
    _ = 1 := by
      rw [← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
      simp

end Gen

end GlobalTheory.Mem.Col2.AdT.AdTieNear

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear


set_option maxHeartbeats 800000 in
theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → 1 ≤ dep' P → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' → CongE P.1 (dep' P) g' g := by
  intro B X I hOk l Z a i fb dep dep' P κ g g' hg h1 hdd hF hF'
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hF hF'
  have hq := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) 0 P 1).2.1
  have hy := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a _ (dep P) P _).2.2.1 hF
  have hy' := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a _ (dep' P) P _).2.2.1 hF'
  exact congE_of_near (F := B.host.F) P.1 (dep P) (dep' P) h1 hdd _ g g'
    (GlobalTheory.TwU.seamGL (sm I l Z) g) (GlobalTheory.TwU.seamGL (sm I l Z) g')
    (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g w) (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g' w)
    hg hq hy hy'

end GlobalTheory.Mem.Col2.AdT.AdTieNear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismsNearSameAdelicCongruentStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_automorphisms_near_same_adelic_congruent : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → 1 ≤ dep' P → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' → CongE P.1 (dep' P) g' g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.AdTieNear.main | exact GlobalTheory.Mem.Col2.AdT.AdTieNear.main | (intros; apply GlobalTheory.Mem.Col2.AdT.AdTieNear.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismCongruentNearFrameReading
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismCongruentNearFrameReading
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.NearCong

open WithZero

theorem mul_cong {K : Type} [Field K] (v : Valuation K ℤᵐ⁰) {n : ℕ} (N : ℕ) (A C : Matrix (Fin n) (Fin n) K)
    (hA : ∀ r s, v ((A - 1) r s) ≤ exp (-(N : ℤ))) (hC : ∀ r s, v ((C - 1) r s) ≤ exp (-(N : ℤ))) :
    ∀ r s, v ((A * C - 1) r s) ≤ exp (-(N : ℤ)) := by
  intro r s
  have he : exp (-(N : ℤ)) ≤ 1 := by
    rw [← exp_zero, exp_le_exp]; omega
  have e : A * C - 1 = (A - 1) * (C - 1) + (A - 1) + (C - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  refine v.map_add_le (v.map_add_le ?_ (hA r s)) (hC r s)
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun k _ => ?_
  rw [map_mul]
  calc v ((A - 1) r k) * v ((C - 1) k s) ≤ exp (-(N : ℤ)) * 1 := mul_le_mul' (hA r k) ((hC k s).trans he)
    _ = exp (-(N : ℤ)) := mul_one _

section Rat
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem congE_inv_mul (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hC : CongE P c g' g) : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) ∈ Formalism.L2.Col.stdAt E n P := by
  intro x hx
  have hgi : g⁻¹ ∈ Formalism.L2.Col.GLint E n P := inv_mem hg
  have e1 : (g⁻¹ * g') x = g⁻¹ (g' x) := rfl
  have e2 : g⁻¹ (g x) = x := by
    show (g⁻¹ * g) x = x
    rw [inv_mul_cancel]; rfl
  have e : (((qOf P : ℕ) : E) ^ c)⁻¹ • ((g⁻¹ * g') x - x) = g⁻¹ ((((qOf P : ℕ) : E) ^ c)⁻¹ • (g' x - g x)) := by
    rw [map_smul, map_sub, e1, e2]
  rw [e]
  exact (hgi _).2 (hC x hx)

theorem val_entry (P : HeightOneSpectrum (𝓞 E)) (hq : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ)) (c : ℕ)
    (h : Sp E n ≃ₗ[E] Sp E n)
    (hh : ∀ x ∈ Formalism.L2.Col.stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • (h x - x) ∈ Formalism.L2.Col.stdAt E n P) (r s : Fin n) :
    P.valuation E (LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s) ≤ exp (-(c : ℤ)) := by
  have hx : (Pi.single s (1 : E) : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    rw [GlobalTheory.TwistRowType.mem_stdAt]
    intro k
    rw [Pi.single_apply]
    split_ifs
    · exact (GlobalTheory.TwistRowType.intSub P).one_mem
    · exact (GlobalTheory.TwistRowType.intSub P).zero_mem
  have h1 := (GlobalTheory.TwistRowType.mem_stdAt P _).1 (hh _ hx) r
  rw [GlobalTheory.UnramCompletion.intAt_iff] at h1
  rw [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_apply, map_mul, map_inv₀, map_pow, hq] at h1
  have e : LinearMap.toMatrix' h.toLinearMap r s - (1 : Matrix (Fin n) (Fin n) E) r s = h (Pi.single s 1) r - (if r = s then 1 else 0) := by
    rw [LinearMap.toMatrix'_apply, Matrix.one_apply]; rfl
  rw [e]
  generalize P.valuation E (h (Pi.single s 1) r - if r = s then 1 else 0) = y at h1
  have hE : (exp (-1 : ℤ) ^ c)⁻¹ = exp (c : ℤ) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_neg]; congr 1; simp
  rw [hE] at h1
  have hm : exp (-(c : ℤ)) * exp (c : ℤ) = 1 := by rw [← exp_add]; simp
  calc y = (exp (-(c : ℤ)) * exp (c : ℤ)) * y := by rw [hm, one_mul]
    _ = exp (-(c : ℤ)) * (exp (c : ℤ) * y) := mul_assoc _ _ _
    _ ≤ exp (-(c : ℤ)) * 1 := mul_le_mul' le_rfl h1
    _ = exp (-(c : ℤ)) := mul_one _

end Rat

section Core
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem vAlg' (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

theorem adAt_ratA (P : HeightOneSpectrum (𝓞 E)) (γ : GL (Fin n) E) (r s : Fin n) :
    adAt F P (((GlobalTheory.TwU.ratA F γ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) ((γ : Matrix (Fin n) (Fin n) E) r s) :=
  adAt_inclE F P _

theorem core (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = exp (-1 : ℤ))
    (hiff : ∀ (N : ℕ) (z : GL (Fin n) (AfE F E)), GlobalTheory.TwU.CongAt P N z ↔
      ∀ r s, Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ exp (-(N : ℤ)))
    (G : (Sp E n ≃ₗ[E] Sp E n) →* GL (Fin n) E)
    (hG : ∀ h r s, (G h : Matrix (Fin n) (Fin n) E) r s = LinearMap.toMatrix' h.toLinearMap r s)
    (c d : ℕ) (hcd : c ≤ d) (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (h : GlobalTheory.TwU.CongAt P d (x⁻¹ * GlobalTheory.TwU.ratA F (G g))) (hC : CongE P c g' g) :
    GlobalTheory.TwU.CongAt P c (x⁻¹ * GlobalTheory.TwU.ratA F (G g')) := by
  have hq' : P.valuation E ((qOf P : ℕ) : E) = exp (-1 : ℤ) := by
    rw [← vAlg', map_natCast]
    exact hq
  have e : x⁻¹ * GlobalTheory.TwU.ratA F (G g') = (x⁻¹ * GlobalTheory.TwU.ratA F (G g)) * GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) := by
    rw [mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hiff] at h
  rw [hiff, e]
  have hdc : exp (-(d : ℤ)) ≤ exp (-(c : ℤ)) := by rw [exp_le_exp]; omega
  have key := mul_cong (Valued.v : Valuation (P.adicCompletion E) ℤᵐ⁰) c
    ((adAt F P).mapMatrix ((x⁻¹ * GlobalTheory.TwU.ratA F (G g) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    ((adAt F P).mapMatrix ((GlobalTheory.TwU.ratA F (G (g⁻¹ * g')) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)))
    (fun r s => (h r s).trans hdc) (fun r s => ?_)
  · intro r s
    have := key r s
    rwa [← map_mul, ← Units.val_mul] at this
  · show Valued.v (adAt F P _ - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ _
    rw [adAt_ratA, hG]
    have h1 : (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s = algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) r s) := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [h1, ← map_sub, vAlg']
    exact val_entry P hq' c _ (congE_inv_mul P c g g' hg hC) r s

end Core

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → CongE P.1 (dep' P) g' g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' := by
  intro B X I hI l Z a i fb dep dep' P κ g g' hg hdep hIn hC
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hIn ⊢
  obtain ⟨hseam, hq, -⟩ := GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a 0 0 P 1
  have hiff := fun N z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hI l Z a ((I.rec7 l Z).R.N i) N P z).2.2
  rw [hseam] at hIn hiff ⊢
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact @core (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ _ _ P.1 hq hiff (GlobalTheory.TwU.seamGL (sm I l Z)) (fun _ _ _ => rfl) (dep' P) (dep P) hdep _ g g' hg hIn hC

end GlobalTheory.Mem.Col2.AdT.NearCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismCongruentNearFrameReadingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_automorphism_congruent_near_frame_reading : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → CongE P.1 (dep' P) g' g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' := by
  first | exact @GlobalTheory.Mem.Col2.AdT.NearCong.main | exact GlobalTheory.Mem.Col2.AdT.NearCong.main | (intros; apply GlobalTheory.Mem.Col2.AdT.NearCong.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEntriesLeExp
namespace GlobalTheory.EntriesExpBound

theorem exists_nat_le_exp (x : WithZero (Multiplicative ℤ)) :
    ∃ k : ℕ, x ≤ WithZero.exp (k : ℤ) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · refine ⟨(WithZero.log x).toNat, ?_⟩
    calc x = WithZero.exp (WithZero.log x) := (WithZero.exp_log hx).symm
      _ ≤ _ := WithZero.exp_le_exp.mpr (Int.self_le_toNat _)

theorem exists_entries_le_exp {K : Type} [inst : Field K]
    [inst_1 : Valued K (WithZero (Multiplicative ℤ))] {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ∃ (k : ℕ), ∀ (r s : Fin m),
      (Valued.v : K → WithZero (Multiplicative ℤ)) (A r s) ≤ WithZero.exp (↑k : ℤ) := by
  choose f hf using fun p : Fin m × Fin m =>
    exists_nat_le_exp ((Valued.v : K → WithZero (Multiplicative ℤ)) (A p.1 p.2))
  refine ⟨Finset.univ.sup f, fun r s => (hf (r, s)).trans ?_⟩
  exact WithZero.exp_le_exp.mpr
    (Int.ofNat_le.mpr (Finset.le_sup (f := f) (Finset.mem_univ (r, s))))

end GlobalTheory.EntriesExpBound
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.OnePrime

section Local

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem exists_bound {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ∃ k : ℕ, ∀ r s, Valued.v (A r s) ≤ WithZero.exp (k : ℤ) := by
  first
  | exact @_root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp
  | exact _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp
  | (apply _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp ..)

theorem mul_bound {m : ℕ} {A C : Matrix (Fin m) (Fin m) K} {a c : WithZero (Multiplicative ℤ)}
    (hA : ∀ r s, Valued.v (A r s) ≤ a) (hC : ∀ r s, Valued.v (C r s) ≤ c) (r s : Fin m) :
    Valued.v ((A * C) r s) ≤ a * c := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hA r j) (hC j s)

end Local

theorem exists_root_rat (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (m n N : ℕ) (hn : 0 < n)
    (q : P.adicCompletion E) (hq : Valued.v q = WithZero.exp (-1 : ℤ)) (G₁ G₂ : GL (Fin m) (P.adicCompletion E)) :
    ∃ (M : GL (Fin m) (P.adicCompletion E)) (γ : GL (Fin m) E),
      (∀ r s, Valued.v (M.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      (∀ r s, Valued.v ((M ^ n).1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      G₁ * M ^ n * G₂ = Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ := by
  haveI : CharZero (P.adicCompletion E) := algebraRat.charZero _
  have hc : Valued.v (q ^ (N + 1)) = WithZero.exp (-((N : ℤ) + 1)) := by
    rw [map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hn1 : Valued.v (n : P.adicCompletion E) ≤ 1 := by
    clear hn
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact Valuation.map_add_le _ ih (by simp)
  have hcN : Valued.v (q ^ (N + 1)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [hc]
    exact WithZero.exp_le_exp.2 (by omega)
  have hε : Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1)) ≠ 0 := by
    rw [map_mul, hc]
    refine mul_ne_zero ?_ WithZero.exp_ne_zero
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨k₁, hk₁⟩ := exists_bound G₂.1
  obtain ⟨k₂, hk₂⟩ := exists_bound (G₂⁻¹).1
  set e := WithZero.log (Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1))) with he
  obtain ⟨γ, hγ⟩ := GlobalTheory.DenseGL.dense_two_sided E P m (k₁ + k₂ + (-e).toNat) (G₁ * G₂)
  let γ' : GL (Fin m) (P.adicCompletion E) := Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ
  have hγ' : γ'.1 = γ.1.map (algebraMap E (P.adicCompletion E)) := rfl
  let B₀ : GL (Fin m) (P.adicCompletion E) := G₁⁻¹ * γ' * G₂⁻¹
  have hB : B₀.1 - 1 = G₂.1 * (((G₁ * G₂)⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) * (G₂⁻¹).1 := by
    rw [← hγ', mul_sub, _root_.sub_mul, mul_one, Units.mul_inv, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
    congr 2
    simp only [B₀]
    group
  have hB2 : ∀ r s, Valued.v ((B₀.1 - 1) r s) ≤ Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1)) := fun r s => by
    rw [hB]
    refine (mul_bound (mul_bound hk₁ fun r s => (hγ r s).1) hk₂ r s).trans ?_
    rw [← WithZero.exp_log hε, ← he, ← WithZero.exp_add, ← WithZero.exp_add]
    refine WithZero.exp_le_exp.2 ?_
    push_cast
    omega
  obtain ⟨M, hM1, hM2⟩ := GlobalTheory.MatNthRoot.exists_nthRoot E P m n (q ^ (N + 1)) B₀.1 hn
    (by rw [hc, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)) hB2
  have hu : IsUnit M := (isUnit_pow_iff hn.ne').1 (hM2 ▸ B₀.isUnit)
  obtain ⟨M, rfl⟩ := hu
  have hM3 : M ^ n = B₀ := Units.ext (by rw [Units.val_pow_eq_pow_val, hM2])
  refine ⟨M, γ, fun r s => (hM1 r s).trans ?_, fun r s => ?_, ?_⟩
  · rw [map_mul]
    exact (mul_le_of_le_one_left' hn1).trans hcN
  · rw [hM3]
    refine (hB2 r s).trans ?_
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left' (pow_le_one' hn1 2)).trans hcN
  · rw [hM3]
    show _ = γ'
    simp only [B₀]
    group


set_option maxHeartbeats 2000000 in
theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), ChiFin I l Z S → ∀ (P : SBof I a), P.1 ∈ I.Q a → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ (N : ℕ) (g₁ g₂ : GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z.1 = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z.1 ∧ ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g₁ * (show GA B (B.R.N i) from z.1) * g₂ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s) := by
  intro B X I hI hPin l Z a T i hi bad S hS P hP v hv N g₁ g₂
  obtain ⟨n, hn, hchi⟩ := hS
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep I hI hPin l Z a T i hi bad S P v hv
  have hd := fun N z => GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a ((I.rec7 l Z).R.N i) N P z
  obtain ⟨hs, hq, -⟩ := hd 0 1
  let φ : AfE B.host.F B.host.E →+* P.1.adicCompletion B.fields.E := adAt B.host.F P.1
  obtain ⟨M, γ, hM1, hM2, hM3⟩ := exists_root_rat B.fields.E P.1 (B.R.N i) n (N + N₀) hn _ hq
    (Matrix.GeneralLinearGroup.map φ g₁) (Matrix.GeneralLinearGroup.map φ g₂)
  obtain ⟨w, hwU, hwv, hwP⟩ := GlobalTheory.Mem.Col2.AdLift.exists_lift I hI hPin l Z a i hi P v hv M
  have hw : w ∈ S.U := hN₀ w hwU hwv (((hd N₀ w).2.2).2 fun r s => by
    rw [hwP]
    exact (hM1 r s).trans (WithZero.exp_le_exp.2 (by omega)))
  let w' : GA B (B.R.N i) := w
  have hw' : Matrix.GeneralLinearGroup.map φ w' = M := Units.ext (Matrix.ext hwP)
  have hz : Matrix.GeneralLinearGroup.map φ (w' ^ n) = M ^ n := by rw [map_pow, hw']
  have hz' : ∀ r s, φ ((w' ^ n).1 r s) = (M ^ n).1 r s := fun r s =>
    congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) hz
  have hbad : v ∉ badG (I.rec7 l Z) := by
    have key : ∀ j : Fin 2, (((B.primes X).g j : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal := fun j =>
      GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hP ((base_fields_primes_ok B X).2.1.g_prime j) (hI.g_mem j)
    rw [hs] at hv
    have key2 : ∀ j : Fin 2, (((B.primes X).g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal := fun j h => by
      rw [hv, Ideal.mem_comap, map_natCast] at h
      exact key j h
    rintro (h | h)
    · exact key2 0 h
    · exact key2 1 h
  refine ⟨⟨w, hw⟩ ^ n, ?_, fun v' hv' => ?_, ((hd N _).2.2).2 fun r s => ?_, γ, fun r s => ?_⟩
  · rw [map_pow]
    exact hchi ⟨w, hw⟩ fun v' hv' => hwv v' fun e => hbad (e ▸ hv')
  · show bc (prV (E := (I.rec7 l Z).host.E) v') (w ^ n) = 1
    calc
      bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') (w ^ n) =
          (bc (prV (E := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) v') w) ^ n := map_pow _ _ _
      _ = 1 := (congrArg (fun x => x ^ n) (hwv v' hv')).trans (one_pow n)
  · have e := hz' r s
    have h2 := hM2 r s
    rw [← e] at h2
    exact h2.trans (WithZero.exp_le_exp.2 (by omega))
  · have e : Matrix.GeneralLinearGroup.map φ (g₁ * w' ^ n * g₂) =
        Matrix.GeneralLinearGroup.map φ g₁ * M ^ n * Matrix.GeneralLinearGroup.map φ g₂ := by
      rw [map_mul, map_mul, hz]
    exact congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) (e.trans hM3)

end GlobalTheory.Mem.Col2.AdT.OnePrime

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartReadsAtClassGL
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulSubOneLeOfValuation
namespace GlobalTheory.MulSubOneValuation

theorem mul_sub_one_le_of_valuation {K Γ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} {γ : Γ} (hγ : γ ≤ 1) {A B : Matrix (Fin n) (Fin n) K}
    (hA : ∀ r s, v (A r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ)
    (hB : ∀ r s, v (B r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ) (r s : Fin n) :
    v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ := by

  have hM : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  have he : (A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s =
      (A - 1) r s + (B - 1) r s + ((A - 1) * (B - 1)) r s := by
    simpa [Matrix.sub_apply, Matrix.add_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) K => M r s) hM
  rw [he, Matrix.mul_apply]
  refine v.map_add_le (v.map_add_le (hA r s) (hB r s)) (v.map_sum_le fun k _ => ?_)
  calc v ((A - 1) r k * (B - 1) k s) = v ((A - 1) r k) * v ((B - 1) k s) := map_mul v _ _
    _ ≤ γ * γ := mul_le_mul' (hA r k) (hB k s)
    _ ≤ γ := mul_le_of_le_one_right' hγ

theorem mul_sub_one_le {E : Type} [Field E] [NumberField E]
    {P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)} {n N : ℕ}
    {A B : Matrix (Fin n) (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)}
    (hA : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (A r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (hB : ∀ r s : Fin n, (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) (B r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (r s : Fin n) :
    (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion E P →
      WithZero (Multiplicative ℤ)) ((A * B) r s - (1 : Matrix (Fin n) (Fin n)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion E P)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  have hγ : WithZero.exp (-(N : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  exact mul_sub_one_le_of_valuation Valued.v hγ hA hB r s

end GlobalTheory.MulSubOneValuation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartReadsAtClassGL
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.FrameMove

open GlobalTheory.Mem.Col2.LevFun GlobalTheory.Mem.Col2.Splice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_mul_ratA_apply {n : ℕ} (g : GL (Fin n) (AfE F E)) (γ : GL (Fin n) E) (r s : Fin n) :
    ((g⁻¹ * GlobalTheory.TwU.ratA F γ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s =
      pullV g (fun t => (γ : Matrix (Fin n) (Fin n) E) t s) r := by
  unfold pullV
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem val_sub_lt_of_liftFr [StarRing E] {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (w : SG) (r s : Fin n) :
    Valued.v (adAt F w.1 (pullV g (p.deco.1.liftFr w (Pi.single s 1)) r) -
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) r s) < 1 := by
  classical
  have hL := GlobalTheory.TopStep.liftFr_spec p.deco.2 w
  have hs := single_mem_stdAt (E := E) (n := n) w.1 s
  have hx : p.deco.1.liftFr w (Pi.single s 1) ∈ p.deco.1.at w.1 := (hL.1 _).2 hs
  obtain ⟨t, ht, htx⟩ := (mem_locP _ _ _).1 hx
  have h1 := h.be w _ htx r
  rw [p.deco.2.be_smul w t _ hx, hL.2 _ hs, redV_single, adAt_pullV_osmul] at h1
  have h2 : HasRes w.1 (adAt F w.1 (pullV g (p.deco.1.liftFr w (Pi.single s 1)) r))
      (Ideal.Quotient.mk w.1.asIdeal (if r = s then 1 else 0)) := by
    refine hasRes_of_mul ht ?_
    convert h1 using 1
    by_cases e : r = s
    · subst e; simp
    · simp [e]
  have h3 := hasRes_sub_lt h2
  convert h3 using 3
  by_cases e : r = s
  · subst e; simp
  · simp [e, Matrix.one_apply]

theorem val_mul_sub_one_le {P : HeightOneSpectrum (𝓞 E)} {n N : ℕ} {A B : Matrix (Fin n) (Fin n) (P.adicCompletion E)}
    (hA : ∀ r s, Valued.v (A r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (hB : ∀ r s, Valued.v (B r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (r s : Fin n) :
    Valued.v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  first
  | exact @_root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le
  | exact _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le
  | (apply _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le ..)

theorem le_exp_neg_one_of_lt_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with h0 | h0
  · rw [h0]; exact zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem seamGL_apply {D : D7} {Xf : Fields} (sd : Seam D Xf) {n : ℕ} (f : Sp Xf.E n ≃ₗ[Xf.E] Sp Xf.E n) (t s : Fin n) :
    ((GlobalTheory.TwU.seamGL sd f : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) t s = sd.iE (f (Pi.single s 1) t) := by
  have h : ((GlobalTheory.TwU.seamGL sd f : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' f.toLinearMap).map (sd.iE : Xf.E →+* D.host.E) := rfl
  rw [h, Matrix.map_apply, LinearMap.toMatrix'_apply]
  rfl

theorem adAt_pullV_fr [StarRing E] {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) (r s : Fin n) :
    adAt F P.1 (pullV g (p.fr P (Pi.single s 1)) r) = (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion E)) r s := by
  have e1 : GlobalTheory.Mem.ColAd.locM P.1 (g⁻¹ * g) = 1 := by rw [inv_mul_cancel, GlobalTheory.Mem.ColAd.locM_one]
  rw [← e1, GlobalTheory.Mem.ColAd.locM_mul, Matrix.mul_apply]
  unfold pullV
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, adAt_inclE, ← h.fr P t s]
  rfl

theorem frame_near : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ P : SBof I a, GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (((K (chOf c)).y ⟨c, rfl⟩).1 * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)) := by
  classical
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb P
  have hpt := hR.pt c
  have hd := fun z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) ((I.cst a).D P) P z).2.2
  unfold GlobalTheory.TwU.NearAt
  rw [hd]
  have hfb2 := (hd _).1 (hfb P).2
  have e : ∀ {G : Type} [Group G] (y k A C : G), (y * A)⁻¹ * C = (A⁻¹ * k) * ((y * k)⁻¹ * C) := by
    intros; group
  have key := e (G := GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) ((K (chOf c)).y ⟨c, rfl⟩).1
    (k (chOf c)) (GlobalTheory.TwU.ratA _ (fb P))
    (GlobalTheory.TwU.ratA _ (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)))
  rw [key]
  intro r s
  show Valued.v (GlobalTheory.Mem.ColAd.locM P.1 (_ * _) r s - _) ≤ _
  erw [GlobalTheory.Mem.ColAd.locM_mul]
  refine val_mul_sub_one_le hfb2 ?_ r s
  clear r s
  intro r s
  show Valued.v (adAt B.host.F P.1 (_) - _) ≤ _
  rw [inv_mul_ratA_apply]
  have hfr := frsF_eq_ptFr I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P
  have hcol : (fun t => ((GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P) :
      GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) :
        Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) t s) =
      ptFr ((I.stp u a i).rep c).1.1 P.1 (Pi.single s 1) :=
    funext fun t => by rw [seamGL_apply]; exact congrArg (fun f => f (Pi.single s 1) t) hfr
  rw [hcol]
  by_cases hG : P.1 ∈ (B.primes X).vGs
  · rw [(hOk.idx_ok a).depthG P hG]
    have e2 : ptFr ((I.stp u a i).rep c).1.1 P.1 = (extTo I.SQ ((I.stp u a i).rep c).1.1).deco.1.liftFr ⟨P.1, hG⟩ := by
      unfold ptFr
      rw [dite_eq_left hG]
      rfl
    rw [e2]
    exact le_exp_neg_one_of_lt_one' (val_sub_lt_of_liftFr hpt ⟨P.1, hG⟩ r s)
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hG
    have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
    have e3 : ptFr ((I.stp u a i).rep c).1.1 P.1 = (extTo I.SQ ((I.stp u a i).rep c).1.1).fr ⟨P.1, hSQ⟩ := rfl
    have h0 := adAt_pullV_fr hpt ⟨P.1, hSQ⟩ r s
    rw [e3]
    erw [h0, sub_self, map_zero]
    exact zero_le'

end GlobalTheory.Mem.Col2.AdT.FrameMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartReadsAtClassGLStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_reads_at_class_GL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ P : SBof I a, GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (((K (chOf c)).y ⟨c, rfl⟩).1 * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.FrameMove.frame_near | exact GlobalTheory.Mem.Col2.AdT.FrameMove.frame_near | (intros; apply GlobalTheory.Mem.Col2.AdT.FrameMove.frame_near <;> assumption)
end
end
