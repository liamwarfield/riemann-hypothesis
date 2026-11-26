module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaSchur

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem mul_star_psi (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) : ψ a * star (ψ a) = 1 := by
  have h : ‖ψ a‖ = 1 := hψ.1.2.1 a
  rw [Complex.star_def, Complex.mul_conj', h]
  simp

theorem heisO_rat {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : WO S T} (hγ : γ ∈ ratL T S) (x : WO S T) :
    heisO ψ S T γ f x = ψ (symplO S T x γ) * f x := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hf.quasi γ x
  rw [← GlobalTheory.WeilVacMove.symplOH_skew] at h
  show ψ (symplOH S T x (ratW T S γ)) * f (x + ratW T S γ) = ψ (symplO S T x (ratW T S γ)) * f x
  rw [add_comm x, h, ← mul_assoc, ← AddChar.map_add_eq_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1]

theorem prod_periodic (hψ : IsStdChar D ψ (-1)) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hf' : IsThetaFunO ψ S T f') {γ : WO S T} (hγ : γ ∈ ratL T S) (x : WO S T) :
    f (γ + x) * star (f' (γ + x)) = f x * star (f' x) := by
  obtain ⟨γ, rfl⟩ := hγ
  show f (ratW T S γ + x) * star (f' (ratW T S γ + x)) = _
  rw [hf.quasi, hf'.quasi, star_mul']
  linear_combination (f x * star (f' x)) * mul_star_psi hψ (-(symplOH S T (ratW T S γ) x))

theorem prod_eq (hψ : IsStdChar D ψ (-1)) (M : Module.End ℂ (WO S T → ℂ))
    (hM : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f))
    (hc : ∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f))
    (hn : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (x : WO S T) :
    M f x * star (M f' x) = f x * star (f' x) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  obtain ⟨l1, l2, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hint : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      Integrable (fun x => g x * star (g' x)) (μ.restrict 𝓕) := fun g g' hg hg' => by
    have hcont : Continuous fun x => g x * star (g' x) := hg.cont.mul hg'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← prod_periodic hψ hg hg' hγ w]
    exact hC _ h
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      have : Continuous fun x : WO S T => symplOH S T x (γ : WO S T) :=
        GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_id' continuous_const
      simp only [← l4]
      exact hψ.1.1.comp (this.add this))
    (fun γ x y => by
      simp only [← l4, l1, AddChar.map_add_eq_mul]
      ring)
    (fun γ γ' x => by
      simp only [← l4, AddSubgroup.coe_add, l2, AddChar.map_add_eq_mul]
      ring)
    (fun x => by
      simp only [← l4, AddSubgroup.coe_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by
      rw [← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M f' x) - f x * star (f' x))
    (((hM f hf).cont.mul (hM f' hf').cont.star).sub (hf.cont.mul hf'.cont.star))
    (fun γ hγ x => by rw [prod_periodic hψ hf hf' hγ, prod_periodic hψ (hM f hf) (hM f' hf') hγ])
    (fun γ => by
      have e : (fun x => ψ (symplO S T x γ) * (M f x * star (M f' x) - f x * star (f' x))) = fun x =>
          M (heisO ψ S T γ f) x * star (M f' x) - heisO ψ S T γ f x * star (f' x) := by
        funext x
        rw [hc _ f hf, heisO_rat hf γ.2, heisO_rat (hM f hf) γ.2]
        ring
      rw [e, integral_sub (hint _ _ (hM _ (hth _ f hf)) (hM f' hf')) (hint _ _ (hth _ f hf) hf'),
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 M hM (hn μ 𝓕 hμ h𝓕) _ _ (hth _ f hf) hf', sub_self])
  exact sub_eq_zero.1 (congrFun key x)

theorem schur : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  intro D ψ hψ S T M hM hc hn
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have h2 : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ∀ x y,
      M f x * star (M f' y) = f x * star (f' y) := fun f f' hf hf' x y => by
    have h := prod_eq hψ M hM hc hn hf (hth (y - x) f' hf') x
    rw [hc _ _ hf'] at h
    simp only [heisO, add_sub_cancel, star_mul'] at h
    linear_combination ψ (symplOH S T x (y - x)) * h -
      (M f x * star (M f' y) - f x * star (f' y)) * mul_star_psi hψ (symplOH S T x (y - x))
  by_cases h0 : ∃ f₀ y, IsThetaFunO ψ S T f₀ ∧ f₀ y ≠ 0
  · obtain ⟨f₀, y, hf₀, hy⟩ := h0
    have h1 := h2 f₀ f₀ hf₀ hf₀ y y
    have hn1 : ‖M f₀ y‖ = ‖f₀ y‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (M f₀ y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ y) / star (M f₀ y), ?_, fun f hf => ?_⟩
    · rw [norm_div, norm_star, norm_star, hn1, div_self (norm_ne_zero_iff.2 hy)]
    · funext x
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 f f₀ hf hf₀, mul_comm]
  · refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hy⟩
    rw [this, map_zero, smul_zero]

end GlobalTheory.ThetaSchur

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurLemma_thetaFunctions_orientedPair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  first | exact @GlobalTheory.ThetaSchur.schur | exact GlobalTheory.ThetaSchur.schur | (intros; apply GlobalTheory.ThetaSchur.schur <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrAtEmb
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift

namespace GlobalTheory.GalOne

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Rec

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

abbrev zAt : Fam (Wc D i) := x0Mat (R.MW i σ)

def ConjW (μ' η' : (AE D)ˣ →* Circle) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  OverK σ ∧ ChiAt R i σ μ' ∧ IsEtaConj σ R.eta η' ∧ IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω ∧
    IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f

end Rec

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}


variable (T R i) in
abbrev OM : Type 1 := OMDat T.toCore R i Unit (fun _ => A.μ0)

abbrev Pinned (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : OM T R i) : Prop :=
  O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)

abbrev sOf (O : OM T R i) (σ' : O.c'.F →+* ℂ) : T.Q.c.F →+* ℂ := σ'.comp (incF T.Q.c O.c' O.hle)


omit [Algebra T.Q.c.F D.what₂.LL] in
abbrev dictS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) :
    GA D (Wc D i) → Σ k, Frame ((T.U ((i : ℕ) + 1) s).X k).Ψ D.R.r := castDict hV (T.dict ((i : ℕ) + 1) s)


omit [Algebra T.Q.c.F D.what₂.LL] in
abbrev muS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) : GA D (Wc D i) → ℂ := castDict hV (T.mu ((i : ℕ) + 1) s)


omit [Algebra T.Q.c.F D.what₂.LL] in
abbrev xS {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (h : GA D (Wc D i)) : Data D.host.E D.R.r :=
  (T.U ((i : ℕ) + 1) s).X (dictS hV h).1

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (O : OM T R i) (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ)

def FactsAt : Prop :=
  res T σ = sOf O σ' ∧ GoodEmb T.Q.c (sOf O σ') ∧ GoodEmb O.c' σ' ∧
    (∀ τ a, (R.MW i σ).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) ∧
    IsONeg (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) ∧
    cart (R.MW i σ) = cartZ (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) ∧
    (∀ ρ, T.x₀ ((i : ℕ) + 1) (sOf O σ') (tauE D ρ) =
      Matrix.reindex (finCongr (rank_Wc i)) (finCongr (rank_Wc i)) (zAt R i σ ρ)) ∧
    (∀ ρ, relab O.c' σ' (tauE D (lab σ ρ)) = tauE D ρ) ∧
    ∀ μ' η' : (AE D)ˣ →* Circle, ChiAt R i σ μ' → IsEtaConj σ R.eta η' →
      (∀ hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i, MuVal (Wc D i) μ' (muS hV)) ∧
      (∀ v ε, NonSplitAt D v ε → UnramAt ε μ' ∧ UnramAt ε (μ' * η'⁻¹)) ∧ HypConj R i σ μ' η'

def PointAt (hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i) (h : GA D (Wc D i)) : Prop :=
  ∃ γ ∈ GQ (Wc D i), ∃ (g : ℕ) (eT : D.what₂.Tau ≃ (xS hV h).Ψ)
    (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' (xS hV h) g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i)))
    (hx : (dictS hV h).2 ∈ (xS hV h).dom),
    IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) (xS hV h) eT Dc.bas ∧ Matched T.Q.c (sOf O σ') (xS hV h) Dc.idx Dc.e ∧
    (xS hV h).p0 = (T.Q.Dw ((i : ℕ) + 1)).q ∧ SelfD (xS hV h) (xS hV h).Λ ∧
    latW (rank_Wc i) (xS hV h).Λ = latG (Wc D i) (γ * h) ∧
    (dictS hV h).2 = frOf (rank_Wc i) eT (mvZ R.θ (γ * h) (zAt R i σ)) ∧
    letI : Algebra T.Q.c.F ℂ := (sOf O σ').toAlgebra
    (∃ (A₀ : AnFib (xS hV h) Dc.bas Dc.idx Dc.e (dictS hV h).2 (xS hV h).Λ
        (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩)) (th : (Fin g → ℂ) → ℂ),
      A₀.Reads 1 (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩).s th ∧
        MeanOne (xS hV h) Dc.bas Dc.idx (dictS hV h).2 (xS hV h).Λ th) ∧
    ∀ (g' : ℕ) (bas : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] (xS hV h).Λ) (idx : Fin g' ≃ (xS hV h).Ψ × Fin D.R.r)
      (e : Fin g' ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))), IsSympl (xS hV h) bas → Matched T.Q.c (sOf O σ') (xS hV h) idx e →
      ∀ (A₁ : AnFib (xS hV h) bas idx e (dictS hV h).2 (xS hV h).Λ
          (ptC (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV h).1 ⟨(dictS hV h).2, hx⟩))
        (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ a, mk a ∈ (xS hV h).Λ) →
        MarkAd (rank_Wc i) T.Q.l (iotaW T i) (γ * h) mk → A₁.Marked mk

def FrAtEmb (hV : T.V ((i : ℕ) + 1) (sOf O σ') = Wc D i)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ : WO (Vc D i) (Wc D i) → ℂ)
    (cc : (T.U ((i : ℕ) + 1) (sOf O σ')).Comp → ℂ) : Prop :=
  FrConst R.ψ R.θ (Vc D i) (rank_Wc i) ω f₀ (T.U ((i : ℕ) + 1) (sOf O σ')) (dictS hV) (muS hV) (zAt R i σ) cc

def TermAt (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (ε : ℤˣ) : Prop :=
  ∀ (h : O.Cl' () → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))),
    RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) →
    ∀ (k : O.Cl' ()) (g' : GA D (Wc D i)) (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ)
      (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r),
      IsSet R.ψ R.θ (Vc D i) (Wc D i) (rank_Wc i) X eT bas → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q →
      ∀ L : Lt D.host.E D.R.r, SelfD X L → latW (rank_Wc i) L = latG (Wc D i) g' →
      ∀ v : TF (Vc D i).rank g, IsVac X bas (T.Q.H.w0 : D.host.E) (tens (stdL D.host.E (Vc D i).rank) L) v →
      ∀ a : ℂ, Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (zAt R i σ))) (a • v) (ω (1, g') f₀) →
      ∀ mk₂ : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), (∀ b, mk₂ b ∈ L) →
        MarkAd (rank_Wc i) (O.dδ ()).l₂ (iotaW T i) g' mk₂ →
      ∀ Y : (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E,
        IsRoots (O.dδ ()).l₂ L ((ε : ℤ) • mk₂) (O.Nc () k) Y →
        GlobalTheory.SW.IsSB (gphi X bas (T.Q.H.w0 : D.host.E) (O.La () k).La L v (fun q => inC O.c' (O.w () k q)) Y) ∧
        Zak R.ψ R.θ (rank_Wc i) eT bas idx (frOf (rank_Wc i) eT (mvZ R.θ g' (zAt R i σ)))
          ((a * σ' (O.ep () k * ((((O.La () k).mIdx (O.Nc () k) D.R.r : O.c'.F))⁻¹ *
            ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (O.dδ ()).l₂) : O.c'.F))⁻¹ *
            ((O.La () k).zCard (O.Nc () k) D.R.r : O.c'.F)))) •
            gphi X bas (T.Q.H.w0 : D.host.E) (O.La () k).La L v (fun q => inC O.c' (O.w () k q)) Y) (ω (h k, g') f)

def IsUp (x : VsV D i D.what₂.LL) (x' : VsV D i O.c'.F) : Prop :=
  (x' : Pol O.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map O.jL (x : Pol D.what₂.LL D.what₂.Tau (Vc D i).rank)

def IsLtAt (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank) : Prop :=
  ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((relab O.c' σ' ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
    (relab O.c' σ' ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (lt ℓ).1) ∧
      ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))

def IoAt {c : CoefA (Vc D i)} (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (f : WO (Vc D i) (Wc D i) → ℂ)
    (Λ : c.W → WO (Vc D i) (Wc D i) → ℂ) (ph : ℂ) : Prop :=
  ∀ x x', IsUp O x x' → ∃ Q : PolF D (Wc D i).rank (Vc D i).rank,
    Λ (c₁ x) = fv R.ψ R.θ (Vc D i) (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).q (zAt R i σ) f Q ∧
    ∀ (X : Data D.host.E D.R.r) (eT : D.what₂.Tau ≃ X.Ψ) (g : ℕ)
      (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' σ' X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))),
      (∀ ρ, (eT ρ).1 = tauE D ρ) → MvPolynomial.C ph * toP (Vc D i) (rank_Wc i) eT Dc.hr Q =
        MvPolynomial.C ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) *
          MvPolynomial.rename Dc.eL (MvPolynomial.map σ' (O.io x'))

def CovAt (c0 : ℂ) : Prop :=
  letI : Algebra (O.dδ ()).c₂.F ℂ := (σ'.comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)).toAlgebra
  ∀ y₂ : FrPt (O.dδ ()).Xo₂ (O.dδ ()).c₂ ℂ, evR (O.dδ ()).Xo₂ (O.dδ ()).c₂ (O.dδ ()).cδ y₂ = c0

end GlobalTheory.GalOne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasis
noncomputable section

namespace GlobalTheory.AdTh.CoefExt

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} (φ : K →+* K')
  {I : Type} [Fintype I] {n : ℕ} (lam : I → DomWeight n) {W : Type} [AddCommGroup W] [Module ℂ W]

theorem map_actP (B : I → GL (Fin n) K) (F : Pol K I n) :
    MvPolynomial.map φ (actP lam B F) = actP lam (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) := by
  have h1 : (MvPolynomial.map φ).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc φ (B τ))).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map φ (trAct B F) = trAct (fun τ => Formalism.UG.bc φ (B τ)) (MvPolynomial.map φ F) :=
    congrArg (fun ψ : Pol K I n →+* Pol K' I n => ψ F) h1
  have h3 : φ (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc φ (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

def up (v : VV K lam) : VV K' lam := ⟨MvPolynomial.map φ (v : Pol K I n), GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ v.2⟩

theorem up_sum (a : VVIdx lam → K) (v : VVIdx lam → VV K lam) :
    up φ lam (∑ j, a j • v j) = ∑ j, φ (a j) • up φ lam (v j) := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [up, Submodule.coe_sum, Submodule.coe_smul, map_sum, smul_eq_C_mul, map_mul, map_C]

theorem exists_coord (v : VV K' lam) : ∃ a : VVIdx lam → K', v = ∑ j, a j • up φ lam (bVV K lam j) := by
  have hv : v ∈ Submodule.span K' (Set.range (bVV K' lam)) := by rw [(bVV K' lam).span_eq]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc φ lam j
    refine ⟨fun k => φ ((bVV K lam).repr ⟨F, hF⟩ k), ?_⟩
    rw [← up_sum, (bVV K lam).sum_repr]
    exact Subtype.ext ((bVV_coe _ _ _).trans hj)
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp [← Finset.sum_add_distrib, add_smul]⟩
  | smul c x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨fun j => c * a j, by simp [Finset.smul_sum, mul_smul]⟩

theorem up_rhoVr {E : Type} [Field E] [NumberField E] [NumberField K] [NumberField K'] (emb : I → E →+* K)
    (g : GL (Fin n) E) (v : VV K lam) :
    up φ lam (rhoVr emb lam g v) = rhoVr (fun τ => φ.comp (emb τ)) lam g (up φ lam v) := by
  apply Subtype.ext
  show MvPolynomial.map φ (actP lam (invTrK (embGL emb g)) (v : Pol K I n)) =
    actP lam (invTrK (embGL (fun τ => φ.comp (emb τ)) g)) (MvPolynomial.map φ (v : Pol K I n))
  rw [map_actP]
  rfl

variable {φ lam} {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

theorem equivariant (hE : ∀ v, c' (up φ lam v) = c₀ v) (T : W →ₗ[ℂ] W) (S : VV K lam →ₗ[K] VV K lam)
    (S' : VV K' lam →ₗ[K'] VV K' lam) (hS : ∀ v, up φ lam (S v) = S' (up φ lam v)) (hT : ∀ v, c₀ (S v) = T (c₀ v))
    (v : VV K' lam) : c' (S' v) = T (c' v) := by
  obtain ⟨a, rfl⟩ := exists_coord φ lam v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_smulₛₗ, ← hS, hE, hT, RingHom.id_apply]

theorem span_top (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hs : Submodule.span ℂ (Set.range fun j => c₀ (bVV K lam j)) = ⊤) : Submodule.span ℂ (Set.range c') = ⊤ := by
  refine top_le_iff.1 (hs ▸ Submodule.span_mono ?_)
  rintro _ ⟨j, rfl⟩
  exact ⟨_, hE _⟩

theorem linearIndependent (hE : ∀ v, c' (up φ lam v) = c₀ v)
    (hli : LinearIndependent ℂ fun j => c₀ (bVV K lam j)) {m : ℕ} (b : Fin m → VV K' lam) (hb : LinearIndependent K' b) :
    LinearIndependent ℂ fun j => c' (b j) := by
  classical
  letI : Algebra K' ℂ := σ'.toAlgebra
  choose a ha using fun j => exists_coord φ lam (b j)
  have h1 : LinearIndependent K' a := by
    refine LinearIndependent.of_comp (Fintype.linearCombination K' fun k => up φ lam (bVV K lam k)) ?_
    convert hb using 1
    funext j
    rw [ha j]
    simp [Fintype.linearCombination_apply]
  have h2 : LinearIndependent ℂ fun j => algebraMap K' ℂ ∘ a j := linearIndependent_algebraMap_comp_iff.2 h1
  have h3 := h2.map' (Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k))
    (LinearMap.ker_eq_bot'.2 fun g hg => funext (Fintype.linearIndependent_iff.1 hli g (by simpa [Fintype.linearCombination_apply] using hg)))
  have e : (fun j => c' (b j)) = ⇑(Fintype.linearCombination ℂ fun k => c₀ (bVV K lam k)) ∘ fun j => algebraMap K' ℂ ∘ a j := by
    funext j
    rw [ha j]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, hE, Function.comp_apply, Fintype.linearCombination_apply]
    rfl
  rw [e]
  exact h3

theorem pairVr_extremal {E : Type} [Field E] [NumberField E] [NumberField K] [StarRing K] (emb : I → E →+* K)
    (v : VV K lam) (hv : (v : Pol K I n) = ten fun τ => extremal K n (lam τ)) : pairVr emb lam 1 v v = 1 := by
  have hG : gramKd emb (1 : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
    funext τ
    simp [gramKd]
  have h := pairingExtremal_holds K I n lam (fun _ => 1) 1 (fun τ => by simp)
  rw [polyAction_one₂] at h
  rw [pairVr, pairK_apply, hG, hv, h]

end GlobalTheory.AdTh.CoefExt

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem inner_of_coefTie {D : D7} {V : HSp D} {C : Bridge.CoefDat D V} {S : Formalism.L2.DIV.CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)}
    {χ : J →* ℂˣ} {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : Formalism.L2.DIV.VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    (h : Bridge.CoefTie V C P lam c0 pair nab del) (v w : Formalism.L2.DIV.VV D.what₂.LL lam) :
    inner ℂ (c0 v) (c0 w) = D.what₂.embLL (pair v w) := by
  obtain ⟨e, -, he, hp, -⟩ := h
  have hi := P.coef_pair (e.symm v) (e.symm w)
  rwa [he, he, ← hp, e.apply_symm_apply, e.apply_symm_apply] at hi


set_option maxHeartbeats 800000 in
theorem coefMap_norm_equivariant_basis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ‖O.c0' O.hw‖ = 1 ∧ (∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE → ∀ v, O.c0' (rhoM O.c' (fun τ => embF O.c' (tauE D τ)) (lamV D i) (γE : Matrix _ _ D.host.E) v) = (R.cV i).ρ γ (O.c0' v)) ∧ Submodule.span ℂ (Set.range O.c0') = ⊤ ∧ ∀ (m : ℕ) (b : Fin m → VsV D i O.c'.F), LinearIndependent O.c'.F b → LinearIndependent ℂ (fun j => O.c0' (b j)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ _ i Tp tup O hP
  obtain ⟨gramR, c0R, c0L, hT, hc⟩ := hP.lift.c0
  have hσ := hP.lift.field
  have hE : ∀ v, O.c0' (CoefExt.up O.jL (lamV D i) v) = c0L i v := by
    intro v
    obtain ⟨w, hw, h⟩ := hc v
    rw [show CoefExt.up O.jL (lamV D i) v = w from Subtype.ext hw.symm]
    exact h
  obtain ⟨h1, h2, h3⟩ := hT.mapL i
  refine ⟨?_, ?_, CoefExt.span_top (W := (R.cV i).W) hE h3,
    fun m b hb => CoefExt.linearIndependent (W := (R.cV i).W) hE h2 b hb⟩
  · have hn := GlobalTheory.StdFrame.neg_eq_false_of_vStd D i hP.lift.std
    have hg : (D.sp.V ((i : ℕ) + 1)).gram = 1 := hP.lift.std.1
    let v : VsV D i D.what₂.LL := ⟨Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.extremal D.what₂.LL _ (lamV D i τ),
      GlobalTheory.Proof.TensorMapDescent.ten_mem _ _ fun τ => Formalism.GradedWeylDivisibility.hwMem _ _ _ le_rfl _ (Formalism.L2.DIV.natW_antitone _)⟩
    have hv : CoefExt.up O.jL (lamV D i) v = O.hw := by
      apply Subtype.ext
      have hw := hP.io.1
      unfold hwOK at hw
      refine Eq.trans ?_ hw.symm
      show MvPolynomial.map O.jL (Formalism.L2.DIV.ten _) = _
      rw [GlobalTheory.Proof.TensorMapDescent.map_ten]
      congr 1
      funext τ
      exact Formalism.L2.DIV.map_extremal _ _ _
    have hG : (if D.sp.Vneg ((i : ℕ) + 1) then -(D.sp.V ((i : ℕ) + 1)).gram else (D.sp.V ((i : ℕ) + 1)).gram) = 1 := by
      rw [hn, hg]; rfl
    have hi := inner_of_coefTie (hT.coefL i A.μ0) v v
    rw [hG] at hi
    replace hi := hi.trans ((congrArg D.what₂.embLL (CoefExt.pairVr_extremal (labLL D) v rfl)).trans (map_one _))
    rw [← hv, hE]
    have hi' : inner ℂ (c0L i v : (R.cV i).W) (c0L i v : (R.cV i).W) = 1 := hi
    rw [inner_self_eq_norm_sq_to_K] at hi'
    have h4 : ‖(c0L i v : (R.cV i).W)‖ ^ 2 = 1 := by
      have h5 := congrArg norm hi'
      simpa using h5
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4
  · intro γ γE hγ v
    have hu : IsUnit (γE.val).det := (Matrix.isUnit_iff_isUnit_det γE.val).1 γE.isUnit
    have hγE : Matrix.nonsingInvUnit γE.val hu = γE := Units.ext rfl
    have hemb : (fun τ => embF O.c' (tauE D τ)) = fun τ => O.jL.comp (labLL D τ) :=
      funext fun τ => (embV_eq_embF O.c' O.jL hσ τ).symm
    rw [rhoM, dite_eq_left hu, hγE, hemb]
    exact CoefExt.equivariant (W := (R.cV i).W) hE ((R.cV i).ρ γ) (Formalism.L2.DIV.rhoVr (labLL D) (lamV D i) γE) _
      (CoefExt.up_rhoVr O.jL (lamV D i) (labLL D) γE) (h1 γ γE hγ) v

end GlobalTheory.AdTh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory

namespace GlobalTheory.WeilPartsF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def GfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (infPartF F E)).comp (matHomF σ J)).ker

def GinfCF (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Subgroup (GAF σ J) :=
  ((Formalism.UG.bc (finPartF F E)).comp (matHomF σ J)).ker

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

structure IsUnitaryOnThetaF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  pres : ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f → IsThetaFunOF σ JS JT xi0 ψ (om p f)
  cont : ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ∀ w, Continuous fun p : GAF σ JS × GAF σ JT => om p f w
  unit : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f, IsThetaFunOF σ JS JT xi0 ψ f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

structure IsFinWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ) (χS χT : (AEF F E)ˣ →* Circle)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)
  split : ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ x y,
    IsDetAtF σ e JS g x → IsDetAtF σ e JT h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT xi0 ψ f →
        ℓ (heisOF σ JS JT xi0 ψ u f) = ℓ f) →
      ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → ℓ (om (g, h) f) = (r : ℂ) * (splitFacOF χS χT x y : ℂ) * ℓ f

structure IsInfWeilF (xi0 : E) (ψ : AddChar (AF F) ℂ)
    (om : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop
    extends IsUnitaryOnThetaF σ JS JT xi0 ψ om where
  triv : ∀ g ∈ GfCF σ JS, ∀ h ∈ GfCF σ JT, ∀ f, IsThetaFunOF σ JS JT xi0 ψ f → om (g, h) f = f
  Heisenberg₂ : ∀ g ∈ GinfCF σ JS, ∀ h ∈ GinfCF σ JT, ∀ w₀ f, IsThetaFunOF σ JS JT xi0 ψ f →
    om (g, h) (heisOF σ JS JT xi0 ψ w₀ f) = heisOF σ JS JT xi0 ψ (actOF σ JS JT g h w₀) (om (g, h) f)

section Lemmas

variable {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E} {ψ : AddChar (AF F) ℂ}

theorem heisOF_add (w : WOF F E nS nT) (f g : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (f + g) = heisOF σ JS JT xi0 ψ w f + heisOF σ JS JT xi0 ψ w g := by
  funext x
  simp only [heisOF, Pi.add_apply, mul_add]

theorem heisOF_smul (c : ℂ) (w : WOF F E nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ w (c • f) = c • heisOF σ JS JT xi0 ψ w f := by
  funext x
  simp only [heisOF, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_add {f g : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) (hg : IsThetaFunOF σ JS JT xi0 ψ g) :
    IsThetaFunOF σ JS JT xi0 ψ (f + g) := {
  quasi γ w := by
    simp only [Pi.add_apply]
    rw [hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    obtain ⟨V, hV, hV'⟩ := hg.level
    exact ⟨U ⊓ V, hU.inter hV, fun u hu h0 => by rw [heisOF_add, hU' u hu.1 h0, hV' u hu.2 h0]⟩
  cont := hf.cont.add hg.cont
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w) }

theorem theta_zero : IsThetaFunOF σ JS JT xi0 ψ (0 : WOF F E nS nT → ℂ) := {
  quasi γ w := by simp
  level := ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext x; simp [heisOF]⟩
  cont := continuous_const
  smooth k L hL h0 w := contDiff_const }

theorem theta_smul (c : ℂ) {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT xi0 ψ f) :
    IsThetaFunOF σ JS JT xi0 ψ (c • f) := {
  quasi γ w := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi]
    ring
  level := by
    obtain ⟨U, hU, hU'⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisOF_smul, hU' u hu h0]⟩
  cont := hf.cont.const_smul c
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).const_smul c }


variable (σ JS JT xi0 ψ) in
def thetaSubF : Submodule ℂ (WOF F E nS nT → ℂ) where
  carrier := {f | IsThetaFunOF σ JS JT xi0 ψ f}
  add_mem' := theta_add
  zero_mem' := theta_zero
  smul_mem' := fun a _ hf => theta_smul a hf

theorem mtF_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : GAF σ J) : mtF σ J (g * g') = mtF σ J g * mtF σ J g' := by
  unfold mtF
  rw [map_mul]
  rfl

theorem actOF_mul (g g' : GAF σ JS) (h h' : GAF σ JT) (u : WOF F E nS nT) :
    actOF σ JS JT (g * g') (h * h') u = actOF σ JS JT g h (actOF σ JS JT g' h' u) := by
  unfold actOF
  rw [_root_.mul_inv_rev, mtF_mul, mtF_mul]
  simp only [Matrix.mul_assoc]

theorem mem_GfCF_of_supp {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {a : AEF F E} (ha : infPartF F E a = 0) {g : GAF σ J}
    (hg : ∀ i j, a * (mtF σ J g - 1) i j = (mtF σ J g - 1) i j) : g ∈ GfCF σ J := by
  rw [GfCF, MonoidHom.mem_ker, MonoidHom.comp_apply]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPartF F E ((mtF σ J g - 1) i j) = 0 := by rw [← hg i j, map_mul, ha, zero_mul]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
  show infPartF F E (mtF σ J g i j) = ((1 : GL (Fin n) (Ainf F ⊗[F] E)) : Matrix _ _ _) i j
  rw [h, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem infPartF_placeIdem {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (h : IsPlaceIdemF F v ε) :
    infPartF F E (algebraMap (AF F) (AEF F E) ε) = 0 := by
  obtain ⟨α, rfl, -⟩ := h
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 α ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 α) = 0 from rfl, TensorProduct.zero_tmul]

theorem mem_GfCF_of_suppAt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} (he : IsSplitIdemF σ e) {g : GAF σ J}
    (hg : SuppAtF σ e J g) : g ∈ GfCF σ J := by
  obtain ⟨-, -, v, ε, h1, h2⟩ := he
  exact mem_GfCF_of_supp (h2 ▸ infPartF_placeIdem h1) hg

theorem isHeckeCharF_pow {η : (AEF F E)ˣ →* Circle} (h : IsHeckeCharF η) (n : ℕ) : IsHeckeCharF (η ^ n) :=
  ⟨h.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.2 x, one_pow]⟩

theorem resEtaF_pow {η : (AEF F E)ˣ →* Circle} (h : ResEtaF η 1) (n : ℕ) : ResEtaF (η ^ n) n :=
  ⟨h.1, fun e he a => by rw [MonoidHom.pow_apply, h.2 e he a, pow_one]⟩

theorem exists_extend {Γ V : Type} [Monoid Γ] [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    (Om : Γ →* Module.End ℂ M) : ∃ om : Γ →* Module.End ℂ V, ∀ p (m : M), om p m = Om p m := by
  obtain ⟨C, hC⟩ := M.exists_isCompl
  let e := M.prodEquivOfIsCompl C hC
  refine ⟨{ toFun := fun p => e.conj ((Om p).prodMap LinearMap.id), map_one' := ?_, map_mul' := fun p q => ?_ }, ?_⟩
  · rw [map_one]
    exact (congrArg e.conj LinearMap.prodMap_id).trans e.conj_id
  · rw [map_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← e.conj_comp, LinearMap.prodMap_comp,
      LinearMap.id_comp]
  · intro p m
    show e (((Om p).prodMap LinearMap.id) (e.symm m)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp [e]

end Lemmas

end GlobalTheory.WeilPartsF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess bas wd wdb)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.FinChart
open scoped ENNReal

namespace GlobalTheory.ChernMA

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {B : LB Y} {φ : Weight p σ B} {A : FinHolAtlas D (CxPts p σ)}

variable [SecondCountableTopology (CxPts p σ)]

theorem restrict_chernPart (h : φ.IsCInf) (ε : ℤˣ) (c : AlgChart p σ D) :
    (φ.chernPart D ε).restrict c.finChart.source = ((volume.restrict c.finChart.target).withDensity
      fun z => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (c.finChart.symm z))).map c.finChart.symm := by
  ext T hT
  have ht := c.finChart.open_target.measurableSet
  have hs : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
    c.finChart.continuousOn_symm.aemeasurable ht
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin D → ℂ)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin D → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin D))
  rw [Measure.restrict_apply hT, Weight.chernPart_apply h ε c
      (hT.inter c.finChart.open_source.measurableSet) inter_subset_right,
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply', Measure.restrict_restrict' ht, inter_comm, AlgChart.finChart_source,
    c.e.image_source_inter_eq', ← hp.setLIntegral_comp_preimage_emb
      (MeasurableEquiv.measurableEmbedding _), inter_comm]
  rfl

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]


end GlobalTheory.ChernMA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess leviV)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier

namespace GlobalTheory

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

namespace Weight

variable {A B : LB X}

theorem SemiPosReg.tens {ψ : Weight p σ A} {φ : Weight p σ B} (hψ : ψ.IsCInf) (hφ : φ.IsCInf)
    (hψ' : ψ.SemiPosReg D) (hφ' : φ.SemiPosReg D) : (ψ.tens φ).SemiPosReg D := fun i c y hy ξ => by
  have h1 := (mem_ptsIn_inf.1 hy.2).1
  have h2 := (mem_ptsIn_inf.1 hy.2).2
  have e := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add (hψ.contDiffAt c hy.1 h1)
    (hφ.contDiffAt c hy.1 h2) ξ
  have := add_nonneg (hψ' i.1 c y ⟨hy.1, h1⟩ ξ) (hφ' i.2 c y ⟨hy.1, h2⟩ ξ)
  rw [← Complex.add_re, ← e] at this
  exact this

theorem SemiPosReg.of_mul {E : LB X} (ψ : Weight p σ E) {φ : Weight p σ B} (hφ : φ.IsCInf)
    (hφ' : φ.SemiPosReg D) (c : ℝ) (hc : 0 ≤ c) (j : E.ι → B.ι)
    (hj : ∀ i y, y ∈ ptsIn p σ (E.U i) → y ∈ ptsIn p σ (B.U (j i)))
    (he : ∀ i y, ψ.φ i y = c * φ.φ (j i) y) : ψ.SemiPosReg D := fun i c' y hy ξ => by
  have h1 := hj i y hy.2
  have hf : (fun v => ((ψ.φ i (c'.e.symm v) : ℝ) : ℂ)) =
      fun v => ((c * φ.φ (j i) (c'.e.symm v) : ℝ) : ℂ) := funext fun v => by rw [he]
  rw [hf, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul c (hφ.contDiffAt c' hy.1 h1) ξ,
    Complex.re_ofReal_mul]
  exact mul_nonneg hc (hφ' (j i) c' y ⟨hy.1, h1⟩ ξ)

end Weight

namespace HermLB

variable {L M : HermLB p}

theorem SemiPos.tens (hL : L.SemiPos D) (hM : M.SemiPos D) : (L.tens M).SemiPos D := fun σ =>
  Weight.SemiPosReg.tens (L.cInf σ) (M.cInf σ) (hL σ) (hM σ)

theorem SemiPos.pow (hL : L.SemiPos D) (m : ℕ) : (L.pow m).SemiPos D := fun σ =>
  Weight.SemiPosReg.of_mul _ (L.cInf σ) (hL σ) ((m : ℤ) : ℝ) (by positivity) (fun j => j PUnit.unit)
    (fun _ _ h => mem_pow_iff.1 h) fun j y => (L.φ σ).zpow_φ (m : ℤ) j y

end HermLB

namespace ArInt

variable {ι : Type} [Fintype ι]

end ArInt

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordEqOfPerConj
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_of_mem (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X x v τ.1 i =
      if hi : X.p0 + i < r then ((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) ⟨X.p0 + i, hi⟩ else 0 := by
  unfold perFr
  rw [dite_eq_left τ.2]

theorem perFr_of_conj (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (j : Fin r)
    (hj : (j : ℕ) = X.p0 - 1 - i) :
    perFr X x v (conjEmb τ.1) i = hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
  have hcc : conjEmb (conjEmb τ.1) = τ.1 := by
    ext a; simp [conjEmb]
  have h1 : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have h2 : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [hcc]; exact τ.2
  have h3 : X.p0 - 1 - i < r := hj ▸ j.2
  unfold perFr
  rw [dite_eq_right h1, dite_eq_left h2, dite_eq_left h3]
  have key : ∀ (σ : E →+* ℂ) (hσ : σ ∈ X.Ψ), σ = τ.1 →
      hermC σ X.Gm (FD.col (mat x ⟨σ, hσ⟩) ⟨X.p0 - 1 - i, h3⟩) (Data.emb σ v) =
        hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
    intro σ hσ h
    subst h
    have : (⟨X.p0 - 1 - i, h3⟩ : Fin r) = j := Fin.ext hj.symm
    rw [this]
  exact key _ h2 hcc

theorem coord_eq_of_per_mem (X : Data E r) (τ : X.Ψ) (a : Fin r) (ha : X.p0 ≤ (a : ℕ)) (i : ℕ)
    (h : ∀ x v, per X x v (τ, a) = perFr X x v τ.1 i) : (a : ℕ) = X.p0 + i := by
  obtain ⟨x, hm⟩ : ∃ x : Frame X.Ψ r, mat x τ = 1 := ⟨fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), rfl⟩
  have h1 := h x (Pi.single a 1)
  rw [per_of_le X _ _ _ ha, perFr_of_mem, hm, inv_one, one_mulVec] at h1
  by_contra hne
  split_ifs at h1 with hi
  · have h2 : (⟨X.p0 + i, hi⟩ : Fin r) ≠ a := fun e => hne (by rw [← e])
    simp [Data.emb, Pi.single_eq_of_ne h2] at h1
  · simp [Data.emb] at h1

theorem coord_eq_of_per_conj (X : Data E r) (τ : X.Ψ) (a : Fin r) (ha : (a : ℕ) < X.p0) (i : ℕ)
    (h : ∀ x v, per X x v (τ, a) = perFr X x v (conjEmb τ.1) i) : (a : ℕ) = X.p0 - 1 - i := by
  have hle := X.p0_le
  obtain ⟨s, t, hst⟩ : ∃ s t, X.Gm s t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact X.Gm_det (Matrix.det_eq_zero_of_row_eq_zero a (hc a))
  obtain ⟨x, hm⟩ : ∃ x : Frame X.Ψ r, mat x τ = Matrix.single s a 1 :=
    ⟨fun _ => (Matrix.single s a 1 : Matrix (Fin r) (Fin r) ℂ), rfl⟩
  have h1 := h x (Pi.single t 1)
  rw [per_of_lt X _ _ _ ha, perFr_of_conj X _ _ τ i ⟨X.p0 - 1 - i, by omega⟩ rfl, hm] at h1
  by_contra hne
  have h2 : a ≠ (⟨X.p0 - 1 - i, by omega⟩ : Fin r) := fun e => hne (by rw [e])
  simp [hermC, FD.col, Data.emb, Matrix.single_apply, Pi.single_apply, h2, apply_ite, hst] at h1

theorem Dic.letter {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} {σ : c.F →+* ℂ}
    {X : Data E r} {g q0 n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (Dc : Dic Dw c σ X g q0 n a)
    (hσ : ∀ τ, Formalism.L2.PjFree.relab c σ τ = τ) (hm : ∀ τ, τ ∉ X.Ψ → Dw.mult τ ≤ X.p0) (ℓ : LtN Dw n) :
    (Dc.eL ℓ).2.2 = ℓ.2.2 ∧
      ((∃ k, (Dc.eL ℓ).2.1 = Sum.inl k ∧ ℓ.1 = (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) ∨
       (∃ k, (Dc.eL ℓ).2.1 = Sum.inr k ∧ ℓ.1 = conjEmb (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1)) := by
  have hd := Dc.dir_eq ℓ
  generalize Dc.eL ℓ = L at hd ⊢
  obtain ⟨t, ρ, b⟩ := L
  obtain ⟨τ, i, b'⟩ := ℓ
  simp only [letterDir] at hd ⊢
  have hb : b = b' := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    simp [Pi.single_eq_of_ne hne] at this
  subst hb
  have hj : Dc.idx.symm (rowOf X Dc.hr (t, ρ)) = Dc.e.symm ⟨τ, i⟩ := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact one_ne_zero this
  have hi : Dc.idx (Dc.e.symm ⟨τ, i⟩) = (t, rowIdx Dc.hr ρ) := by rw [← hj, Equiv.apply_symm_apply]; rfl
  have hty := Dc.ty_eq (Dc.e.symm ⟨τ, i⟩)
  have hper : ∀ x v, per X x v (t, rowIdx Dc.hr ρ) = perFr X x v τ i := fun x v => by
    have := Dc.per_eq x v (Dc.e.symm ⟨τ, i⟩)
    rwa [pv, Function.comp_apply, hi, hσ, Equiv.apply_symm_apply] at this
  rw [hi, hσ, Equiv.apply_symm_apply] at hty
  refine ⟨rfl, ?_⟩
  rcases ρ with k | k
  · have h1 : τ = t.1 := hty.symm.trans (rowType_rowOf_inl X Dc.hr t k)
    subst h1
    have h2 := coord_eq_of_per_mem X t _ (by simp) i hper
    rw [rowIdx_inl] at h2
    exact Or.inl ⟨k, rfl, rfl, by omega⟩
  · have h1 : τ = conjEmb t.1 := hty.symm.trans (rowType_rowOf_inr X Dc.hr t k)
    subst h1
    have hk := k.2
    have h2 := coord_eq_of_per_conj X t _ (by rw [rowIdx_inr]; omega) i hper
    rw [rowIdx_inr] at h2
    have h3 := hm _ ((X.cmType t.1).1 t.2)
    have h4 : (i : ℕ) < X.p0 := lt_of_lt_of_le i.2 h3
    exact Or.inr ⟨k, rfl, rfl, by omega⟩

end Letters


end GlobalTheory.AdTh
end
