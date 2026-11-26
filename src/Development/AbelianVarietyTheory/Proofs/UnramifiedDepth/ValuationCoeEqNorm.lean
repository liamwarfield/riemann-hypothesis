module

public import ReciprocityTheory.DualLattices.SubMemOfCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
open Ideal

namespace GlobalTheory.PadicComplexHost

variable (p : ℕ) [hp : Fact p.Prime]

theorem valuation_coe_eq_norm (x : ℂ_[p]) : ((Valued.v x : NNReal) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl),
    Valuation.embedding_restrict]

theorem norm_p : ‖((p : ℕ) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← valuation_coe_eq_norm, PadicComplex.valuation_p]; simp

theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

theorem mem_iff_norm (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [← valuation_coe_eq_norm]
  change Valued.v x ≤ 1 ↔ _
  exact_mod_cast Iff.rfl

theorem not_isUnit_p : ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]) := by
  intro h
  have h1 := (PadicComplexInt.integers p).one_of_isUnit h
  rw [map_natCast] at h1
  have h2 := valuation_coe_eq_norm p ((p : ℕ) : ℂ_[p])
  rw [h1, norm_p] at h2
  have := inv_p_lt_one p
  rw [← h2] at this
  simp at this

theorem smodEq_iff (n : ℕ) (x y : 𝓞_ℂ_[p]) :
    x ≡ y [SMOD ((span {((p : ℕ) : 𝓞_ℂ_[p])}) ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton, (PadicComplexInt.integers p).dvd_iff_le, map_pow, map_natCast,
    ← norm_p, ← norm_pow, ← valuation_coe_eq_norm, ← valuation_coe_eq_norm, NNReal.coe_le_coe]
  rfl

theorem tendsto_inv_p_pow :
    Filter.Tendsto (fun n : ℕ => (p : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_p_lt_one p)

theorem isHausdorff : IsHausdorff (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun x hx => ?_⟩
  have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := fun n => by
    simpa using (smodEq_iff p n x 0).1 (hx n)
  have h0 : ‖(x : ℂ_[p])‖ ≤ 0 :=
    ge_of_tendsto (tendsto_inv_p_pow p) (Filter.Eventually.of_forall h)
  exact Subtype.ext (norm_le_zero_iff.1 h0)

theorem isPrecomplete : IsPrecomplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := by
  refine ⟨fun f hf => ?_⟩
  have h : ∀ {m n : ℕ}, m ≤ n → ‖(f m : ℂ_[p]) - (f n : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ m :=
    fun hmn => (smodEq_iff p _ _ _).1 (hf hmn)
  have hc : CauchySeq fun n => (f n : ℂ_[p]) := by
    refine cauchySeq_of_le_geometric (p : ℝ)⁻¹ 1 (inv_p_lt_one p) fun n => ?_
    rw [dist_eq_norm, one_mul]
    exact h (Nat.le_succ n)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hm : ∀ m : ℕ, ‖(f m : ℂ_[p]) - L‖ ≤ (p : ℝ)⁻¹ ^ m := fun m =>
    le_of_tendsto ((tendsto_const_nhds.sub hL).norm)
      ((Filter.eventually_ge_atTop m).mono fun n hn => h hn)
  have hLO : L ∈ 𝓞_ℂ_[p] := by
    rw [mem_iff_norm]
    exact le_of_tendsto hL.norm
      (Filter.Eventually.of_forall fun n => (mem_iff_norm p _).1 (f n).2)
  exact ⟨⟨L, hLO⟩, fun n => (smodEq_iff p n _ _).2 (hm n)⟩

theorem isAdicComplete : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] :=
  { isHausdorff p, isPrecomplete p with }

theorem main : ∀ (p : ℕ) [Fact p.Prime], ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p])
    (ε : PreTilt 𝓞_ℂ_[p] p), (Valued.v : Valuation ℂ_[p] NNReal).Integers 𝓞_ℂ_[p] ∧
      IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p := by
  intro p _
  have h1 : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]) := ⟨not_isUnit_p p⟩
  have h2 := isAdicComplete p
  obtain ⟨ε, hε⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) ℂ_[p] Valued.v 𝓞_ℂ_[p]
    (PadicComplexInt.integers p)
  exact ⟨h1, h2, ε, PadicComplexInt.integers p, hε⟩

end GlobalTheory.PadicComplexHost
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilCoord

section Alg

variable {R : Type} [CommRing R] {n : ℕ} {B : Type} [CommRing B] [Algebra R B]

theorem ext_of_nil (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (φ₁ φ₂ : B →ₐ[R] A)
    (h : ∀ b, IsNilpotent (φ₁ b - φ₂ b))
    (hs : ∀ j : Fin n, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by
  letI : Algebra (MvPolynomial (Fin n) R) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hπ
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A := φ₁.comp π
  have hρ2 : φ₂.comp π = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin n) R] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  obtain ⟨s, hsg⟩ := (inferInstance : Algebra.FiniteType (MvPolynomial (Fin n) R) B).out
  let J : Ideal A := Ideal.span ((fun b => φ₁ b - φ₂ b) '' (s : Set B))
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical
      (Submodule.fg_span (s.finite_toSet.image _)), Ideal.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact h b
  have : ψ₁ = ψ₂ := by
    apply Algebra.FormallyUnramified.lift_unique J hJ
    apply AlgHom.ext_of_adjoin_eq_top hsg
    intro b hb
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨b, hb, rfl⟩
  ext x
  exact AlgHom.congr_fun this x

theorem exists_of_nil (π : MvPolynomial (Fin n) R →ₐ[R] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra R A] (e : B →ₐ[R] A) (a : Fin n → A)
    (ha : ∀ j, IsNilpotent (a j)) :
    ∃ φ : B →ₐ[R] A, (∀ b, IsNilpotent (φ b - e b)) ∧
      ∀ j, φ (π (MvPolynomial.X j)) = e (π (MvPolynomial.X j)) + a j := by
  letI : Algebra (MvPolynomial (Fin n) R) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hπ
  let ρ : MvPolynomial (Fin n) R →ₐ[R] A :=
    MvPolynomial.aeval (fun j => e (π (MvPolynomial.X j)) + a j)
  letI : Algebra (MvPolynomial (Fin n) R) A := ρ.toRingHom.toAlgebra
  let J : Ideal A := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical
      (Submodule.fg_span (Set.finite_range _)), Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact ha b
  let mk : A →ₐ[MvPolynomial (Fin n) R] A ⧸ J := Ideal.Quotient.mkₐ _ J
  have hf₀ : ((Ideal.Quotient.mkₐ R J).comp e).comp π = (Ideal.Quotient.mkₐ R J).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
      MvPolynomial.aeval_X]
    rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.subset_span ⟨j, rfl⟩
  let f₀ : B →ₐ[MvPolynomial (Fin n) R] A ⧸ J :=
    { ((Ideal.Quotient.mkₐ R J).comp e).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hf₀ p }
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hker : IsNilpotent (RingHom.ker (mk : A →+* A ⧸ J)) := by
    have : RingHom.ker (mk : A →+* A ⧸ J) = J := Ideal.mk_ker
    rw [this]
    exact hJ
  let φ' := Algebra.FormallySmooth.liftOfSurjective f₀ mk hmk hker
  have hφ' : mk.comp φ' = f₀ := Algebra.FormallySmooth.comp_liftOfSurjective f₀ mk hmk hker
  have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
  refine ⟨{ φ'.toRingHom with commutes' := fun r => ?_ }, fun b => ?_, fun j => ?_⟩
  · show φ' (algebraMap R B r) = _
    rw [← π.commutes, hc, ρ.commutes]
  · have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (e b) := AlgHom.congr_fun hφ' b
    rw [Ideal.Quotient.eq] at e1
    obtain ⟨N, hN⟩ := hJ
    refine ⟨N, ?_⟩
    have := Ideal.pow_mem_pow e1 N
    rw [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact this
  · show φ' (π _) = _
    rw [hc]
    exact MvPolynomial.aeval_X _ j

end Alg

theorem exists_etale_chart {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    [IsLocalRing R₀] (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ (C : Chart G) (π : MvPolynomial (Fin g) R₀ →ₐ[R₀] Γ(G.left, C.U)), π.toRingHom.Etale := by
  let e0 : Spec (CommRingCat.of R₀) ⟶ G.left := (η[G]).left
  obtain ⟨U, hU, V, hV, hx, e, h⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (e0 (IsLocalRing.closedPoint R₀))
  have hsp : ∀ p : PrimeSpectrum R₀, p ⤳ IsLocalRing.closedPoint R₀ := fun p =>
    (PrimeSpectrum.le_iff_specializes _ _).mp
      (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum R₀).isPrime.ne_top)
  have hw : e0 ≫ G.hom = 𝟙 _ := Over.w (η[G])
  have hU' : U = ⊤ := by
    rw [eq_top_iff]
    intro p _
    refine (hsp p).mem_open U.isOpen ?_
    have h1 : (e0 ≫ G.hom) (IsLocalRing.closedPoint R₀) ∈ U := by
      exact (Scheme.Hom.comp_apply e0 G.hom (IsLocalRing.closedPoint R₀)).symm ▸ e hx
    rw [hw] at h1
    exact h1
  subst hU'
  let C : Chart G := ⟨V, hV, fun p _ => (hsp p).mem_open (e0 ⁻¹ᵁ V).isOpen hx⟩
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension g (alg0 C) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv h
  obtain ⟨π, hπ1, hπ2⟩ := h2.exists_etale_mvPolynomial
  clear_value C
  exact ⟨C, { π with commutes' := fun r => RingHom.congr_fun hπ1 r }, hπ2⟩

theorem nilpotent_coordinates :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G),
      (∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) := by
  intro R₀ _ G _ _ _ g hG
  classical
  obtain ⟨C, π, hπ⟩ := exists_etale_chart G g hG
  have key : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S),
      ∃ φ : Γ(G.left, C.U) →ₐ[R₀] S, (∀ i, IsNilpotent (a i)) →
        (∀ b, IsNilpotent (φ b - algebraMap R₀ S (eps C b))) ∧
        ∀ j, φ (π (MvPolynomial.X j)) = algebraMap R₀ S (eps C (π (MvPolynomial.X j))) + a j := by
    intro S _ _ a
    by_cases ha : ∀ i, IsNilpotent (a i)
    · obtain ⟨φ, h⟩ := exists_of_nil π hπ ((Algebra.ofId R₀ S).comp (eps C)) a ha
      exact ⟨φ, fun _ => h⟩
    · exact ⟨(Algebra.ofId R₀ S).comp (eps C), fun h => absurd h ha⟩
  choose F hF using key
  have uniq : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S) (φ : Γ(G.left, C.U) →ₐ[R₀] S),
      (∀ i, IsNilpotent (a i)) → (∀ b, IsNilpotent (φ b - algebraMap R₀ S (eps C b))) →
      (∀ j, φ (π (MvPolynomial.X j)) = algebraMap R₀ S (eps C (π (MvPolynomial.X j))) + a j) →
      φ = F S a := by
    intro S _ _ a φ ha h1 h2
    refine ext_of_nil π hπ _ _ (fun b => ?_) (fun j => ?_)
    · have := (Commute.all _ _).isNilpotent_sub (h1 b) ((hF S a ha).1 b)
      rwa [sub_sub_sub_cancel_right] at this
    · rw [h2, (hF S a ha).2]
  refine ⟨fun S _ _ a => pt C (F S a), ?_, ?_, ?_, ?_⟩
  · intro S _ _
    show pt C (F S 0) = 1
    rw [← uniq S 0 ((Algebra.ofId R₀ S).comp (eps C)) (fun _ => IsNilpotent.zero)
      (fun b => by simp [Algebra.ofId_apply]) (fun j => by simp [Algebra.ofId_apply]), pt_eps]
  · intro S _ _ S' _ _ φ a ha
    show spMap φ ≫ pt C (F S a) = pt C (F S' _)
    rw [spMap_pt]
    congr 1
    refine uniq S' _ _ (fun i => (ha i).map φ) (fun b => ?_) (fun j => ?_)
    · have := ((hF S a ha).1 b).map φ
      rwa [map_sub, AlgHom.commutes] at this
    · rw [AlgHom.comp_apply, (hF S a ha).2, map_add (f := _), AlgHom.commutes]
  · intro S _ _ a b ha hb h
    have h1 : F S a = F S b := pt_injective C h
    funext j
    have h2 := (hF S a ha).2 j
    rw [h1, (hF S b hb).2 j] at h2
    exact (add_left_cancel h2).symm
  · intro S _ _ S' _ _ ρ hρ hn z hz
    rw [← pt_eps C S'] at hz
    obtain ⟨φ, rfl⟩ := exists_pt C z (le_preimage_of_nil C ρ hρ hn z _ hz)
    rw [spMap_pt] at hz
    have h1 := pt_injective C hz
    have h2 : ∀ b, φ b - algebraMap R₀ S (eps C b) ∈ RingHom.ker ρ := by
      intro b
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero]
      exact AlgHom.congr_fun h1 b
    refine ⟨fun j => φ (π (MvPolynomial.X j)) - algebraMap R₀ S (eps C (π (MvPolynomial.X j))),
      fun j => h2 _, ?_⟩
    show pt C φ = pt C (F S _)
    congr 1
    exact uniq S _ φ (fun j => hn _ (h2 _)) (fun b => hn _ (h2 b)) (fun j => by rw [add_sub_cancel])

end GlobalTheory.NilCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinRepExistsIsPullbackSpec
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finRep_exists_isPullback_spec {X Y : Scheme.{0}} (m : X ⟶ Y) [IsFinite m] [Flat m]
    (O : CommRingCat.{0}) (u : Spec O ⟶ Y) :
    ∃ (A : CommRingCat.{0}) (φ : O ⟶ A) (y : Spec A ⟶ X),
      φ.hom.Finite ∧ φ.hom.Flat ∧ IsPullback y (Spec.map φ) m u := by
  let N := Limits.pullback m u
  haveI : IsAffine N := isAffine_of_isAffineHom (Limits.pullback.snd m u)
  let f : Spec Γ(N, ⊤) ⟶ Spec O := N.isoSpec.inv ≫ Limits.pullback.snd m u
  have hf : Spec.map (Spec.preimage f) = f := Spec.map_preimage f
  refine ⟨Γ(N, ⊤), Spec.preimage f, N.isoSpec.inv ≫ Limits.pullback.fst m u, ?_, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff, hf]
    infer_instance
  · rw [← HasRingHomProperty.Spec_iff (P := @Flat), hf]
    infer_instance
  · rw [hf]
    refine (IsPullback.of_hasPullback m u).of_iso N.isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_ <;> simp [f]

theorem finRep_one_left {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
    {P S : Type} [CommRing P] [Algebra R₀ P] [CommRing S] [Algebra R₀ S] (g : P →ₐ[R₀] S) :
    (1 : sp (R₀ := R₀) S ⟶ G).left =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (1 : sp (R₀ := R₀) P ⟶ G).left := by
  rw [← spMap_left, ← Over.comp_left, MonObj.comp_one]

theorem finRep_kernel_mul_finite_free :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ), IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra (O : Type) A) (_ : Algebra R₀ A) (_ : IsScalarTower R₀ (O : Type) A),
      Module.Free (O : Type) A ∧ Module.Finite (O : Type) A ∧ ∃ y : sp (R₀ := R₀) A ⟶ G, y ^ p = 1 ∧
      ∀ (S : Type) [CommRing S] [Algebra (O : Type) S] [Algebra R₀ S] [IsScalarTower R₀ (O : Type) S] (z : sp (R₀ := R₀) S ⟶ G), z ^ p = 1 →
        ∃! φ : A →ₐ[(O : Type)] S, spMap (φ.restrictScalars R₀) ≫ y = z) := by
  intro R₀ _ G _ _ O p hfin hflat _
  obtain ⟨A, φ, y, hφf, hφl, hpb⟩ := finRep_exists_isPullback_spec ((𝟙 G) ^ p : G ⟶ G).left
    (CommRingCat.of (O : Type)) (1 : sp (R₀ := R₀) (O : Type) ⟶ G).left
  letI : Algebra (O : Type) A := φ.hom.toAlgebra
  letI : Algebra R₀ A := (φ.hom.comp (algebraMap R₀ (O : Type))).toAlgebra
  haveI : IsScalarTower R₀ (O : Type) A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (O : Type) A := hφf
  haveI : Module.Flat (O : Type) A := hφl
  have hpow : ∀ {T : Over (Spec (CommRingCat.of R₀))} (z : T ⟶ G),
      z.left ≫ ((𝟙 G) ^ p : G ⟶ G).left = (z ^ p).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hy : y ≫ G.hom = (sp (R₀ := R₀) A).hom := by
    rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hpb.w, Category.assoc,
      Over.w (1 : sp (R₀ := R₀) (O : Type) ⟶ G)]
    simp only [sp, Over.mk_hom]
    rw [← Spec.map_comp]
    rfl
  let y' : sp (R₀ := R₀) A ⟶ G := Over.homMk y hy
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.free_of_flat_of_isLocalRing, inferInstance, y', ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [← hpow, finRep_one_left G (IsScalarTower.toAlgHom R₀ (O : Type) A)]
    exact hpb.w
  · intro S _ _ _ _ z hz
    have hw : z.left ≫ ((𝟙 G) ^ p : G ⟶ G).left =
        Spec.map (CommRingCat.ofHom (algebraMap (O : Type) S)) ≫
          (1 : sp (R₀ := R₀) (O : Type) ⟶ G).left := by
      rw [hpow, hz, finRep_one_left G (IsScalarTower.toAlgHom R₀ (O : Type) S)]
      rfl
    let l : Spec (CommRingCat.of S) ⟶ Spec A := hpb.lift _ _ hw
    have hl : Spec.map (Spec.preimage l) = l := Spec.map_preimage l
    have h1 : φ ≫ Spec.preimage l = CommRingCat.ofHom (algebraMap (O : Type) S) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hl]
      exact hpb.lift_snd _ _ hw
    refine ⟨⟨(Spec.preimage l).hom, fun r => congrArg (fun f => f.hom r) h1⟩, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change Spec.map (Spec.preimage l) ≫ y = z.left
      rw [hl]
      exact hpb.lift_fst _ _ hw
    · intro ψ hψ
      have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom : A ⟶ CommRingCat.of S) = l := by
        apply hpb.hom_ext
        · rw [hpb.lift_fst _ _ hw, ← hψ]
          rfl
        · rw [hpb.lift_snd _ _ hw, ← Spec.map_comp]
          congr 1
          ext r
          exact ψ.commutes r
      have h3 := Spec.map_injective (h2.trans hl.symm)
      ext a
      exact congrArg (fun f => f.hom a) h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfNaturalOnNilpotent
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private noncomputable abbrev serNatI (R₀ κ : Type) [CommRing R₀] (N : ℕ) : Ideal (MvPolynomial κ R₀) :=
  Ideal.span (Set.range fun j : κ => (MvPolynomial.X j : MvPolynomial κ R₀) ^ N)

private lemma serNat_coeff {R₀ κ : Type} [CommRing R₀] [DecidableEq κ] {N : ℕ}
    {q : MvPolynomial κ R₀} (hq : q ∈ serNatI R₀ κ N) :
    ∀ m : κ →₀ ℕ, (∀ j, m j < N) → AddMonoidAlgebra.coeff q m = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨j, rfl⟩ m hm
    simp only [MvPolynomial.coeff_X_pow]
    rw [if_neg]
    rintro rfl
    simpa using hm j
  · intro m _; simp
  · intro x y _ _ hx hy m hm
    rw [MvPolynomial.coeff_add, hx m hm, hy m hm, add_zero]
  · intro r x _ hx m hm
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2, mul_zero]
    intro j
    have : p.1 + p.2 = m := by simpa using hp
    have h2 := hm j
    rw [← this, Finsupp.add_apply] at h2
    omega

private lemma serNat_nil {R₀ κ : Type} [CommRing R₀] (N : ℕ) (j : κ) :
    (Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)) ^ N = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨j, rfl⟩

private lemma serNat_aeval {R₀ κ : Type} [CommRing R₀] [Fintype κ] [DecidableEq κ]
    {S : Type} [CommRing S] [Algebra R₀ S] {N : ℕ} {a : κ → S} (ha : ∀ i, a i ^ N = 0)
    (q : MvPolynomial κ R₀) :
    MvPolynomial.aeval a q = ∑ e : κ → Fin N, algebraMap R₀ S (AddMonoidAlgebra.coeff
      q (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ))) * ∏ i, a i ^ (e i : ℕ) := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add (f := _), MvPolynomial.coeff_add, add_mul, Finset.sum_add_distrib, hp, hq]
  | monomial m r =>
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    by_cases hm : ∀ j, m j < N
    · rw [Finset.sum_eq_single (fun j => (⟨m j, hm j⟩ : Fin N))]
      · rw [MvPolynomial.coeff_monomial, if_pos]
        ext j; simp
      · intro e _ he
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply he
        funext j
        apply Fin.ext
        simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · push Not at hm
        obtain ⟨j, hj⟩ := hm
        rw [Finset.prod_eq_zero (f := fun i => a i ^ m i) (Finset.mem_univ j)
          (pow_eq_zero_of_le hj (ha j)), mul_zero]
      · intro e _
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply hm
        intro j
        simp [h]

theorem exists_series_of_natural_on_nilpotent :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) := by
  intro hE R₀ _ κ _ _ c hc
  choose p hp using fun N : ℕ => Ideal.Quotient.mk_surjective (I := serNatI R₀ κ N)
    (c (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N)
      (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)))
  have key : ∀ (N : ℕ) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, a i ^ N = 0) →
      c S a = MvPolynomial.aeval a (p N) := by
    intro N S _ _ a ha
    let φ : (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ (serNatI R₀ κ N) (MvPolynomial.aeval a) (by
        intro x hx
        have : serNatI R₀ κ N ≤ RingHom.ker (MvPolynomial.aeval (R := R₀) a) := by
          refine Ideal.span_le.2 ?_
          rintro _ ⟨j, rfl⟩
          simp [RingHom.mem_ker, ha j]
        exact this hx)
    have hφ : ∀ x, φ (Ideal.Quotient.mk (serNatI R₀ κ N) x) = MvPolynomial.aeval a x :=
      fun x => rfl
    have h := hc _ S φ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => ⟨N, serNat_nil N j⟩)
    rw [← hp N, hφ] at h
    simp only [hφ, MvPolynomial.aeval_X] at h
    exact h.symm
  have compat : ∀ N M : ℕ, N ≤ M → ∀ m : κ →₀ ℕ, (∀ j, m j < N) →
      AddMonoidAlgebra.coeff (p M) m = AddMonoidAlgebra.coeff (p N) m := by
    intro N M h m hm
    have h1 := key M _ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => pow_eq_zero_of_le h (serNat_nil N j))
    have h2 : MvPolynomial.aeval (R := R₀)
        (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
        = Ideal.Quotient.mkₐ R₀ (serNatI R₀ κ N) := by
      ext j; simp
    rw [← hp N, h2, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at h1
    have h3 := serNat_coeff h1 m hm
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at h3
    exact h3.symm
  refine ⟨fun m => AddMonoidAlgebra.coeff (p (Finset.univ.sup m + 1)) m, ?_⟩
  intro S _ _ a ha
  choose n hn using ha
  have hN : ∀ i, a i ^ (Finset.univ.sup n) = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)
  generalize Finset.univ.sup n = N at hN
  refine Eq.trans ?_ ((hE _ S a).1 N hN).symm
  rw [key N S a hN, serNat_aeval hN]
  unfold tEval
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 2
  set m : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ) with hm
  change _ = AddMonoidAlgebra.coeff (p (Finset.univ.sup m + 1)) m
  rw [← compat N (max N (Finset.univ.sup m + 1)) (le_max_left _ _) m (fun j => by simp [hm]),
    compat _ _ (le_max_right _ _) m
      (fun j => Nat.lt_succ_of_le (Finset.le_sup (f := m) (Finset.mem_univ j)))]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GroupLawPowerSeries
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChLaw

private lemma nil_of_mem_span {S : Type} [CommRing S] {s : Set S} (hs : ∀ a ∈ s, IsNilpotent a)
    {c : S} (hc : c ∈ Ideal.span s) : IsNilpotent c := by
  have h : Ideal.span s ≤ nilradical S := Ideal.span_le.2 fun a ha => mem_nilradical.2 (hs a ha)
  exact mem_nilradical.1 (h hc)

theorem groupLaw_powerSeries :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (g : ℕ) (x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)),
    ((∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : Fin g → S),
        (∀ i, IsNilpotent (a i)) → spMap φ ≫ x S a = x S' (fun i => φ (a i))) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b) ∧
      (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (ρ : S →ₐ[R₀] S'), Function.Surjective ρ →
        (∀ a ∈ RingHom.ker ρ, IsNilpotent a) → ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)) →
    ∃ F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) →
      (∀ k, fAdd F a b k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ x S a * x S b = x S (fAdd F a b)) := by
  classical
  intro _ h2 R₀ _ G _ _ g x ⟨h0, hnat, hinj, hsur⟩
  have hex : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∃ c : Fin g → S,
        (∀ k, c k ∈ Ideal.span (Set.range a ∪ Set.range b)) ∧ (∀ k, IsNilpotent (c k)) ∧
        x S a * x S b = x S c := by
    intro S _ _ a b ha hb
    set I : Ideal S := Ideal.span (Set.range a ∪ Set.range b) with hI
    have hnil : ∀ c ∈ I, IsNilpotent c := fun c hc =>
      nil_of_mem_span (by rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩); exacts [ha i, hb i]) hc
    have hker : ∀ c, c ∈ RingHom.ker (Ideal.Quotient.mkₐ R₀ I) ↔ c ∈ I := fun c => by
      rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    have hz : spMap (Ideal.Quotient.mkₐ R₀ I) ≫ (x S a * x S b) = 1 := by
      have ea : (fun i => Ideal.Quotient.mkₐ R₀ I (a i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inl ⟨i, rfl⟩))
      have eb : (fun i => Ideal.Quotient.mkₐ R₀ I (b i)) = 0 := funext fun i =>
        (hker _).2 (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
      rw [MonObj.comp_mul, hnat _ _ _ a ha, hnat _ _ _ b hb, ea, eb, h0, _root_.mul_one]
    obtain ⟨c, hc, hzc⟩ := hsur S (S ⧸ I) (Ideal.Quotient.mkₐ R₀ I)
      (Ideal.Quotient.mkₐ_surjective R₀ I) (fun c hc => hnil c ((hker c).1 hc)) _ hz
    exact ⟨c, fun k => (hker _).1 (hc k), fun k => hnil _ ((hker _).1 (hc k)), hzc⟩
  choose cc hc1 hc2 hc3 using hex
  have hF : ∀ k : Fin g, ∃ f : MvPowerSeries (Fin g ⊕ Fin g) R₀,
      ∀ (S : Type) [CommRing S] [Algebra R₀ S] (u : Fin g ⊕ Fin g → S)
        (hu : ∀ i, IsNilpotent (u i)),
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k =
          nEval f u := by
    intro k
    obtain ⟨f, hf⟩ := h2 (R₀ := R₀) (κ := Fin g ⊕ Fin g)
      (fun S _ _ u => if hu : ∀ i, IsNilpotent (u i) then
        cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i)) (fun _ => hu _) (fun _ => hu _) k
        else 0) (by
        intro S _ _ S' _ _ φ u hu
        have hu' : ∀ i, IsNilpotent (φ (u i)) := fun i => (hu i).map φ
        simp only [dif_pos hu, dif_pos hu']
        have := hinj S'
          (fun j => φ (cc S (fun i => u (Sum.inl i)) (fun i => u (Sum.inr i))
            (fun _ => hu _) (fun _ => hu _) j))
          (cc S' (fun i => φ (u (Sum.inl i))) (fun i => φ (u (Sum.inr i)))
            (fun _ => hu' _) (fun _ => hu' _))
          (fun j => (hc2 _ _ _ _ _ j).map φ) (hc2 _ _ _ _ _) (by
            rw [← hnat _ _ φ _ (hc2 _ _ _ _ _), ← hc3, ← hc3, MonObj.comp_mul,
              hnat _ _ φ _ (fun _ => hu _), hnat _ _ φ _ (fun _ => hu _)])
        exact congrFun this k)
    refine ⟨f, fun S _ _ u hu => ?_⟩
    have := hf S u hu
    simpa only [dif_pos hu] using this
  choose F hF using hF
  refine ⟨F, fun S _ _ a b ha hb => ?_⟩
  have e : fAdd F a b = cc S a b ha hb := by
    funext k
    have hu : ∀ i, IsNilpotent (Sum.elim a b i) := by
      rintro (i | i); exacts [ha i, hb i]
    exact (hF k S (Sum.elim a b) hu).symm
  rw [e]
  exact ⟨hc1 S a b ha hb, hc3 S a b ha hb⟩

end GlobalTheory.ChLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfNil
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothNilLift

theorem exists_lift_of_nil {R A W K : Type} [CommRing R] [CommRing A] [CommRing W] [CommRing K]
    [Algebra R A] [Algebra R W] [Algebra R K] [Algebra.Smooth R A] (ρ : W →ₐ[R] K)
    (hρ : Function.Surjective ρ) (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (φ : A →ₐ[R] K) :
    ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  choose w hw using fun i : Fin n => hρ (φ (f (MvPolynomial.X i)))
  let g : MvPolynomial (Fin n) R →ₐ[R] W := MvPolynomial.aeval w
  have hg : ρ.comp g = φ.comp f := by
    ext i
    simp [g, hw]
  have hg' : ∀ p, ρ (g p) = φ (f p) := fun p => AlgHom.congr_fun hg p
  let J : Ideal W := (RingHom.ker f.toRingHom).map g.toRingHom
  have hJ : J ≤ RingHom.ker ρ := by
    refine Ideal.map_le_iff_le_comap.mpr fun p hp => ?_
    have hp' : f p = 0 := hp
    change ρ (g p) = 0
    rw [hg', hp', map_zero]
  have hJfg : J.FG := hker.map _
  have hJn : IsNilpotent J :=
    (Ideal.FG.isNilpotent_iff_le_nilradical hJfg).mpr fun a ha => hn a (hJ ha)
  let g₀ : (MvPolynomial (Fin n) R ⧸ RingHom.ker f) →ₐ[R] W ⧸ J :=
    Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp g) fun p hp =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.toRingHom hp)
  let E := Ideal.quotientKerAlgEquivOfSurjective hf
  let ψ₀ : A →ₐ[R] W ⧸ J := g₀.comp E.symm.toAlgHom
  have hψ₀ : ∀ p, ψ₀ (f p) = Ideal.Quotient.mk J (g p) := by
    intro p
    have h1 : E.symm (f p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change g₀ (E.symm (f p)) = _
    rw [h1]
    rfl
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.exists_lift J hJn ψ₀
  refine ⟨ψ, AlgHom.ext fun a => ?_⟩
  obtain ⟨p, rfl⟩ := hf a
  have h2 : Ideal.Quotient.mk J (ψ (f p)) = Ideal.Quotient.mk J (g p) :=
    (AlgHom.congr_fun hψ (f p)).trans (hψ₀ p)
  have h3 : ρ (ψ (f p) - g p) = 0 := hJ (Ideal.Quotient.eq.mp h2)
  rw [map_sub, sub_eq_zero] at h3
  change ρ (ψ (f p)) = _
  rw [h3, hg']

theorem exists_point_lift {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀)))
    [Smooth X.hom] {W K : Type} [CommRing W] [CommRing K] [Algebra R₀ W] [Algebra R₀ K]
    [IsLocalRing K] (ρ : W →ₐ[R₀] K) (hρ : Function.Surjective ρ)
    (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (z : sp (R₀ := R₀) K ⟶ X) :
    ∃ y : sp (R₀ := R₀) W ⟶ X, spMap ρ ≫ y = z := by
  let x : Spec (CommRingCat.of K) ⟶ X.left := z.left
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint K))) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum K) ⤳ IsLocalRing.closedPoint K :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum K).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen hmem
  let a0 : R₀ →+* Γ(X.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ X.hom.appLE ⊤ U le_top).hom
  letI : Algebra R₀ Γ(X.left, U) := a0.toAlgebra
  have hover : hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom a0) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of R₀))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, CommRingCat.ofHom_hom, Spec.map_comp]
  haveI : Algebra.Smooth R₀ Γ(X.left, U) := by
    have h1 : RingHom.Smooth (X.hom.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Smooth) X.hom inferInstance
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R₀))⟩ ⟨U, hU⟩ le_top
    have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom :=
      RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv.bijective
    exact h2.comp h1
  let φ := x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hφx : Spec.map φ ≫ hU.fromSpec = x := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
      (isAffineOpen_top (Spec (CommRingCat.of K))) hx
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  have hφ : φ.hom.comp a0 = algebraMap R₀ K := by
    have e : Spec.map (CommRingCat.ofHom (φ.hom.comp a0)) =
        Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := by
      calc Spec.map (CommRingCat.ofHom (φ.hom.comp a0))
          = Spec.map φ ≫ Spec.map (CommRingCat.ofHom a0) := by
            rw [← Spec.map_comp]; rfl
        _ = Spec.map φ ≫ hU.fromSpec ≫ X.hom := by rw [hover]
        _ = x ≫ X.hom := by rw [← Category.assoc, hφx]
        _ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := Over.w z
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let φ' : Γ(X.left, U) →ₐ[R₀] K := ⟨φ.hom, fun r => RingHom.congr_fun hφ r⟩
  obtain ⟨ψ, hψ⟩ := exists_lift_of_nil ρ hρ hn φ'
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec) ?_, ?_⟩
  · simp only [sp, Over.mk_hom]
    rw [Category.assoc, hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec = x
    rw [← hφx, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact AlgHom.congr_fun hψ a

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    Smooth G.hom → ∀ (K W : LAlg R₀) (ρW : LHom W K), IsNilOver ρW → SM B K W ρW) := by
  intro R₀ _ G _ _ B e hb _ hnat hsm K W ρW hρ
  refine ⟨hρ, fun x => ?_⟩
  obtain ⟨y, hy⟩ := exists_point_lift G ρW.1 hρ.1 hρ.2 (e K x)
  obtain ⟨y', rfl⟩ := (hb W).2 y
  exact ⟨y', (hb K).1 (by rw [hnat, hy])⟩

end GlobalTheory.SmoothNilLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsEqTangent
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory.CotPoints

private lemma comp_assoc' {R₀ : Type} [CommRing R₀] {A B C D : LAlg R₀} (h : LHom C D)
    (g : LHom B C) (f : LHom A B) : (h.comp g).comp f = h.comp (g.comp f) := rfl

private lemma coords_bijective {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {g : ℕ} (b : Module.Basis (Fin g) R M) :
    Function.Bijective (fun m : Fin g → N => ∑ k, b k ⊗ₜ[R] m k) := by
  classical
  have h : (fun m : Fin g → N => ∑ k, b k ⊗ₜ[R] m k) =
      (TensorProduct.equivFinsuppOfBasisLeft (N := N) b).symm ∘ Finsupp.equivFunOnFinite.symm := by
    funext m
    simp only [Function.comp, TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp
  rw [h]
  exact (LinearEquiv.bijective _).comp (Equiv.bijective _)

private lemma coords_nsmul {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {g : ℕ} (b : Module.Basis (Fin g) R M) (n : ℕ)
    (m : Fin g → N) : n • ∑ k, b k ⊗ₜ[R] m k = ∑ k, b k ⊗ₜ[R] (n • m k) := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => (map_nsmul (TensorProduct.mk R M N (b k)) n (m k)).symm

section

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)

private lemma ptMap_spec (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = LHom.id Tw.O ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = ptOf B D.L.τ t ∧
      ∀ j (φ' : LHom (D.fin.AAx j) Tw.O), φ'.comp (D.fin.sO j) = LHom.id Tw.O →
        B.map φ' (D.fin.y j) = ptOf B D.L.τ t → j = D.ptIdx t ∧ HEq φ' (D.ptMap t) :=
  Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))

private lemma ptOf_zero : ptOf B D.L.τ (0 : Nb p g) = 0 := by
  simp [ptOf]

end

theorem points_eq_tangent :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ (S : LAlg R₀) (s : LHom Tw.O S) (π : LHom S Tw.O) (hπ : π.SqZero), π.comp s = LHom.id Tw.O →
    (∀ m : Fin g → π.ker, (∀ k, p • m k = 0) → ∃! φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s ∧ π.comp φ = (D.ptMap 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) ∧
    (∀ φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s → π.comp φ = (D.ptMap 0) → ∃! m : Fin g → π.ker, (∀ k, p • m k = 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k))) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D S s π hπ hs
  obtain ⟨-, h2, h3⟩ := ptMap_spec D 0
  rw [ptOf_zero D] at h2 h3
  refine ⟨fun m hm => ?_, fun φ hφ hπφ => ?_⟩
  · have hz : p • B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k) = 0 := by
      rw [← map_nsmul, coords_nsmul]
      simp [hm]
    obtain ⟨i, φ, e1, e2, e3⟩ := D.fin.univ S s _ hz
    have h4 := h3 i (π.comp φ) (by rw [comp_assoc', e1, hs])
      (by rw [B.map_comp, e2]; exact (B.tg_ker π hπ _).2 ⟨_, rfl⟩)
    obtain ⟨hi, hφ⟩ := h4
    subst hi
    refine ⟨φ, ⟨e1, eq_of_heq hφ, e2⟩, fun φ' h' => ?_⟩
    exact eq_of_heq (e3 _ φ' h'.1 h'.2.2).2
  · have h0 : B.map π (B.map φ (D.fin.y (D.ptIdx 0))) = 0 := by
      rw [← B.map_comp, hπφ, h2]
    obtain ⟨v, hv⟩ := (B.tg_ker π hπ _).1 h0
    have hb := coords_bijective (N := π.ker) D.ch.gb
    obtain ⟨m, hm⟩ := hb.2 v
    have hm' : ∑ k, D.ch.gb k ⊗ₜ[R₀] m k = v := hm
    have hp : p • v = 0 := by
      apply B.tg_inj π hπ
      rw [map_nsmul, hv, ← map_nsmul, D.fin.y_p, map_zero, map_zero]
    refine ⟨m, ⟨fun k => ?_, by rw [hm', hv]⟩, fun m' h' => ?_⟩
    · have : (fun k => p • m k) = (0 : Fin g → π.ker) := by
        apply hb.1
        show ∑ k, D.ch.gb k ⊗ₜ[R₀] (p • m k) = ∑ k, D.ch.gb k ⊗ₜ[R₀] (0 : Fin g → π.ker) k
        rw [← coords_nsmul, hm', hp]
        simp
      exact congrFun this k
    · apply hb.1
      apply B.tg_inj π hπ
      show B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m' k) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)
      rw [← h'.2, hm', hv]

end GlobalTheory.CotPoints
end
