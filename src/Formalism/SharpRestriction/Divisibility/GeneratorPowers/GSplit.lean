module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.IdemDen

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem split_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) :
    (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).card = Module.finrank ℚ E ∧
      (normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).Nodup := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hIdef
  set p' : Ideal ℤ := Ideal.span {((p : ℕ) : ℤ)} with hp'def
  have hmax : p'.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : p' ≠ ⊥ := by
    rw [hp'def, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) p' = I := by
    rw [hp'def, Ideal.map_span, Set.image_singleton, map_natCast]
  have hI0 : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := normalizedFactors I with hMdef

  have hmem : ∀ P : Ideal (𝓞 E), P ∈ M ↔ P.IsPrime ∧ I ≤ P := fun P => Ideal.mem_normalizedFactors_iff hI0
  have hne : ∀ P ∈ M, P ≠ ⊥ := fun P hP h0 => hI0 (eq_bot_iff.2 (h0 ▸ ((hmem P).1 hP).2))
  have hlies : ∀ P ∈ M, P.LiesOver p' := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (hmem P).1 hP
    have hle : p' ≤ P.under ℤ := by
      rw [hp'def, Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) ((p : ℕ) : ℤ) ∈ P
      rw [map_natCast]
      exact hIP (Ideal.subset_span rfl)
    have hnt : P.under ℤ ≠ ⊤ := by
      intro ht
      apply hPp.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : ℤ) ∈ P.under ℤ := by rw [ht]; trivial
      change algebraMap ℤ (𝓞 E) 1 ∈ P at h1
      rwa [map_one] at h1
    exact ⟨hmax.eq_of_le hnt hle⟩
  have hcard1 : M.toFinset.card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset]
    have himg : HeightOneSpectrum.asIdeal '' {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal} =
        (M.toFinset : Set (Ideal (𝓞 E))) := by
      ext P
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset]
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine (hmem _).2 ⟨v.isPrime, ?_⟩
        rw [hIdef, Ideal.span_le, Set.singleton_subset_iff]
        exact hv
      · intro hP
        obtain ⟨hPp, hIP⟩ := (hmem P).1 hP
        exact ⟨⟨P, hPp, hne P hP⟩, hIP (Ideal.subset_span rfl), rfl⟩
    rw [← himg, Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)]
  haveI := hmax
  have hsum := Ideal.sum_ramification_inertia (R := ℤ) (S := 𝓞 E) ℚ E hp0
  have hfs : IsDedekindDomain.primesOverFinset p' (𝓞 E) = M.toFinset := by
    rw [IsDedekindDomain.primesOverFinset, hmap, hMdef, factors_eq_normalizedFactors]
  have hle : ∑ P ∈ M.toFinset, M.count P ≤ Module.finrank ℚ E := by
    rw [← hsum, hfs]
    refine Finset.sum_le_sum fun P hP => ?_
    have hPM : P ∈ M := Multiset.mem_toFinset.1 hP
    haveI := hlies P hPM
    haveI : P.IsPrime := ((hmem P).1 hPM).1
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count (by rw [hmap]; exact hI0) ‹P.IsPrime› (hne P hPM), hmap]
    exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg'_pos p' P)
  have hcard : M.card = ∑ P ∈ M.toFinset, M.count P := (Multiset.toFinset_sum_count_eq M).symm
  have h1 : M.toFinset.card ≤ M.card := Multiset.toFinset_card_le M
  have hMc : M.card = Module.finrank ℚ E := le_antisymm (hcard ▸ hle) (hcard1 ▸ h1)
  exact ⟨hMc, Multiset.toFinset_card_eq_card_iff_nodup.1 (hcard1.trans hMc.symm)⟩


open Formalism.BasicNotions in
theorem g_splits (D : D7) (i : Fin 2) :
    (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).card = Module.finrank ℚ D.host.E ∧
      (normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).Nodup :=
  split_of_ncard (D.host.g_prime i) (D.nd.g_split i)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

section Jet

variable {S : Type} [CommRing S]

theorem cc_aeval {κ κ' : Type} (ψ : κ' → MvPolynomial κ S) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (P : MvPolynomial κ' S) : constantCoeff (aeval ψ P) = constantCoeff P := by
  have key : (constantCoeff : MvPolynomial κ S →+* S).comp (aeval ψ).toRingHom = constantCoeff :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp [hψ])
  exact DFunLike.congr_fun key P

theorem mem_orig_of_cc {κ : Type} (P : MvPolynomial κ S) (h : constantCoeff P = 0) : P ∈ orig S κ := by
  have hr : (Set.range (X : κ → MvPolynomial κ S)) = X '' Set.univ := Set.image_univ.symm
  show P ∈ Ideal.span (Set.range X)
  rw [hr, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm h
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hm0 (Finsupp.ext fun a => by simp [hcon a])
  exact ⟨i, Set.mem_univ _, hi⟩

private theorem jetMap_mk_lemma {κ κ' : Type} (m : ℕ) (f : κ → MvPolynomial κ' S) (hf : ∀ i, f i ∈ orig S κ')
    (P : MvPolynomial κ S) :
    jetMap (m := m) f hf (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval f P) := by
  rfl

private theorem jetSubstP_mk_eq_mk_aeval_sub_C {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval (fun i => φ i - C (constantCoeff (φ i))) P) := by
  rfl

theorem jetSubstP_comp {κ κ' κ'' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (ψ : κ' → MvPolynomial κ'' S)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    (jetSubstP m ψ).comp (jetSubstP m φ) = jetSubstP m (fun i => aeval ψ (φ i)) := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S κ ^ (m + 1)) x
  show jetSubstP m ψ (jetSubstP m φ (Ideal.Quotient.mk _ P)) =
    jetSubstP m (fun i => aeval ψ (φ i)) (Ideal.Quotient.mk _ P)
  simp only [jetSubstP_mk_eq_mk_aeval_sub_C, hφ, hψ, cc_aeval ψ hψ, map_zero, sub_zero]
  exact congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext (f := (aeval ψ).comp (aeval φ))
    (g := aeval fun i => aeval ψ (φ i)) fun i => by simp) P)

end Jet

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev rel {n n' : ℕ} (σ : Fin n → Fin n') : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S :=
  fun p => X (σ p.1, p.2)

private theorem subst_jpt_lemma_3 {n n' : ℕ} (m : ℕ) (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (i : Fin n) (k : Fin n') (h : ∀ j, ψ (i, j) = X (k, j)) :
    homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  have key : (jetSubstP m ψ).comp (jetCopy d m i) = jetCopy d m k := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S (Fin 1 × Fin d) ^ (m + 1)) y
    show jetSubstP m ψ (jetCopy d m i (Ideal.Quotient.mk _ P)) = jetCopy d m k (Ideal.Quotient.mk _ P)
    simp only [jetCopy, jetMap_mk_lemma, jetSubstP_mk_eq_mk_aeval_sub_C]
    exact congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext
      (f := (aeval fun p => ψ p - C (constantCoeff (ψ p))).comp
        (aeval fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)))
      (g := aeval fun p : Fin 1 × Fin d => (X (k, p.2) : MvPolynomial (Fin n' × Fin d) S))
      fun p => by simp [h]) P)
  unfold jptG
  rw [← Category.assoc, homAt_comp, key]

theorem relabel_jpt {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (i : Fin n) :
    homAt x0 (jetSubstP m (rel d (S := S) σ)) ≫ jptG t x0 d x m i = jptG t x0 d x m (σ i) := by
  exact subst_jpt_lemma_3 t x0 d x m (rel d σ) i (σ i) fun j => rfl

end Pts

section Gen

end Gen

section Ser

variable {S : Type} [CommRing S] (d : ℕ)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

theorem psJet_ev_rel {n n' : ℕ} (m : ℕ) (σ : Fin n → Fin n') (f : PS S n d) :
    psJet m (ev (fun i => pt S d (σ i)) f) = jetSubstP m (rel d (S := S) σ) (psJet m f) := by
  have hc : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin n × Fin d => (fun i => pt S d (σ i) : Fin n → Pt S n' d) p.1 p.2) p) = 0 := by
    rintro ⟨k, j⟩
    simp [pt]
  rw [ev, FBIdJet.psJet_subst m _ hc f]
  apply DFunLike.congr_fun
  refine jet_hom_ext fun p => ?_
  obtain ⟨k, j⟩ := p
  rw [jetMap_mk, aeval_X]
  simp only [pt, jetSubstP, jetMap_mk, aeval_X, rel, constantCoeff_X, map_zero, sub_zero]
  exact FBIdSy.mk_psTrunc_X m _

theorem mk_rename {κ κ' : Type} (m : ℕ) (ρ : κ → κ') (P : MvPolynomial κ S) :
    (Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (rename ρ P)) =
      jetMap (m := m) (fun i => (X (ρ i) : MvPolynomial κ' S)) (fun _ => X_mem_orig _)
        (Ideal.Quotient.mk _ P) := by
  have hr : rename ρ P = aeval (fun i => (X (ρ i) : MvPolynomial κ' S)) P :=
    DFunLike.congr_fun (MvPolynomial.algHom_ext (f := rename ρ) (g := aeval fun i => (X (ρ i) : MvPolynomial κ' S))
      fun i => by simp) P
  rw [hr, jetMap_mk_lemma]

theorem cc_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    constantCoeff (psTrunc m f) = MvPowerSeries.constantCoeff f := by
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [MvPolynomial.constantCoeff_monomial]
  rw [Finset.sum_ite_eq']
  rw [if_pos]
  · first
      | exact MvPowerSeries.coeff_zero_eq_constantCoeff_apply f
      | simp
      | rfl
  · simp [degLE]
    exact ⟨fun _ => 0, by ext; simp⟩

theorem cc_psIn {n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : PS S n d) :
    constantCoeff (psIn d m r f) = MvPowerSeries.constantCoeff f := by
  unfold psIn
  first
    | (rw [MvPolynomial.constantCoeff_rename]; exact cc_psTrunc m f)
    | simp [cc_psTrunc]
    | (rw [show (rename fun p : Fin n × Fin d => (r p.1, p.2)) (psTrunc m f) =
          aeval (fun p : Fin n × Fin d => (X (r p.1, p.2) : MvPolynomial (Fin n' × Fin d) S)) (psTrunc m f) from
          DFunLike.congr_fun (MvPolynomial.algHom_ext fun i => by simp) _]
       rw [cc_aeval _ (fun p => by simp)]
       exact cc_psTrunc m f)

end Ser

section Comm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

end Comm

section AxTools

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem subst_jpt {n n' : ℕ} (m : ℕ) (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) (k : Fin n')
    (h : ∀ j, ψ (i, j) = X (k, j)) :
    homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  exact subst_jpt_lemma_3 t x0 d x m ψ i k h

end AxTools

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem expChartOf_of (hAct : ExpActOfSt) : ExpChartOfSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C
  obtain ⟨φ, hφ⟩ := isExpOf_exists C
  exact ⟨φ, hφ, ExpChartJet.isExpChart_of_expOf C φ hφ (hAct E H Dw l Xo c S y C φ hφ)⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)

attribute [local instance] Over.cartesianMonoidalCategory

namespace ExpBijectiveUniformisation

section Help

variable {X Y Z : Scheme.{0}}

lemma wchart_comp_le (L : LB X) (g : Y ⟶ X) (z : Z ⟶ Y) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => z ≫ g) (fun _ => j 0) ≤ z ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => g) j := by
  intro y hy
  have h1 : (z ≫ g).base y ∈ L.U (j 0) := Set.mem_iInter.1 hy ⟨⟩
  show z.base y ∈ (⋂ k : Fin 1, g.base ⁻¹' (L.U (j k) : Set X))
  refine Set.mem_iInter.2 fun k => ?_
  rw [Fin.fin_one_eq_zero k]
  exact h1

def genCast {L L' : LB X} (h : L = L') {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (b : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L' φ ε) :=
  h ▸ b

def sumQ {X1 Xn : Type} [AddCommGroup X1] [AddCommGroup Xn] {n : ℕ} (xe : Xn ≃+ (Fin n → X1)) (Q : X1 → ℤ) :
    Xn → ℤ :=
  fun x => ∑ i, Q (xe x i)

end Help

section GermN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def jcN (V F : Type) [CommRing V] [Field F] [Algebra V F] (d n m : ℕ) (i : Fin n) :
    Sp (Jet F (Fin n × Fin d) m) ⟶ Sp (Jet V (Fin 1 × Fin d) m) :=
  spMap (((jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m) :
      Jet F (Fin 1 × Fin d) m →+* Jet F (Fin n × Fin d) m).comp
    (jetCoef (algebraMap V F) (Fin 1 × Fin d) m))

def jptN {V : Type} [CommRing V] {t : SAB H (Sp V)} {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (F : Type)
    [Field F] [Algebra V F] (n m : ℕ) (i : Fin n) : Sp (Jet F (Fin n × Fin d) m) ⟶ t.G.left :=
  jcN V F d n m i ≫ (xT m).left

def IsGermN {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} (P : PELUnif I t) {d n : ℕ}
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V)
    (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t)
    {D' : DegData V I} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Sp V)} [GrpObj G']
    [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} (pG : IsPowGrp G' t.G n)
    {U' : Unif I D' A' G'} (PU : UnifPowOf pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] (q : ℕ)
    (σ' : U'.toUnifPre.SecGF F q) (f : PS F n d) : Prop :=
  ∀ m, ∃ (z : Sp (Jet F (Fin n × Fin d) m) ⟶ (UnifPre.GF (R := V) (G := G') F).left)
    (τ : LB.Gen (LB.LinComb U'.LG.L (K := PUnit.{1}) (fun _ => z ≫ UnifPre.gFK (R := V) (G := G') F)
      (fun _ => (q : ℤ))))
    (b : LB.Gen (LB.LinComb P.U.LG.L (K := Fin n)
      (fun i => (z ≫ UnifPre.gFK (R := V) (G := G') F) ≫ (pG.pr i).left) (fun _ => (q : ℤ)))),
    z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
      spMap (algebraMap F (Jet F (Fin n × Fin d) m)) ∧
    (∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i) ∧
    GeneratorPullback.MapsAt P.U.LG.L U'.LG.L (fun i => (pG.pr i).left) PU.wL (z ≫ UnifPre.gFK (R := V) (G := G') F) q τ b ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (genCast (congrArg RigLB.L P.bundle) _ _ b)
      (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)) ∧
    ∀ j : Fin 1 → U'.LG.L.ι,
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map
          (homOfLE (wchart_comp_le U'.LG.L (UnifPre.gFK (R := V) (G := G') F) z j)).op).hom
        ((z.app _).hom (σ'.f j)) =
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map (homOfLE le_top).op).hom (toΓ _ (psJet m f)) *
        (τ.s (fun _ => j 0)).val

end GermN

section St

open IsLocalRing

end St

end ExpBijectiveUniformisation

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrA
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Ring

variable {V K : Type} [CommRing V] [CommRing K] (f : V →+* K)

theorem jetCoef_mk (κ : Type) (m : ℕ) (p : MvPolynomial κ V) :
    jetCoef f κ m (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

theorem psTrunc_map {σ : Type} [Fintype σ] [DecidableEq σ] (m : ℕ) (F : MvPowerSeries σ V) :
    psTrunc m (MvPowerSeries.map f F) = MvPolynomial.map f (psTrunc m F) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [psTrunc, map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem jetCoef_alg (κ : Type) (m : ℕ) :
    (jetCoef f κ m).comp (algebraMap V (Jet V κ m)) = (algebraMap K (Jet K κ m)).comp f := by
  refine RingHom.ext fun v => ?_
  first
  | (show jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
     rw [jetCoef_mk, MvPolynomial.map_C])
  | (simp only [RingHom.comp_apply]
     rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
       MvPolynomial.algebraMap_eq, jetCoef_mk, MvPolynomial.map_C])

theorem jetCoef_aug (κ : Type) (m : ℕ) :
    ((jetAug : Jet K κ m →ₐ[K] K) : Jet K κ m →+* K).comp (jetCoef f κ m) =
      f.comp ((jetAug : Jet V κ m →ₐ[V] V) : Jet V κ m →+* V) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C a))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.C a)))
    rw [jetCoef_mk, MvPolynomial.map_C]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.C (f a)) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.C a))
    simp
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)))
    rw [jetCoef_mk, MvPolynomial.map_X]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.X i) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.X i))
    simp

theorem jetCoef_trunc (κ : Type) (m : ℕ) :
    ((jetTrunc : Jet K κ (m + 1) →ₐ[K] Jet K κ m) : Jet K κ (m + 1) →+* Jet K κ m).comp (jetCoef f κ (m + 1)) =
      (jetCoef f κ m).comp ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_)
  first
  | rfl
  | simp [jetCoef_mk, jetTrunc]

theorem jetCoef_map {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ')
    (hφ' : ∀ i, MvPolynomial.map f (φ i) ∈ orig K κ') :
    (jetCoef f κ' m).comp ((jetMap φ hφ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetMap (fun i => MvPolynomial.map f (φ i)) hφ' : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.C a))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.C a)))
    rw [jetCoef_mk]
    simp
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.X i))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.X i)))
    rw [jetCoef_mk]
    simp

end Ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqC
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

namespace GaugeR

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

@[reducible] def barStar (H : Host E) : StarRing (𝓞 E) where
  star := H.bar
  star_involutive a := by
    apply RingOfIntegers.ext
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  star_mul a b := by
    show H.bar (a * b) = H.bar b * H.bar a
    rw [map_mul, mul_comm]
  star_add a b := map_add H.bar a b

variable {H : Host E} {Dw : Datum H} {l : Level H}

def chi (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (σ : E →+* ℂ) : 𝓞 E →+* S :=
  (algebraMap c.F S).comp (embK c σ)

theorem embK_conj (c : Coeff l) (σ : E →+* ℂ) (a : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate σ) a = embK c σ (H.bar a) := by
  apply Subtype.ext
  show (ComplexEmbedding.conjugate σ) (a : E) = σ ((H.bar a : 𝓞 E) : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, NumberField.IsCMField.complexEmbedding_complexConj]

theorem hunit_chi (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (σ τ : E →+* ℂ) (h : σ ≠ τ) :
    ∃ a, IsUnit (chi c S σ a - chi c S τ a) := by
  classical
  have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
    by_contra hc
    push_neg at hc
    apply h
    ext x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hc a) (hc b)
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_⟩
  have hne : embK c σ a - embK c τ a ≠ 0 := by
    intro h0
    apply ha
    exact congrArg (fun z : c.F => (z : ℂ)) (sub_eq_zero.mp h0)
  have hu := (hne.isUnit).map (algebraMap c.F S)
  simpa [chi, map_sub] using hu

def nu (Dw : Datum H) : Lt1 Dw ≃ Fin 1 × Fin (dL Dw) where
  toFun ℓ := ((0 : Fin 1), ltIdx Dw ℓ)
  invFun p := (ltIdx Dw).symm p.2
  left_inv ℓ := by simp
  right_inv p := Prod.ext (Subsingleton.elim _ _) (by simp)

theorem exists_embDomain (x : Fin 1 × Fin (dL Dw) →₀ ℕ) : ∃ y, Finsupp.embDomain (nu Dw).toEmbedding y = x := by
  refine ⟨Finsupp.equivMapDomain (nu Dw).symm x, ?_⟩
  rw [Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding, ← Finsupp.equivMapDomain_eq_mapDomain]
  ext p
  simp [Finsupp.equivMapDomain_apply]

theorem degree_embDomain {α β : Type} (f : α ↪ β) (y : α →₀ ℕ) : (Finsupp.embDomain f y).degree = y.degree := by
  classical
  show ∑ i ∈ (Finsupp.embDomain f y).support, (Finsupp.embDomain f y) i = ∑ i ∈ y.support, y i
  rw [Finsupp.support_embDomain, Finset.sum_map]
  simp

private theorem coeff_rename_emb_lemma {S : Type} [CommRing S] (p : MvPowerSeries (Lt1 Dw) S)
    (y : Lt1 Dw →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) (MvPowerSeries.rename (nu Dw).toEmbedding p) =
      MvPowerSeries.coeff y p :=
  MvPowerSeries.coeff_embDomain_rename _ _ _

theorem rename_rescale {S : Type} [CommRing S] (s : Fin 1 × Fin (dL Dw) → S) (p : MvPowerSeries (Lt1 Dw) S) :
    MvPowerSeries.rename (nu Dw).toEmbedding (MvPowerSeries.rescale (fun ℓ => s (nu Dw ℓ)) p) =
      MvPowerSeries.rescale s (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
  ext x
  obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
  simp only [coeff_rename_emb_lemma, MvPowerSeries.coeff_rescale, Finsupp.prod_embDomain] <;> rfl

def sc (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (a : 𝓞 E) : Fin 1 × Fin (dL Dw) → S :=
  fun p => algebraMap c.F S (embK c ((ltIdx Dw).symm p.2).1 a)

theorem ratio_exp (hR : GaugeRatioSt) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (r : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (h1 : MvPowerSeries.constantCoeff r = 1)
    (hr : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r * MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r) :
    ∃ q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, MvPowerSeries.constantCoeff q = 0 ∧
      (∀ m, MvPowerSeries.coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ ℓ ℓ' : Lt1 Dw, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 +
          Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1) q ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp S) := by
  letI : StarRing (𝓞 E) := barStar H
  let r' : MvPowerSeries (Lt1 Dw) S := fun y => MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r
  have hcr' : ∀ y, MvPowerSeries.coeff y r' = MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y) r :=
    fun y => rfl
  have hrr : MvPowerSeries.rename (nu Dw).toEmbedding r' = r := by
    ext x
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) x
    rw [coeff_rename_emb_lemma, hcr']
  have hinj : ∀ p p' : MvPowerSeries (Lt1 Dw) S,
      MvPowerSeries.rename (nu Dw).toEmbedding p = MvPowerSeries.rename (nu Dw).toEmbedding p' → p = p' := by
    intro p p' hpp
    ext y
    have hc := congrArg (MvPowerSeries.coeff (Finsupp.embDomain (nu Dw).toEmbedding y)) hpp
    simpa only [coeff_rename_emb_lemma] using hc
  have hsc : ∀ b : 𝓞 E, (fun ℓ : Lt1 Dw => sc (Dw := Dw) c S b (nu Dw ℓ)) = fun ℓ => chi c S ℓ.1 b := by
    intro b
    funext ℓ
    simp [sc, chi, nu]
  have hscale : ∀ (b : 𝓞 E) (p : MvPowerSeries (Lt1 Dw) S),
      MvPowerSeries.rename (nu Dw).toEmbedding (scaleBy (rk := Dw.mult) (chi c S) b p) =
        MvPowerSeries.rescale (sc (Dw := Dw) c S b) (MvPowerSeries.rename (nu Dw).toEmbedding p) := by
    intro b p
    (rw [← rename_rescale, hsc b]) <;> rfl
  have hr0' : MvPowerSeries.constantCoeff r' = 1 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcr', Finsupp.embDomain_zero,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h1]
  have hr' : ∀ a : 𝓞 E, scaleBy (rk := Dw.mult) (chi c S) (1 + a * star a) r' =
      scaleBy (rk := Dw.mult) (chi c S) a r' ^ 2 * r' * scaleBy (rk := Dw.mult) (chi c S) (a * star a) r' := by
    intro a
    apply hinj
    rw [map_mul, map_mul, map_pow, hscale, hscale, hscale, hrr]
    exact hr a
  have hcc : ∀ (σ : E →+* ℂ) (a : 𝓞 E), chi c S (ComplexEmbedding.conjugate σ) a = chi c S σ (star a) := by
    intro σ a
    simp only [chi, RingHom.comp_apply]
    (rw [embK_conj]) <;> rfl
  obtain ⟨q', hq0, hqdeg, hqpair, hqexp⟩ :=
    hR (𝓞 E) S (E →+* ℂ) Dw.mult (chi c S) ComplexEmbedding.conjugate hcc
      (fun σ τ hστ => hunit_chi c S σ τ hστ) r' hr0' hr'
  have hq0r : MvPowerSeries.constantCoeff (MvPowerSeries.rename (nu Dw).toEmbedding q') = 0 := by
    rw [MvPowerSeries.constantCoeff_rename, hq0]
  refine ⟨MvPowerSeries.rename (nu Dw).toEmbedding q', hq0r, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [coeff_rename_emb_lemma] at hm
    rw [degree_embDomain]
    exact hqdeg y hm
  · intro ℓ ℓ' hm
    have hsum : Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1 + Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ') 1 =
        Finsupp.embDomain (nu Dw).toEmbedding (Finsupp.single ℓ 1 + Finsupp.single ℓ' 1) := by
      (rw [Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single]) <;> rfl
    rw [hsum, coeff_rename_emb_lemma] at hm
    exact hqpair ℓ ℓ' hm
  · ext m
    obtain ⟨y, rfl⟩ := exists_embDomain (Dw := Dw) m
    rw [← hrr, coeff_rename_emb_lemma, hqexp,
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0),
      PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq0r)]
    congr 1
    funext d
    rw [← map_pow, coeff_rename_emb_lemma]

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
