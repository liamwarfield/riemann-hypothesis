module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FramesDifferByIsometryAndTriangularOfPeriods

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePart
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePart
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar.OnePart

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem adjoin_scalar {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M)) (S : M → Prop)
    (h : ∀ x ∈ s, ∃ l : ℂ, ∀ u, S u → x u = l • u) :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, ∀ u, S u → a u = l • u := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r =>
    refine ⟨r, fun u _ => ?_⟩
    simp [Module.algebraMap_end_apply]
  | add x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨l + m, fun u hu => by rw [LinearMap.add_apply, hl u hu, hm u hu, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    exact ⟨m * l, fun u hu => by rw [Module.End.mul_apply, hm u hu, map_smul, hl u hu, smul_smul]⟩

variable {D : D7}

theorem scalar_of_split {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : Formalism.DivisionValues.conjPl P ≠ P) (S : M → Prop) (fu : ∀ u, S u → ∀ k ∈ hyp V P, π k u = u) (a b : List ℤ → ℂ)
    (ha : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π P (Finsupp.single (splitLab V.rank k) 1) u = a (splitLab V.rank k) • u)
    (hb : ∀ u, S u → ∀ k, k ≤ V.rank →
      opOf π (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab V.rank k) 1) u = b (splitLab V.rank k) • u) (d : List ℤ) :
    ∃ l : ℂ, ∀ u, S u → opOf π P (Finsupp.single d 1) u = l • u := by
  obtain ⟨z, hz, hzu⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d
  have gen : ∀ x ∈ {x : Module.End ℂ M | ∃ k, k ≤ V.rank ∧ (x = opOf π P (Finsupp.single (splitLab V.rank k) 1) ∨
      x = opOf π P (Finsupp.single (dualLab (splitLab V.rank k)) 1))}, ∃ l : ℂ, ∀ u, S u → x u = l • u := by
    rintro x ⟨k, hk, rfl | rfl⟩
    · exact ⟨a (splitLab V.rank k), fun u hu => ha u hu k hk⟩
    · refine ⟨b (splitLab V.rank k), fun u hu => ?_⟩
      have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π u (fu u hu)
      rw [GlobalTheory.Hk3.dualC, Finsupp.mapDomain_single] at hc
      rw [← hc]
      exact hb u hu k hk
  obtain ⟨l, hl⟩ := adjoin_scalar _ S gen z hz
  exact ⟨l, fun u hu => by rw [← hzu u (fu u hu), hl u hu]⟩

theorem postOn_hk_single {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (P : Pl D.host.E) (d : List ℤ) (U : MMap M) :
    postOn M (hk V P (Finsupp.single d 1)) U = opOf (rRep M) P (Finsupp.single d 1) U := by
  unfold rRep
  simp only [hk, opOf, Finsupp.sum_single_index, one_smul, zero_smul]
  ext v g
  simp [postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply, Finset.sum_apply]

private theorem star_algebraMap_eq (c : D.host.F) : star (algebraMap D.host.F D.host.E c) = algebraMap D.host.F D.host.E c := by
  have hm : (algebraMap D.host.F D.host.E c) ∈ NumberField.maximalRealSubfield D.host.E :=
    NumberField.IsTotallyReal.le_maximalRealSubfield D.host.F c.2
  exact (NumberField.IsCMField.complexConj_eq_self_iff _ _).mpr hm

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem good_conj (R : RealDat D A Ks) (t : T0) (P : Pl D.host.E) (hP : Good R t P) : Good R t (Formalism.DivisionValues.conjPl P) := by
  intro PP hPP
  obtain ⟨h1, h2⟩ := hP PP hPP
  rw [GlobalTheory.GoodPrimes.isConjPl_iff] at h2 ⊢
  refine ⟨fun e => h2 ?_, fun e => h1 ?_⟩
  · rw [e, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  · have e' := congrArg Formalism.DivisionValues.conjPl e
    rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at e'
    exact e'.symm

theorem good_of_offS (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (P : Pl D.host.E)
    (h : OffS D (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P) : Good R A.μ0 P := by
  classical
  intro PP hPP
  have hPg : PP ∈ R.Pg := by
    rcases hPP with h1 | h1
    · exact h1
    · rw [GlobalTheory.LiftLower.Q_base hL] at h1
      simp at h1
  obtain ⟨x, hx, hy⟩ := h ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (Finset.mem_image_of_mem _ hPg)
  have hx' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ PP.asIdeal := hx
  have hcoe : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (x : D.host.F) := by
    first
    | rfl
    | (rw [← IsScalarTower.algebraMap_apply (𝓞 D.host.F) (𝓞 D.host.E) D.host.E,
          IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E]; rfl)
  have hnot := hy _ hcoe
  refine ⟨fun e => hnot (by rw [← e]; exact hx'), fun hc => ?_⟩
  obtain ⟨c', hc'P, hc'eq⟩ := hc _ hx'
  exact hy c' (by rw [hc'eq, hcoe, star_algebraMap_eq]) hc'P

private theorem primeIdem_and_sphOp_of_isHeckeOpFull {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : Pl D.host.E} {d : List ℤ} {Rp : Finset (GA D V)}
    (h : Hecke₂ V J χ Sb P d Rp) :
    (∃ e f, IsPrimeIdem P e f ∧ OffS D Sb P ∧ (∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧
      (∀ g ∈ J, SuppF V f g → χ g = 1)) ∧ SphOp V P d Rp := by
  unfold Hecke₂ at h
  obtain ⟨e, f, ϖ, α, hS, hPf, h1, h2, h3, hJ, hχ, hα, hd, hR, hc⟩ := h
  refine ⟨⟨e, f, hPf, hS, hJ, hχ⟩, ?_⟩
  have hset : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    ext k
    exact ⟨fun hk => ⟨(hJ k hk.2).1 hk.1, hk.2⟩, fun hk => ⟨(hJ k hk.2).2 hk.1, hk.2⟩⟩
  unfold SphOp Hecke₂
  refine ⟨e, f, ϖ, α, GlobalTheory.LevOp.offS_empty, hPf, h1, h2, h3, fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hd, hR, ?_⟩
  rw [← hset]
  exact hc

private theorem mult_map_mul_right_eq_of_chi_eq_one {θ} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {U : MMap M} (hU : U ∈ Mult θ M J χ) (k : GA D V) (hk : k ∈ J) (hχ : χ k = 1) :
    ∀ v g, U v (g * k) = U v g := by
  induction hU using Submodule.span_induction with
  | mem T hT =>
    intro v g
    rw [hT.lev v k hk g, hχ, one_mul]
  | zero => intro v g; rfl
  | add T T' _ _ h1 h2 =>
    intro v g
    simp only [MultilinearMap.add_apply, Pi.add_apply, h1 v g, h2 v g]
  | smul c T _ h1 =>
    intro v g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h1 v g]

theorem mem_one_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (b : Pl D.host.E → List ℤ → ℂ), ∃ ev, ∀ w : (R.HW i σ).H, (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d → postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) → w ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hM i σ b
  classical
  obtain ⟨Sw, hSw⟩ : ∃ Sw : MMap (R.MW i σ) → Prop, ∀ u, Sw u ↔ ∃ w : (R.HW i σ).H,
      (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d →
        postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) ∧
      u = (R.HW i σ).e w := ⟨_, fun _ => Iff.rfl⟩
  refine ⟨fun P d => if h : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u
    then h.choose else 0, ?_⟩
  intro w hw
  have hW : ∀ w' : (R.HW i σ).H, (R.HW i σ).e w' ∈ R.Wall i σ := by
    intro w'
    rw [← (hM i σ).2.1]
    exact LinearMap.mem_range_self _ w'
  simp only [GlobalTheory.LiftLower.partH, Submodule.mem_comap, partFull, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨hW w, ?_⟩
  intro P d Rp hfull
  obtain ⟨⟨e, f, hPf, hS, hJ, hχ⟩, hsph⟩ := primeIdem_and_sphOp_of_isHeckeOpFull hfull
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := good_of_offS R hL P hS
  have hfix : ∀ w' : (R.HW i σ).H, ∀ k ∈ hyp (Wc D i) P,
      rRep (R.MW i σ) k ((R.HW i σ).e w') = (R.HW i σ).e w' := by
    intro w' k hk
    obtain ⟨hk1, hk2⟩ := (GlobalTheory.LevOp.mem_hyp hPf).1 hk
    have hkJ := (hJ k hk2).2 hk1
    have hinv := mult_map_mul_right_eq_of_chi_eq_one (hW w') k hkJ (hχ k hkJ hk2)
    unfold rRep
    ext v g
    simp [postOn, rLin, LinearMap.compMultilinearMap_apply, hinv]
  have hSfix : ∀ u, Sw u → ∀ k ∈ hyp (Wc D i) P, rRep (R.MW i σ) k u = u := by
    intro u hu k hk
    obtain ⟨w', -, rfl⟩ := (hSw u).1 hu
    exact hfix w' k hk
  have hex : ∃ l : ℂ, ∀ u, Sw u → opOf (rRep (R.MW i σ)) P (Finsupp.single d 1) u = l • u := by
    by_cases hc : Formalism.DivisionValues.conjPl P = P
    · refine ⟨b P d, fun u hu => ?_⟩
      obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
      rw [← postOn_hk_single]
      exact hw' P d hG (Or.inr ⟨hc, Rp, hsph⟩)
    · refine scalar_of_split (rRep (R.MW i σ)) P hc Sw hSfix (b P) (b (Formalism.DivisionValues.conjPl P)) ?_ ?_ d
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        exact hw' P _ hG (Or.inl ⟨hc, k, hk, rfl⟩)
      · intro u hu k hk
        obtain ⟨w', hw', rfl⟩ := (hSw u).1 hu
        rw [← postOn_hk_single]
        refine hw' (Formalism.DivisionValues.conjPl P) _ (good_conj R A.μ0 P hG) (Or.inl ⟨?_, k, hk, rfl⟩)
        rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
        exact fun h => hc h.symm
  have hsum : heckeOn (R.MW i σ) Rp ((R.HW i σ).e w) = ∑ γ ∈ Rp, rRep (R.MW i σ) γ ((R.HW i σ).e w) := by
    unfold rRep
    ext v g
    simp [heckeOn, postOn, heckeLin, rLin, LinearMap.compMultilinearMap_apply]
  rw [hsum, ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors (Wc D i) P).1 d Rp hsph).2 _ (rRep (R.MW i σ)) _ (hfix w), dite_eq_left hex]
  exact hex.choose_spec _ ((hSw _).2 ⟨w, hw, rfl⟩)

end GlobalTheory.ConjScalar.OnePart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePartStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaForm_eigen_mem_single_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (b : Pl D.host.E → List ℤ → ℂ), ∃ ev, ∀ w : (R.HW i σ).H, (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d → postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) → w ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  first | exact @GlobalTheory.ConjScalar.OnePart.mem_one_part | exact GlobalTheory.ConjScalar.OnePart.mem_one_part | (intros; apply GlobalTheory.ConjScalar.OnePart.mem_one_part <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionOfSmoothLocalDescentReduced
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFactorThroughProjection
namespace GlobalTheory.FactorThroughProjection

theorem exists_factor_through_projection {J : Type} [Fintype J] [DecidableEq J] (A : J → Type)
    [inst : (i : J) → CommRing (A i)] {k : Type} [inst_1 : CommRing k] [IsDomain k]
    (χ : ((i : J) → A i) →+* k) :
    ∃ (i : J) (ψ : A i →+* k), ∀ (x : (i : J) → A i), χ x = ψ (x i) := by
  have hsum : ∑ i : J, χ (Pi.single i (1 : A i)) = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    have h : ∑ i : J, (Pi.single i (1 : A i) : (j : J) → A j) = 1 :=
      Finset.univ_sum_single (1 : (j : J) → A j)
    rw [h, map_one]
  have hne : ∑ i : J, χ (Pi.single i (1 : A i)) ≠ 0 := by
    rw [hsum]; exact one_ne_zero
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hmul : ∀ a b : A i, (Pi.single i (a * b) : (j : J) → A j)
      = Pi.single i a * Pi.single i b := by
    intro a b
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  have hone : χ (Pi.single i (1 : A i)) = 1 := by
    apply mul_left_cancel₀ hi
    rw [← map_mul, ← hmul, mul_one, mul_one]
  let ψ : A i →+* k :=
    { toFun := fun a => χ (Pi.single i a)
      map_one' := hone
      map_mul' := fun a b => by rw [hmul, map_mul]
      map_zero' := by simp
      map_add' := fun a b => by rw [Pi.single_add, map_add (f := _)] }
  refine ⟨i, ψ, fun x => ?_⟩
  change χ x = χ (Pi.single i (x i))
  have hx : (Pi.single i (x i) : (j : J) → A j) = x * Pi.single i (1 : A i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [hx, map_mul, hone, mul_one]

end GlobalTheory.FactorThroughProjection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionOfSmoothLocalDescentReduced
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.SmoothLocalDescent

theorem eq_of_forall_geom {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rw [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this
  exact this

theorem exists_factor_pi {J : Type} [Fintype J] [DecidableEq J] (A : J → Type)
    [∀ i, CommRing (A i)] {k : Type} [CommRing k] [IsDomain k] (χ : (∀ i, A i) →+* k) :
    ∃ (i : J) (ψ : A i →+* k), ∀ x, χ x = ψ (x i) := by
  first
  | exact @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection
  | exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection
  | (apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection ..)


open scoped TensorProduct in
theorem exists_lift_geom (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.FaithfullyFlat R S] (k : Type) [Field k] [IsAlgClosed k]
    (χ : R →+* k) : ∃ χ' : S →+* k, χ'.comp (algebraMap R S) = χ := by
  letI : Algebra R k := χ.toAlgebra
  haveI : Nontrivial (k ⊗[R] S) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
  letI : Field ((k ⊗[R] S) ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (k ⊗[R] S) := inferInstance
  haveI : Module.Finite k ((k ⊗[R] S) ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  let g : ((k ⊗[R] S) ⧸ m) →ₐ[k] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨g.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := S)).toRingHom), ?_⟩
  ext x
  have e : (1 : k) ⊗ₜ[R] algebraMap R S x = algebraMap k (k ⊗[R] S) (χ x) := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
    rfl
  change g (Ideal.Quotient.mk m ((1 : k) ⊗ₜ[R] algebraMap R S x)) = χ x
  rw [e]
  exact g.commutes (χ x)


open scoped TensorProduct in
theorem exists_preimage_of_geom (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] [Module.FaithfullyFlat R S] (w : S)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ₁ χ₂ : S →+* k),
      χ₁.comp (algebraMap R S) = χ₂.comp (algebraMap R S) → χ₁ w = χ₂ w) :
    ∃ u : R, algebraMap R S u = w := by
  haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R S
  haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced S (S ⊗[R] S)
  have key : w ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] w := by
    refine eq_of_forall_geom _ _ fun k _ _ χ => ?_
    refine h k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom) ?_
    ext x
    change χ (algebraMap R S x ⊗ₜ[R] (1 : S)) = χ ((1 : S) ⊗ₜ[R] algebraMap R S x)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact (Algebra.IsEffective.of_faithfullyFlat R S w).1 (by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, key, sub_self])

end GlobalTheory.SmoothLocalDescent

namespace GlobalTheory.SmoothLocalDescent

theorem exists_of_finite_cover (K B : Type) [CommRing K] [CommRing B] [Algebra K B]
    [_root_.IsReduced B]
    (F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], (B →ₐ[K] Ω) → Ω)
    {J : Type} [Fintype J] [DecidableEq J] (A : J → Type) [∀ i, CommRing (A i)]
    [∀ i, Algebra B (A i)] [∀ i, Algebra K (A i)] [∀ i, IsScalarTower K B (A i)]
    [∀ i, Algebra.Smooth B (A i)] (a : ∀ i, A i)
    (hcov : ∀ q : PrimeSpectrum B, ∃ i, q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (A i))))
    (hval : ∀ i (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : A i →ₐ[K] Ω),
      χ' (a i) = F Ω (χ'.comp (IsScalarTower.toAlgHom K B (A i)))) :
    ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ : B →ₐ[K] Ω), χ b = F Ω χ := by
  haveI : Algebra.Smooth B (∀ i, A i) := ⟨inferInstance, inferInstance⟩
  haveI : Module.Flat B (∀ i, A i) := inferInstance
  haveI : Module.FaithfullyFlat B (∀ i, A i) := by
    refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, Q, hQ⟩ := hcov p
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom A i) Q, ?_⟩
    rw [← hQ]
    rfl

  have key : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : (∀ i, A i) →+* Ω),
      (∀ x : K, χ' (algebraMap B (∀ i, A i) (algebraMap K B x)) = algebraMap K Ω x) →
      ∃ ρ : B →ₐ[K] Ω, (∀ y, ρ y = χ' (algebraMap B (∀ i, A i) y)) ∧ χ' a = F Ω ρ := by
    intro Ω _ _ _ χ' hK
    obtain ⟨i, ψ, hψ⟩ := exists_factor_pi A χ'
    have hB : ∀ y, ψ (algebraMap B (A i) y) = χ' (algebraMap B (∀ i, A i) y) := fun y => by
      rw [hψ]; rfl
    have hc : ∀ x : K, ψ (algebraMap K (A i) x) = algebraMap K Ω x := fun x => by
      rw [IsScalarTower.algebraMap_apply K B (A i), hB, hK]
    let ψa : A i →ₐ[K] Ω := { ψ with commutes' := hc }
    refine ⟨ψa.comp (IsScalarTower.toAlgHom K B (A i)), fun y => hB y, ?_⟩
    rw [hψ]
    exact hval i Ω ψa
  obtain ⟨b, hb⟩ := exists_preimage_of_geom B (∀ i, A i) a fun k _ _ χ₁ χ₂ h12 => by
    letI : Algebra K k := (χ₁.comp ((algebraMap B (∀ i, A i)).comp (algebraMap K B))).toAlgebra
    have h12' : ∀ y, χ₁ (algebraMap B (∀ i, A i) y) = χ₂ (algebraMap B (∀ i, A i) y) :=
      fun y => RingHom.congr_fun h12 y
    obtain ⟨ρ₁, hρ₁, e₁⟩ := key k χ₁ fun x => rfl
    obtain ⟨ρ₂, hρ₂, e₂⟩ := key k χ₂ fun x => (h12' _).symm
    have : ρ₁ = ρ₂ := AlgHom.ext fun y => by rw [hρ₁, hρ₂, h12']
    rw [e₁, e₂, this]
  refine ⟨b, fun Ω _ _ _ χ => ?_⟩
  obtain ⟨χ', hχ'⟩ := exists_lift_geom B (∀ i, A i) Ω χ.toRingHom
  have hχ'y : ∀ y, χ' (algebraMap B (∀ i, A i) y) = χ y := fun y => RingHom.congr_fun hχ' y
  obtain ⟨ρ, hρ, e⟩ := key Ω χ' fun x => by rw [hχ'y]; exact χ.commutes x
  have : ρ = χ := AlgHom.ext fun y => by rw [hρ, hχ'y]
  rw [← this, ← e, ← hb, hρ]

end GlobalTheory.SmoothLocalDescent

namespace GlobalTheory.SmoothLocalDescent

theorem exists_of_smooth_locally : ∀ (K B : Type) [CommRing K] [CommRing B] [Algebra K B] [IsReduced B] (F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], (B →ₐ[K] Ω) → Ω), (∀ q : PrimeSpectrum B, ∃ (B' : Type) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra K B') (_ : IsScalarTower K B B') (b' : B'), Algebra.Smooth B B' ∧ q ∈ Set.range (PrimeSpectrum.comap (algebraMap B B')) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : B' →ₐ[K] Ω), χ' b' = F Ω (χ'.comp (IsScalarTower.toAlgHom K B B'))) → ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ : B →ₐ[K] Ω), χ b = F Ω χ := by
  intro K B _ _ _ _ F h
  choose B' iR iB iK iT b' hsm hq hval using h
  letI : ∀ q, CommRing (B' q) := iR
  letI : ∀ q, Algebra B (B' q) := iB
  letI : ∀ q, Algebra K (B' q) := iK
  haveI : ∀ q, IsScalarTower K B (B' q) := iT
  haveI : ∀ q, Algebra.Smooth B (B' q) := hsm
  let U : PrimeSpectrum B → Set (PrimeSpectrum B) := fun q =>
    Set.range (PrimeSpectrum.comap (algebraMap B (B' q)))
  have hopen : ∀ q, IsOpen (U q) := fun q => by
    have := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := B) (S := B' q) _ isOpen_univ
    rwa [Set.image_univ] at this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen
    (fun q _ => Set.mem_iUnion.2 ⟨q, hq q⟩)
  classical
  exact exists_of_finite_cover K B F (J := t) (fun i => B' i.1) (fun i => b' i.1)
    (fun q => by
      obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
      exact ⟨⟨i, hi⟩, hqi⟩)
    (fun i => hval i.1)

end GlobalTheory.SmoothLocalDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionOfSmoothLocalDescentReducedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_function_of_smooth_local_descent_reduced : ∀ (K B : Type) [CommRing K] [CommRing B] [Algebra K B] [IsReduced B] (F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], (B →ₐ[K] Ω) → Ω), (∀ q : PrimeSpectrum B, ∃ (B' : Type) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra K B') (_ : IsScalarTower K B B') (b' : B'), Algebra.Smooth B B' ∧ q ∈ Set.range (PrimeSpectrum.comap (algebraMap B B')) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : B' →ₐ[K] Ω), χ' b' = F Ω (χ'.comp (IsScalarTower.toAlgHom K B B'))) → ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ : B →ₐ[K] Ω), χ b = F Ω χ := by
  first | exact @GlobalTheory.SmoothLocalDescent.exists_of_smooth_locally | exact GlobalTheory.SmoothLocalDescent.exists_of_smooth_locally | (intros; apply GlobalTheory.SmoothLocalDescent.exists_of_smooth_locally <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightDerivativeRightConvolutionEqTestFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightDerivativeRightConvolutionEqTestFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConvRDeriv

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem oneP_add' (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) (s t : ℝ) :
    oneP θ V τ X (s + t) = oneP θ V τ X s * oneP θ V τ X t := by
  have e : ∀ r : ℝ, NormedSpace.exp (r • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun r =>
    GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX r
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (e s) (e t), add_smul,
    Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)]

theorem leftDeriv (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    starFn (Rder θ V τ X (starFn f)) ∈ CcGA V ∧ ∀ z t, HasDerivAt (fun s => f ((oneP θ V τ X s)⁻¹ * z))
      (starFn (Rder θ V τ X (starFn f)) ((oneP θ V τ X t)⁻¹ * z)) t := by
  have hh : starFn f ∈ CcGA V := starFn_mem_ccAd hf
  have hsm := ccGA_smooth_and_Rder_mem D V θ hθ _ hh
  have hd0 : ∀ w, HasDerivAt (fun t : ℝ => starFn f (w * oneP θ V τ X t)) (Rder θ V τ X (starFn f) w) 0 := fun w =>
    (((isSmoothRealFam_oneP hθ hX).1.contDiff hh w).differentiable (by simp) 0).hasDerivAt
  refine ⟨starFn_mem_ccAd (hsm.2 τ X hX), fun z t => ?_⟩
  have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd0 (z⁻¹ * oneP θ V τ X t))
  have h2 : HasDerivAt (fun s : ℝ => starFn f (z⁻¹ * oneP θ V τ X s)) (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t)) t :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      simp only [mul_assoc, ← oneP_add' hθ hX, add_sub_cancel])
  have h3 := h2.star
  have ef : (fun s => f ((oneP θ V τ X s)⁻¹ * z)) = fun s => star (starFn f (z⁻¹ * oneP θ V τ X s)) := by
    funext s; simp [starFn, mul_inv_rev, Complex.star_def]
  have ev : starFn (Rder θ V τ X (starFn f)) ((oneP θ V τ X t)⁻¹ * z) =
      star (Rder θ V τ X (starFn f) (z⁻¹ * oneP θ V τ X t)) := by
    simp [starFn, mul_inv_rev, Complex.star_def]
  rw [ef, ev]; exact h3

theorem Rder_convR : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}, X ∈ lieAt V τ → ∃ f' ∈ GlobalTheory.Orb.CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, Rder θ V τ X (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) = GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) := by
  intro D V μ _ _ θ hθ f hf τ X hX
  obtain ⟨hf', hD⟩ := leftDeriv hθ hX hf
  set f' := starFn (Rder θ V τ X (starFn f)) with hf'_def
  set u := oneP θ V τ X with hu_def
  have hu := isSmoothRealFam_oneP hθ hX
  have huc : Continuous u := hu.2.1
  have hu0 : u 0 = 1 := hu.2.2
  obtain ⟨hfc, hfs⟩ := continuous_of_mem_ccAd hf
  obtain ⟨hf'c, hf's⟩ := continuous_of_mem_ccAd hf'
  refine ⟨f', hf', ?_, fun F => ?_⟩
  · refine closure_minimal (fun y hy => ?_) (isClosed_tsupport f)
    by_contra hy'
    apply hy
    have ht : Tendsto (fun s : ℝ => (u s)⁻¹ * y) (𝓝 0) (𝓝 y) := by
      simpa [hu0] using ((huc.inv.mul continuous_const).tendsto (f := fun s : ℝ => (u s)⁻¹ * y) 0)
    have hev : (fun s : ℝ => f ((u s)⁻¹ * y)) =ᶠ[𝓝 0] fun _ => 0 :=
      ht.eventually (notMem_tsupport_iff_eventuallyEq.1 hy')
    have h1 := (hD y 0).deriv
    rw [hu0, inv_one, one_mul, hev.deriv_eq, deriv_const] at h1
    exact h1.symm
  · set φ := lift (GQ V) F
    have hφ : LocallyIntegrable φ μ :=
      locallyIntegrable_iff.2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
    funext g
    obtain ⟨M, hM⟩ := hf'c.bounded_above_of_compact_support hf's
    have hK : IsCompact ((fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f')) :=
      ((isCompact_closedBall 0 1).prod hf's.isCompact).image (by fun_prop)
    set K := (fun p : ℝ × GA D V => g * u p.1 * p.2) '' (Metric.closedBall 0 1 ×ˢ tsupport f')
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
      (F := fun t y => f ((u t)⁻¹ * (g⁻¹ * y)) * φ y) (F' := fun t y => f' ((u t)⁻¹ * (g⁻¹ * y)) * φ y)
      (bound := K.indicator fun y => M * ‖φ y‖) (s := Metric.closedBall 0 1) (Metric.closedBall_mem_nhds 0 zero_lt_one)
      (.of_forall fun t => (hfc.comp (by fun_prop)).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
      (by simpa [hu0] using (GlobalTheory.AutomorphicL2Local.continuous_integral_inv_mul_of_locallyIntegrable hfc hfs hφ).1 g)
      ((hf'c.comp (by fun_prop)).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
      (.of_forall fun y t ht => ?_)
      ((integrable_indicator_iff hK.measurableSet).2 ((hφ.integrableOn_isCompact hK).norm.const_mul M))
      (.of_forall fun y t _ => (hD (g⁻¹ * y) t).mul_const (φ y))
    · have e1 : (fun t : ℝ => convR μ f φ (g * u t)) = fun t => ∫ y, f ((u t)⁻¹ * (g⁻¹ * y)) * φ y ∂μ := by
        funext t; rw [convR_eq]; simp only [mul_inv_rev, mul_assoc]
      have e2 : convR μ f' φ g = ∫ y, f' ((u 0)⁻¹ * (g⁻¹ * y)) * φ y ∂μ := by
        rw [convR_eq, hu0]; simp
      show deriv (fun t : ℝ => convR μ f φ (g * u t)) 0 = _
      rw [e1, e2]
      exact key.2.deriv
    · by_cases hy : y ∈ K
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport (f := f') fun h => hy ⟨(t, _), ⟨?_, h⟩, ?_⟩]
        · simp
        · exact ht
        · simp [mul_assoc]

end GlobalTheory.ConvRDeriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightDerivativeRightConvolutionEqTestFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_rightConvolution_eq_test_function : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}, X ∈ lieAt V τ → ∃ f' ∈ GlobalTheory.Orb.CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, Rder θ V τ X (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) = GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) := by
  first | exact @GlobalTheory.ConvRDeriv.Rder_convR | exact GlobalTheory.ConvRDeriv.Rder_convR | (intros; apply GlobalTheory.ConvRDeriv.Rder_convR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramesDifferByIsometryOfTriangularPeriods
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramesDifferByIsometryOfTriangularPeriods
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix ComplexConjugate

noncomputable section

namespace GlobalTheory.PeriodBorelQ

open GlobalTheory.FramePeriod GlobalTheory.PeriodBorel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem natPer_move_q {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E} (h : QMatch X X' N a) (τ : E →+* ℂ) (q : ℕ)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) (n : ℕ) :
    natPer τ X'.Gm q ((a : Matrix (Fin r) (Fin r) E).map τ * M)
      (Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v)) n = natPer τ X.Gm q M (Data.emb τ v) n := by
  have he : Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ Data.emb τ v := by
    funext k; simp [Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).map τ
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · exact h.hermC_eq τ (col M ⟨n, hn⟩) _
    · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
  · rfl

theorem natPer_natCast_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (q : ℕ) (M : Matrix (Fin r) (Fin r) ℂ)
    (N : ℕ) (v : Fin r → E) (n : ℕ) :
    natPer τ G q M (Data.emb τ ((N : E) • v)) n = (N : ℂ) * natPer τ G q M (Data.emb τ v) n := by
  have he : Data.emb τ ((N : E) • v) = (N : ℂ) • Data.emb τ v := by
    funext k; simp [Data.emb]
  unfold natPer
  split_ifs with hn
  · rw [he, locPer_apply, locPer_apply]
    split_ifs
    · rw [FD.hermC_smul_right, Complex.conj_natCast]
    · rw [Matrix.mulVec_smul]; rfl
  · simp

theorem borel_of_periods_q : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (h : QMatch X X' N a), 0 < N → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * Formalism.L2.PjFree.perFr X x v τ j) → ∃ b ∈ Bor X'.Ψ r, x' = rmul (lact a (castFr h.psi x)) b ∧ (IsUnitFr X x → IsUnitFr X' x' → (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ τ, ∀ i < m τ, ‖A τ i i‖ = 1) := by
  intro E _ _ _ r X X' N a h hN0 m hm1 hm2 x hx x' hx' A hA hper
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have hz := h.mem_dom hx
  set z := lact a (castFr h.psi x) with hzd
  have hlat : ∀ w ∈ X'.Λ, ∃ v ∈ X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ v = (N : E) • w := by
    intro w hw
    refine ⟨_, h.lat' w hw, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hloc := fun τ : X'.Ψ => loc_borel X' τ.1 (mat z τ) (mat x' τ) (hz τ).1 (hx' τ).1 (A τ.1) (A (conjEmb τ.1))
    (hA _) (hA _)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm1 τ.1 (h.mem τ)
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_mem X' x' _ τ.1 τ.2, hper τ.1 i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [perFr_mem X x v τ.1 (h.mem τ), ← natPer_move_q h, h.p0, hav, natPer_natCast_smul, mul_left_comm]
      rfl)
    (fun i hi w hw => by
      obtain ⟨v, hv, hav⟩ := hlat w hw
      have hm := hm2 _ (conjEmb_not_mem X (h.mem τ))
      rw [h.p0] at hm
      refine mul_left_cancel₀ hN ?_
      rw [← natPer_natCast_smul, ← hav, ← perFr_conj X' x' _ τ.1 τ.2 i hi, hper _ i (hm ▸ hi) v hv, hm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [perFr_conj X x v τ.1 (h.mem τ) j (h.p0 ▸ Finset.mem_range.1 hj), ← natPer_move_q h, h.p0, hav,
        natPer_natCast_smul, mul_left_comm]
      rfl)
  let b : Frame X'.Ψ r := fun τ => ((mat z τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ)
  have hb : b ∈ Bor X'.Ψ r := fun τ => by
    refine ⟨?_, (hloc τ).1⟩
    show ((mat z τ)⁻¹ * mat x' τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hz τ).1) (hx' τ).1
  have hxb : x' = rmul z b := by
    funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (mat z τ) (mat x' τ) (isUnit_iff_ne_zero.2 (hz τ).1)).symm
  refine ⟨b, hb, hxb, fun hu hu' => ?_⟩
  have hbd : ∀ τ i, ‖b τ i i‖ = 1 := by
    intro τ i
    have e := FrameDegreeData.ratio_rmul X' z hz hb τ i
    rw [← hxb, norm_div, norm_div, hu', hu', hzd, h.dmin_eq, h.dmin_eq, hu, hu, div_one, _root_.mul_one] at e
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 e.symm
  refine ⟨hbd, fun τ i hi => ?_⟩
  by_cases hτ : τ ∈ X.Ψ
  · rw [hm1 τ hτ, h.p0] at hi
    exact ((hloc ⟨τ, h.psi ▸ hτ⟩).2 (hbd _)).1 i hi
  · rw [hm2 τ hτ, h.p0] at hi
    have := ((hloc ⟨conjEmb τ, h.psi ▸ conjEmb_mem X hτ⟩).2 (hbd _)).2 i hi
    rwa [PeriodBorel.conjEmb_conjEmb] at this

end GlobalTheory.PeriodBorelQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramesDifferByIsometryOfTriangularPeriodsStatement
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_differ_by_isometry_of_triangular_periods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) (h : QMatch X X' N a), 0 < N → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * Formalism.L2.PjFree.perFr X x v τ j) → ∃ b ∈ Bor X'.Ψ r, x' = rmul (lact a (castFr h.psi x)) b ∧ (IsUnitFr X x → IsUnitFr X' x' → (∀ τ i, ‖b τ i i‖ = 1) ∧ ∀ τ, ∀ i < m τ, ‖A τ i i‖ = 1) := by
  first | exact @GlobalTheory.PeriodBorelQ.borel_of_periods_q | exact GlobalTheory.PeriodBorelQ.borel_of_periods_q | (intros; apply GlobalTheory.PeriodBorelQ.borel_of_periods_q <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormRightConvolutionLeAdelicHeightPow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormRightConvolutionLeAdelicHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ENNReal

namespace GlobalTheory.ConvGrowth

open GlobalTheory.AutomorphicL2Unitary

theorem lintegral_sq_le {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    {S : Set G} (hS : MeasurableSet S) (N : ℝ≥0∞) (hN : ∀ x : G, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (F : L2 Γ μ) :
    ∫⁻ z in S, ‖lift Γ F z‖ₑ ^ (2 : ℝ) ∂μ ≤ N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ := by
  have hm : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  rw [← lintegral_indicator hS,
    lintegral_eq_lintegral_tsum (Γ := Γ) ((hm.enorm.pow_const _).indicator hS),
    ← lintegral_const_mul'' _ ((Lp.aestronglyMeasurable F).enorm.pow_const _)]
  refine lintegral_mono fun q => ?_
  have e : ∀ γ : Γ, S.indicator (fun z => ‖lift Γ F z‖ₑ ^ (2 : ℝ)) ((γ : G) * q.out) =
      {γ : Γ | (γ : G) * q.out ∈ S}.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) γ := by
    intro γ
    by_cases hγ : (γ : G) * q.out ∈ S
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem (show γ ∈ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]
      simp only [GlobalTheory.AutomorphicL2Unitary.lift, mk_mul, Quotient.out_eq]
    · rw [Set.indicator_of_notMem hγ,
        Set.indicator_of_notMem (show γ ∉ {γ : Γ | (γ : G) * q.out ∈ S} from hγ)]
  rw [tsum_congr e, ← tsum_subtype, ENNReal.tsum_set_const]
  gcongr
  exact hN _

theorem norm_convR_le_height : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Ω : Set (GA D V)}, IsCompact Ω → (∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A)) → ∃ (A : ℕ) (C : ℝ), ∀ f' : GA D V → ℂ, Continuous f' → tsupport f' ⊆ Ω → ∀ M : ℝ, (∀ y, ‖f' y‖ ≤ M) → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (g : GA D V), ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g‖ ≤ C * M * ‖F‖ * GlobalTheory.Grow.height V g ^ A := by
  intro D V μ _ _ Ω hΩ ⟨A, C, hC⟩
  refine ⟨A, (μ Ω ^ (1 / 2 : ℝ)).toReal * Real.sqrt (max C 0), ?_⟩
  intro f' hf' hsupp M hM F g
  set b : ℝ := Real.sqrt (max C 0) * GlobalTheory.Grow.height V g ^ A with hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hh : 0 ≤ GlobalTheory.Grow.height V g := zero_le_one.trans (GlobalTheory.Grow.one_le_height V g)
  have hb0 : 0 ≤ b := by positivity
  set S : Set (GA D V) := (g * ·) '' Ω with hSdef
  have hSc : IsCompact S := hΩ.image (continuous_const_mul g)
  have hS : MeasurableSet S := hSc.isClosed.measurableSet
  have hcount : ∀ x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ S}.encard ≤ ENNReal.ofReal b ^ 2 := by
    intro x
    obtain ⟨hfin, hle⟩ := hC g x
    rw [← hfin.cast_ncard_eq, ← ENNReal.ofReal_pow hb0]
    have e : b ^ 2 = max C 0 * GlobalTheory.Grow.height V g ^ (2 * A) := by
      rw [hb, mul_pow, Real.sq_sqrt (le_max_right _ _), ← pow_mul, mul_comm A 2]
    rw [e]
    calc (((({γ : GQ V | (γ : GA D V) * x ∈ S}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞)
        = ENNReal.ofReal ({γ : GQ V | (γ : GA D V) * x ∈ S}.ncard : ℝ) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  set φ : GA D V → ℂ := GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F with hφ
  have hm : AEStronglyMeasurable φ μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have hmp : MeasurePreserving (g * ·) (μ.restrict Ω) (μ.restrict S) := by
    have := (measurePreserving_mul_left μ g).restrict_preimage_emb (measurableEmbedding_mulLeft g) S
    rwa [hSdef, preimage_image_eq _ (mul_right_injective g)] at this
  have hm' : AEStronglyMeasurable (φ ∘ (g * ·)) (μ.restrict Ω) :=
    hm.restrict.comp_measurePreserving hmp

  have h1 : ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' φ g‖ₑ ≤ ENNReal.ofReal M * eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator hΩ.measurableSet]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y => ?_)
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy, enorm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (zero_le)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hM y)
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport fun h => hy (hsupp h)]
      simp
    exact hm'

  have h2 : eLpNorm (φ ∘ (g * ·)) 1 (μ.restrict Ω) ≤ eLpNorm φ 2 (μ.restrict S) * μ Ω ^ (1 / 2 : ℝ) := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm').trans (le_of_eq ?_)
    rw [eLpNorm_comp_measurePreserving hm.restrict hmp, Measure.restrict_apply_univ]
    norm_num

  have h3 : eLpNorm φ 2 (μ.restrict S) ≤ ENNReal.ofReal b * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    calc (∫⁻ z in S, ‖φ z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal b ^ 2 * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow (lintegral_sq_le (GQ V) μ hS _ hcount F) (by norm_num)
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast two_ne_zero]
    exact Lp.aestronglyMeasurable F
    exact hm.restrict
  have hE := h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right h3 zero_le))
    zero_le)
  have hμ : μ Ω ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hΩ.measure_lt_top.ne
  have hfin : ENNReal.ofReal M * (ENNReal.ofReal b * eLpNorm F 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ) * μ Ω ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top F)) hμ)
  have := ENNReal.toReal_mono hfin hE
  rw [toReal_enorm] at this
  refine this.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0,
    ENNReal.toReal_ofReal hb0, ← Lp.norm_def, hb]
  ring

end GlobalTheory.ConvGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormRightConvolutionLeAdelicHeightPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_rightConvolution_le_adelic_height_pow : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Ω : Set (GA D V)}, IsCompact Ω → (∃ (A : ℕ) (C : ℝ), ∀ g x : GA D V, {γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.Finite ∧ ({γ : GQ V | (γ : GA D V) * x ∈ (g * ·) '' Ω}.ncard : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ (2 * A)) → ∃ (A : ℕ) (C : ℝ), ∀ f' : GA D V → ℂ, Continuous f' → tsupport f' ⊆ Ω → ∀ M : ℝ, (∀ y, ‖f' y‖ ≤ M) → ∀ (F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ) (g : GA D V), ‖GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g‖ ≤ C * M * ‖F‖ * GlobalTheory.Grow.height V g ^ A := by
  first | exact @GlobalTheory.ConvGrowth.norm_convR_le_height | exact GlobalTheory.ConvGrowth.norm_convR_le_height | (intros; apply GlobalTheory.ConvGrowth.norm_convR_le_height <;> assumption)
end
end
