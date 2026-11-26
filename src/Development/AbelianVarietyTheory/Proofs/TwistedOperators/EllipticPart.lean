module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalClassTermEqVolumeMulProdOrbitalIntegrals
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePreimageOfNhdsZero
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix Topology

noncomputable section

namespace GlobalTheory.TrFinite

theorem finite_preimage_of_nhds_zero {A G : Type} [AddCommGroup A] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (f : A →+ G) {U : Set G} (hU : U ∈ 𝓝 (0 : G)) (h : ∀ x, f x ∈ U → x = 0)
    {K : Set G} (hK : IsCompact K) : {x | f x ∈ K}.Finite := by
  obtain ⟨V, hV0, hV⟩ : ∃ V ∈ 𝓝 (0 : G), ∀ a ∈ V, ∀ b ∈ V, a - b ∈ U := by
    have ht : Tendsto (fun p : G × G => p.1 - p.2) (𝓝 ((0 : G), (0 : G))) (𝓝 0) := by
      simpa using (continuous_sub.tendsto ((0 : G), (0 : G)))
    have h2 := ht hU
    rw [nhds_prod_eq] at h2
    obtain ⟨V1, h1, V2, h2', hs⟩ := Filter.mem_prod_iff.1 h2
    exact ⟨V1 ∩ V2, inter_mem h1 h2', fun a ha b hb => @hs (a, b) ⟨ha.1, hb.2⟩⟩
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => (fun y => y - k) ⁻¹' V) (fun k _ => by
    have hc : Continuous fun y : G => y - k := continuous_id.sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV0))
  have hsub : {x | f x ∈ K} ⊆ ⋃ k ∈ t, {x | f x - k ∈ V} := fun x hx => by
    have := ht hx
    simp only [Set.mem_iUnion, Set.mem_preimage] at this ⊢
    exact this
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun k _ => ?_) hsub
  refine Set.Subsingleton.finite fun x hx y hy => ?_
  have hm : f (x - y) ∈ U := by
    have := hV _ hx _ hy
    rwa [sub_sub_sub_cancel_right, ← map_sub] at this
  exact sub_eq_zero.1 (h _ hm)

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end GlobalTheory.TrFinite

namespace GlobalTheory.TrFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem charpoly_conj_ratEmb (γ : GRat σ J) (x : GAd σ J) :
    (((matHom (AF F) σ J (x⁻¹ * ratEmb σ J γ * x) : GL (Fin n) (AF F ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly = γ.1.1.charpoly.map (inclR (AF F)) := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']
  exact Matrix.charpoly_map _ _

theorem finite_ratEmb_mem {K : Set (GAd σ J)} (hK : IsCompact K) : {γ : GRat σ J | ratEmb σ J γ ∈ K}.Finite := by
  haveI : DiscreteTopology (ratPts σ J) := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have hcl : IsClosed (ratPts σ J : Set (GAd σ J)) := Subgroup.isClosed_of_discrete
  have hfin : ((Subtype.val : ratPts σ J → GAd σ J) ⁻¹' K).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  let g : GRat σ J → ratPts σ J := fun γ => ⟨ratEmb σ J γ, range_ratEmb σ J ▸ ⟨γ, rfl⟩⟩
  have hg : Function.Injective g := fun a b h => ratEmb_injective σ J (congrArg Subtype.val h)
  exact Set.Finite.preimage (f := g) hg.injOn hfin

theorem finite_charpoly_and_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J)), IsCompact C →
    {Q : E[X] | ∃ γ : GRat σ J, γ.1.1.charpoly = Q ∧ ∃ x, x⁻¹ * ratEmb σ J γ * x ∈ C}.Finite ∧
      ∀ x, {γ : GRat σ J | x⁻¹ * ratEmb σ J γ * x ∈ C}.Finite := by
  intro F E _ _ _ _ _ σ _ n J C hC
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  refine ⟨?_, fun x => ?_⟩
  ·
    let c : Fin (n + 1) → GAd σ J → AF F ⊗[F] E := fun i g =>
      (((matHom (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly.coeff i
    have hc : ∀ i, Continuous (c i) := fun i =>
      (continuous_coeff_charpoly n i).comp (Units.continuous_val.comp continuous_subtype_val)
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
    let T : Fin (n + 1) → Set E := fun i => {e | (inclR (AF F)).toAddMonoidHom e ∈ c i '' C}
    have hT : ∀ i, (T i).Finite := fun i =>
      finite_preimage_of_nhds_zero _ hU hU0 (hC.image (hc i))
    let S := {Q : E[X] | ∃ γ : GRat σ J, γ.1.1.charpoly = Q ∧ ∃ x, x⁻¹ * ratEmb σ J γ * x ∈ C}
    let φ : E[X] → Fin (n + 1) → E := fun Q i => Q.coeff i
    have hdeg : ∀ Q ∈ S, Q.natDegree = n := by
      rintro Q ⟨γ, rfl, -⟩
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hinj : Set.InjOn φ S := fun P hP Q hQ h => by
      ext i
      by_cases hi : i ≤ n
      · exact congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
      · push_neg at hi
        rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg P hP]; exact hi),
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg Q hQ]; exact hi)]
    have himg : φ '' S ⊆ Set.pi Set.univ T := by
      rintro _ ⟨Q, ⟨γ, rfl, x, hx⟩, rfl⟩ i -
      refine ⟨_, hx, ?_⟩
      change (((matHom (AF F) σ J (x⁻¹ * ratEmb σ J γ * x) : GL (Fin n) (AF F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly.coeff i = inclR (AF F) (γ.1.1.charpoly.coeff i)
      rw [charpoly_conj_ratEmb, coeff_map]
    exact Set.Finite.of_finite_image ((Set.Finite.pi hT).subset himg) hinj
  · have hK : IsCompact ((fun g => x * g * x⁻¹) '' C) :=
      hC.image ((continuous_const.mul continuous_id).mul continuous_const)
    refine (finite_ratEmb_mem σ J hK).subset fun γ hγ => ⟨_, hγ, ?_⟩
    change x * (x⁻¹ * ratEmb σ J γ * x) * x⁻¹ = ratEmb σ J γ
    group

end GlobalTheory.TrFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCharpolyKernelEqStableOrbitalIntegrals
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamilies
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalNormClassesEqLocalUnramifiedCM
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalNormClassesEqLocalUnramifiedCM
open Set Filter Polynomial NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.TrEll.Hasse

abbrev Ten {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r) (k : Type) [CommRing k]
    [Algebra F k] : Type := k ⊗[F] Fld P

section Bridge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  (P : PPol (IsCMField.complexConj E).toAlgHom r)

def toSR : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r :=
  ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1, by rw [coeff_zero_eq_eval_zero]; exact P.2.2.2.2.1, by
    have h := P.2.2.2.2.2
    rw [sharp, ← coeff_zero_eq_eval_zero] at h
    exact h⟩

variable (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

def incl : k ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P) →+* Ten P k :=
  (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.inclPlus (toSR P) k).toRingHom

theorem incl_injective : Function.Injective (incl P k) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := k) (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P)).val.toLinearMap
    Subtype.val_injective

theorem sigR_incl (a) : sigR k (star' P) (incl P k a) = incl P k a :=
  GlobalTheory.TraceClasses.involBase_inclPlus (toSR P) k a

theorem exists_incl_eq_add (z : Ten P k) : ∃ a, incl P k a = z + sigR k (star' P) z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s y =>
    refine ⟨s ⊗ₜ ⟨y + star' P y, ?_⟩, TensorProduct.tmul_add _ _ _⟩
    change star' P (y + star' P y) = y + star' P y
    have : star' P (star' P y) = y := GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_invol (toSR P) y
    rw [map_add (f := _), this, add_comm]
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]; ring⟩

theorem exists_incl_eq {z : Ten P k} (hz : sigR k (star' P) z = z) : ∃ a, incl P k a = z := by
  obtain ⟨a, ha⟩ := exists_incl_eq_add P k ((2⁻¹ : maximalRealSubfield E) • z)
  refine ⟨a, ?_⟩
  have : sigR k (star' P) ((2⁻¹ : maximalRealSubfield E) • z) = (2⁻¹ : maximalRealSubfield E) • sigR k (star' P) z :=
    map_smul (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k) (star' P)) _ _
  rw [ha, this, hz, ← add_smul]
  norm_num

def unitMap : (k ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P))ˣ →* plusUnits P k :=
  (Units.map (incl P k).toMonoidHom).codRestrict _ fun a => Units.ext (sigR_incl P k a)

theorem unitMap_surjective : Function.Surjective (unitMap P k) := by
  intro x
  obtain ⟨a, ha⟩ := exists_incl_eq P k (z := x.1.1) (congrArg Units.val x.2)
  obtain ⟨b, hb⟩ := exists_incl_eq P k (z := (x⁻¹).1.1) (congrArg Units.val (x⁻¹).2)
  have h : a * b = 1 := incl_injective P k (by rw [map_mul, ha, hb, map_one]; exact x.1.mul_inv)
  exact ⟨Units.mkOfMulEqOne a b h, Subtype.ext (Units.ext ha)⟩

theorem mk_unitMap_eq_iff (a b) : (QuotientGroup.mk (unitMap P k a) : Cls P k) = QuotientGroup.mk (unitMap P k b) ↔
    (QuotientGroup.mk a : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.NormClass (toSR P) k) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
def clsMap : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.NormClass (toSR P) k →* Cls P k :=
  QuotientGroup.map _ _ (unitMap P k) fun _ h => h

theorem clsMap_injective : Function.Injective (clsMap P k) := by
  intro q q' h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
  exact (mk_unitMap_eq_iff P k a b).1 h

theorem clsMap_surjective : Function.Surjective (clsMap P k) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, rfl⟩ := unitMap_surjective P k x
  exact ⟨QuotientGroup.mk a, rfl⟩

theorem hform_eq (J : Matrix (Fin r) (Fin r) E) (u u' : Fin r → k ⊗[maximalRealSubfield E] E) :
    Formalism.UG.hform (sigR k (IsCMField.complexConj E).toAlgHom) (JR k J) u' u = GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.gramForm k Jᵀ u u' := by
  rw [Formalism.UG.hform, GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.gramForm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change GlobalTheory.HermLocal.ccBase E k (u' j) * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * u i =
    u i * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * GlobalTheory.HermLocal.ccBase E k (u' j)
  ring

theorem isometric_iff (J : Matrix (Fin r) (Fin r) E) (a) :
    (∃ φ, IsIsom P k J (incl P k a) φ) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Isometric (toSR P) k Jᵀ a := by
  constructor
  · rintro ⟨φ, h⟩
    exact ⟨φ.toAddEquiv, fun e y => φ.map_smul e y, fun y y' => (hform_eq k J _ _).symm.trans (h y y')⟩
  · rintro ⟨φ, h1, h2⟩
    exact ⟨{ φ with map_smul' := h1 }, fun y y' => (hform_eq k J _ _).trans (h2 y y')⟩

theorem clsMap_mem_iff (J : Matrix (Fin r) (Fin r) E) (q) :
    clsMap P k q ∈ XSet P k J ↔ q ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.classes (toSR P) k Jᵀ := by
  constructor
  · rintro ⟨x, φ, e, h⟩
    obtain ⟨a, rfl⟩ := unitMap_surjective P k x
    exact ⟨a, clsMap_injective P k e, (isometric_iff P k J a.1).1 ⟨φ, h⟩⟩
  · rintro ⟨a, rfl, h⟩
    obtain ⟨φ, h⟩ := (isometric_iff P k J a.1).2 h
    exact ⟨unitMap P k a, φ, rfl, h⟩

theorem incl_toLocalPlus (a) : incl P k (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocalPlus (toSR P) k a) =
    Algebra.TensorProduct.map (Algebra.ofId (maximalRealSubfield E) k) (AlgHom.id _ (Fld P))
      (incl P (maximalRealSubfield E) a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact (map_zero _).symm
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]; exact (map_add _ _ _).symm

theorem mapsCls_iff (q) (c : Cls P k) :
    MapsCls P (k := maximalRealSubfield E) (Algebra.ofId (maximalRealSubfield E) k) (clsMap P _ q) c ↔
      c = clsMap P k (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocal (toSR P) k q) := by
  constructor
  · rintro ⟨x, x', e, rfl, h⟩
    obtain ⟨a, rfl⟩ := unitMap_surjective P _ x
    obtain rfl : QuotientGroup.mk a = q := clsMap_injective P _ e
    refine congrArg QuotientGroup.mk (Subtype.ext (Units.ext ?_))
    exact h.trans (incl_toLocalPlus P k a.1).symm
  · rintro rfl
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨unitMap P _ a, unitMap P k (Units.map (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocalPlus (toSR P) k).toMonoidHom a), rfl, rfl,
      incl_toLocalPlus P k a.1⟩

end Bridge

theorem rational_eq_local : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ q q' : Cls P F, q ∈ XSet P F J → q' ∈ XSet P F J → (∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Cls P (Fv F v), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q a ∧ MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q' a) → (∀ w : InfinitePlace F, ∃ a : Cls P w.Completion, MapsCls P (k := F) (Algebra.ofId F w.Completion) q a ∧ MapsCls P (k := F) (Algebra.ofId F w.Completion) q' a) → q = q') ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P (Fv F v) J) → (∀ w, qa w ∈ XSet P w.Completion J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ q : Cls P F, q ∈ XSet P F J ∧ (∀ v : HeightOneSpectrum (𝓞 F), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q (qf v)) ∧ ∀ w : InfinitePlace F, MapsCls P (k := F) (Algebra.ofId F w.Completion) q (qa w) := by
  intro E _ _ F _ σ hcm hur r P J hJ
  obtain ⟨h1, h2, h3, h4⟩ := hcm
  haveI : Algebra.IsQuadraticExtension F E := ⟨h3⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  obtain rfl : F = maximalRealSubfield E := CMExtension.eq_maximalRealSubfield E F
  obtain rfl : σ = (IsCMField.complexConj E).toAlgHom := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact AlgHom.ext fun x => φ.injective ((h4 φ x).trans (IsCMField.complexEmbedding_complexConj E φ x).symm)
  have H := GlobalTheory.TraceClasses.rationalEqAdelic E hur r Jᵀ (fun a b => hJ.1 a b)
    (by rw [Matrix.det_transpose]; exact hJ.2) (toSR P)
  constructor
  · intro q q' hq hq' hf ha
    obtain ⟨q, rfl⟩ := clsMap_surjective P _ q
    obtain ⟨q', rfl⟩ := clsMap_surjective P _ q'
    refine congrArg _ (H.injOn ((clsMap_mem_iff P _ J q).1 hq) ((clsMap_mem_iff P _ J q').1 hq')
      (Prod.ext (funext fun v => ?_) (funext fun w => ?_)))
    · obtain ⟨a, e, e'⟩ := hf v
      exact clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))
    · obtain ⟨a, e, e'⟩ := ha w
      exact clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))
  · intro qf qa hf ha h1
    choose xf hxf using fun v => clsMap_surjective P _ (qf v)
    choose xa hxa using fun w => clsMap_surjective P _ (qa w)
    obtain ⟨q, hq, e⟩ := H.surjOn (show (xf, xa) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.adelicClasses (toSR P) Jᵀ from
      ⟨fun v => (clsMap_mem_iff P _ J _).1 (by rw [hxf]; exact hf v),
        fun w => (clsMap_mem_iff P _ J _).1 (by rw [hxa]; exact ha w), by
        refine (Filter.eventually_cofinite.1 h1).subset fun v hv hv1 => hv ?_
        have : xf v = 1 := clsMap_injective P _ (by rw [hxf, hv1, map_one])
        exact ⟨1, RingHom.isIntegralElem_one _, RingHom.isIntegralElem_one _, this.symm⟩⟩)
    refine ⟨clsMap P _ q, (clsMap_mem_iff P _ J q).2 hq, fun v => (mapsCls_iff P _ q _).2 ?_,
      fun w => (mapsCls_iff P _ q _).2 ?_⟩
    · exact (hxf v).symm.trans (congrArg _ (congrFun (congrArg Prod.fst e) v).symm)
    · exact (hxa w).symm.trans (congrArg _ (congrFun (congrArg Prod.snd e) w).symm)

end GlobalTheory.TrEll.Hasse
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalNormClassesEqLocalUnramifiedCMStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ q q' : Cls P F, q ∈ XSet P F J → q' ∈ XSet P F J → (∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Cls P (Fv F v), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q a ∧ MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q' a) → (∀ w : InfinitePlace F, ∃ a : Cls P w.Completion, MapsCls P (k := F) (Algebra.ofId F w.Completion) q a ∧ MapsCls P (k := F) (Algebra.ofId F w.Completion) q' a) → q = q') ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P (Fv F v) J) → (∀ w, qa w ∈ XSet P w.Completion J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ q : Cls P F, q ∈ XSet P F J ∧ (∀ v : HeightOneSpectrum (𝓞 F), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q (qf v)) ∧ ∀ w : InfinitePlace F, MapsCls P (k := F) (Algebra.ofId F w.Completion) q (qa w) := by
  first | exact @GlobalTheory.TrEll.Hasse.rational_eq_local | exact GlobalTheory.TrEll.Hasse.rational_eq_local | (intros; apply GlobalTheory.TrEll.Hasse.rational_eq_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamilies
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll.RatClasses

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ} {P : PPol σ r}
  {J : Matrix (Fin n) (Fin n) E} {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k']

theorem mapsCls_unique {ψ : k →ₐ[F] k'} {q : Cls P k} {a b : Cls P k'} (ha : MapsCls P ψ q a)
    (hb : MapsCls P ψ q b) : a = b := by
  obtain ⟨x, x', hx, rfl, ex⟩ := ha
  obtain ⟨y, y', hy, rfl, ey⟩ := hb
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hx.trans hy.symm))
  let m := Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P))
  have hm : ∀ z, sigR k' (star' P) (m z) = m (sigR k (star' P) z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [m, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ⟨Units.map m.toMonoidHom c, ?_⟩)
  have hc' : x.1.1 * (c.1 * sigR k (star' P) c.1) = y.1.1 := by
    have : c.1 * sigR k (star' P) c.1 = (x.1⁻¹ * y.1).1 := congrArg Units.val hc
    rw [this, Units.val_mul, Units.mul_inv_cancel_left]
  change _ = x'.1⁻¹ * y'.1
  rw [eq_inv_mul_iff_mul_eq]
  apply Units.ext
  change x'.1.1 * (m c.1 * sigR k' (star' P) (m c.1)) = y'.1.1
  rw [ex, ey, hm, ← hc', map_mul, map_mul]

theorem mapH_diagH (ψ : k →ₐ[F] k') (γ : Formalism.UG.UJ (σ : E →+* E) J) :
    mapH σ J ψ (diagH σ J k γ) = diagH σ J k' γ :=
  Subtype.ext (Units.ext (Matrix.ext fun r s => by
    change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] (γ.1.1 r s)) = (1 : k') ⊗ₜ[F] (γ.1.1 r s)
    simp))

variable [NumberField F] [NumberField E] (hc : IsCMExt F E σ) (hJ : IsHermND σ J)
include hc hJ

theorem hasCls_unique {γ : HA k σ J} {q q' : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ q') : q = q' := by
  obtain ⟨x, φ, h, rfl, e⟩ := h
  obtain ⟨x', φ', h', rfl, e'⟩ := h'
  exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').2.1 (by rw [e, e'])

theorem hasCls_of_isConj {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (e : IsConj γ γ') :
    HasCls P k J γ' q := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨g, rfl⟩ := isConj_iff.1 e
  exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x φ h).2.2.2 g

theorem isConj_of_hasCls {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ' q) :
    IsConj γ γ' := by
  obtain ⟨x, φ, h, e, rfl⟩ := h
  obtain ⟨x', φ', h', e', rfl⟩ := h'
  obtain ⟨g, hg⟩ := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').1 (e.trans e'.symm)
  exact isConj_iff.2 ⟨g, (hg _).symm⟩

theorem exists_mapsCls (ψ : k →ₐ[F] k') {γ : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) :
    ∃ q', MapsCls P ψ q q' ∧ HasCls P k' J (mapH σ J ψ γ) q' := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨x', φ', h', e1, e2, -⟩ := GlobalTheory.T.hermitian_isometry_base_change F E σ hc r n P J hJ k k' ψ x φ h
  exact ⟨_, ⟨x, x', rfl, rfl, e1⟩, x', φ', h', rfl, e2⟩

theorem exists_mapsCls_rat (k : Type) [CommRing k] [Algebra F k] {γ : GRat σ J} {q : Cls P F}
    (h : HasCls P F J (diagH σ J F γ) q) :
    ∃ q', MapsCls P (k := F) (Algebra.ofId F k) q q' ∧ HasCls P k J (diagH σ J k γ) q' := by
  simpa only [mapH_diagH] using exists_mapsCls hc hJ (Algebra.ofId F k) h

theorem exists_hasCls_rat {P : PPol σ n} (γ : GRat σ J) (h : γ.1.1.charpoly = P.1) :
    ∃ q, HasCls P F J (diagH σ J F γ) q := by
  obtain ⟨P', e, hq⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).2 γ (h ▸ P.2.2.1)
  obtain rfl : P' = P := Subtype.ext (e.symm.trans h)
  exact hq

theorem charpoly_of_hasCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) :
    γ.1.1.charpoly = P.1 := by
  obtain ⟨x, φ, h, -, e⟩ := h
  have h1 := (GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hc r n P J hJ F x φ h).1
  rw [e] at h1
  apply Polynomial.map_injective (inclR (F := F) (E := E) F) (inclR (F := F) (E := E) F).injective
  rw [← h1, ← Matrix.charpoly_map]
  rfl

theorem isConj_of_diagH {γ γ' : GRat σ J} (h : IsConj (diagH σ J F γ) (diagH σ J F γ')) : IsConj γ γ' := by
  have hb := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).1
  obtain ⟨g, e⟩ := isConj_iff.1 h
  obtain ⟨g, rfl⟩ := hb.2 g
  exact isConj_iff.2 ⟨g, hb.1 (by simpa only [map_mul, map_inv] using e)⟩

theorem existsUnique_hasCls_rat {P : PPol σ n} (k : Type) [CommRing k] [Algebra F k] (γ : GRat σ J)
    (h : γ.1.1.charpoly = P.1) : ∃! q, HasCls P k J (diagH σ J k γ) q := by
  obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
  obtain ⟨q', -, hq'⟩ := exists_mapsCls_rat hc hJ k hq
  exact ⟨q', hq', fun _ h => hasCls_unique hc hJ h hq'⟩

theorem exists_common {γ γ' : GRat σ J} {q q' : Cls P F} (h : HasCls P F J (diagH σ J F γ) q)
    (h' : HasCls P F J (diagH σ J F γ') q')
    (H : ∀ a, HasCls P k J (diagH σ J k γ) a → HasCls P k J (diagH σ J k γ') a) :
    ∃ a, MapsCls P (k := F) (Algebra.ofId F k) q a ∧ MapsCls P (k := F) (Algebra.ofId F k) q' a := by
  obtain ⟨a, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  obtain ⟨b, h3, h4⟩ := exists_mapsCls_rat hc hJ k h'
  exact ⟨a, h1, hasCls_unique hc hJ h4 (H a h2) ▸ h3⟩

theorem hasCls_of_mapsCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) {a : Cls P k}
    (H : MapsCls P (k := F) (Algebra.ofId F k) q a) : HasCls P k J (diagH σ J k γ) a := by
  obtain ⟨b, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  exact mapsCls_unique h1 H ▸ h2

end General

theorem rat_classes_iff_local (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E)
    (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E)
    (hJ : IsHermND σ J) :
    (∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → (∀ v, ∃! q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q) ∧
      (∀ w, ∃! q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q) ∧
      ∀ᶠ v in cofinite, HasCls P _ J (proj σ J v (ratEmb σ J γ)) 1) ∧
    (∀ γ γ' : GRat σ J, γ.1.1.charpoly = P.1 → γ'.1.1.charpoly = P.1 → (IsConj γ γ' ↔
      (∀ v q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q → HasCls P _ J (proj σ J v (ratEmb σ J γ')) q) ∧
        ∀ w q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q → HasCls P _ J (projArch σ J w (ratEmb σ J γ')) q)) ∧
    ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion),
      (∀ v, qf v ∈ XSet P _ J) → (∀ w, qa w ∈ XSet P _ J) → (∀ᶠ v in cofinite, qf v = 1) →
      ∃ γ : GRat σ J, γ.1.1.charpoly = P.1 ∧ (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v)) ∧
        ∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w) := by
  have e1 : ∀ v γ, proj σ J v (ratEmb σ J γ) = diagH σ J (Fv F v) γ := proj_ratEmb σ J
  have e2 : ∀ w γ, projArch σ J w (ratEmb σ J γ) = diagH σ J w.Completion γ := projArch_ratEmb σ J
  obtain ⟨H1, H2⟩ := GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM E F σ hc hu r P J hJ
  refine ⟨fun γ h => ⟨fun v => ?_, fun w => ?_, ?_⟩, fun γ γ' h h' => ⟨fun e => ⟨fun v q hq => ?_, fun w q hq => ?_⟩,
    fun H => ?_⟩, fun qf qa hf ha h1 => ?_⟩
  · rw [e1]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · rw [e2]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · have := isLattice_stdLattice (E := E) (n := r)
    filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hc r P J hJ (stdLattice E r),
      eventually_proj_mem_stabLoc σ J (stdLattice E r) (ratEmb σ J γ)] with v hv hm
    obtain ⟨q, hq, -⟩ := existsUnique_hasCls_rat hc hJ (Fv F v) γ h
    rw [← e1] at hq
    exact hv.2.1 _ q hq ⟨1, by simpa only [inv_one, one_mul, mul_one] using hm⟩ ▸ hq
  · exact hasCls_of_isConj hc hJ hq ((proj σ J v).map_isConj ((ratEmb σ J).map_isConj e))
  · exact hasCls_of_isConj hc hJ hq ((projArch σ J w).map_isConj ((ratEmb σ J).map_isConj e))
  · simp only [e1, e2] at H
    obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
    obtain ⟨q', hq'⟩ := exists_hasCls_rat hc hJ γ' h'
    obtain rfl : q = q' := H1 q q' (hq.mem P) (hq'.mem P) (fun v => exists_common hc hJ hq hq' (H.1 v))
      fun w => exists_common hc hJ hq hq' (H.2 w)
    exact isConj_of_diagH hc hJ (isConj_of_hasCls hc hJ hq hq')
  · obtain ⟨q, hq, h2, h3⟩ := H2 qf qa hf ha h1
    obtain ⟨g, hg⟩ := exists_hasCls P hq
    obtain ⟨γ, rfl⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc r J hJ).1.2 g
    refine ⟨γ, charpoly_of_hasCls hc hJ hg, fun v => ?_, fun w => ?_⟩
    · rw [e1]; exact hasCls_of_mapsCls hc hJ hg (h2 v)
    · rw [e2]; exact hasCls_of_mapsCls hc hJ hg (h3 w)

end GlobalTheory.TrEll.RatClasses
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamiliesStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_classes_iff_local_class_families : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → (∀ v, ∃! q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q) ∧ (∀ w, ∃! q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q) ∧ ∀ᶠ v in cofinite, HasCls P _ J (proj σ J v (ratEmb σ J γ)) 1) ∧ (∀ γ γ' : GRat σ J, γ.1.1.charpoly = P.1 → γ'.1.1.charpoly = P.1 → (IsConj γ γ' ↔ (∀ v q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q → HasCls P _ J (proj σ J v (ratEmb σ J γ')) q) ∧ ∀ w q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q → HasCls P _ J (projArch σ J w (ratEmb σ J γ')) q)) ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P _ J) → (∀ w, qa w ∈ XSet P _ J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ γ : GRat σ J, γ.1.1.charpoly = P.1 ∧ (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v)) ∧ ∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w) := by
  first | exact @GlobalTheory.TrEll.RatClasses.rat_classes_iff_local | exact GlobalTheory.TrEll.RatClasses.rat_classes_iff_local | (intros; apply GlobalTheory.TrEll.RatClasses.rat_classes_iff_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsumRestrictedFamilyEqProdFinsum
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem finsum_restrictedFamily_eq_prod_finsum : ∀ (V W : Type) [Fintype W] (C : V → Type) [∀ v, One (C v)] (X : ∀ v, Set (C v)) (Y : W → Type) [∀ w, Finite (Y w)], (∀ v, (X v).Finite) → ∀ (o : ∀ v, X v → ℂ) (oa : ∀ w, Y w → ℂ), (∀ᶠ v in cofinite, (1 : C v) ∈ X v ∧ ∀ q : X v, (q.1 = 1 → o v q = 1) ∧ (q.1 ≠ 1 → o v q = 0)) → (Function.support fun p : {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1} => (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w)).Finite ∧ ∑ᶠ p : {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1}, (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w) = (∏ᶠ v, ∑ᶠ q : X v, o v q) * ∏ w, ∑ᶠ q : Y w, oa w q := by
  intro V W _ C _ X Y _ hX o oa hev
  classical
  have hfin := Filter.eventually_cofinite.1 hev
  set S : Finset V := hfin.toFinset with hSdef
  have hS : ∀ v, v ∉ S → ((1 : C v) ∈ X v ∧ ∀ q : X v, (q.1 = 1 → o v q = 1) ∧ (q.1 ≠ 1 → o v q = 0)) := by
    intro v hv
    by_contra h
    exact hv (by simpa [hSdef] using h)
  haveI : ∀ v, Fintype (X v) := fun v => (hX v).fintype
  haveI : ∀ w, Fintype (Y w) := fun w => Fintype.ofFinite _
  let Sub := {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1}
  let F : Sub → ℂ := fun p => (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w)
  let emb : (∀ v : S, X v) × (∀ w, Y w) → Sub := fun t =>
    ⟨(fun v => if h : v ∈ S then t.1 ⟨v, h⟩ else ⟨1, (hS v h).1⟩, t.2), by
      refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
      by_contra h
      simp [dif_neg (show v ∉ S from h)] at hv⟩
  have hmul : ∀ p : Sub, (Function.mulSupport fun v => o v (p.1.1 v)).Finite := by
    intro p
    refine (S.finite_toSet.union (Filter.eventually_cofinite.1 p.2)).subset ?_
    intro v hv
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (((hS v h.1).2 _).1 h.2)
  have hsupp : Function.support F ⊆ Set.range emb := by
    intro p hp
    have h1 : ∀ v, v ∉ S → (p.1.1 v).1 = 1 := by
      intro v hv
      by_contra hne
      apply hp
      show (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w) = 0
      rw [finprod_eq_zero _ v (((hS v hv).2 _).2 hne) (hmul p), zero_mul]
    refine ⟨(fun v => p.1.1 v, p.1.2), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · funext v
      by_cases hv : v ∈ S
      · simp only [emb, dif_pos hv]
      · simp only [emb, dif_neg hv]
        exact Subtype.ext (h1 v hv).symm
    · rfl
  have hinj : Function.Injective emb := by
    intro t t' h
    have h' := congrArg (fun p : Sub => p.1) h
    simp only [emb, Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    refine Prod.ext (funext fun v => ?_) h2
    have := congrFun h1 v.1
    simpa only [dif_pos v.2] using this
  have hval : ∀ t, F (emb t) = (∏ v : S, o v (t.1 v)) * ∏ w, oa w (t.2 w) := by
    intro t
    show (∏ᶠ v, o v ((emb t).1.1 v)) * ∏ w, oa w (t.2 w) = _
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [emb, dif_pos v.2]
    · intro v hv
      by_contra h
      apply hv
      simp only [emb, dif_neg (show v ∉ S from h)]
      exact ((hS v h).2 _).1 rfl
  have hsupp' : Function.support F ⊆ ↑(Finset.univ.image emb) := by
    intro p hp
    obtain ⟨t, rfl⟩ := hsupp hp
    simp
  refine ⟨(Finset.univ.image emb).finite_toSet.subset hsupp', ?_⟩
  show ∑ᶠ p, F p = _
  rw [finsum_eq_sum_of_support_subset _ hsupp', Finset.sum_image (fun a _ b _ h => hinj h)]
  simp only [hval]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Fintype.sum_mul_sum, ← Fintype.prod_sum, ← Fintype.prod_sum]
  congr 1
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [finsum_eq_sum_of_fintype]
    · intro v hv
      by_contra h
      apply hv
      show ∑ᶠ q : X v, o v q = 1
      rw [finsum_eq_single _ ⟨1, (hS v h).1⟩]
      · exact ((hS v h).2 _).1 rfl
      · intro q hq
        exact ((hS v h).2 q).2 (fun e => hq (Subtype.ext e))
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [finsum_eq_sum_of_fintype]

end GlobalTheory.TrEll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCharpolyKernelEqStableOrbitalIntegrals
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll

open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt (ratClass classKernel)

theorem classKernel_eq_sum {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (g : H) (f : G → ℂ)
    (x : G) (T : Finset H) (hT : ∀ δ, f (x⁻¹ * ι δ * x) ≠ 0 → δ ∈ T) :
    classKernel ι.range (ι g) f x = ∑ δ ∈ T, {δ | IsConj g δ}.indicator (fun δ => f (x⁻¹ * ι δ * x)) δ := by
  let e : {δ | IsConj g δ} → ratClass ι.range (ι g) := fun δ => ⟨ι δ, by
    obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
    exact ⟨ι c⁻¹, ⟨_, rfl⟩, by rw [← hc]; simp⟩⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b h => Subtype.ext (hι (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, _, ⟨c, rfl⟩, rfl⟩
    exact ⟨⟨c⁻¹ * g * c, isConj_iff.2 ⟨c⁻¹, by simp⟩⟩, Subtype.ext (by simp [e])⟩
  rw [classKernel, ← (Equiv.ofBijective e he).tsum_eq fun δ => f (x⁻¹ * δ * x)]
  refine (tsum_subtype {δ | IsConj g δ} fun δ => f (x⁻¹ * ι δ * x)).trans (tsum_eq_sum fun δ hδ => ?_)
  by_contra h
  exact hδ (hT δ fun h0 => h (by simp [indicator, h0]))

theorem finsum_eq_sum_classKernel {G H I : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι)
    (p : H → Prop) (g : I → H) (hp : ∀ δ, p δ ↔ ∃ i, IsConj (g i) δ) (hg : ∀ i j, IsConj (g i) (g j) → i = j)
    (f : G → ℂ) (S : Finset I) (hS : ∀ i ∉ S, ∀ x, f (x⁻¹ * ι (g i) * x) = 0) (x : G)
    (hx : {δ | f (x⁻¹ * ι δ * x) ≠ 0}.Finite) :
    ∑ᶠ δ : {δ // p δ}, f (x⁻¹ * ι δ.1 * x) = ∑ i ∈ S, classKernel ι.range (ι (g i)) f x := by
  classical
  rw [Finset.sum_congr rfl fun i _ => classKernel_eq_sum ι hι (g i) f x hx.toFinset fun δ h => hx.mem_toFinset.2 h,
    Finset.sum_comm]
  refine (finsum_set_coe_eq_finsum_mem (f := fun δ => f (x⁻¹ * ι δ * x)) {δ | p δ}).trans ?_
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset (s := hx.toFinset) _ fun δ h => by
    simpa using fun h0 => h (by simp [indicator, h0])]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  by_cases h : p δ
  · obtain ⟨i, hi⟩ := (hp δ).1 h
    have hiS : i ∈ S := by
      by_contra hn
      obtain ⟨c, hc⟩ := isConj_iff.1 hi
      refine hx.mem_toFinset.1 hδ ?_
      rw [← hS i hn ((ι c)⁻¹ * x), ← hc]
      simp [mul_assoc]
    rw [indicator_of_mem (show δ ∈ {δ | p δ} from h), Finset.sum_eq_single_of_mem i hiS fun j _ hj =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => hj (hg j i (hc.trans hi.symm))) _,
      indicator_of_mem (show δ ∈ {δ | IsConj (g i) δ} from hi)]
  · rw [indicator_of_notMem (show δ ∉ {δ | p δ} from h), Finset.sum_eq_zero fun j _ =>
      indicator_of_notMem (s := {δ | IsConj (g j) δ}) (fun (hc : IsConj (g j) δ) => h ((hp δ).2 ⟨j, hc⟩)) _]

theorem classKernel_eq_zero {G : Type} [Group G] (Γ : Subgroup G) (γ : G) (f : G → ℂ) (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    classKernel Γ γ f = 0 := by
  funext x
  refine (tsum_congr ?_).trans tsum_zero
  rintro ⟨_, c, -, rfl⟩
  rw [← h (c * x)]
  simp [mul_assoc]

theorem finite_of_eventually_eq_one {V Y : Type} [Finite Y] {C : V → Type} [∀ v, One (C v)] [∀ v, Finite (C v)]
    {X : ∀ v, Set (C v)} {p : (∀ v, X v) × Y → Prop} (A : Set {q // p q})
    (h : ∀ᶠ v in cofinite, ∀ i ∈ A, (i.1.1 v).1 = 1) : A.Finite := by
  have : Finite {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} := eventually_cofinite.1 h
  refine Set.Finite.of_finite_image
    (f := fun i : {q // p q} => ((fun v : {v | ¬ ∀ i ∈ A, (i.1.1 v).1 = 1} => i.1.1 v), i.1.2)) (Set.toFinite _)
    fun i hi j hj e => Subtype.ext (Prod.ext (funext fun v => ?_) (congrArg Prod.snd e :))
  by_cases hv : ∀ i ∈ A, (i.1.1 v).1 = 1
  · exact Subtype.ext ((hv i hi).trans (hv j hj).symm)
  · exact congrFun (congrArg Prod.fst e) ⟨v, hv⟩

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
  {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}

theorem exists_isCompact_tensor (ha : ∀ w, HasCompactSupport (fa w)) (hf : IsFinFamily σ J L ff) :
    ∃ C, IsCompact C ∧ ∀ y, tensor σ J fa ff y ≠ 0 → y ∈ C := by
  refine ⟨_, (infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod
    ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (isCompact_univ_pi ha))
      hf.tensorFin_mem.2), fun y hy => ?_⟩
  rw [tensor_eq_infFin] at hy
  exact ⟨fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hy) w (Finset.mem_univ w)),
    subset_tsupport _ (right_ne_zero_of_mul hy)⟩

theorem ne_zero_of_tensor (hf : IsFinFamily σ J L ff) {y : GAd σ J} (hy : tensor σ J fa ff y ≠ 0) (v) :
    ff v (proj σ J v y) ≠ 0 := by
  rw [tensor_eq_infFin] at hy
  simpa only [projFinLoc_projFin] using (hf.tensorFin_ne_zero_iff _).1 (right_ne_zero_of_mul hy) v


omit [NumberField F] [NumberField E] in
theorem charpoly_eq_of_isConj {γ δ : GRat σ J} (h : IsConj γ δ) : δ.1.1.charpoly = γ.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have : (c * γ * c⁻¹).1.1 = c.1.1 * γ.1.1 * (c.1⁻¹).1 := rfl
  rw [this, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end Adelic

theorem integral_polKernel : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → Integrable (descend (ratPts σ J) (polKernel P J (tensor σ J fa ff))) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf v) (ff v)) * ∏ w, Phi (J := J) (μa w) (dta w) (fa w) := by
  classical
  intro E _ _ F _ σ hCM hun r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  obtain ⟨H1, H2, H3⟩ := GlobalTheory.T.rational_unitary_classes_iff_local_class_families E F σ hCM hun r P J hJ
  obtain ⟨Ff, Fa⟩ := GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places F E σ hCM r P
  have hae := GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hCM r P J hJ L
  have hcl := GlobalTheory.T.rationalClassTerm_eq_volume_mul_prod_orbitalIntegrals F E σ hCM r P J hJ L μa μf μ hμ fa ff hfa hff dta dtf dt hdt
  let I := {p : (∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) × (∀ w : InfinitePlace F, XSet P w.Completion J) //
    ∀ᶠ v in cofinite, (p.1 v).1 = 1}
  obtain ⟨hsupp, hsum⟩ := finsum_restrictedFamily_eq_prod_finsum (HeightOneSpectrum (𝓞 F)) (InfinitePlace F)
    (fun v => Cls P (Fv F v)) (fun v => XSet P (Fv F v) J) (fun w => XSet P w.Completion J) (fun v => Set.toFinite _)
    (fun v => orbCls (μf v) (dtf v) (ff v)) (fun w => orbCls (μa w) (dta w) (fa w)) (by
      filter_upwards [hae, hff.2, hμ.eventually_eq_one, IsRestrictedProd.eventually_eq_one hdt] with v h1 h2 h3 h4
      rw [h2]
      exact ⟨h1.1, h1.2.2.2 _ _ (hμ.haar_loc v) (IsRestrictedProd.haar_loc hdt v) h3 h4⟩)
  choose g g1 g2 g3 using fun i : I => H3 (fun v => (i.1.1 v).1) (fun w => (i.1.2 w).1) (fun v => (i.1.1 v).2)
    (fun w => (i.1.2 w).2) i.2
  have hp : ∀ δ : GRat σ J, δ.1.1.charpoly = P.1 ↔ ∃ i, IsConj (g i) δ := fun δ => by
    refine ⟨fun h => ?_, fun ⟨i, hi⟩ => (charpoly_eq_of_isConj hi).trans (g1 i)⟩
    obtain ⟨a1, a2, a3⟩ := H1 δ h
    choose qf qf1 qf2 using a1
    choose qa qa1 qa2 using a2
    let i : I := ⟨(fun v => ⟨qf v, (qf1 v).mem⟩, fun w => ⟨qa w, (qa1 w).mem⟩), a3.mono fun v hv => (qf2 v 1 hv).symm⟩
    refine ⟨i, IsConj.symm ((H2 δ (g i) h (g1 i)).2 ⟨fun v q hq => ?_, fun w q hq => ?_⟩)⟩
    · rw [qf2 v q hq]; exact g2 i v
    · rw [qa2 w q hq]; exact g3 i w
  have hg : ∀ i j, IsConj (g i) (g j) → i = j := fun i j h => by
    obtain ⟨b1, b2⟩ := (H2 _ _ (g1 i) (g1 j)).1 h
    obtain ⟨a1, a2, -⟩ := H1 _ (g1 j)
    have e1 : ∀ v, i.1.1 v = j.1.1 v := fun v => Subtype.ext ((a1 v).unique (b1 v _ (g2 i v)) (g2 j v))
    have e2 : ∀ w, i.1.2 w = j.1.2 w := fun w => Subtype.ext ((a2 w).unique (b2 w _ (g3 i w)) (g3 j w))
    exact Subtype.ext (Prod.ext (funext e1) (funext e2))
  have hfin : {i : I | ∃ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) ≠ 0}.Finite := by
    refine finite_of_eventually_eq_one _ ?_
    filter_upwards [hae, hff.2] with v h1 h2
    rintro i ⟨x, hx⟩
    have h3 := ne_zero_of_tensor hff hx v
    rw [h2, map_mul, map_mul, map_inv] at h3
    exact h1.2.1 _ _ (g2 i v) ⟨_, by_contra fun hn => h3 (indicator_of_notMem hn _)⟩
  have hS : ∀ i ∉ hfin.toFinset, ∀ x, tensor σ J fa ff (x⁻¹ * ratEmb σ J (g i) * x) = 0 := fun i hi x =>
    by_contra fun h => hi (hfin.mem_toFinset.2 ⟨x, h⟩)
  obtain ⟨C, hC, hC'⟩ := exists_isCompact_tensor (fun w => (hfa w).2) hff
  have hker0 : ∀ x, polKernel P J (tensor σ J fa ff) x = ∑ i ∈ hfin.toFinset,
      classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff) x := fun x => by
    rw [polKernel, ← range_ratEmb]
    exact finsum_eq_sum_classKernel (ratEmb σ J) (ratEmb_injective σ J) _ g hp hg _ _ hS x
      (((GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hCM r J C hC).2 x).subset fun δ h => hC' _ h)
  have hker : descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) = fun q => ∑ i ∈ hfin.toFinset,
      descend (ratPts σ J) (classKernel (ratPts σ J) (ratEmb σ J (g i)) (tensor σ J fa ff)) q := by
    funext q
    simp only [descend, hker0]
  have hi := fun i : I => hcl (g i) (g1 i) i.1.1 i.1.2 (g2 i) (g3 i)
  rw [hker]
  refine ⟨integrable_finsetSum _ fun i _ => (hi i).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hi i).1, Finset.sum_congr rfl fun i _ => (hi i).2, mul_assoc]
  simp only [Phi]
  rw [← hsum, mul_finsum' _ _ hsupp]
  refine (finsum_eq_sum_of_support_subset _ fun i hn => ?_).symm
  by_contra h
  refine hn ((hi i).2.symm.trans ?_)
  rw [classKernel_eq_zero _ _ _ (hS i h)]
  simp only [descend, Pi.zero_apply, integral_zero]

end GlobalTheory.TrEll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCharpolyKernelEqStableOrbitalIntegralsStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_charpolyKernel_eq_stableOrbitalIntegrals : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → Integrable (descend (ratPts σ J) (polKernel P J (tensor σ J fa ff))) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf v) (ff v)) * ∏ w, Phi (J := J) (μa w) (dta w) (fa w) := by
  first | exact @GlobalTheory.TrEll.integral_polKernel | exact GlobalTheory.TrEll.integral_polKernel | (intros; apply GlobalTheory.TrEll.integral_polKernel <;> assumption)
end
end

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEllSum


open Classical in
theorem finsum_subtype_ite {G : Type} (p : G → Prop) {u : G → ℂ} (hu : (Function.support u).Finite) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ δ ∈ hu.toFinset, if p δ then u δ else 0 := by
  rw [finsum_subtype_eq_finsum_cond (f := u) (p := p), finsum_eq_sum_of_support_subset (s := hu.toFinset)]
  · exact Finset.sum_congr rfl fun δ _ => finsum_eq_if
  · intro δ hδ
    simp only [Finite.coe_toFinset]
    intro h0
    exact hδ (by simp [h0])

theorem finsum_group {G Q I : Type} (c : G → Q) (ι : I → Q) (hι : Function.Injective ι) (p : G → Prop)
    (hp : ∀ g, p g ↔ ∃ i, c g = ι i) {u : G → ℂ} (hu : (Function.support u).Finite) (S : Finset I)
    (hS : ∀ g i, u g ≠ 0 → c g = ι i → i ∈ S) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ i ∈ S, ∑ᶠ δ : {δ // c δ = ι i}, u δ.1 := by
  classical
  rw [finsum_subtype_ite p hu, Finset.sum_congr rfl fun i _ => finsum_subtype_ite (fun δ => c δ = ι i) hu,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' : u g ≠ 0 := by simpa using hg
  by_cases h : p g
  · obtain ⟨i, hi⟩ := (hp g).1 h
    rw [ite_eq_left h, Finset.sum_eq_single_of_mem i (hS g i hg' hi) fun j _ hj =>
      ite_eq_right fun e => hj (hι (e.symm.trans hi)), ite_eq_left hi]
  · rw [ite_eq_right h]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right fun e => h ((hp g).2 ⟨i, e⟩)).symm

theorem elliptic_expansion {E : Type} [Field E] [NumberField E] {F : Subfield E} [NumberField F] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {r : ℕ} {J : Matrix (Fin r) (Fin r) E}
    (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L]
    {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GAd σ J)}
    (hμ : IsRestrictedProd σ J L μa μf μ) {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (ha : ∀ w, fa w ∈ CcArch σ J w) (hf : IsFinFamily σ J L ff)
    (dta : ∀ (P : PPol σ r) (w : InfinitePlace F), Measure (Tor P w.Completion))
    (dtf : ∀ (P : PPol σ r) (v : HeightOneSpectrum (𝓞 F)), Measure (Tor P (Fv F v)))
    (dt : ∀ P : PPol σ r, Measure (Tor P (AF F))) (ht : ∀ P, IsTorusMeas P (dta P) (dtf P) (dt P))
    (K : GAd σ J → ℂ)
    (hK : K = fun x => ∑ᶠ δ : {δ : GRat σ J // Irreducible δ.1.1.charpoly}, tensor σ J fa ff (x⁻¹ * ratEmb σ J δ.1 * x))
    (t : PPol σ r → ℂ)
    (hterm : t = fun P => ((torVol P (dt P)).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf P v) (ff v)) *
      ∏ w, Phi (J := J) (μa w) (dta P w) (fa w)) :
    (∀ P, (torVol P (dt P) ≠ ⊤ ∧ (∀ v, PhiOK (J := J) (μf v) (dtf P v) (ff v)) ∧
      ∀ᶠ v in cofinite, Phi (J := J) (μf v) (dtf P v) (ff v) = 1) ∧ ∀ w, PhiOK (J := J) (μa w) (dta P w) (fa w)) ∧
    (Function.support t).Finite ∧ Integrable (descend (ratPts σ J) K) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ) ∧
      ∫ q, descend (ratPts σ J) K q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ = ∑ᶠ P, t P := by
  have ha' : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w) := fun w =>
    ⟨continuous_of_mem_ccSmooth (continuous_archCoord σ J w) (ha w), (ha w).1⟩
  have hc := (continuous_of_mem_ccAd (tensor_mem_ccAd ha hf)).2
  obtain ⟨hfin, hfinx⟩ := GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hcm r J _ hc
  have hpol := fun P => GlobalTheory.T.integral_charpolyKernel_eq_stableOrbitalIntegrals E F σ hcm hun r P J hJ L μa μf μ hμ fa ff ha' hf (dta P) (dtf P) (dt P) (ht P)
  have hinj : Function.Injective (Subtype.val : PPol σ r → E[X]) := Subtype.val_injective
  set S : Finset (PPol σ r) := (hfin.preimage (f := fun P : PPol σ r => P.1) hinj.injOn).toFinset with hSdef
  have hS : ∀ (x : GAd σ J) (γ : GRat σ J) (P : PPol σ r), tensor σ J fa ff (x⁻¹ * ratEmb σ J γ * x) ≠ 0 →
      γ.1.1.charpoly = P.1 → P ∈ S := fun x γ P h e =>
    (Finite.mem_toFinset _).2 ⟨γ, e, x, subset_tsupport _ h⟩
  have hsum : descend (ratPts σ J) K = fun q => ∑ P ∈ S, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q := by
    funext q
    rw [hK]
    refine finsum_group (fun γ : GRat σ J => γ.1.1.charpoly) _ hinj _ (fun γ => ⟨fun h => ?_, ?_⟩)
      (u := fun γ => tensor σ J fa ff ((Quotient.out q)⁻¹ * ratEmb σ J γ * Quotient.out q))
      ((hfinx (Quotient.out q)).subset fun γ h => subset_tsupport _ h) S (hS _)
    · obtain ⟨P, hP, -⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hcm r J hJ).2 γ h
      exact ⟨P, hP⟩
    · rintro ⟨P, hP⟩
      rw [hP]
      exact P.2.2.1
  have hsupp : Function.support t ⊆ S := fun P hP => by
    by_contra hn
    refine hP ?_
    rw [hterm]
    refine (hpol P).2.symm.trans (integral_eq_zero_of_ae (.of_forall fun q => ?_))
    refine finsum_eq_zero_of_forall_eq_zero fun δ => ?_
    by_contra h
    exact hn (hS _ δ.1 P h δ.2)
  refine ⟨fun P => ⟨⟨(GlobalTheory.T.unitaryTorus_compact_quotient_finite_volume F E σ hcm r P).2 _ (ht P).haar, fun v => ?_, ?_⟩, fun w => ?_⟩,
    S.finite_toSet.subset hsupp, ?_, ?_⟩
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).1 v _ _ _ (hμ.haar_loc v) ((ht P).haar_loc v) (hf.1 v).1.continuous
      (hf.1 v).2
  · have := isLattice_stdLattice (E := Fld P) (n := 1)
    filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hcm r P J hJ L, hf.2, hμ.eventually_eq_one,
      IsRestrictedProd.eventually_eq_one (ht P)] with v h1 h2 h3 h4
    have h5 := h1.2.2.2 (μf v) (dtf P v) (hμ.haar_loc v) ((ht P).haar_loc v) h3 h4
    rw [h2, Phi, finsum_eq_single _ ⟨1, h1.1⟩ fun q hq => (h5 q).2 fun e => hq (Subtype.ext e)]
    exact (h5 _).1 rfl
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).2 w _ _ _ (hμ.haar_arch w) ((ht P).haar_arch w) (ha' w).1 (ha' w).2
  · rw [hsum]
    exact integrable_finsetSum _ fun P _ => (hpol P).1
  · rw [hsum, integral_finsetSum _ fun P _ => (hpol P).1, finsum_eq_sum_of_support_subset _ hsupp, hterm]
    exact Finset.sum_congr rfl fun P _ => (hpol P).2

end GlobalTheory.TrEllSum
