module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RightTranslationActionApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.ConstNotCusp

variable (E : Type) [Field E] [NumberField E] (a r : ℕ)

theorem discreteTopology_ratN : DiscreteTopology (ratN E a r) := by
  obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
  obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hW : IsOpen (Set.pi Set.univ fun _ : BlockIx a r => V) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hVo
  convert hW.preimage (continuous_subtype_val (p := fun x => x ∈ ratN E a r)) using 1
  ext ⟨_, x, rfl⟩
  constructor
  · intro h p _
    have h1 := congrFun (congrArg Subtype.val (Set.mem_singleton_iff.1 h)) p
    exact h1.symm ▸ hV0
  · intro h
    have hx : x = 0 := funext fun p => h0 (x p) (hVU (h p trivial))
    subst hx
    exact Subtype.ext (map_zero _)

theorem exists_compact_ratN : ∃ K : Set (BlockIx a r → Ad E), IsCompact K ∧
    ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele E
  refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  choose y hy using fun p => h (x p)
  refine ⟨_, ⟨fun p => -y p, rfl⟩, fun p _ => ?_⟩
  change algebraMap E (Ad E) (-y p) + x p ∈ K
  rw [map_neg, neg_add_eq_sub]
  exact hy p

theorem not_isCuspidal_oneFn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    2 ≤ a → ¬ IsCuspidal (oneFn E a).1 := by
  intro E _ _ _ a ha h
  haveI : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : T2Space (Ad E) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  letI : MeasurableSpace (BlockIx a 1 → Ad E) := borel _
  haveI : BorelSpace (BlockIx a 1 → Ad E) := ⟨rfl⟩
  haveI := discreteTopology_ratN E a 1
  obtain ⟨K, hK, hcov⟩ := exists_compact_ratN E a 1
  obtain ⟨⟨μ, F, hμ, hF, h1⟩, -⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratN E a 1) K hK hcov
  have h2 : ∫ _ in F, (1 : ℂ) ∂μ = 0 := h 1 one_pos (by omega) μ F hμ hF 1
  simp [Measure.real, h1] at h2

end GlobalTheory.ConstNotCusp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusTensorEqModulusNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusTensorEqModulusNorm
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem modu_eq_modu_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (u : R ⊗[F] E) (k : R), IsUnit u → algebraMap R (R ⊗[F] E) k = u * sigR R σ u → IsUnit k ∧ modu (R ⊗[F] E) u = modu R k := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ u k hu hk
  obtain ⟨-, -, h2, hc⟩ := h
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hc, hc, star_star]
  have hss : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = _
      rw [hσ]
  let b : Module.Basis (Fin 2) R (R ⊗[F] E) :=
    Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E h2)
  have hku : IsUnit k := by
    have h1 : IsUnit (algebraMap R (R ⊗[F] E) k) := by
      rw [hk]; exact hu.mul (hu.map _)
    have h3 := h1.map (Algebra.norm R)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin] at h3
    exact (isUnit_pow_iff two_ne_zero).1 h3
  refine ⟨hku, ?_⟩
  letI : StarRing (R ⊗[F] E) :=
    { star := sigR R σ
      star_involutive := hss
      star_mul := fun x y => by rw [map_mul, mul_comm]
      star_add := fun x y => map_add _ x y }
  haveI : ContinuousStar (R ⊗[F] E) := ⟨GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ⟩
  rw [modu, modu, dite_eq_left hu, dite_eq_left hku]
  exact GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm R (R ⊗[F] E) b.equivFun.symm
    (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap) hu.unit hku.unit hk

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusTensorEqModulusNormStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarModulus_tensor_eq_modulus_norm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (u : R ⊗[F] E) (k : R), IsUnit u → algebraMap R (R ⊗[F] E) k = u * sigR R σ u → IsUnit k ∧ modu (R ⊗[F] E) u = modu R k := by
  first | exact @GlobalTheory.GaugeEx.modu_eq_modu_norm | exact GlobalTheory.GaugeEx.modu_eq_modu_norm | (intros; apply GlobalTheory.GaugeEx.modu_eq_modu_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep

section Coord

variable {K L : Type} [Field K] [Field L] (σ : K →+* L)

theorem exists_coords : ∃ (ι : Type) (e : ι → L) (c : ι → L →+ K), (∀ i k a, c i (σ k * a) = k * c i a) ∧
    ∀ a, ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i * σ (c i a) = a := by
  letI : Algebra K L := σ.toAlgebra
  let b := Module.Basis.ofVectorSpace K L
  refine ⟨_, b, fun i => (b.coord i).toAddMonoidHom, fun i k a => ?_, fun a => ⟨(b.repr a).support, fun T' hT => ?_⟩⟩
  · exact (b.coord i).map_smul k a
  · conv_rhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset _ hT _ (by simp)]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

variable {I : Type}

def coefMap (c : L →+ K) (p : MvPolynomial I L) : MvPolynomial I K :=
  ∑ m ∈ p.support, MvPolynomial.monomial m (c (p.coeff m))

theorem coeff_coefMap (c : L →+ K) (p : MvPolynomial I L) (m : I →₀ ℕ) : (coefMap c p).coeff m = c (p.coeff m) := by
  classical
  simp only [coefMap, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

theorem coefMap_add (c : L →+ K) (p q : MvPolynomial I L) : coefMap c (p + q) = coefMap c p + coefMap c q := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_add, map_add (f := _)]

theorem coefMap_zero (c : L →+ K) : coefMap c (0 : MvPolynomial I L) = 0 := by
  ext m
  simp only [coeff_coefMap, MvPolynomial.coeff_zero, map_zero]
  change c 0 = 0
  exact map_zero c

theorem coefMap_sum {J : Type*} (c : L →+ K) (s : Finset J) (p : J → MvPolynomial I L) :
    coefMap c (∑ j ∈ s, p j) = ∑ j ∈ s, coefMap c (p j) := by
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_coefMap, MvPolynomial.coeff_sum, map_sum]

variable {σ}

theorem coefMap_smul_map {c : L →+ K} (hc : ∀ k a, c (σ k * a) = k * c a) (a : L) (p : MvPolynomial I K) :
    coefMap c (a • MvPolynomial.map σ p) = c a • p := by
  ext m
  rw [coeff_coefMap, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, smul_eq_mul,
    mul_comm, hc, mul_comm]

theorem coefMap_smul {c : L →+ K} (hc : ∀ k a, c (σ k * a) = k * c a) (k : K) (p : MvPolynomial I L) :
    coefMap c (σ k • p) = k • coefMap c p := by
  ext m
  rw [coeff_coefMap, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, coeff_coefMap, smul_eq_mul, smul_eq_mul, hc]

theorem exists_sum_coefMap {ι : Type} {e : ι → L} {c : ι → L →+ K}
    (h : ∀ a, ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i * σ (c i a) = a) (p : MvPolynomial I L) :
    ∃ T : Finset ι, ∀ T' : Finset ι, T ⊆ T' → ∑ i ∈ T', e i • MvPolynomial.map σ (coefMap (c i) p) = p := by
  classical
  choose T hT using h
  refine ⟨p.support.biUnion fun m => T (p.coeff m), fun T' hT' => ?_⟩
  ext m
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, coeff_coefMap, smul_eq_mul]
  by_cases hm : m ∈ p.support
  · exact hT _ _ ((Finset.subset_biUnion_of_mem (fun m => T (p.coeff m)) hm).trans hT')
  · simp [MvPolynomial.notMem_support_iff.1 hm]

variable (σ)

theorem linearIndependent_map_pi {D J : Type*} {f : J → D → MvPolynomial I K} (hf : LinearIndependent K f) :
    LinearIndependent L fun j d => MvPolynomial.map σ (f j d) := by
  obtain ⟨ι, e, c, hc, h⟩ := exists_coords σ
  rw [linearIndependent_iff'] at hf ⊢
  intro s g hg j hj
  have h0 : ∀ i, c i (g j) = 0 := fun i => by
    refine hf s (fun j => c i (g j)) (funext fun d => ?_) j hj
    have h1 := congrArg (coefMap (c i)) (congrFun hg d)
    rw [Finset.sum_apply, coefMap_sum, Pi.zero_apply, coefMap_zero] at h1
    rw [Finset.sum_apply, Pi.zero_apply, ← h1]
    exact Finset.sum_congr rfl fun k _ => (coefMap_smul_map (hc i) _ _).symm
  obtain ⟨T, hT⟩ := h (g j)
  rw [← hT T le_rfl]
  simp [h0]

theorem VV_induction {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {P : Pol L ι n → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (a : L) (v : VV K lam), P (a • MvPolynomial.map σ v.1))
    (x : Pol L ι n) (hx : x ∈ VV L lam) : P x := by
  have e : x = ∑ i, (bVV L lam).repr ⟨x, hx⟩ i • bVVfun L lam i := by
    conv_lhs => rw [show x = ((⟨x, hx⟩ : VV L lam) : Pol L ι n) from rfl, ← (bVV L lam).sum_repr ⟨x, hx⟩]
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe]
  rw [e]
  refine Finset.sum_induction _ P hadd h0 fun i _ => ?_
  obtain ⟨F, hF, hF'⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc σ lam i
  rw [hF']
  exact hs _ ⟨F, hF⟩

variable {σ}

theorem coefMap_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {c : L →+ K}
    (hc : ∀ k a, c (σ k * a) = k * c a) (x : Pol L ι n) (hx : x ∈ VV L lam) : coefMap c x ∈ VV K lam := by
  refine VV_induction σ lam (P := fun x => coefMap c x ∈ VV K lam) ?_ (fun x y hx hy => ?_) (fun a v => ?_) x hx
  · rw [coefMap_zero]; exact zero_mem _
  · rw [coefMap_add]; exact add_mem hx hy
  · rw [coefMap_smul_map hc]; exact Submodule.smul_mem _ _ v.2

end Coord

section CForms

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n)

theorem coefMap_rhoC {c : ℂ →+ X.K} (hc : ∀ k a, c (σ k * a) = k * c a) (γ : UF X.E n) (x : Pol ℂ X.Tau n)
    (hx : x ∈ VV ℂ lam) :
    coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) ⟨coefMap c x, coefMap_mem_VV lam hc x hx⟩).1 := by
  have h : ∃ y : VV X.K lam, y.1 = coefMap c x ∧ coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) y).1 := by
    refine VV_induction σ lam (P := fun x => ∃ y : VV X.K lam, y.1 = coefMap c x ∧
      coefMap c (rhoC σ lam γ x) = (rhoV X.emb lam (ufGL X.E n γ) y).1) ⟨0, (coefMap_zero c).symm, ?_⟩ ?_ ?_ x hx
    · rw [map_zero, coefMap_zero, map_zero]
      rfl
    · rintro x y ⟨u, hu, hu'⟩ ⟨v, hv, hv'⟩
      refine ⟨u + v, by rw [coefMap_add, ← hu, ← hv]; rfl, ?_⟩
      rw [map_add (f := _), coefMap_add, hu', hv', map_add (f := _)]
      rfl
    · intro a v
      refine ⟨c a • v, (coefMap_smul_map hc a v.1).symm, ?_⟩
      rw [map_smul, rhoC_map, coefMap_smul_map hc, map_smul]
      rfl
  obtain ⟨y, hy, h⟩ := h
  rw [h]
  exact congrArg (fun z => (rhoV X.emb lam (ufGL X.E n γ) z).1) (Subtype.ext hy)

variable (L : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)

def coordForm {c : ℂ →+ X.K} (hc : ∀ k a, c (σ k * a) = k * c a) (F : cForms ST σ lam Λ) :
    (formGSD (squarePk X lam L) Λ).EqFun :=
  ⟨fun d => ⟨coefMap c (F.1 d), coefMap_mem_VV lam hc _ (F.2 d).1⟩, fun g d => Subtype.ext <| by
    refine (congrArg (coefMap c) ((F.2 d).2 g)).trans ?_
    rw [coefMap_smul hc, coefMap_rhoC σ lam hc _ _ (F.2 d).1]
    rfl⟩

theorem toCForm_linearIndependent {J : Type*} {φ : J → (formGSD (squarePk X lam L) Λ).EqFun} (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun j => toCForm σ lam L Λ (φ j) := by
  refine LinearIndependent.of_comp (cForms ST σ lam Λ).subtype ?_
  let i : (formGSD (squarePk X lam L) Λ).EqFun →ₗ[X.K] (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → Pol X.K X.Tau n) :=
    { toFun := fun φ d => (φ.1 d).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hi : Function.Injective i := fun _ _ e => Subtype.ext (funext fun d => Subtype.ext (congrFun e d))
  exact linearIndependent_map_pi σ (h.map' i (LinearMap.ker_eq_bot.2 hi))

theorem exists_finite_determining (hX : X.Ok) : ∃ s : Set (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)), s.Finite ∧
    ∀ F : cForms ST σ lam Λ, (∀ d ∈ s, F.1 d = 0) → F = 0 := by
  obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
  refine ⟨s, hs, fun F hF => Subtype.ext (funext fun d => ?_)⟩
  obtain ⟨d0, hd0, g, rfl⟩ := hrep d
  have h := ((mem_cForms σ lam Λ F.1).1 F.2 d0).2 g 1
  rw [hF d0 hd0, map_zero, smul_zero] at h
  exact h

theorem toCForm_span (hX : X.Ok) : Submodule.span ℂ (Set.range (toCForm σ lam L Λ)) = ⊤ := by
  classical
  obtain ⟨ι, e, c, hc, h⟩ := exists_coords σ
  obtain ⟨s, hs, hdet⟩ := exists_finite_determining (ST := ST) σ lam Λ hX
  refine eq_top_iff.2 fun F _ => ?_
  choose T hT using fun d => exists_sum_coefMap h (F.1 d)
  have e1 : F = ∑ i ∈ hs.toFinset.biUnion T, e i • toCForm σ lam L Λ (coordForm σ lam L Λ (hc i) F) := by
    refine sub_eq_zero.1 (hdet _ fun d hd => ?_)
    rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sum, Finset.sum_apply, sub_eq_zero]
    exact (hT d _ (Finset.subset_biUnion_of_mem T (hs.mem_toFinset.2 hd))).symm
  rw [e1]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem toCForm_span_of_span (hX : X.Ok) {J : Type*} {φ : J → (formGSD (squarePk X lam L) Λ).EqFun}
    (h : Submodule.span X.K (Set.range φ) = ⊤) : Submodule.span ℂ (Set.range fun j => toCForm σ lam L Λ (φ j)) = ⊤ := by
  refine eq_top_iff.2 ((toCForm_span σ lam L Λ hX).ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨ψ, rfl⟩
  have hψ : ψ ∈ Submodule.span X.K (Set.range φ) := h ▸ trivial
  induction hψ using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end CForms

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)

theorem toMtilde_linearIndependent {J : Type*} {φ : J → MtildeV W Ch sel mu P} (h : LinearIndependent X.K φ) :
    LinearIndependent ℂ fun j => toMtP W Ch sel mu P σ (φ j) := toCForm_linearIndependent σ W.sgTrue _ _ h

theorem toMtilde_span (hX : X.Ok) : Submodule.span ℂ (Set.range (toMtP W Ch sel mu P σ)) = ⊤ := toCForm_span σ W.sgTrue _ _ hX

end Rows

end GlobalTheory.Mem.Col2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSection
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSection
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.OrbitSection

theorem exists_section_real {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (C : Set ℝ) [CompactSpace C] (c₀ : C) (f : C → X) (hf : Continuous f) :
    ∃ τ : X → C, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  have h : ∀ y : X, ∃ c : C, (y ∈ Set.range f → f c = y ∧ ∀ c', f c' = y → (c : ℝ) ≤ c') ∧
      (y ∉ Set.range f → c = c₀) := by
    intro y
    by_cases hy : y ∈ Set.range f
    · have hc : IsCompact (f ⁻¹' {y}) := (isClosed_singleton.preimage hf).isCompact
      obtain ⟨c, hc1, hc2⟩ := hc.exists_isMinOn (f := fun c : C => (c : ℝ)) hy
        continuous_subtype_val.continuousOn
      exact ⟨c, fun _ => ⟨hc1, fun c' h' => hc2 h'⟩, fun h => absurd hy h⟩
    · exact ⟨c₀, fun h => absurd h hy, fun _ => rfl⟩
  choose τ h1 h2 using h
  refine ⟨τ, ?_, fun y hy => (h1 y hy).1⟩
  have hm : Measurable fun y => (τ y : ℝ) := by
    refine measurable_of_Iic fun a => ?_
    have he : (fun y => (τ y : ℝ)) ⁻¹' Set.Iic a =
        f '' {c : C | (c : ℝ) ≤ a} ∪ ((Set.range f)ᶜ ∩ {_y | (c₀ : ℝ) ≤ a}) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_setOf_eq]
      by_cases hy : y ∈ Set.range f
      · constructor
        · intro h
          exact Or.inl ⟨τ y, h, (h1 y hy).1⟩
        · rintro (⟨c, hc, hcy⟩ | h)
          · exact ((h1 y hy).2 c hcy).trans hc
          · exact absurd hy h.1
      · rw [h2 y hy]
        constructor
        · intro h
          exact Or.inr ⟨hy, h⟩
        · rintro (⟨c, -, hcy⟩ | h)
          · exact absurd ⟨c, hcy⟩ hy
          · exact h.2
    rw [he]
    refine MeasurableSet.union ?_ (MeasurableSet.inter ?_ (MeasurableSet.const _))
    · exact ((isClosed_le continuous_subtype_val continuous_const).isCompact.image
        hf).isClosed.measurableSet
    · exact (isCompact_range hf).isClosed.measurableSet.compl
  exact hm.subtype_mk (h := fun y => (τ y).2)

theorem exists_section_compact {K X : Type} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (f : K → X) (hf : Continuous f) :
    ∃ τ : X → K, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  letI := TopologicalSpace.metrizableSpaceMetric K
  obtain ⟨p, hp, hps⟩ := exists_nat_bool_continuous_surjective_of_compact K
  have : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  let q : cantorSet → K := p ∘ cantorSetHomeomorphNatToBool
  have hq : Continuous q := hp.comp cantorSetHomeomorphNatToBool.continuous
  have hqs : Function.Surjective q := hps.comp cantorSetHomeomorphNatToBool.surjective
  obtain ⟨τ, h1, h2⟩ := exists_section_real cantorSet ⟨0, zero_mem_cantorSet⟩ (f ∘ q)
    (hf.comp hq)
  refine ⟨q ∘ τ, hq.measurable.comp h1, fun y hy => h2 y ?_⟩
  rwa [hqs.range_comp]

theorem measurableSet_orbit_and_exists_section : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), MeasurableSet {y : X | ∃ g : G, g • x₀ = y} ∧ ∃ s : X → G, Measurable s ∧ ∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀
  classical
  have hπ : Continuous fun g : G => g • x₀ := by fun_prop
  let K : ℕ → Set G := fun n => insert 1 (compactCovering G n)
  have hK : ∀ n, IsCompact (K n) := fun n => (isCompact_compactCovering G n).insert 1
  have hKU : ∀ g : G, ∃ n, g ∈ K n := fun g => by
    obtain ⟨n, hn⟩ := exists_mem_compactCovering g
    exact ⟨n, Or.inr hn⟩
  let A : ℕ → Set X := fun n => (fun g : G => g • x₀) '' K n
  have hA : ∀ n, MeasurableSet (A n) := fun n => ((hK n).image hπ).isClosed.measurableSet
  have hO : MeasurableSet {y : X | ∃ g : G, g • x₀ = y} := by
    have : {y : X | ∃ g : G, g • x₀ = y} = ⋃ n, A n := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨g, hg⟩
        obtain ⟨n, hn⟩ := hKU g
        exact ⟨n, g, hn, hg⟩
      · rintro ⟨n, g, -, hg⟩
        exact ⟨g, hg⟩
    rw [this]
    exact MeasurableSet.iUnion hA
  have hs : ∀ n, ∃ s : X → G, Measurable s ∧ ∀ y ∈ A n, s y • x₀ = y := by
    intro n
    have : CompactSpace (K n) := isCompact_iff_compactSpace.1 (hK n)
    have : Nonempty (K n) := ⟨⟨1, Or.inl rfl⟩⟩
    obtain ⟨τ, h1, h2⟩ := exists_section_compact (fun g : K n => (g : G) • x₀)
      (hπ.comp continuous_subtype_val)
    refine ⟨fun y => τ y, measurable_subtype_coe.comp h1, ?_⟩
    rintro y ⟨g, hg, hgy⟩
    exact h2 y ⟨⟨g, hg⟩, hgy⟩
  choose s hs1 hs2 using hs
  have hex : ∀ y : X, ∃ n, (y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) := by
    intro y
    by_cases hy : ∃ g : G, g • x₀ = y
    · obtain ⟨g, hg⟩ := hy
      obtain ⟨n, hn⟩ := hKU g
      exact ⟨n, Or.inl ⟨g, hn, hg⟩⟩
    · exact ⟨0, Or.inr hy⟩
  refine ⟨hO, fun y => s (Nat.find (hex y)) y, ?_, fun y hy => ?_⟩
  · exact Measurable.find (p := fun n y => y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) hs1 (fun n => (hA n).union hO.compl) hex
  · exact hs2 _ y ((Nat.find_spec (hex y)).resolve_right (not_not.2 hy))

end GlobalTheory.OrbitSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableSetOrbitExistsMeasurableSectionStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_orbit_exists_measurable_section : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), MeasurableSet {y : X | ∃ g : G, g • x₀ = y} ∧ ∃ s : X → G, Measurable s ∧ ∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y := by
  first | exact @GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section | exact GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section | (intros; apply GlobalTheory.OrbitSection.measurableSet_orbit_and_exists_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitary
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.InfGroup

section General

variable {S : Type} [CommRing S] {I : Type} {M : ℕ}

def lift (e : S ≃+* (I → ℂ)) (m : I → Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) S :=
  Matrix.of fun a b => e.symm fun i => m i a b

variable {e : S ≃+* (I → ℂ)} {θ : I → (S →+* ℂ)}

theorem lift_map (he : ∀ x i, e x i = θ i x) (m : I → Matrix (Fin M) (Fin M) ℂ) (i : I) :
    (lift e m).map (θ i) = m i := by
  ext a b
  simp [lift, ← he]

theorem ext_map (he : ∀ x i, e x i = θ i x) {X Y : Matrix (Fin M) (Fin M) S}
    (h : ∀ i, X.map (θ i) = Y.map (θ i)) : X = Y := by
  ext a b
  apply e.injective
  funext i
  rw [he, he]
  exact congrFun (congrFun (h i) a) b

theorem cT_map {s : S →+* S} {t : S →+* ℂ} (hs : ∀ x, t (s x) = star (t x))
    (X : Matrix (Fin M) (Fin M) S) : (Formalism.UG.cT s X).map t = (X.map t)ᴴ := by
  ext a b
  simp [Formalism.UG.cT, hs]

theorem conj_mul {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X Y : Matrix n n ℂ) :
    A * X * B * (A * Y * B) = A * (X * Y) * B := by
  calc A * X * B * (A * Y * B) = A * X * (B * A) * Y * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.mul_one]

theorem conj_conj {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X : Matrix n n ℂ) :
    B * (A * X * B) * A = X := by
  calc B * (A * X * B) * A = (B * A) * X * (B * A) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp

theorem conj_unitary {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) {G X : Matrix n n ℂ} {K : Matrix m m ℂ}
    (hK : Bᴴ * G * B = K) (hX : Xᴴ * G * X = G) :
    (A * X * B)ᴴ * K * (A * X * B) = K := by
  rw [← hK]
  calc (A * X * B)ᴴ * (Bᴴ * G * B) * (A * X * B)
      = Bᴴ * (Xᴴ * ((B * A)ᴴ * G * (B * A)) * X) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hBA, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]

theorem exists_equiv [TopologicalSpace S] (he : ∀ x i, e x i = θ i x) (hc : Continuous e)
    (hc' : Continuous e.symm) (s : S →+* S) (hs : ∀ x i, θ i (s x) = star (θ i x))
    (J : Matrix (Fin M) (Fin M) S) (P Q : I → ℕ)
    (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ)
    (B : ∀ i, Matrix (Fin M) (Fin (P i) ⊕ Fin (Q i)) ℂ)
    (hAB : ∀ i, A i * B i = 1) (hBA : ∀ i, B i * A i = 1)
    (hA : ∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (θ i)) :
    ∃ f : Formalism.UG.UJ s J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (f h i) * A i =
      A i * ((h.1 : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).map (θ i) := by
  have hB : ∀ i, (B i)ᴴ * J.map (θ i) * B i = Formalism.UG.Jpq (P i) (Q i) := by
    intro i
    rw [← hA]
    calc (B i)ᴴ * ((A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i) * B i
        = (A i * B i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * (A i * B i) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAB]; simp
  have hone : ∀ i, (1 : Matrix (Fin M) (Fin M) S).map (θ i) = 1 := fun i =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hθ : ∀ i, Continuous (θ i) := fun i => by
    have : (θ i : S → ℂ) = fun x => e x i := funext fun x => (he x i).symm
    rw [this]
    exact (continuous_apply i).comp hc
  have hfw : ∀ (h : Formalism.UG.UJ s J) (i : I), ∃ g : UpqT (P i) (Q i),
      UpqT.mat g = A i * h.1.1.map (θ i) * B i := by
    intro h i
    have hh : Formalism.UG.cT s h.1.1 * J * h.1.1 = J := h.2
    have h2 := congrArg (fun X => Matrix.map X (θ i)) hh
    simp only [Matrix.map_mul, cT_map (fun x => hs x i)] at h2
    have : A i * h.1.1.map (θ i) * B i ∈ Set.range (UpqT.mat (P := P i) (Q := Q i)) := by
      rw [GlobalTheory.UpqTopology.range_mat]
      exact conj_unitary (hBA i) (hB i) h2
    exact this
  choose fw hfw using hfw
  have hmul : ∀ {p q : ℕ} (a b : UpqT p q), UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b :=
    fun _ _ => rfl
  have hm1 : ∀ {p q : ℕ}, UpqT.mat (1 : UpqT p q) = 1 := rfl
  have hinj : ∀ (p q : ℕ), Function.Injective (UpqT.mat (P := p) (Q := q)) :=
    fun _ _ => GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
  let L : (∀ i, UpqT (P i) (Q i)) → Matrix (Fin M) (Fin M) S :=
    fun g => lift e fun i => B i * UpqT.mat (g i) * A i
  have hL : ∀ g i, (L g).map (θ i) = B i * UpqT.mat (g i) * A i := fun g i => lift_map he _ i
  have hLmul : ∀ g g', L g * L g' = L (g * g') := by
    intro g g'
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, hL, hL, hL, conj_mul (hAB i), Pi.mul_apply, hmul]
  have hL1 : L 1 = 1 := by
    refine ext_map he fun i => ?_
    rw [hL, Pi.one_apply, hm1, Matrix.mul_one, hBA, hone]
  have hLu : ∀ g, Formalism.UG.cT s (L g) * J * L g = J := by
    intro g
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (fun x => hs x i), hL]
    exact conj_unitary (hAB i) (hA i) (GlobalTheory.UpqTopology.mat_unitary (g i))
  have hLc : Continuous L := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine hc'.comp (continuous_pi fun i => ?_)
    have : Continuous fun g : ∀ i, UpqT (P i) (Q i) => B i * UpqT.mat (g i) * A i :=
      (continuous_const.matrix_mul
        (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_apply i))).matrix_mul continuous_const
    exact this.matrix_elem a b
  let bw : (∀ i, UpqT (P i) (Q i)) → Formalism.UG.UJ s J := fun g =>
    ⟨⟨L g, L g⁻¹, by rw [hLmul, mul_inv_cancel, hL1], by rw [hLmul, inv_mul_cancel, hL1]⟩, hLu g⟩
  haveI : ∀ i, IsTopologicalGroup (UpqT (P i) (Q i)) := fun i => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  refine ⟨
    { toFun := fw
      invFun := bw
      left_inv := fun h => ?_
      right_inv := fun g => ?_
      map_mul' := fun h h' => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun h i => ?_⟩
  · refine Subtype.ext (Units.ext (ext_map he fun i => ?_))
    change (L (fw h)).map (θ i) = _
    rw [hL, hfw, conj_conj (hBA i)]
  · funext i
    apply hinj
    rw [hfw]
    change A i * (L g).map (θ i) * B i = _
    rw [hL, conj_conj (hAB i)]
  · funext i
    apply hinj
    rw [Pi.mul_apply, hmul, hfw, hfw, hfw, conj_mul (hBA i), ← Matrix.map_mul]
    rfl
  · refine continuous_pi fun i => GlobalTheory.UpqTopology.isInducing_mat.continuous_iff.2 ?_
    have : (UpqT.mat ∘ fun h => fw h i) = fun h : Formalism.UG.UJ s J => A i * h.1.1.map (θ i) * B i :=
      funext fun h => hfw h i
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.comp continuous_subtype_val).matrix_map
      (hθ i))).matrix_mul continuous_const
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hLc, hLc.comp continuous_inv⟩) _
  · change UpqT.mat (fw h i) * A i = _
    rw [hfw, Matrix.mul_assoc, hBA, Matrix.mul_one]

end General

theorem real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)) (P Q : I → ℕ) (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → (∀ i, Formalism.UG.HasSignature (J.map (τ i)) (P i) (Q i)) → (∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (τ i)) → ∃ e : HA (Ainf F) σ J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (e h i) * A i = A i * ((HA.mat (Ainf F) σ J h : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) := by
  intro F E _ _ _ _ _ σ M J I _ τ θ P Q A hcm hfam hθ hsig hA
  obtain ⟨e, he, hc, hc', hs⟩ := GlobalTheory.T.exists_archAdeleTensor_equiv_complex_cmType F E σ I τ θ hcm hfam hθ
  choose B hAB hBA using fun i =>
    (GlobalTheory.Mem.SignatureFactor.exists_factor M (P i) (Q i) _ (hsig i)).2.2 (A i) (hA i)
  refine exists_equiv he hc hc' (sigR (Ainf F) σ) (fun x i => by rw [← he, ← he, hs])
    (JR (Ainf F) J) P Q A B hAB hBA fun i => ?_
  rw [hA]
  ext a b
  exact ((hθ i).1 (J a b)).symm

end GlobalTheory.Mem.InfGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitaryStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_realPoints_equiv_pi_indefiniteUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)) (P Q : I → ℕ) (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → (∀ i, Formalism.UG.HasSignature (J.map (τ i)) (P i) (Q i)) → (∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (τ i)) → ∃ e : HA (Ainf F) σ J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (e h i) * A i = A i * ((HA.mat (Ainf F) σ J h : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) := by
  first | exact @GlobalTheory.Mem.InfGroup.real_points | exact GlobalTheory.Mem.InfGroup.real_points | (intros; apply GlobalTheory.Mem.InfGroup.real_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupPointsEquivOfChangeOfBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupPointsEquivOfChangeOfBasis
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeFrameBasis

open GlobalTheory.VolTransport

theorem eq_conj {A : Type} [CommRing A] {M : ℕ} {T T' x y : Matrix (Fin M) (Fin M) A}
    (h : T * T' = 1) (k : x * T' = T' * y) : y = T * x * T' := by
  rw [Matrix.mul_assoc, k, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem conj_rel {A : Type} [CommRing A] {M : ℕ} {T T' : Matrix (Fin M) (Fin M) A}
    (h : T' * T = 1) (x : Matrix (Fin M) (Fin M) A) : x * T' = T' * (T * x * T') := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem frame_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → (∃! e : HA R σ J ≃* HA R σ J', ∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ ∀ e : HA R σ J ≃* HA R σ J', (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ M J J' P hJ
  have h0 : IsoPair (σ : E →+* E) J J' ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)
      (P : Matrix (Fin M) (Fin M) E) := by
    refine ⟨Units.inv_mul P, Units.mul_inv P, ?_, hJ.symm⟩
    rw [hJ]
    calc _ = Formalism.UG.cT (σ : E →+* E) ((P : Matrix (Fin M) (Fin M) E) * ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) * J *
          ((P : Matrix (Fin M) (Fin M) E) * ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  have h : IsoPair (sigR R σ) (JR R J) (JR R J')
      (((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R))
      ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)) :=
    h0.map (inclR (F := F) R) (fun _ => rfl)
  let e0 : HA R σ J ≃* HA R σ J' := conjE h
  have hm : ∀ g, ((HA.mat R σ J' (e0 g) : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) *
        ((HA.mat R σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
        (P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) := fun _ => rfl
  have hu : ∀ e : HA R σ J ≃* HA R σ J',
      (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → e = e0 := by
    intro e he
    ext g
    apply Subtype.ext
    apply Units.ext
    refine Eq.trans ?_ (hm g).symm
    exact eq_conj h.1 (he g)
  refine ⟨⟨e0, fun g => ?_, hu⟩, fun e he => ?_⟩
  · exact conj_rel h.2.1 _
  · rw [hu e he]
    have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    exact ⟨conjU_continuous h, conjU_continuous h.symm⟩

end GlobalTheory.GaugeFrameBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupPointsEquivOfChangeOfBasisStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → (∃! e : HA R σ J ≃* HA R σ J', ∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ ∀ e : HA R σ J ≃* HA R σ J', (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → Continuous e ∧ Continuous e.symm := by
  first | exact @GlobalTheory.GaugeFrameBasis.frame_basis | exact GlobalTheory.GaugeFrameBasis.frame_basis | (intros; apply GlobalTheory.GaugeFrameBasis.frame_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureSmulFactorsEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureSmulFactorsEqSmul
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdScale

theorem finite_mulSupport_sub {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (p : ι → Prop) : (Function.mulSupport fun v : {v // p v} => (r v.1 : ℝ)).Finite := by
  refine (hr.preimage (f := (Subtype.val : {v // p v} → ι)) Subtype.val_injective.injOn).subset ?_
  intro v hv h
  exact hv (by simp [h])

theorem summable_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) : Summable fun v => |r v * f v - 1| := by
  refine hf.congr_cofinite ?_
  filter_upwards [hr.compl_mem_cofinite] with v hv
  have : r v = 1 := by simpa using hv
  simp [this]

theorem finprod_eq {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ((∏ᶠ v, r v : ℝ≥0) : ℝ) = (∏ v ∈ S, (r v : ℝ)) * ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : (Function.mulSupport fun v => (r v : ℝ)).Finite :=
    hr.subset fun v hv h => hv (by simp [h])
  have h1 : ((∏ᶠ v, r v : ℝ≥0) : ℝ) = ∏ᶠ v, (r v : ℝ) :=
    NNReal.toRealHom.toMonoidHom.map_finprod hr
  rw [h1, ← tprod_eq_finprod (L := SummationFilter.unconditional ι) h0, ← Finset.tprod_subtype' S (fun v => (r v : ℝ))]
  exact (Multipliable.tprod_mul_tprod_compl (f := fun v => (r v : ℝ)) (s := (S : Set ι))
    (multipliable_of_hasFiniteMulSupport (finite_mulSupport_sub r hr _))
    (multipliable_of_hasFiniteMulSupport (finite_mulSupport_sub r hr _))).symm

theorem tprod_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ∏' v : {v // v ∉ S}, ((r v.1 : ℝ) * f v.1) =
      (∏' v : {v // v ∉ S}, (r v.1 : ℝ)) * ∏' v : {v // v ∉ S}, f v.1 := by
  refine Multipliable.tprod_mul
    (multipliable_of_hasFiniteMulSupport (finite_mulSupport_sub r hr _)) ?_
  have h := multipliable_one_add_of_summable (f := fun v : {v // v ∉ S} => f v.1 - 1)
    (hf.subtype (fun v => v ∉ S))
  simpa using h

theorem finprod_ennreal {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (S : Finset ι) :
    ∃ c : ℝ≥0, (∏ᶠ v, r v) = (∏ v ∈ S, r v) * c ∧ (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
    rw [tprod_eq_finprod (finite_mulSupport_sub r hr _)]
    exact finprod_nonneg fun v => (r v.1).2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := ⟨⟨_, h0⟩, rfl⟩
  refine ⟨c, ?_, hc⟩
  apply NNReal.coe_injective
  rw [finprod_eq r hr S, ← hc]
  simp

theorem isProd_smul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ri : ℝ≥0)
    (r : HeightOneSpectrum (𝓞 F) → ℝ≥0) (h : IsProd b ν mi mv)
    (hr : (Function.mulSupport r).Finite) :
    IsProd b ((ri * ∏ᶠ v, r v) • ν) (ri • mi) (fun v => r v • mv v) := by
  obtain ⟨⟨hi, hv, hs⟩, hf⟩ := h
  have key : ∀ v, ((r v • mv v) (latV b v)).toReal = r v * (mv v (latV b v)).toReal := by
    intro v
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  refine ⟨⟨inferInstance, fun v => inferInstance, ?_⟩, ?_⟩
  · simp only [key]
    exact summable_scale _ r hs hr
  · intro S fi fv hfi hfv
    obtain ⟨c, hc, hc'⟩ := finprod_ennreal r hr S
    have ht : tailProd b (fun v => r v • mv v) S = c * tailProd b mv S := by
      unfold tailProd
      simp only [key]
      rw [tprod_scale (fun v => (mv v (latV b v)).toReal) r hs hr S, ← hc',
        ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    rw [Measure.restrict_smul, lintegral_smul_measure, hf S fi fv hfi hfv, ht, hc]
    simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
    push_cast
    ring

end GlobalTheory.GaugeEx.ProdScale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureSmulFactorsEqSmulStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ri : ℝ≥0) (r : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsProd b ν mi mv → (Function.mulSupport r).Finite → IsProd b ((ri * ∏ᶠ v, r v) • ν) (ri • mi) (fun v => r v • mv v) := by
  first | exact @GlobalTheory.GaugeEx.ProdScale.isProd_smul | exact GlobalTheory.GaugeEx.ProdScale.isProd_smul | (intros; apply GlobalTheory.GaugeEx.ProdScale.isProd_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowZeroMulRightIff
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Datum
open scoped Matrix

namespace GlobalTheory.TwistDatumRight

section
variable {κ : Type} [CommRing κ] {b r : ℕ}

theorem topL_mul_right (y : Matrix (Fin b) (Fin r) κ) (h : Matrix (Fin r) (Fin r) κ) :
    topL r (y * h) = topL r y * h := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, hi, Matrix.mul_apply]
  · simp [topL, hi, Matrix.mul_apply]

theorem lowZero_mul_right {y : Matrix (Fin b) (Fin r) κ} (hy : LowZero r y) (h : Matrix (Fin r) (Fin r) κ) :
    LowZero r (y * h) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => by rw [hy i k hi k.2, zero_mul]

theorem lowZero_mul_right_iff (y : Matrix (Fin b) (Fin r) κ) (h : GL (Fin r) κ) :
    LowZero r (y * h.1) ↔ LowZero r y := by
  refine ⟨fun H => ?_, fun H => lowZero_mul_right H _⟩
  have := lowZero_mul_right H (h⁻¹).1
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this

theorem det_topL_mul_right (y : Matrix (Fin b) (Fin r) κ) (h : GL (Fin r) κ) :
    (topL r (y * h.1)).det = ((Matrix.GeneralLinearGroup.det h : κˣ) : κ) * (topL r y).det := by
  rw [topL_mul_right, Matrix.det_mul, mul_comm, Matrix.GeneralLinearGroup.val_det_apply]

end

theorem omegaQ_mul_right : ∀ (D : D7) (b r : ℕ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (h : ∀ PP : Pl D.host.E, GL (Fin r) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin r) (kP PP)), (∀ PP ∈ Q, y' PP = y PP * (h PP).1) → omegaQ Q r ξ (-1) y' = ((∏ PP ∈ Q, ξ PP (Matrix.GeneralLinearGroup.det (h PP)) : ℂˣ) : ℂ)⁻¹ * omegaQ Q r ξ (-1) y := by
  intro D b r Q ξ h y y' hy
  have hiff : (∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det) ↔
      (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) := by
    refine forall₂_congr fun PP hP => ?_
    rw [hy PP hP, lowZero_mul_right_iff, det_topL_mul_right, Units.isUnit_units_mul]
  unfold omegaQ
  by_cases c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dite_eq_left c, dite_eq_left (hiff.2 c), ← Finset.prod_attach Q, Units.coe_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : ((hiff.2 c) PP.1 PP.2).2.unit =
        Matrix.GeneralLinearGroup.det (h PP.1) * (c PP.1 PP.2).2.unit := by
      apply Units.ext
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hy PP.1 PP.2, det_topL_mul_right]
    rw [e, map_mul, Units.val_mul, zpow_neg_one, zpow_neg_one, mul_inv]
  · rw [dite_eq_right c, dite_eq_right (fun h' => c (hiff.1 h')), mul_zero]

end GlobalTheory.TwistDatumRight
end
