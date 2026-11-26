module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionExteriorProductAssocComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecomp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.TypeLeaf.iotaOQ_continuous_injective (D : _root_.Formalism.BasicNotions.D7) (i : D.nd.Loc) :
    Continuous (_root_.Formalism.MainNotions.N.iotaOQ D.nd D.naut i) ∧ Function.Injective (_root_.Formalism.MainNotions.N.iotaOQ D.nd D.naut i) := by
  refine ⟨_root_.GlobalTheory.CoeffEmbedding.continuous_iotaOQ _ _ _ D.nd D.naut i, ?_⟩
  unfold _root_.Formalism.MainNotions.N.iotaOQ
  exact (D.naut.iotaQ i).injective.comp (IsFractionRing.injective _ _)

end GlobalTheory.TypeLeaf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.BurnsideField

open scoped MonoidAlgebra

theorem span_range_eq_top_of_isAlgClosed {G K V : Type} [Group G] [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V)
    (h : τ.IsIrreducible) : Submodule.span K (Set.range τ) = ⊤ := by
  classical
  have hscal : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := K[G]) (V := τ.asModule) K).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  have hsurj : Function.Surjective τ.asAlgebraHom := by
    intro f
    let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
      { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
        map_add' := fun x y => by simp
        map_smul' := fun φ m => by
          obtain ⟨c, hc⟩ := hscal φ
          simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F
      (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
    refine ⟨r, b.ext fun i => ?_⟩
    have := congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    exact this.symm
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨r, rfl⟩ := hsurj f
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | single g c =>
    rw [Representation.asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

theorem span_mat_eq_top_of_isIrrSub {Γ K : Type} [Group Γ] [Field K] [IsAlgClosed K] {r : ℕ}
    (σ : Γ →* GL (Fin r) K) (h : IsIrrSub σ ⊤) : Submodule.span K (Set.range (mat σ)) = ⊤ := by
  classical
  let τ : Representation K Γ (Fin r → K) :=
    { toFun := fun g => Matrix.toLin' (mat σ g)
      map_one' := by simp [mat]; rfl
      map_mul' := fun g g' => by simp [mat, Matrix.toLin'_mul]; rfl }
  have hτ : ∀ g v, τ g v = (mat σ g).mulVec v := fun g v => Matrix.toLin'_apply _ _
  have hirr : τ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation τ) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      exact (congrArg Subrepresentation.toSubmodule hbt).symm
    refine ⟨fun W => ?_⟩
    rcases h.2.2 W.toSubmodule le_top (fun g v hv => by
      have := W.apply_mem_toSubmodule g hv
      rwa [hτ] at this) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  have hs := span_range_eq_top_of_isAlgClosed τ hirr
  have hm : Set.range (mat σ) = (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)) '' Set.range τ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (LinearMap.toMatrix'_toLin' (mat σ g)).symm
  rw [hm]
  have := Submodule.map_span (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)).toLinearMap
    (Set.range τ)
  rw [hs, Submodule.map_top, LinearEquiv.range] at this
  exact this.symm

theorem span_eq_top_of_span_map {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k)
    (h : Submodule.span K (Set.range fun g => (M g).map (algebraMap k K)) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let F : Matrix (Fin r) (Fin r) K →ₗ[K] K :=
    { toFun := fun X => ∑ i, ∑ j, X i j * algebraMap k K (f (Matrix.single i j 1))
      map_add' := fun X Y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c X => by simp [Finset.mul_sum, mul_assoc] }
  have hF : ∀ X : Matrix (Fin r) (Fin r) k, F (X.map (algebraMap k K)) = algebraMap k K (f X) := by
    intro X
    conv_rhs => rw [Matrix.matrix_eq_sum_single X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    change ∑ i, ∑ j, algebraMap k K (X i j) * algebraMap k K (f (Matrix.single i j 1)) = _
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, map_mul]
  have hker : (⊤ : Submodule K (Matrix (Fin r) (Fin r) K)) ≤ LinearMap.ker F := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    have : f (M g) = 0 := hf (Submodule.subset_span ⟨g, rfl⟩)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hF, this, map_zero]
  apply hf0
  refine LinearMap.ext fun X => ?_
  have h1 : F (X.map (algebraMap k K)) = 0 := hker trivial
  rw [hF] at h1
  exact (algebraMap k K).injective (by rw [h1]; simp)

theorem span_mat_eq_top_of_absIrrSub :
    ∀ {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (ρ : Γ →* GL (Fin r) k), AbsIrrSub ρ ⊤ → Submodule.span k (Set.range (mat ρ)) = ⊤ := by
  intro Γ k _ _ r ρ h
  classical
  have htop : Submodule.span (AlgebraicClosure k)
      ((fun v : Fin r → k => (algebraMap k (AlgebraicClosure k)) ∘ v) ''
      ((⊤ : Submodule k (Fin r → k)) : Set (Fin r → k))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (AlgebraicClosure k) (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, trivial, ?_⟩
    ext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [hx]
  unfold AbsIrrSub at h
  rw [htop] at h
  have h2 := span_mat_eq_top_of_isIrrSub _ h
  have h3 : mat (mapRep (algebraMap k (AlgebraicClosure k)) ρ) =
      fun g => (mat ρ g).map (algebraMap k (AlgebraicClosure k)) := by
    funext g
    ext p q
    simp [mat, mapRep]
  rw [h3] at h2
  exact span_eq_top_of_span_map (mat ρ) h2

end GlobalTheory.BurnsideField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducibleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_repMatrix_eq_top_of_absIrreducible : ∀ {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (ρ : Γ →* GL (Fin r) k), AbsIrrSub ρ ⊤ → Submodule.span k (Set.range (mat ρ)) = ⊤ := by
  first | exact @GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub | exact GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub | (intros; apply GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.HostJumpSets

open AdmissibleParameterJ

variable {D : D7}

theorem Jp_finite (j : ℕ) (ρ : D.what₂.Tau) : (Jp D j ρ).Finite := by
  refine (((Set.finite_range fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D).union
    (Set.finite_range fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)).union
    (Set.finite_range fun c : Fin D.R.t => ((c : ℕ) : ℚ))).subset ?_
  rintro q ((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨c, hc, rfl⟩)
  · exact Or.inl (Or.inl ⟨a, rfl⟩)
  · exact Or.inl (Or.inr ⟨a, rfl⟩)
  · exact Or.inr ⟨⟨c, hc⟩, rfl⟩

theorem refl_injective : Function.Injective (AdmissibleParameterJ.refl D) := by
  intro x y h
  simp only [AdmissibleParameterJ.refl] at h
  linarith

theorem refl_surjective : Function.Surjective (AdmissibleParameterJ.refl D) := by
  intro y
  refine ⟨((D.R.t : ℚ) - 1) - y, ?_⟩
  simp only [AdmissibleParameterJ.refl]
  ring

theorem JJ_finite (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : (JJ D up j ρ).Finite := by
  cases up
  · exact (Jp_finite j ρ).preimage refl_injective.injOn
  · exact Jp_finite j ρ

theorem JJ_ncard (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : (JJ D up j ρ).ncard = (Jp D j ρ).ncard := by
  cases up
  · exact Set.ncard_preimage_of_injective_subset_range refl_injective
      (fun q _ => refl_surjective q)
  · rfl

theorem abs_le_two_b (L : SizeData₂ D) (hJe : JumpAbsoluteBound L) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) (q : ℚ) (hq : q ∈ JJ D up j ρ) : |(q : ℝ)| ≤ 2 * L.sc.b :=
  ((hJe.1 j hj1 hj2 ρ up q hq).trans hJe.2.1).trans hJe.2.2.2

theorem elem_ok (L : SizeData₂ D) (hJb : CloudCentreDistance L) (hJc : jcCondition L) (hJe : JumpAbsoluteBound L)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m) (ρ : D.what₂.Tau)
    (up : Bool) (a : ℤ) (ha : (a : ℚ) ∈ JJ D up j ρ) :
    ((0 ≤ a ∧ a < D.R.t) ∨ |(a : ℚ) - PairedCharacterCondition.cen (D := D)| ≤ (⌊L.etaSz⌋₊ : ℚ) + 1 ∨
        PairedCharacterCondition.cloud (D := D) up (⌊3 * L.sc.b⌋₊ + 2 + 0) a) ∧ a ≠ -1 ∧ a ≠ D.R.t := by
  have hnot := (hJc j hj1 hj2 ρ).2.1 up
  refine ⟨?_, fun h => hnot.1 (by rw [h] at ha; exact_mod_cast ha),
    fun h => hnot.2 (by rw [h] at ha; exact_mod_cast ha)⟩
  have hfl : 3 * L.sc.b < (⌊3 * L.sc.b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfe : L.etaSz < (⌊L.etaSz⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _

  have hcl : ∀ q ∈ cloudJ D j ρ, (D.R.t : ℚ) + 1 < q ∧ q ≤ ((⌊3 * L.sc.b⌋₊ + 2 + 0 : ℕ) : ℚ) := by
    intro q hq
    refine ⟨(hJc j hj1 hj2 ρ).2.2.1 q hq, ?_⟩
    have h2 := abs_le_two_b L hJe hj1 hj2 ρ true q (Or.inl (Or.inl hq))
    have h3 : (q : ℝ) ≤ ((⌊3 * L.sc.b⌋₊ + 2 + 0 : ℕ) : ℝ) := by
      push_cast
      linarith [le_abs_self (q : ℝ)]
    exact_mod_cast h3
  have hlow : ∀ q ∈ lowJ D j ρ, |q - c0 D| ≤ (⌊L.etaSz⌋₊ : ℚ) + 1 := by
    intro q hq
    have h1 := (hJb j hj1 hj2 ρ).2.1 q hq
    have h2 : ((|q - c0 D| : ℚ) : ℝ) ≤ (((⌊L.etaSz⌋₊ : ℚ) + 1 : ℚ) : ℝ) := by
      push_cast at h1 ⊢
      linarith
    exact_mod_cast h2
  cases up
  ·
    change AdmissibleParameterJ.refl D (a : ℚ) ∈ Jp D j ρ at ha
    rcases ha with (hq | hq) | ⟨c, hc, hx⟩
    · right; right
      obtain ⟨h1, h2⟩ := hcl _ hq
      simp only [PairedCharacterCondition.cloud, PairedCharacterCondition.cen, AdmissibleParameterJ.refl] at h1 h2 ⊢
      simp only [Bool.false_eq_true, if_false]
      constructor <;> linarith
    · right; left
      have h := hlow _ hq
      simp only [PairedCharacterCondition.cen, AdmissibleParameterJ.refl, c0] at h ⊢
      rw [show (a : ℚ) - ((D.R.t : ℚ) - 1) / 2 = -((D.R.t : ℚ) - 1 - (a : ℚ) - ((D.R.t : ℚ) - 1) / 2) by ring,
        abs_neg]
      exact h
    · left
      simp only [AdmissibleParameterJ.refl] at hx
      have hx' : (a : ℚ) = ((D.R.t : ℤ) - 1 - (c : ℤ) : ℤ) := by push_cast; linarith
      have hx'' : a = (D.R.t : ℤ) - 1 - c := by exact_mod_cast hx'
      omega
  · change (a : ℚ) ∈ Jp D j ρ at ha
    rcases ha with (hq | hq) | ⟨c, hc, hx⟩
    · right; right
      obtain ⟨h1, h2⟩ := hcl _ hq
      simp only [PairedCharacterCondition.cloud, PairedCharacterCondition.cen, if_true]
      constructor <;> linarith
    · right; left
      exact hlow _ hq
    · left
      have hx'' : a = c := by exact_mod_cast hx
      omega

theorem algHom_eq_of_finrank_one {F K A : Type} [Field F] [Field K] [Ring A] [Algebra F K] [Algebra F A]
    (h : finrank F K = 1) (f g : K →ₐ[F] A) : f = g := by
  ext x
  have hx : x ∈ (⊥ : Subalgebra F K) := by
    rw [Subalgebra.bot_eq_top_of_finrank_eq_one h]; trivial
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hx
  simp

theorem emb_inj (D : D7) : Function.Injective D.host.emb := by
  intro g g' h
  have h1 : D.host.sigmaOf g = D.host.sigmaOf g' :=
    AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)
  exact (D.host.gal).symm.injective h1

theorem decide_flip {P Q : Prop} {iP : Decidable P} {iQ : Decidable Q} (h : P ↔ ¬ Q) :
    @decide P iP = !@decide Q iQ := by
  by_cases hq : Q
  · rw [decide_eq_true hq, decide_eq_false (fun hp => h.1 hp hq)]; rfl
  · rw [decide_eq_false hq, decide_eq_true (h.2 hq)]; rfl

theorem typeU_flip (D : D7) (ep : Bool) (g : D.R.GG) :
    TypeU D ep g ↔ ¬ TypeU D ep (g * D.R.cc) := by
  have hP := Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g
  unfold TypeU
  cases ep <;> by_cases h : g ∈ D.R.Psi <;> simp_all

def incl (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 :=
  ((D.nbr i w hw).Kw.1.val).codRestrict (D.nbr i w hw).LL.1.toSubalgebra
    (fun x => (D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x)

end GlobalTheory.HostJumpSets

end

noncomputable section

namespace GlobalTheory.HostJumpSets

open AdmissibleParameterJ

theorem main : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → (D.R.t : ℝ) ≤ L.sc.b → ∀ (i : D.nd.Loc) (k : Fin 2) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), D.nd.l i = D.host.g k → GoodR D.nd i r → ∃ (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i r ⌊L.etaSz⌋₊ (⌊3 * L.sc.b⌋₊ + 2) 0 sg U := by
  intro D L ep hJa hJb hJc hJe _htb i k r hk hgood
  obtain ⟨hdeg, hemb⟩ := GlobalTheory.TypePlace.type_prime_places D i k hk
  have hj := D.nd.j_range i
  have hex := fun w (hw : w ∈ placesOver D.host.E (D.nd.l i)) =>
    hJa i r hgood w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (incl D i w hw)
  choose gf ρf hR hJ using hex
  classical
  let sg : HeightOneSpectrum (𝓞 D.host.E) → Bool := fun w =>
    if hw : w ∈ placesOver D.host.E (D.nd.l i) then decide (TypeU D ep (gf w hw)) else false
  let U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ := fun w =>
    if hw : w ∈ placesOver D.host.E (D.nd.l i) then
      (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)).filter
        (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw))
    else ∅
  have hsg : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), sg w = decide (TypeU D ep (gf w hw)) :=
    fun w hw => dif_pos hw
  refine ⟨sg, U, ?_, ?_⟩
  · intro w w' hw hc _hne
    have hw' : w' ∈ placesOver D.host.E (D.nd.l i) := by
      have := hc ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.nd.l i : ℕ) : 𝓞 D.host.E) (by simp)
      exact this.1 hw
    have hind : ∀ v (hv : v ∈ placesOver D.host.E (D.nd.l i)),
        InducesW D.nd i (gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i v hv) (incl D i v hv)) v := fun v hv =>
      (GlobalTheory.LocalEmbedding.inducesW_and_exists_emb D i v hv _ (incl D i v hv) _ (fun _ => rfl)).1
    have heq : gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (incl D i w hw) =
        (gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i w' hw') (incl D i w' hw')).comp (D.host.conj : D.host.E →+* D.host.E) := by
      apply hemb
      intro x
      let X : 𝓞 D.host.E := ⟨(D.host.conj : D.host.E →+* D.host.E) (x : D.host.E),
        (RingOfIntegers.isIntegral_coe x).map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom⟩
      rw [hind w hw x, RingHom.comp_apply]
      have h2 := hind w' hw' X
      rw [show ((X : 𝓞 D.host.E) : D.host.E) = (D.host.conj : D.host.E →+* D.host.E) (x : D.host.E) from rfl] at h2
      rw [h2]
      exact hc x X rfl
    have hg : gf w hw = gf w' hw' * D.R.cc := by
      apply emb_inj D
      rw [Formalism.L2.Geo.emb_mul_cc_comp, ← (hR w hw).1, ← (hR w' hw').1, heq]
      rfl
    rw [hsg w hw, hsg w' hw', hg]
    exact decide_flip (typeU_flip D ep (gf w' hw'))
  · intro w hw
    have hU : U w = (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)).filter
        (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw)) := dif_pos hw
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, ← Set.ncard_coe_finset]
      have h1 : ((Finset.filter (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw))
          (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) : Finset ℤ) : Set ℤ).ncard ≤
          (JJ D (sg w) (D.nd.j i) (ρf w hw)).ncard :=
        Set.ncard_le_ncard_of_injOn (fun a : ℤ => (a : ℚ))
          (fun a ha => (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2)
          (fun a _ b _ h => Int.cast_injective h) (JJ_finite _ _ _)
      rw [JJ_ncard] at h1
      exact h1.trans_eq ((hJb _ hj.1 hj.2 (ρf w hw)).2.2.2.2.2)
    · intro x τ a ha
      obtain rfl : τ = incl D i w hw := algHom_eq_of_finrank_one (hdeg w hw).1 _ _
      have e : TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rTwO D.nd i r x) = Br.loc D.nbr i w hw (rTwO D.nd i r x) := by
        ext; rfl
      have h1 := ((hJ w hw).1 x a).1
      rw [e] at h1
      have hmem := h1.1 ha
      rw [← hsg w hw] at hmem
      rw [hU, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨?_, hmem⟩
      have hb := abs_le_two_b L hJe hj.1 hj.2 (ρf w hw) _ _ hmem
      have hfl : 3 * L.sc.b < (⌊3 * L.sc.b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h0 : 0 ≤ L.sc.b := by linarith [abs_nonneg ((a : ℚ) : ℝ)]
      rw [abs_le] at hb
      push_cast at hb
      have h3 : (a : ℝ) ≤ ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
      have h4 : -((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℝ) ≤ (a : ℝ) := by push_cast; linarith
      constructor
      · exact_mod_cast h4
      · exact_mod_cast h3
    · intro a ha
      rw [hU, Finset.mem_filter] at ha
      exact elem_ok L hJb hJc hJe hj.1 hj.2 (ρf w hw) (sg w) a ha.2

end GlobalTheory.HostJumpSets

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrimeStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signs_and_jump_sets_at_type_prime : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → (D.R.t : ℝ) ≤ L.sc.b → ∀ (i : D.nd.Loc) (k : Fin 2) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), D.nd.l i = D.host.g k → GoodR D.nd i r → ∃ (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i r ⌊L.etaSz⌋₊ (⌊3 * L.sc.b⌋₊ + 2) 0 sg U := by
  first | exact @GlobalTheory.HostJumpSets.main | exact GlobalTheory.HostJumpSets.main | (intros; apply GlobalTheory.HostJumpSets.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorization
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorization
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace BridgeWittDvd

section Witt
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem dvd_iff (x : WittVector p k) : (p : WittVector p k) ∣ x ↔ x.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton]
  exact WittVector.mem_span_p_iff_coeff_zero_eq_zero x

theorem exists_limit (w : ℕ → WittVector p k) (h : ∀ n, (p : WittVector p k) ^ n ∣ w (n + 1) - w n) :
    ∃ z : WittVector p k, ∀ n, (p : WittVector p k) ^ n ∣ z - w n := by
  have hc : IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := inferInstance
  have key : ∀ (n : ℕ) (x y : WittVector p k),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p k)} ^ n • ⊤ : Submodule (WittVector p k) (WittVector p k))] ↔
        (p : WittVector p k) ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have step : ∀ m d : ℕ, (p : WittVector p k) ^ m ∣ w (m + d) - w m := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : w (m + (d + 1)) - w m = (w (m + d + 1) - w (m + d)) + (w (m + d) - w m) := by
        rw [← add_assoc]; ring
      rw [e]
      exact dvd_add ((pow_dvd_pow _ (Nat.le_add_right m d)).trans (h _)) ih
  obtain ⟨z, hz⟩ := hc.toIsPrecomplete.prec (f := w) (fun {m n} hmn => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [key, ← dvd_neg, neg_sub]
    exact step m d)
  refine ⟨z, fun n => ?_⟩
  rw [← dvd_neg, neg_sub]
  exact (key n _ _).1 (hz n)

theorem series_dvd (s : (WittVector p k)⟦X⟧)
    (h : PowerSeries.map (WittVector.constantCoeff (p := p) (R := k)) s = 0) :
    (p : (WittVector p k)⟦X⟧) ∣ s := by
  have hd : ∀ n, ∃ c, PowerSeries.coeff n s = (p : WittVector p k) * c := by
    intro n
    apply (dvd_iff _).2
    have := congrArg (PowerSeries.coeff n) h
    simpa using this
  choose c hc using hd
  refine ⟨PowerSeries.mk c, ?_⟩
  ext1 n
  rw [← map_natCast (PowerSeries.C (R := WittVector p k)) p, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem decomp (w : WittVector p k) (h0 : w ≠ 0) :
    ∃ (n : ℕ) (v : WittVector p k), IsUnit v ∧ w = (p : WittVector p k) ^ n * v := by
  obtain ⟨n, v, e⟩ := WittVector.exists_eq_pow_p_mul' w h0
  exact ⟨n, v, v.isUnit, e⟩
end Witt

theorem perfect_frac (p : ℕ) [Fact p.Prime] (R F : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [CharP R p] [CharP F p] [PerfectRing R p] : PerfectRing F p := by
  refine PerfectRing.ofSurjective F p fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨a', rfl⟩ := (bijective_frobenius R p).2 a
  obtain ⟨b', rfl⟩ := (bijective_frobenius R p).2 b
  exact ⟨algebraMap R F a' / algebraMap R F b', by simp [frobenius_def, div_pow]⟩

end BridgeWittDvd

theorem Bridge.kisin_reduction_unit_at_uniformizer : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (K : Formalism.BasicNotions.Loc.FinExt l) (bk : GlobalTheory.BSP.BK K), (∀ w ∈ bk.OE, l.cast ∣ w → ∃ v ∈ bk.OE, w = l.cast * v) ∧ (∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW PowerSeries.X : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ (s : bk.S), ¬l.cast ∣ s → ∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW s : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ w ∈ bk.OE, w ≠ OfNat.ofNat 0 → ∃ (k : ℕ) (v : Formalism.BasicNotions.Loc.WCb l) (v' : Formalism.BasicNotions.Loc.WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = OfNat.ofNat 1 ∧ w = HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast k * v) ∧ (∀ (w : ℕ → Formalism.BasicNotions.Loc.WCb l), (∀ (n : ℕ), w n ∈ bk.OE) → (∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ w (n + OfNat.ofNat 1) - w n) → ∃ z ∈ bk.OE, ∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ z - w n) ∧ (∀ (g : ↥(Formalism.BasicNotions.Loc.GK K)), bk.FixFlat g → ∀ w ∈ bk.OE, DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (F := Formalism.BasicNotions.Loc.GQ l →* Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (GlobalTheory.Prism.galW l) (g.val (p := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ x ∈ Formalism.BasicNotions.Loc.GK K)) : Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) w = w) ∧ ∀ w ∈ bk.OE, Membership.mem (α := Formalism.BasicNotions.Loc.WCb l) bk.OE (DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l →ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (Formalism.BasicNotions.Loc.frobW l) w : Formalism.BasicNotions.Loc.WCb l) := by
  intro l _ K bk
  haveI : PerfectRing (Cb l) l := BridgeWittDvd.perfect_frac l (OCb l) (Cb l)
  obtain ⟨ek, -, hek, hinj, -, -⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  obtain ⟨-, hS, hX, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨hsat, hcl, hφ, hgal, hunit⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have hsatn : ∀ (n : ℕ) (v : WCb l), ((l : ℕ) : WCb l) ^ n * v ∈ bk.OE → v ∈ bk.OE := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, mul_assoc] at hv
      exact hsat v (ih _ hv)
  refine ⟨?_, hunit _ (hS _) hX, ?_, ?_, ?_, hgal, hφ⟩
  · rintro w hw ⟨v, rfl⟩
    exact ⟨v, hsat v hw, rfl⟩
  · intro s hs
    refine hunit _ (hS s) (WittVector.isUnit_of_coeff_zero_ne_zero _ fun h0 => hs ?_)
    apply BridgeWittDvd.series_dvd
    apply hinj
    rw [hek, map_zero]
    have e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := rfl
    rw [e] at h0
    exact (FaithfulSMul.algebraMap_injective (OCb l) (Cb l)) (h0.trans (map_zero _).symm)
  · intro w hw h0
    obtain ⟨n, v, hv, e⟩ := BridgeWittDvd.decomp (p := l) (k := Cb l) w h0
    have hvO : v ∈ bk.OE := hsatn n v (e ▸ hw)
    obtain ⟨v', hv', e'⟩ := hunit v hvO hv
    exact ⟨n, v, v', hvO, hv', e', e⟩
  · intro w hw h
    obtain ⟨z, hz⟩ := BridgeWittDvd.exists_limit (p := l) (k := Cb l) w h
    exact ⟨z, hcl z fun n => ⟨w n, hw n, hz n⟩, hz⟩

namespace GlobalTheory.OEDvr

variable {l : ℕ} [hl : Fact l.Prime]

theorem perfectRing_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

variable {K : FinExt l} (bk : BK K)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w ∈ bk.OE, ((l : ℕ) : WCb l) ∣ w → ∃ v ∈ bk.OE, w = (l : WCb l) * v) ∧ (∃ w ∈ bk.OE, bk.evW X * w = 1) ∧ (∀ s : bk.S, ¬ (l : bk.S) ∣ s → ∃ w ∈ bk.OE, bk.evW s * w = 1) ∧ (∀ w ∈ bk.OE, w ≠ 0 → ∃ (k : ℕ) (v v' : WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = 1 ∧ w = (l : WCb l) ^ k * v) ∧ (∀ w : ℕ → WCb l, (∀ n, w n ∈ bk.OE) → (∀ n, (l : WCb l) ^ n ∣ w (n + 1) - w n) → ∃ z ∈ bk.OE, ∀ n, (l : WCb l) ^ n ∣ z - w n) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) :=
  Bridge.kisin_reduction_unit_at_uniformizer

end GlobalTheory.OEDvr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_elements_unit_factorization : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w ∈ bk.OE, ((l : ℕ) : WCb l) ∣ w → ∃ v ∈ bk.OE, w = (l : WCb l) * v) ∧ (∃ w ∈ bk.OE, bk.evW X * w = 1) ∧ (∀ s : bk.S, ¬ (l : bk.S) ∣ s → ∃ w ∈ bk.OE, bk.evW s * w = 1) ∧ (∀ w ∈ bk.OE, w ≠ 0 → ∃ (k : ℕ) (v v' : WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = 1 ∧ w = (l : WCb l) ^ k * v) ∧ (∀ w : ℕ → WCb l, (∀ n, w n ∈ bk.OE) → (∀ n, (l : WCb l) ^ n ∣ w (n + 1) - w n) → ∃ z ∈ bk.OE, ∀ n, (l : WCb l) ^ n ∣ z - w n) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) := by
  first | exact @GlobalTheory.OEDvr.main | exact GlobalTheory.OEDvr.main | (intros; apply GlobalTheory.OEDvr.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BKGal

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul_coord (P : PhiMod O K l e a ι) (m : OA l O) (c : ι → OA l O) :
    inclL t ϖ P (fun i => m * c i) = inclO l O m • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply]
  have h : (fun i => inclO l O (m * c i)) = inclO l O m • fun i => inclO l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [h, Matrix.mulVec_smul]

theorem IsCrisVal.sub {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') : IsCrisVal t ϖ P jB (w - w') (b - b') := by
  obtain ⟨m, c, hu, hc, hb⟩ := h
  obtain ⟨m', c', hu', hc', hb'⟩ := h'
  refine ⟨m * m', fun i => m' * c i - m * c' i, by rw [map_mul]; exact hu.mul hu', ?_, ?_⟩
  · have e1 : (fun i => m' * c i - m * c' i) = (fun i => m' * c i) - (fun i => m * c' i) := rfl
    rw [e1, map_sub, inclL_smul_coord, inclL_smul_coord, ← hc, ← hc', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (inclO l O m')]
  · have e2 : (fun i => toB l O (m' * c i - m * c' i)) =
        toB l O m' • (fun i => toB l O (c i)) - toB l O m • (fun i => toB l O (c' i)) :=
      funext fun i => by simp only [map_sub, map_mul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e2, map_sub, map_smul, map_smul, ← hb, ← hb', smul_sub, smul_smul, smul_smul, map_mul,
      mul_comm (toB l O m')]

end GlobalTheory.BKGal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvari
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLqPerm

theorem isChar_one {G : Type} [Group G] : IsChar (fun _ : G => (1 : ℂ)) := by
  refine ⟨FDRep.of (Representation.trivial ℂ G ℂ), fun x => ?_⟩
  change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) x) = 1
  simp [Representation.trivial, LinearMap.trace_id]

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

variable {g : ℕ} [Fact g.Prime]

theorem isChar_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) := by
  induction L with
  | nil => exact isChar_one
  | cons p L ih =>
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    exact ((GlobalTheory.T.harishChandra_induction_character_restriction_decomp g p.1 (degL L) (degL (p :: L)) hdeg).1 p.2 (hcL L (degL L))
      (hL p (by simp)) (ih fun q hq => hL q (by simp [hq])))

theorem degL_perm {L L' : List (Pc g)} (h : L.Perm L') : degL L = degL L' := by
  unfold degL
  exact (h.map _).sum_eq

theorem hc_congr_mid (a : ℕ) (α : Gn g a → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc a m α (F m) n = hc a m' α (F m') n := by subst h; rfl

theorem hc_congr_left (c : ℕ) (γ : Gn g c → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc m c (F m) γ n = hc m' c (F m') γ n := by subst h; rfl

theorem hcL_perm {L L' : List (Pc g)} (h : L.Perm L') :
    (∀ p ∈ L, IsChar p.2) → ∀ n, n = degL L → hcL L n = hcL L' n := by
  induction h with
  | nil => intro _ n _; rfl
  | cons x h ih =>
    rename_i L₁ L₂
    intro hc1 n hn
    rw [hcL_cons, hcL_cons, ih (fun q hq => hc1 q (by simp [hq])) _ rfl]
    exact hc_congr_mid x.1 x.2 (hcL L₂) n _ _ (degL_perm h)
  | swap x y L₁ =>
    intro hc1 n hn
    have hx : IsClass x.2 := isClass_of_isChar (hc1 x (by simp))
    have hy : IsClass y.2 := isClass_of_isChar (hc1 y (by simp))
    have hL : IsClass (hcL L₁ (degL L₁)) :=
      isClass_of_isChar (isChar_hcL L₁ fun q hq => hc1 q (by simp [hq]))
    have hn' : n = y.1 + x.1 + degL L₁ := by rw [hn]; simp [degL]; omega
    have hn'' : n = x.1 + y.1 + degL L₁ := by rw [hn']; omega
    have e1 : degL (x :: L₁) = x.1 + degL L₁ := by simp [degL]
    have e2 : degL (y :: L₁) = y.1 + degL L₁ := by simp [degL]
    simp only [hcL_cons]
    rw [hc_congr_mid y.1 y.2 (fun m => hc x.1 (degL L₁) x.2 (hcL L₁ (degL L₁)) m) n _ _ e1,
      hc_congr_mid x.1 x.2 (fun m => hc y.1 (degL L₁) y.2 (hcL L₁ (degL L₁)) m) n _ _ e2]
    rw [← (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g y.1 x.1 (degL L₁) n y.2 x.2 _ hy hx hL).1 hn',
      ← (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g x.1 y.1 (degL L₁) n x.2 y.2 _ hx hy hL).1 hn'',
      (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g y.1 x.1 (degL L₁) (y.1 + x.1) y.2 x.2 _ hy hx hL).2.1 rfl]
    exact hc_congr_left (degL L₁) (hcL L₁ (degL L₁)) (fun m => hc x.1 y.1 x.2 y.2 m) n _ _ (Nat.add_comm _ _)
  | trans h₁ h₂ ih₁ ih₂ =>
    intro hc1 n hn
    rw [ih₁ hc1 n hn, ih₂ (fun q hq => hc1 q (h₁.mem_iff.mpr hq)) n (hn.trans (degL_perm h₁))]

end GlobalTheory.GLqPerm

theorem GlobalTheory.gl_list_product_perm_char : ∀ (g : ℕ) [Fact g.Prime] (L L' : List (Pc g)) (n : ℕ), n = degL L → (∀ p ∈ L, IsChar p.2) → IsChar (hcL L n) ∧ (L.Perm L' → hcL L n = hcL L' n) := by
  intro g _ L L' n hn hL
  subst hn
  exact ⟨GlobalTheory.GLqPerm.isChar_hcL L hL, fun h => GlobalTheory.GLqPerm.hcL_perm h hL _ rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListIsCharacterAndPermInvariStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraProductList_isCharacter_and_perm_invariant : ∀ (g : ℕ) [Fact g.Prime] (L L' : List (Pc g)) (n : ℕ), n = degL L → (∀ p ∈ L, IsChar p.2) → IsChar (hcL L n) ∧ (L.Perm L' → hcL L n = hcL L' n) := by
  first | exact @GlobalTheory.gl_list_product_perm_char | exact GlobalTheory.gl_list_product_perm_char | (intros; apply GlobalTheory.gl_list_product_perm_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfIsOfFinOrderOfCharpoly
noncomputable section

namespace GlobalTheory.Triple

open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open Neutral.B1 hiding IsPlaceOver
open Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)

theorem eq_one_of_isOfFinOrder_of_charpoly {K : Type} [Field K] [CharZero K] {n : ℕ} {A : GL (Fin n) K}
    (hA : IsOfFinOrder A) (hc : (A : Matrix (Fin n) (Fin n) K).charpoly = (X - 1) ^ n) : A = 1 := by
  obtain ⟨m, hm, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hA
  have h1 : minpoly K (A : Matrix (Fin n) (Fin n) K) ∣ X ^ m - C 1 := minpoly.dvd _ _ (by
    rw [map_sub, map_pow, aeval_X, map_one, map_one, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self])
  have h2 := ((separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero).squarefree.squarefree_of_dvd
    h1).isRadical n _ (hc ▸ Matrix.minpoly_dvd_charpoly _)
  have h3 := aeval_eq_zero_of_dvd_aeval_eq_zero h2 (minpoly.aeval K _)
  rw [map_sub, aeval_X, map_one, sub_eq_zero] at h3
  exact Units.ext h3

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    M.charpolyRev.map f = (M.map f).charpolyRev := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h]

theorem eval_charpolyRev {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (z : R) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm z]

theorem charpolyRev_of_inv {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) {m : Multiset ℂ}
    (hB : B.charpoly = (m.map fun a => X - C a).prod) : A.charpolyRev = (m.map fun a => 1 - C a⁻¹ * X).prod := by
  have e : ∀ z : ℂ, (Matrix.scalar (Fin n) z - B).det = (m.map fun a => z - a).prod := fun z => by
    rw [← Matrix.eval_charpoly, hB, eval_multiset_prod, Multiset.map_map]
    simp
  have h0 : (Matrix.scalar (Fin n) 0 - B).det ≠ 0 := by
    rw [map_zero, zero_sub, Matrix.det_neg]
    exact mul_ne_zero (by simp) (Matrix.isUnit_det_of_left_inverse h).ne_zero
  apply Polynomial.funext
  intro z
  refine mul_right_cancel₀ h0 ?_
  have e1 : (1 - z • A) * (Matrix.scalar (Fin n) 0 - B) = Matrix.scalar (Fin n) z - B := by
    rw [map_zero, zero_sub, mul_neg, sub_mul, one_mul, smul_mul_assoc, h, neg_sub, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  rw [eval_charpolyRev, ← Matrix.det_mul, e1, e, e, eval_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  refine congrArg _ (Multiset.map_congr rfl fun a ha => ?_)
  have ha0 : a ≠ 0 := fun h1 => h0 (by
    rw [e]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by rw [h1, sub_self]⟩))
  simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem sum_coeff_charpolyRev {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∑ k ∈ Finset.range (n + 1), M.charpolyRev.coeff k = (1 - M).det := by
  have h : M.charpolyRev.natDegree < n + 1 := by
    rw [← Matrix.reverse_charpoly, Nat.lt_succ_iff]
    exact (reverse_natDegree_le _).trans (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  have := eval_eq_sum_range' h 1
  simp only [one_pow, mul_one, eval_charpolyRev, one_smul] at this
  exact this.symm

variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}

theorem cyclotomicEps_eq_one_on_inertia {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : σ ∈ Ine (F := D.host.E) A) : eps0 X i σ = 1 := by
  have h1 : cycZ D.host.E D.nd.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hv hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  rw [eps0, MonoidHom.comp_apply, h1, map_one]

theorem cyclotomicEps_frobenius_eq_norm {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {σ : GalE D} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 X i σ : (X.O0 i)ˣ) : X.O0 i) = (normV v : ℕ) := by
  show algebraMap ℤ_[X.l i] (X.O0 i) ((cycZ D.host.E D.nd.Om (X.l i) σ : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) = _
  rw [cycZ_of_isFrob hv hA hσ, map_natCast]

def twistW (s : X.Sig i) : GalE D →* (X.O0 i)ˣ := eps0 X i ^ D.R.t * (chiS i s)⁻¹

def matW (s : X.Sig i) (g : GalE D) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) :=
  ((twistW s g : (X.O0 i)ˣ) : X.O0 i) • ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))

theorem matW_eq (s : X.Sig i) (g : GalE D) :
    matW s g = (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g := by
  rw [matW, Tmat, smul_smul, twistW, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_pow_eq_pow_val]

theorem matW_mul_inv (s : X.Sig i) (g : GalE D) : matW s g * matW s g⁻¹ = 1 := by
  rw [matW, matW, smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one,
    map_one, Units.val_one, Units.val_one, one_smul]

variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {s : X.Sig i}

section With

variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : Zbar (X.l i) →+* FbAt D w}

end With

theorem notMem_of_mem_pD {v : PlE D.host} (hv : v ∈ X.pD i) :
    v ∉ placesOver D.host.E (X.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have h : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    X.pD_eq i ▸ Finset.mem_coe.2 hv
  have hl : (X.l i).Prime := (X.lPrime i).out
  split_ifs at h with e
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime hl (e ▸ D.host.pde_ne.symm) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h⟩
  · exact ⟨GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime hl (Ne.symm e) h,
      fun k => GlobalTheory.GalChar.notMem_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h⟩

theorem matW_of_mem_Ine (hu : UnrRho i s) {v : PlE D.host} (hl : v ∉ placesOver D.host.E (X.l i))
    (hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k)) {A : ValuationSubring D.nd.Om}
    (hA : IsPlaceOver (F := D.host.E) A v) {g : GalE D} (hI : g ∈ Ine (F := D.host.E) A) :
    matW s g = (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
  rw [matW_eq, Tmat, cyclotomicEps_eq_one_on_inertia hl hA hI, hu v hl hg A hA g hI, Units.val_one, Units.val_one, one_pow, one_smul]

variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}

end GlobalTheory.Triple

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsU
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.CycBridge

theorem locChi_epsU : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (g : Br.G D.nbr i w hw), Br.locChi D.nbr i w hw (epsU D.nd i) g = cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g :=
  fun D i w hw g => Units.ext (GlobalTheory.Survey.CrystallineCharacterRatio.locChi_eps D i w hw g)

end GlobalTheory.CycBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionary
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AdmissibleDictionary

theorem main : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  intro D i
  exact GlobalTheory.TameFixedLift.main D.nd i

end GlobalTheory.AdmissibleDictionary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisation
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.admissible_shape_and_epsilon_at_every_localisation

theorem main : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible (D := D) i ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  intro D i
  refine ⟨fun w hw => ?_, GlobalTheory.TameFixedLift.main D.nd i⟩
  exact UpperTheory.KStar.Cyc.kw_le_roots D.host.toHostRaw (D.nbr i w hw)

end GlobalTheory.admissible_shape_and_epsilon_at_every_localisation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleShapeAndEpsilonAtEveryLocalisationStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_shape_and_epsilon_at_every_localisation : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible (D := D) i ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i := by
  first | exact @GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main | exact GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main | (intros; apply GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main <;> assumption)
end
end
