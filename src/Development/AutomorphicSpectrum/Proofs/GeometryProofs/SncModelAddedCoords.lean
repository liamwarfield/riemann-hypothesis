module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoords
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldCoordsGenerated
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldCoordsGenerated
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChartFrac

theorem exists_eq_div_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω),
    CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ a : Ω, ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ t ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), t ≠ 0 ∧ a = s / t := by
  intro X Ω _ ξ κ x h c hc a
  have hchart : InChart ξ x c (TieArith.genCpt ξ) :=
    ⟨hc, fun c' => TieArith.mem_regAt_genCpt ξ h.gen _⟩
  obtain ⟨t, ht, hu, hta⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x h c (TieArith.genCpt ξ) hchart a).mp
    (TieArith.mem_regAt_genCpt ξ h.gen a)
  exact ⟨t * a, hta, t, ht, hu.1, (mul_div_cancel_left₀ a hu.1).symm⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrac
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldCoordsGeneratedStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fraction_field_coords_generated : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω),
    CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ a : Ω, ∃ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ t ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), t ≠ 0 ∧ a = s / t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart | exact GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFrac.exists_eq_div_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankTranscendenceDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankTranscendenceDegree
namespace GlobalTheory.CompanionTheory.Kaehler

theorem finrank_kaehlerDifferential_of_adjoin_eq_top (K L : Type) [Field K] [Field L] [Algebra K L]
    (I : Type) [Fintype I] (u : I → L) (hu : AlgebraicIndependent K u)
    (hadj : IntermediateField.adjoin K (Set.range u) = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  classical
  letI : Algebra (MvPolynomial I K) L := (MvPolynomial.aeval u).toRingHom.toAlgebra
  have hmap : ∀ q : MvPolynomial I K, algebraMap (MvPolynomial I K) L q = MvPolynomial.aeval u q :=
    fun _ => rfl
  have : IsScalarTower K (MvPolynomial I K) L :=
    IsScalarTower.of_algebraMap_eq fun x => by rw [hmap, AlgHom.commutes]
  have : FaithfulSMul (MvPolynomial I K) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hu
  have : IsFractionRing (MvPolynomial I K) L := IsFractionRing.of_field (MvPolynomial I K) L fun z => by
    have hz : z ∈ IntermediateField.adjoin K (Set.range u) := by rw [hadj]; trivial
    obtain ⟨r, s, h⟩ := (IntermediateField.mem_adjoin_range_iff K u z).1 hz
    exact ⟨r, s, h⟩
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors (MvPolynomial I K))
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale K (MvPolynomial I K) L
  rw [Module.finrank_eq_card_basis (hbc.basis (KaehlerDifferential.mvPolynomialBasis K I))]

end GlobalTheory.CompanionTheory.Kaehler
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankTranscendenceDegreeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_rank_transcendence_degree : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (I : Type) [Fintype I] (u : I → L),
    AlgebraicIndependent K u → IntermediateField.adjoin K (Set.range u) = ⊤ →
    Module.finrank L (KaehlerDifferential K L) = Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | exact GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top | (intros; apply GlobalTheory.CompanionTheory.Kaehler.finrank_kaehlerDifferential_of_adjoin_eq_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankLocalizationBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationKaehlerPrimeIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationKaehlerPrimeIdeal
namespace GlobalTheory.CompanionTheory.Ar.BoundaryPull

open MvPolynomial

theorem coe_aeval_subalgebra {K : Type} [Field K] [CharZero K] {τ : Type}
    (S : Subalgebra ℚ K) (r : τ → K) (h : ∀ p, r p ∈ S) (g : MvPolynomial τ ℤ) :
    ((aeval (fun p => (⟨r p, h p⟩ : S)) g : S) : K) = aeval r g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem vanishing_rename_iff :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type)
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (bd : Ideal (MvPolynomial σ ℤ)) (S : Subalgebra ℚ Ω₀) (S' : Subalgebra ℚ Ω) (θ : S →+* S'),
    (∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s) → (∀ p, r₀ p ∈ S) → (∀ p, r₁ p ∈ S') →
    ∀ q : Ideal S',
    ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
      (∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q.comap θ)) := by
  intro Ω₀ Ω _ _ _ _ _ σ σ' r₀ r₁ v hv bd S S' θ hθ h₀ h₁ q
  have key : ∀ b : MvPolynomial σ ℤ,
      MvPolynomial.aeval r₁ (MvPolynomial.rename v b) = algebraMap Ω₀ Ω (MvPolynomial.aeval r₀ b) := by
    intro b
    induction b using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, hv]
  constructor
  · intro H g hg s hs
    refine Ideal.mem_comap.2 (H (MvPolynomial.rename v g) (Ideal.mem_map_of_mem _ hg) (θ s) ?_)
    rw [hθ, hs, key]
  · intro H g hg s hs
    have claim : ∃ t ∈ q, (t : Ω) = MvPolynomial.aeval r₁ g := by
      have hspan : g ∈ Ideal.span ((MvPolynomial.rename v : MvPolynomial σ ℤ → MvPolynomial σ' ℤ) '' (bd : Set _)) := hg
      refine Submodule.span_induction (p := fun g _ => ∃ t ∈ q, (t : Ω) = MvPolynomial.aeval r₁ g)
        ?_ ?_ ?_ ?_ hspan
      · rintro _ ⟨b, hb, rfl⟩
        let s₀ : S := aeval (fun p => (⟨r₀ p, h₀ p⟩ : S)) b
        have hs₀ : (s₀ : Ω₀) = aeval r₀ b := coe_aeval_subalgebra S r₀ h₀ b
        refine ⟨θ s₀, Ideal.mem_comap.1 (H b hb s₀ hs₀), ?_⟩
        rw [hθ, hs₀, key]
      · exact ⟨0, q.zero_mem, by simp⟩
      · rintro x y _ _ ⟨t, ht, hx⟩ ⟨u, hu, hy⟩
        exact ⟨t + u, q.add_mem ht hu, by simp [hx, hy]⟩
      · rintro c x _ ⟨t, ht, hx⟩
        refine ⟨aeval (fun p => (⟨r₁ p, h₁ p⟩ : S')) c * t, q.mul_mem_left _ ht, ?_⟩
        simp [coe_aeval_subalgebra S' r₁ h₁ c, hx]
    obtain ⟨t, ht, hts⟩ := claim
    have : s = t := Subtype.ext (hs.trans hts.symm)
    exact this ▸ ht

end GlobalTheory.CompanionTheory.Ar.BoundaryPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationKaehlerPrimeIdealStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_kaehler_prime_ideal : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type)
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (bd : Ideal (MvPolynomial σ ℤ)) (S : Subalgebra ℚ Ω₀) (S' : Subalgebra ℚ Ω) (θ : S →+* S'),
    (∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s) → (∀ p, r₀ p ∈ S) → (∀ p, r₁ p ∈ S') →
    ∀ q : Ideal S',
    ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
      (∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q.comap θ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff | exact GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BoundaryPull.vanishing_rename_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisTower
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisTower
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KaehlerTower

theorem append_of_shortExact {A M₁ M₂ M₃ : Type*} [CommRing A]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) {e m : ℕ} (u : Fin e → M₁) (w : Fin m → M₂)
    (hu : LinearIndependent A u) (hus : Submodule.span A (Set.range u) = ⊤)
    (hw : LinearIndependent A (fun i => g (w i)))
    (hws : Submodule.span A (Set.range fun i => g (w i)) = ⊤) :
    LinearIndependent A (Fin.append (fun i => f (u i)) w) ∧
      Submodule.span A (Set.range (Fin.append (fun i => f (u i)) w)) = ⊤ := by
  have happ : Fin.append (fun i => f (u i)) w =
      Sum.elim (fun i => f (u i)) w ∘ finSumFinEquiv.symm := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp
  have hfu : LinearIndependent A (fun i => f (u i)) :=
    hu.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hw' : LinearIndependent A w := LinearIndependent.of_comp g hw
  have hcomp : ∀ y, g (f y) = 0 := fun y => (hfg (f y)).mpr ⟨y, rfl⟩
  have hdisj : Disjoint (Submodule.span A (Set.range fun i => f (u i)))
      (Submodule.span A (Set.range w)) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hgx : g x = 0 := by
      have hle : Submodule.span A (Set.range fun i => f (u i)) ≤ LinearMap.ker g := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hcomp _
      exact hle hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hx'
    have h0 : ∑ i, c i • g (w i) = 0 := by simpa [map_sum] using hgx
    have hc := (Fintype.linearIndependent_iff.mp hw) c h0
    simp [hc]
  constructor
  · rw [happ]
    exact (hfu.sum_type hw' hdisj).comp _ finSumFinEquiv.symm.injective
  · rw [happ, Set.range_comp, finSumFinEquiv.symm.surjective.range_eq, Set.image_univ,
      Set.Sum.elim_range, Submodule.span_union, eq_top_iff]
    intro x _
    have hgx : g x ∈ Submodule.span A (Set.range fun i => g (w i)) := hws ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hgx
    have hker : g (x - ∑ i, c i • w i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hc]
    obtain ⟨y, hy⟩ := (hfg _).mp hker
    have hy' : y ∈ Submodule.span A (Set.range u) := hus ▸ Submodule.mem_top
    have hfy : f y ∈ Submodule.span A (Set.range fun i => f (u i)) := by
      have := Submodule.mem_map_of_mem (f := f) hy'
      rwa [Submodule.map_span, ← Set.range_comp] at this
    have hsum : ∑ i, c i • w i ∈ Submodule.span A (Set.range w) :=
      Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hx : x = f y + ∑ i, c i • w i := by rw [hy]; abel
    rw [hx]
    exact Submodule.add_mem_sup hfy hsum

theorem kaehler_basis_tower : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra.FormallySmooth S T] (e m : ℕ) (z : Fin e → S) (w : Fin m → T),
    LinearIndependent S (fun i => KaehlerDifferential.D R S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D R S (z i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) ∧
    Submodule.span T (Set.range fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) = ⊤ := by
  intro R S T _ _ _ _ _ _ _ _ e m z w hz hzs hw hws
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
    have : Subsingleton (Algebra.H1Cotangent S T) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    rw [Subsingleton.elim y 0, map_zero]
  have hex : Function.Exact (KaehlerDifferential.mapBaseChange R S T)
      (KaehlerDifferential.map R S T T) := KaehlerDifferential.exact_mapBaseChange_map R S T
  let b : Module.Basis (Fin e) S (Ω[S⁄R]) := Module.Basis.mk hz hzs.ge
  let bT := Algebra.TensorProduct.basis T b
  have hb : ∀ i, bT i = (1 : T) ⊗ₜ[S] KaehlerDifferential.D R S (z i) := by
    intro i
    simp [bT, b]
  have hmain := append_of_shortExact (KaehlerDifferential.mapBaseChange R S T)
    (KaehlerDifferential.map R S T T) hinj hex (fun i => bT i)
    (fun i => KaehlerDifferential.D R T (w i)) bT.linearIndependent bT.span_eq
    (by simpa [KaehlerDifferential.map_D] using hw)
    (by simpa [KaehlerDifferential.map_D] using hws)
  have hfun : (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) =
      Fin.append (fun i => KaehlerDifferential.mapBaseChange R S T (bT i))
        (fun i => KaehlerDifferential.D R T (w i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [hb, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
    · simp
  rw [hfun]
  exact hmain

end GlobalTheory.CompanionTheory.KaehlerTower
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisTowerStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_tower_alt : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra.FormallySmooth S T] (e m : ℕ) (z : Fin e → S) (w : Fin m → T),
    LinearIndependent S (fun i => KaehlerDifferential.D R S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D R S (z i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    LinearIndependent T (fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) ∧
    Submodule.span T (Set.range fun i => KaehlerDifferential.D R T (Fin.append (fun i => algebraMap S T (z i)) w i)) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower | exact GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower | (intros; apply GlobalTheory.CompanionTheory.KaehlerTower.kaehler_basis_tower <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseIsLocalizationAway
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseIsLocalizationAway
namespace GlobalTheory.CompanionTheory.Ggeo

theorem adjoin_inv_isLocalization_away (Ω : Type) [Field Ω] [CharZero Ω] (A S' : Subalgebra ℚ Ω)
    (G : Set Ω) (hA : A = Algebra.adjoin ℚ G) (g : A) (hg : g ≠ 0)
    (hS : S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ G)) (hle : A ≤ S') :
    @IsLocalization.Away A _ g S' _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  letI : Algebra A S' := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have hg0 : (g : Ω) ≠ 0 := fun h => hg (Subtype.ext h)
  have hinv : (g : Ω)⁻¹ ∈ S' := by
    rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
  have key : ∀ x ∈ S', ∃ (n : ℕ) (a : A), x * (g : Ω) ^ n = (a : Ω) := by
    intro x hx
    rw [hS] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact ⟨1, 1, by simp [hg0]⟩
      · refine ⟨0, ⟨x, ?_⟩, by simp⟩
        rw [hA]; exact Algebra.subset_adjoin hx
    | algebraMap r => exact ⟨0, algebraMap ℚ A r, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, b, hb⟩ := hy
      refine ⟨n + m, a * g ^ m + b * g ^ n, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, b, hb⟩ := hy
      refine ⟨n + m, a * b, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
  refine IsLocalization.Away.mk g ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨(g : Ω)⁻¹, hinv⟩ : S') ?_
    apply Subtype.ext
    change (g : Ω) * (g : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ hg0
  · intro s
    obtain ⟨n, a, ha⟩ := key s s.2
    refine ⟨n, a, ?_⟩
    apply Subtype.ext
    change (s : Ω) * (g : Ω) ^ n = (a : Ω)
    exact ha
  · intro a b hab
    refine ⟨0, ?_⟩
    have : (a : Ω) = (b : Ω) := congrArg (fun x : S' => (x : Ω)) hab
    rw [Subtype.ext this]

end GlobalTheory.CompanionTheory.Ggeo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinInverseIsLocalizationAwayStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_inverse_is_localization_away : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (A S' : Subalgebra ℚ Ω) (G : Set Ω), A = Algebra.adjoin ℚ G →
    ∀ (g : A), g ≠ 0 → S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ G) → ∀ (hle : A ≤ S'),
    @IsLocalization.Away A _ g S' _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away | exact GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away | (intros; apply GlobalTheory.CompanionTheory.Ggeo.adjoin_inv_isLocalization_away <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankLocalizationBound
namespace GlobalTheory.CompanionTheory.Ar.LocalStep

theorem exists_away_basis (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] [Algebra ℚ S] [Algebra.Smooth S T] [Algebra.Smooth ℚ S]
    (e r : ℕ) (hr : Module.finrank L (KaehlerDifferential K L) = r) (z : Fin e → S)
    (hli : LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)))
    (hsp : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤)
    (P : Ideal T) [P.IsPrime] :
    ∃ g : T, g ∉ P ∧ ∀ (T' : Type) [CommRing T'] [IsDomain T'] [Algebra T T'] [IsLocalization.Away g T']
      [Algebra ℚ T'] [Algebra T' L] [IsScalarTower T T' L],
      Algebra.Smooth ℚ T' ∧ ∃ z' : Fin (e + r) → T',
        (∀ i, z' (Fin.castAdd r i) = algebraMap T T' (algebraMap S T (z i))) ∧
        LinearIndependent T' (fun i => KaehlerDifferential.D ℚ T' (z' i)) ∧
        Submodule.span T' (Set.range fun i => KaehlerDifferential.D ℚ T' (z' i)) = ⊤ := by
  haveI : Algebra.IsSmoothAt S P := inferInstance
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth S P
  refine ⟨g, hg, ?_⟩
  intro T' _ _ _ _ _ _ _
  letI : Algebra S T' := ((algebraMap T T').comp (algebraMap S T)).toAlgebra
  haveI : IsScalarTower S T T' := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℚ S T' := .of_algebraMap_eq fun x =>
    DFunLike.congr_fun (Subsingleton.elim (algebraMap ℚ T') ((algebraMap S T').comp (algebraMap ℚ S))) x
  haveI : IsScalarTower S T' L := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply S T L, IsScalarTower.algebraMap_apply S T T',
      ← IsScalarTower.algebraMap_apply T T' L]
  let f : Localization.Away g ≃ₐ[T] T' := IsLocalization.algEquiv (Submonoid.powers g) _ _
  haveI : Algebra.IsStandardSmooth S T' := Algebra.IsStandardSmooth.of_algEquiv (f.restrictScalars S)
  haveI : Algebra.Smooth S T' := inferInstance
  have hsm : Algebra.Smooth ℚ T' := Algebra.Smooth.comp ℚ S T'
  refine ⟨hsm, ?_⟩
  obtain ⟨m, w, hli', hsp'⟩ : ∃ (m : ℕ) (w : Fin m → T'),
      LinearIndependent T' (fun i => KaehlerDifferential.D S T' (w i)) ∧
      Submodule.span T' (Set.range fun i => KaehlerDifferential.D S T' (w i)) = ⊤ := by
    obtain ⟨-, I, b, hb⟩ := (Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential
      (R := S) (S := T')).1 inferInstance
    haveI : Finite I := Module.Finite.finite_basis b
    cases nonempty_fintype I
    let b' := b.reindex (Fintype.equivFin I)
    have hb' : ∀ i, ∃ x, KaehlerDifferential.D S T' x = b' i := fun i => by
      obtain ⟨x, hx⟩ := hb ⟨(Fintype.equivFin I).symm i, rfl⟩
      exact ⟨x, by simpa [b'] using hx⟩
    choose w hw using hb'
    refine ⟨_, w, ?_, ?_⟩
    · simpa only [hw] using b'.linearIndependent
    · simpa only [hw] using b'.span_eq
  haveI : IsDomain T := (IsFractionRing.injective T L).isDomain (algebraMap T L)
  haveI : IsFractionRing T' L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers g) T' L
  have hm : Module.finrank L (KaehlerDifferential K L) = m := GlobalTheory.T.kaehler_finrank_fraction_field S T' K L m w hli' hsp'
  obtain rfl : r = m := hr.symm.trans hm
  obtain ⟨h1, h2⟩ := GlobalTheory.T.kaehler_basis_tower_alt ℚ S T' e r z w hli hsp hli' hsp'
  exact ⟨_, fun i => by rw [Fin.append_left]; rfl, h1, h2⟩

theorem local_step : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type) [Finite σ']
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (e r : ℕ) (bd : Ideal (MvPolynomial σ ℤ)), Module.finrank Ω (KaehlerDifferential Ω₀ Ω) = r →
    ∀ (h : Ω₀), h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert h⁻¹ (Set.range r₀)) →
    T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (Set.range r₁)) →
    ∀ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) → ψ.Smooth →
    IsFractionRing S Ω₀ → IsFractionRing T Ω → Algebra.Smooth ℚ S →
    ∀ (z : Fin e → S) (n : ℕ), n ≤ e → LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) →
    ∀ (P : Ideal (Algebra.adjoin ℚ (Set.range r₁))), P.IsPrime →
    ∀ h₁ : Algebra.adjoin ℚ (Set.range r₁), (h₁ : Ω) = algebraMap Ω₀ Ω h → h₁ ∉ P →
    ∃ t : Algebra.adjoin ℚ (Set.range r₁), t ∉ P ∧ ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range r₁)) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + r) → S') (n' : ℕ), n' ≤ e + r ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
            ∃ i : Fin (e + r), (i : ℕ) < n' ∧ z' i ∈ q) := by
  intro Ω₀ Ω _ _ _ _ _ σ σ' _ r₀ r₁ v hv e r bd hr h hh S T hS hT ψ hψ hsm hfS hfT hsS z n hn hli hsp hq
    P hP h₁ hh₁ hh₁P
  letI : Algebra S T := ψ.toAlgebra
  haveI : Algebra.Smooth S T := hsm
  haveI : IsScalarTower S T Ω := .of_algebraMap_eq fun s => (hψ s).symm
  haveI : IsScalarTower S Ω₀ Ω := .of_algebraMap_eq fun s => rfl
  have hr₁T : ∀ p, r₁ p ∈ T := fun p => by
    rw [hT]; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hle₁ : Algebra.adjoin ℚ (Set.range r₁) ≤ T := Algebra.adjoin_le (by rintro _ ⟨p, rfl⟩; exact hr₁T p)
  letI : Algebra (Algebra.adjoin ℚ (Set.range r₁)) T := (Subalgebra.inclusion hle₁).toRingHom.toAlgebra
  have hne₁ : h₁ ≠ 0 := fun h0 => hh₁P (h0 ▸ P.zero_mem)
  haveI : IsLocalization.Away h₁ T :=
    GlobalTheory.T.adjoin_inverse_is_localization_away Ω _ T (Set.range r₁) rfl h₁ hne₁ (by rw [hT, hh₁]) hle₁
  have hdisj : Disjoint ((Submonoid.powers h₁ : Submonoid (Algebra.adjoin ℚ (Set.range r₁))) :
      Set (Algebra.adjoin ℚ (Set.range r₁))) (↑P : Set (Algebra.adjoin ℚ (Set.range r₁))) := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  haveI hPT : (P.map (algebraMap _ T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers h₁) T P hP hdisj
  have hcomap : (P.map (algebraMap _ T)).comap (algebraMap _ T) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers h₁) T hP hdisj
  obtain ⟨g, hgP, Hg⟩ := exists_away_basis S T Ω₀ Ω e r hr z hli hsp (P.map (algebraMap _ T))
  obtain ⟨k, g₀, hk⟩ := IsLocalization.Away.surj h₁ g
  have hg₀ : g₀ ∉ P := by
    intro hmem
    have h1 := Ideal.mem_map_of_mem (algebraMap _ T) hmem
    rw [← hk] at h1
    rcases hPT.mem_or_mem h1 with h2 | h2
    · exact hgP h2
    · have h3 := hPT.mem_of_pow_mem _ h2
      have h4 : h₁ ∈ (P.map (algebraMap _ T)).comap (algebraMap _ T) := h3
      rw [hcomap] at h4
      exact hh₁P h4
  refine ⟨g₀ * h₁, hP.mul_notMem hg₀ hh₁P, ?_⟩
  intro S' hS'
  have hk' : (g : Ω) * (h₁ : Ω) ^ k = (g₀ : Ω) := congrArg T.val hk
  have hg0 : g ≠ 0 := fun h0 => hgP (h0 ▸ Ideal.zero_mem _)
  have hgΩ : (g : Ω) ≠ 0 := fun h0 => hg0 (Subtype.ext h0)
  have hHΩ : (h₁ : Ω) ≠ 0 := fun h0 => hne₁ (Subtype.ext h0)
  have hg₀Ω : (g₀ : Ω) ≠ 0 := by rw [← hk']; exact mul_ne_zero hgΩ (pow_ne_zero _ hHΩ)
  have ht : (((g₀ * h₁ : Algebra.adjoin ℚ (Set.range r₁)) : _) : Ω) = (g₀ : Ω) * h₁ := rfl
  have hr₁S' : ∀ p, r₁ p ∈ S' := fun p => by
    rw [hS']; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  have hle' : Algebra.adjoin ℚ (Set.range r₁) ≤ S' := Algebra.adjoin_le (by rintro _ ⟨p, rfl⟩; exact hr₁S' p)
  have htS' : ((g₀ : Ω) * h₁)⁻¹ ∈ S' := by
    rw [hS', ht]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
  have hTS' : T ≤ S' := by
    rw [hT]
    refine Algebra.adjoin_le (Set.insert_subset ?_ (by rintro _ ⟨p, rfl⟩; exact hr₁S' p))
    have : (algebraMap Ω₀ Ω h)⁻¹ = ((g₀ : Ω) * h₁)⁻¹ * (g₀ : Ω) := by
      rw [← hh₁]; field_simp
    rw [SetLike.mem_coe, this]
    exact S'.mul_mem htS' (hle' g₀.2)
  have hEq : S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ (T : Set Ω)) := by
    refine le_antisymm ?_ (Algebra.adjoin_le (Set.insert_subset ?_ hTS'))
    · rw [hS']
      refine Algebra.adjoin_le (Set.insert_subset ?_ ?_)
      · have hinv : (h₁ : Ω)⁻¹ ∈ T := by
          rw [hT, hh₁]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
        have : (((g₀ * h₁ : Algebra.adjoin ℚ (Set.range r₁)) : _) : Ω)⁻¹ = (g : Ω)⁻¹ * ((h₁ : Ω)⁻¹) ^ (k + 1) := by
          rw [ht, ← hk', inv_pow, ← mul_inv, mul_assoc, ← pow_succ]
        rw [SetLike.mem_coe, this]
        exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _))
          (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ hinv)) _)
      · rintro _ ⟨p, rfl⟩
        exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (hr₁T p))
    · have : (g : Ω)⁻¹ = ((g₀ : Ω) * h₁)⁻¹ * (h₁ : Ω) ^ (k + 1) := by
        rw [← hk', mul_assoc, ← pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hHΩ), mul_one]
      rw [SetLike.mem_coe, this]
      exact S'.mul_mem htS' (S'.pow_mem (hle' h₁.2) _)
  letI : Algebra T S' := (Subalgebra.inclusion hTS').toRingHom.toAlgebra
  haveI : IsLocalization.Away g S' := GlobalTheory.T.adjoin_inverse_is_localization_away Ω T S' (T : Set Ω) (Algebra.adjoin_eq T).symm g hg0 hEq hTS'
  haveI : IsScalarTower T S' Ω := .of_algebraMap_eq fun _ => rfl
  obtain ⟨hsm', z', hz', hli', hsp'⟩ := Hg S'
  refine ⟨hsm', z', n, by omega, hli', hsp', ?_⟩
  intro q hq'
  let θ : S →+* S' := (algebraMap T S').comp ψ
  have hθ : ∀ s, ((θ s : S') : Ω) = algebraMap Ω₀ Ω s := fun s => hψ s
  have hr₀S : ∀ p, r₀ p ∈ S := fun p => by
    rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  rw [GlobalTheory.T.localization_kaehler_prime_ideal Ω₀ Ω σ σ' r₀ r₁ v hv bd S S' θ hθ hr₀S hr₁S' q, hq (q.comap θ) (hq'.comap θ)]
  constructor
  · rintro ⟨i, hi, hmem⟩
    refine ⟨Fin.castAdd r i, by simpa using hi, ?_⟩
    rw [hz']; exact hmem
  · rintro ⟨j, hj, hmem⟩
    have hje : (j : ℕ) < e := by omega
    refine ⟨⟨j, hje⟩, hj, ?_⟩
    have : j = Fin.castAdd r ⟨j, hje⟩ := Fin.ext rfl
    rw [this, hz'] at hmem
    exact hmem

end GlobalTheory.CompanionTheory.Ar.LocalStep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerRankLocalizationBoundStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_rank_localization_bound : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (σ σ' : Type) [Finite σ']
    (r₀ : σ → Ω₀) (r₁ : σ' → Ω) (v : σ → σ'), (∀ p, algebraMap Ω₀ Ω (r₀ p) = r₁ (v p)) →
    ∀ (e r : ℕ) (bd : Ideal (MvPolynomial σ ℤ)), Module.finrank Ω (KaehlerDifferential Ω₀ Ω) = r →
    ∀ (h : Ω₀), h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
    S = Algebra.adjoin ℚ (insert h⁻¹ (Set.range r₀)) →
    T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (Set.range r₁)) →
    ∀ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) → ψ.Smooth →
    IsFractionRing S Ω₀ → IsFractionRing T Ω → Algebra.Smooth ℚ S →
    ∀ (z : Fin e → S) (n : ℕ), n ≤ e → LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) →
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    (∀ q : Ideal S, q.IsPrime → ((∀ g ∈ bd, ∀ s : S, (s : Ω₀) = MvPolynomial.aeval r₀ g → s ∈ q) ↔
      ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) →
    ∀ (P : Ideal (Algebra.adjoin ℚ (Set.range r₁))), P.IsPrime →
    ∀ h₁ : Algebra.adjoin ℚ (Set.range r₁), (h₁ : Ω) = algebraMap Ω₀ Ω h → h₁ ∉ P →
    ∃ t : Algebra.adjoin ℚ (Set.range r₁), t ∉ P ∧ ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range r₁)) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + r) → S') (n' : ℕ), n' ≤ e + r ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename v), ∀ s : S', (s : Ω) = MvPolynomial.aeval r₁ g → s ∈ q) ↔
            ∃ i : Fin (e + r), (i : ℕ) < n' ∧ z' i ∈ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalStep.local_step | exact GlobalTheory.CompanionTheory.Ar.LocalStep.local_step | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalStep.local_step <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothMapLocalizationCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothMapLocalizationCompat
namespace GlobalTheory.CompanionTheory.Ar.LocalisedSmooth

def denomMonoid {R : Type} [CommRing R] (c : R) : Submonoid R where
  carrier := {x | ∃ n k : ℕ, n ≠ 0 ∧ x = (n : R) * c ^ k}
  one_mem' := ⟨1, 0, one_ne_zero, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, k, hn, rfl⟩ ⟨m, l, hm, rfl⟩
    exact ⟨n * m, k + l, mul_ne_zero hn hm, by push_cast; ring⟩

theorem map_denomMonoid {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (c : R) :
    (denomMonoid c).map f = denomMonoid (f c) := by
  ext x
  constructor
  · rintro ⟨_, ⟨n, k, hn, rfl⟩, rfl⟩
    exact ⟨n, k, hn, by simp⟩
  · rintro ⟨n, k, hn, rfl⟩
    exact ⟨_, ⟨n, k, hn, rfl⟩, by simp⟩

theorem exists_nat_mul_mem {Ω : Type} [Field Ω] [CharZero Ω] (A : Subalgebra ℤ Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (A : Set Ω)) : ∃ N : ℕ, N ≠ 0 ∧ (N : Ω) * x ∈ A := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_nz, ?_⟩
    have : (r.den : Ω) * algebraMap ℚ Ω r = ((r.num : ℤ) : Ω) := by
      have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [this]
    exact intCast_mem A _
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (x + y) = (m : Ω) * ((n : Ω) * x) + (n : Ω) * ((m : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem A _) hnx) (mul_mem (natCast_mem A _) hmy)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (x * y) = ((n : Ω) * x) * ((m : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact mul_mem hnx hmy

theorem isLocalization_adjoin {Ω : Type} [Field Ω] [CharZero Ω] (A : Subalgebra ℤ Ω)
    (S : Subalgebra ℚ Ω) [Algebra A S] (hι : ∀ a : A, ((algebraMap A S a : S) : Ω) = a)
    (c : A) (N : ℕ) (hN : N ≠ 0) (h : Ω) (h0 : h ≠ 0) (hc : (c : Ω) = N * h)
    (hS : S = Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω))) :
    IsLocalization (denomMonoid c) S := by
  have hNΩ : (N : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hinv : h⁻¹ ∈ S := hS ▸ Algebra.subset_adjoin (Set.mem_insert _ _)
  have hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (algebraMap A S (n : A)) := by
    intro n hn
    have hnΩ : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
    refine IsUnit.of_mul_eq_one (algebraMap ℚ S (n : ℚ)⁻¹) (Subtype.ext ?_)
    have h1 : ((algebraMap ℚ S (n : ℚ)⁻¹ : S) : Ω) = (n : Ω)⁻¹ := by
      change algebraMap ℚ Ω (n : ℚ)⁻¹ = _
      simp
    rw [Subalgebra.coe_mul, hι, h1]
    simp [hnΩ]
  have hcu : IsUnit (algebraMap A S c) := by
    refine IsUnit.of_mul_eq_one (algebraMap ℚ S (N : ℚ)⁻¹ * ⟨h⁻¹, hinv⟩) (Subtype.ext ?_)
    have h1 : ((algebraMap ℚ S (N : ℚ)⁻¹ : S) : Ω) = (N : Ω)⁻¹ := by
      change algebraMap ℚ Ω (N : ℚ)⁻¹ = _
      simp
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hι, h1, hc]
    simp only [Subalgebra.coe_one]
    field_simp
  have hcmem : c ∈ denomMonoid c := ⟨1, 1, one_ne_zero, by simp⟩
  have hnmem : ∀ n : ℕ, n ≠ 0 → (n : A) ∈ denomMonoid c := fun n hn => ⟨n, 0, hn, by simp⟩
  have key : ∀ w ∈ Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω)),
      ∃ (a : A) (m : denomMonoid c), w * (((m : A)) : Ω) = a := by
    intro w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · refine ⟨(N : A), ⟨c, hcmem⟩, ?_⟩
        simp only [hc]
        push_cast
        field_simp
      · exact ⟨⟨x, hx⟩, 1, by simp⟩
    | algebraMap r =>
      refine ⟨(r.num : A), ⟨(r.den : A), hnmem _ r.den_nz⟩, ?_⟩
      have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
      push_cast
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    | add x y _ _ hx hy =>
      obtain ⟨a, m, hx⟩ := hx
      obtain ⟨b, l, hy⟩ := hy
      refine ⟨a * (l : A) + b * (m : A), m * l, ?_⟩
      push_cast
      rw [← hx, ← hy]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨a, m, hx⟩ := hx
      obtain ⟨b, l, hy⟩ := hy
      refine ⟨a * b, m * l, ?_⟩
      push_cast
      rw [← hx, ← hy]
      ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, k, hn, rfl⟩
    simp only [map_mul, map_pow]
    exact (hnat n hn).mul (hcu.pow k)
  · intro z
    obtain ⟨a, m, hz⟩ := key z (hS ▸ z.2)
    refine ⟨(a, m), Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, hι, hι]
    exact hz
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : Ω) = y := by rw [← hι, ← hι, hxy]
    rw [Subtype.ext this]

end GlobalTheory.CompanionTheory.Ar.LocalisedSmooth


open GlobalTheory.CompanionTheory.Ar.LocalisedSmooth in
theorem GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised
    (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (A₀ : Subalgebra ℤ Ω₀) (A₁ : Subalgebra ℤ Ω) (φ : A₀ →+* A₁)
    (hφ : ∀ a, ((φ a : A₁) : Ω) = algebraMap Ω₀ Ω a) (hsm : φ.Smooth)
    (h : Ω₀) (hh : h ∈ Algebra.adjoin ℚ (A₀ : Set Ω₀)) (h0 : h ≠ 0)
    (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω)
    (hS : S = Algebra.adjoin ℚ (insert h⁻¹ (A₀ : Set Ω₀)))
    (hT : T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (A₁ : Set Ω))) :
    ∃ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) ∧ ψ.Smooth := by
  obtain ⟨N, hN, hNh⟩ := exists_nat_mul_mem A₀ hh
  let c₀ : A₀ := ⟨(N : Ω₀) * h, hNh⟩
  have hc₀ : (c₀ : Ω₀) = N * h := rfl
  have hc₁ : ((φ c₀ : A₁) : Ω) = N * algebraMap Ω₀ Ω h := by
    rw [hφ, hc₀, map_mul, map_natCast]
  have hAS : ∀ a : A₀, (a : Ω₀) ∈ S := fun a =>
    hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ a.2)
  have hAT : ∀ a : A₁, (a : Ω) ∈ T := fun a =>
    hT ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ a.2)
  let ι₀ : A₀ →+* S := (A₀.val : A₀ →+* Ω₀).codRestrict S.toSubsemiring hAS
  let ι₁ : A₁ →+* T := (A₁.val : A₁ →+* Ω).codRestrict T.toSubsemiring hAT
  letI : Algebra A₀ S := ι₀.toAlgebra
  letI : Algebra A₁ T := ι₁.toAlgebra
  haveI L₀ : IsLocalization (denomMonoid c₀) S :=
    isLocalization_adjoin A₀ S (fun _ => rfl) c₀ N hN h h0 hc₀ hS
  haveI L₁ : IsLocalization (denomMonoid (φ c₀)) T :=
    isLocalization_adjoin A₁ T (fun _ => rfl) (φ c₀) N hN (algebraMap Ω₀ Ω h)
      ((map_ne_zero _).2 h0) hc₁ hT
  have hle : denomMonoid c₀ ≤ (denomMonoid (φ c₀)).comap φ := by
    intro x hx
    rw [Submonoid.mem_comap, ← map_denomMonoid]
    exact ⟨x, hx, rfl⟩
  let ψ : S →+* T := IsLocalization.map T φ hle
  have hψ : ∀ a : A₀, ψ (algebraMap A₀ S a) = algebraMap A₁ T (φ a) := fun a =>
    IsLocalization.map_eq hle a
  refine ⟨ψ, ?_, ?_⟩
  · have : ((T.val : T →+* Ω).comp ψ) = (algebraMap Ω₀ Ω).comp (S.val : S →+* Ω₀) := by
      refine IsLocalization.ringHom_ext (denomMonoid c₀) (RingHom.ext fun a => ?_)
      change ((ψ (algebraMap A₀ S a) : T) : Ω) = algebraMap Ω₀ Ω (a : Ω₀)
      rw [hψ]
      exact hφ a
    exact fun s => RingHom.congr_fun this s
  · letI : Algebra S T := ψ.toAlgebra
    letI : Algebra A₀ A₁ := φ.toAlgebra
    letI : Algebra A₀ T := ((algebraMap A₁ T).comp φ).toAlgebra
    haveI : IsScalarTower A₀ A₁ T := .of_algebraMap_eq' rfl
    haveI : IsScalarTower A₀ S T := .of_algebraMap_eq fun a => (hψ a).symm
    have hsub : Algebra.algebraMapSubmonoid A₁ (denomMonoid c₀) = denomMonoid (φ c₀) :=
      map_denomMonoid φ c₀
    haveI : IsLocalization (Algebra.algebraMapSubmonoid A₁ (denomMonoid c₀)) T := by
      rw [hsub]; exact L₁
    haveI P : Algebra.IsPushout A₀ A₁ S T :=
      Algebra.isPushout_of_isLocalization (denomMonoid c₀) S A₁ T
    exact RingHom.Smooth.isStableUnderBaseChange A₀ A₁ S T hsm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothMapLocalizationCompatStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_map_localization_compat : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (A₀ : Subalgebra ℤ Ω₀)
    (A₁ : Subalgebra ℤ Ω) (φ : A₀ →+* A₁), (∀ a, ((φ a : A₁) : Ω) = algebraMap Ω₀ Ω a) → φ.Smooth →
    ∀ h : Ω₀, h ∈ Algebra.adjoin ℚ (A₀ : Set Ω₀) → h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
      S = Algebra.adjoin ℚ (insert h⁻¹ (A₀ : Set Ω₀)) →
      T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (A₁ : Set Ω)) →
      ∃ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) ∧ ψ.Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | exact GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelAddedCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.SncPull
open GlobalTheory.CompanionTheory.Ar.SncRefine

theorem adjoin_insert_eq {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : Ω) :
    Algebra.adjoin ℚ (insert t ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω) : Set Ω)) =
      Algebra.adjoin ℚ (insert t (Set.range (bratio y c))) := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro b (rfl | hb)
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · have h : Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) ≤
          (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).restrictScalars ℤ := Algebra.adjoin_le (by
        rintro _ ⟨d, rfl⟩
        exact seg_ratio_mem y c (Algebra.adjoin ℚ (insert t (Set.range (bratio y c)))).toSubring
          (fun p => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)) d)
      exact h hb
  · refine Algebra.adjoin_mono (Set.insert_subset_insert ?_)
    rintro _ ⟨p, rfl⟩
    obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩

theorem map_mem_adjoin {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    {W : Set Ω₀} {W' : Set Ω} (hW : ∀ w ∈ W, algebraMap Ω₀ Ω w ∈ W') {b : Ω₀} (hb : b ∈ Algebra.adjoin ℚ W) :
    algebraMap Ω₀ Ω b ∈ Algebra.adjoin ℚ W' := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hW x hx)
  | algebraMap r =>
    have : algebraMap Ω₀ Ω (algebraMap ℚ Ω₀ r) = algebraMap ℚ Ω r := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_cover {R : Type} [CommRing R] (G : R → Prop) (h : ∀ P : Ideal R, P.IsPrime → ∃ t, t ∉ P ∧ G t) :
    ∃ (m : ℕ) (f a : Fin m → R), ∑ l, a l * f l = 1 ∧ ∀ l, G (f l) := by
  classical
  have hs : Ideal.span {t | G t} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨t, ht, hG⟩ := h M hM.isPrime
    exact ht (hle (Ideal.subset_span hG))
  have h1 : (1 : R) ∈ Ideal.span {t | G t} := hs ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.1 h1
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun l => (e l : R), fun l => c (e l), ?_, fun l => hc (e l).2⟩
  rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact Equiv.sum_comp e fun x : c.support => c x • (x : R)

theorem isSncModel_pull : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (e : ℕ) (bd : Ideal (MRing J)) (I : Type) [Fintype I] (u : I → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) → Smooth f →
    AlgebraicIndependent Ω₀ u → IntermediateField.adjoin Ω₀ (Set.range u) = ⊤ →
    Cmp.IsSncModel y e bd →
    Cmp.IsSncModel (addY y x') (e + Fintype.card I) (bd.map (MvPolynomial.rename (addV J N))) := by
  classical
  intro X X' Ω₀ Ω _ _ _ _ _ ξ ξ' f K _ J _ y N x' e bd I _ u hq hq' tie tie' hd hsm hu hadj hsnc c₁ hc₁
  let c : (k : K) → J k := fun k => c₁ (Sum.inr k)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h =>
    hc₁ (Sum.inr k) (show algebraMap Ω₀ Ω (y ⟨k, c k⟩) = 0 by rw [h, map_zero])
  have hv : ∀ p, algebraMap Ω₀ Ω (bratio y c p) = bratio (addY y x') c₁ (addV J N p) := fun p => map_div₀ _ _ _
  have hxc : seg y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hxc₁ : seg (addY y x') c₁ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc₁ k
  have hblk : ∀ p, bratio (addY y x') c₁ p ∈
      Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁) := fun p => by
    obtain ⟨d, hd⟩ := exists_seg_ratio (addY y x') c₁ hc₁ p
    rw [hd]
    exact Algebra.subset_adjoin ⟨d, rfl⟩
  obtain ⟨φ, hφ, hφs⟩ := GlobalTheory.T.dominant_smooth_map_coords X X' Ω₀ Ω ξ ξ' f (algebraMap Ω₀ Ω) _ _ (seg y) (seg (addY y x'))
    hq hq' tie tie' hd hsm c c₁ hxc hxc₁ (fun d => by
      have e1 : seg y d / seg y c = ∏ k, bratio y c ⟨k, d k⟩ := (Finset.prod_div_distrib _ _).symm
      rw [e1, map_prod]
      refine prod_mem fun k _ => ?_
      rw [hv]
      exact hblk _)
  obtain ⟨m, f₀, a₀, hf, ha, hsum, H⟩ := hsnc c hc
  have hfin := GlobalTheory.T.kaehler_rank_transcendence_degree Ω₀ Ω I u hu hadj
  have hW : ∀ w ∈ Set.range (bratio y c), algebraMap Ω₀ Ω w ∈ Set.range (bratio (addY y x') c₁) := by
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (hv p).symm⟩
  let R₁ := Algebra.adjoin ℚ (Set.range (bratio (addY y x') c₁))
  have hfr : ∀ (A : Subalgebra ℤ Ω₀) (S : Subalgebra ℚ Ω₀), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω₀, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω₀ := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hfr₁ : ∀ (A : Subalgebra ℤ Ω) (S : Subalgebra ℚ Ω), (∀ a ∈ A, a ∈ S) →
      (∀ a : Ω, ∃ s ∈ A, ∃ t ∈ A, t ≠ 0 ∧ a = s / t) → IsFractionRing S Ω := fun A S hAS h =>
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨s, hs, t, ht, -, rfl⟩ := h z
      exact ⟨⟨s, hAS s hs⟩, ⟨t, hAS t ht⟩, rfl⟩
  have hloc : ∀ P : Ideal R₁, P.IsPrime → ∃ t : R₁, t ∉ P ∧ ((t : Ω) ≠ 0 → ∀ S' : Subalgebra ℚ Ω,
      S' = Algebra.adjoin ℚ (insert (t : Ω)⁻¹ (Set.range (bratio (addY y x') c₁))) →
      Algebra.Smooth ℚ S' ∧ ∃ (z' : Fin (e + Fintype.card I) → S') (n' : ℕ), n' ≤ e + Fintype.card I ∧
        LinearIndependent S' (fun i => KaehlerDifferential.D ℚ S' (z' i)) ∧
        Submodule.span S' (Set.range fun i => KaehlerDifferential.D ℚ S' (z' i)) = ⊤ ∧
        ∀ q : Ideal S', q.IsPrime →
          ((∀ g ∈ bd.map (MvPolynomial.rename (addV J N)), ∀ s : S',
              (s : Ω) = MvPolynomial.aeval (bratio (addY y x') c₁) g → s ∈ q) ↔
            ∃ i : Fin (e + Fintype.card I), (i : ℕ) < n' ∧ z' i ∈ q)) := by
    intro P hP
    let fl : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (f₀ l), map_mem_adjoin hW (hf l)⟩
    let al : Fin m → R₁ := fun l => ⟨algebraMap Ω₀ Ω (a₀ l), map_mem_adjoin hW (ha l)⟩
    have hone : ∑ l, al l * fl l = 1 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      show ∑ l, algebraMap Ω₀ Ω (a₀ l) * algebraMap Ω₀ Ω (f₀ l) = 1
      simp only [← map_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hsum, map_one]
    obtain ⟨l, hl⟩ : ∃ l, fl l ∉ P := by
      by_contra hcon
      push Not at hcon
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hone ▸ Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hcon l)))
    have h0 : f₀ l ≠ 0 := fun h => hl (by
      have : fl l = 0 := Subtype.ext (by show algebraMap Ω₀ Ω (f₀ l) = 0; rw [h, map_zero])
      rw [this]
      exact P.zero_mem)
    obtain ⟨hSm, z, n, hn, hli, hspan, hbd⟩ := H l h0 _ rfl
    have hle₀ : Algebra.adjoin ℚ (Set.range (bratio y c)) ≤ Algebra.adjoin ℚ
        ((Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c) : Subalgebra ℤ Ω₀) : Set Ω₀) :=
      Algebra.adjoin_le (by
        rintro _ ⟨p, rfl⟩
        obtain ⟨d, hd⟩ := exists_seg_ratio y c hc p
        rw [hd]
        exact Algebra.subset_adjoin (Algebra.subset_adjoin ⟨d, rfl⟩))
    obtain ⟨ψ, hψ, hψs⟩ := GlobalTheory.T.smooth_map_localization_compat Ω₀ Ω _ _ φ hφ hφs (f₀ l) (hle₀ (hf l)) h0
      (Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))))
      (Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))))
      (adjoin_insert_eq y c hc _).symm (adjoin_insert_eq (addY y x') c₁ hc₁ _).symm
    have hA₀ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg y d / seg y c),
        a ∈ Algebra.adjoin ℚ (insert (f₀ l)⁻¹ (Set.range (bratio y c))) := fun a ha' => by
      rw [← adjoin_insert_eq y c hc]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    have hA₁ : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun d => seg (addY y x') d / seg (addY y x') c₁),
        a ∈ Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω (f₀ l))⁻¹ (Set.range (bratio (addY y x') c₁))) := fun a ha' => by
      rw [← adjoin_insert_eq (addY y x') c₁ hc₁]
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha')
    obtain ⟨t, ht, hG⟩ := GlobalTheory.T.kaehler_rank_localization_bound Ω₀ Ω _ _ (bratio y c) (bratio (addY y x') c₁) (addV J N) hv e _ bd hfin (f₀ l) h0 _ _ rfl rfl
      ψ hψ hψs (hfr _ _ hA₀ (GlobalTheory.T.fraction_field_coords_generated X Ω₀ ξ _ (seg y) tie c hxc))
      (hfr₁ _ _ hA₁ (GlobalTheory.T.fraction_field_coords_generated X' Ω ξ' _ (seg (addY y x')) tie' c₁ hxc₁)) hSm z n hn hli hspan hbd P hP (fl l) rfl hl
    exact ⟨t, ht, fun _ => hG⟩
  obtain ⟨m', f', a', hs', hG⟩ := exists_cover _ hloc
  refine ⟨m', fun l => (f' l : Ω), fun l => (a' l : Ω), fun l => (f' l).2, fun l => (a' l).2, ?_, fun l hl S' hS' => ?_⟩
  · have := congrArg (Subtype.val) hs'
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this
  · obtain ⟨h1, z', n', h2, h3, h4, h5⟩ := hG l hl S' hS'
    exact ⟨h1, z', n', h2, h3, h4, h5⟩

end GlobalTheory.CompanionTheory.Ar.SncPull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelAddedCoordsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_model_added_coords : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (e : ℕ) (bd : Ideal (MRing J)) (I : Type) [Fintype I] (u : I → Ω),
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) → Smooth f →
    AlgebraicIndependent Ω₀ u → IntermediateField.adjoin Ω₀ (Set.range u) = ⊤ →
    Cmp.IsSncModel y e bd →
    Cmp.IsSncModel (addY y x') (e + Fintype.card I) (bd.map (MvPolynomial.rename (addV J N))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncPull.isSncModel_pull | exact GlobalTheory.CompanionTheory.Ar.SncPull.isSncModel_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.SncPull.isSncModel_pull <;> assumption)
end
