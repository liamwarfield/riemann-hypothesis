module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
public import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBound
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Frames

open GlobalTheory.CompanionTheory.Ar

variable {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {i : Ω₀ →+* Ω} {Li Li₀ : Type} [AddCommGroup Li] [Module Ω Li]
  [AddCommGroup Li₀] [Module Ω₀ Li₀] {ι : Li₀ →+ Li}

theorem linearIndependent_comp_basis (h : IsExtOver i ι) {K : Type} (B : Module.Basis K Ω₀ Li₀) :
    LinearIndependent Ω fun k => ι (B k) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  have e : s ≃ Fin s.card := s.equivFin
  have hb : LinearIndependent Ω₀ (fun k : Fin s.card => B (e.symm k : K)) :=
    B.linearIndependent.comp (fun k => (e.symm k : K)) (Subtype.val_injective.comp e.symm.injective)
  have h3 := (h.2 s.card _ hb).comp e e.injective
  convert h3 using 1
  funext k
  simp

theorem exists_dual_ext (h : IsExtOver i ι) (hs : Submodule.span Ω (Set.range ι) = ⊤)
    (φ : Module.Dual Ω₀ Li₀) : ∃ φ' : Module.Dual Ω Li, ∀ e, φ' (ι e) = i (φ e) := by
  classical
  let B := Module.Basis.ofVectorSpace Ω₀ Li₀
  have hli : LinearIndependent Ω fun k => ι (B k) := linearIndependent_comp_basis h B
  have hmem : ∀ e : Li₀, ι e ∈ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    intro e
    have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [h.1]; exact Submodule.smul_mem _ _ hx
  have hsp : ⊤ ≤ Submodule.span Ω (Set.range fun k => ι (B k)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    exact hmem e
  let B' := Module.Basis.mk hli hsp
  refine ⟨B'.constr Ω (fun k => i (φ (B k))), fun e => ?_⟩
  have he : e ∈ Submodule.span Ω₀ (Set.range B) := by rw [B.span_eq]; exact Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    have hk : ι (B k) = B' k := (Module.Basis.mk_apply hli hsp k).symm
    rw [hk, Module.Basis.constr_basis]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul a x _ hx =>
    rw [h.1]
    simp only [map_smul, hx, smul_eq_mul, map_mul]

theorem two_frames (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li]
    [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li) (hext : IsExtOver i ι)
    (hs : Submodule.span Ω (Set.range ι) = ⊤) (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ)
    (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω)
    (m : Ω₀) (hL : Submodule.span W L = Submodule.span W (ι '' L₀))
    (hT : ∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) (hTb : ∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j))
    (hm : ∀ j, m • b₀ j ∈ L₀) (hπ : ∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0)
    (hint : ∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) (hκ : ∀ j, κ • b j ∈ L)
    (hb : ∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) :
    (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧
      ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  classical
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have hin : ι (m • b₀ j) ∈ Submodule.span W L := by
      rw [hL]; exact Submodule.subset_span ⟨_, hm j, rfl⟩
    have key : ∀ x ∈ Submodule.span W L, T x ∈ Submodule.span W (Set.range b) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hT y hy
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy =>
        rw [Subring.smul_def, map_smul]
        have hw := Submodule.smul_mem _ w hy
        rwa [Subring.smul_def] at hw
    have hj := key _ hin
    rwa [hext.1, map_smul, hTb, smul_smul, mul_comm] at hj
  · have hv : κ • b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a)) :=
      Submodule.smul_mem _ κ (hb j)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hv
    have hcW : ∀ a, i m * c a ∈ W := by
      intro a
      obtain ⟨ψ, hψ⟩ := exists_dual_ext hext hs (π₀ a)
      have hψv : ψ (κ • b j) = c a := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hc, map_sum, Finset.sum_eq_single a]
        · rw [map_smul, hψ, hπ, if_pos rfl, map_one, smul_eq_mul, mul_one]
        · intro x _ hx
          rw [map_smul, hψ, hπ, if_neg (Ne.symm hx), map_zero, smul_zero]
        · intro ha; exact absurd (Finset.mem_univ a) ha
      have hspan : κ • b j ∈ Submodule.span W (ι '' L₀) := by
        rw [← hL]; exact Submodule.subset_span (hκ j)
      have key : ∀ x ∈ Submodule.span W (ι '' L₀), i m * ψ x ∈ W := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨e, he, rfl⟩ := hy
          rw [hψ, ← map_mul]; exact hint a e he
        | zero => simp
        | add y z _ _ hy hz => rw [map_add (f := _), mul_add]; exact W.add_mem hy hz
        | smul w y _ hy =>
          rw [Subring.smul_def, map_smul, smul_eq_mul, mul_left_comm]
          exact W.mul_mem w.2 hy
      rw [← hψv]; exact key _ hspan
    rw [mul_smul, ← hc, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [smul_smul]
    have ha := Submodule.smul_mem (Submodule.span W (Set.range fun a => ι (b₀ a))) (⟨_, hcW a⟩ : W)
      (Submodule.subset_span ⟨a, rfl⟩)
    rwa [Subring.smul_def] at ha

end GlobalTheory.CompanionTheory.Ar.Frames
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBoundStatement
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_span_projection_bound : ∀ (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li), IsExtOver i ι → Submodule.span Ω (Set.range ι) = ⊤ → ∀ (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ) (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω) (m : Ω₀), Submodule.span W L = Submodule.span W (ι '' L₀) → (∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) → (∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j)) → (∀ j, m • b₀ j ∈ L₀) → (∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0) → (∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) → (∀ j, κ • b j ∈ L) → (∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) → (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧ ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Frames.two_frames | exact GlobalTheory.CompanionTheory.Ar.Frames.two_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Frames.two_frames <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericField
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericField
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

theorem genU_diag (s : S) (k : Fin (r s)) : genU Ω r s k k = 1 := by
  simp [genU]

theorem genU_above (s : S) (l k : Fin (r s)) (h : l < k) : genU Ω r s l k = 0 := by
  have h1 : ¬ k < l := not_lt.mpr h.le
  simp [genU, h1, h.ne]

theorem genU_below (s : S) (l k : Fin (r s)) (h : k < l) :
    genU Ω r s l k = algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r)
      (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩) := by
  simp only [genU, dif_pos h]

theorem genU_det (s : S) : (genU Ω r s).det = 1 := by
  have hlow : (genU Ω r s).IsLowerTriangular := by
    intro i j hij
    exact genU_above s i j (by simpa using hij)
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  exact Finset.prod_eq_one fun i _ => genU_diag s i

theorem genField_adjoin_eq_top :
    IntermediateField.adjoin Ω
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) = ⊤ := by
  set K := IntermediateField.adjoin Ω
    (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => genU Ω r q.1 q.2.1 q.2.2) with hK
  have hX : ∀ i : GenIx r,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X i) ∈ K := by
    intro i
    obtain ⟨s, ⟨⟨l, k⟩, h⟩⟩ := i
    apply IntermediateField.subset_adjoin
    exact ⟨⟨s, (l, k)⟩, genU_below s l k h⟩
  have hP : ∀ p : MvPolynomial (GenIx r) Ω,
      algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K := by
    intro p
    refine MvPolynomial.induction_on
      (motive := fun p => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) p ∈ K) p ?_ ?_ ?_
    · intro a
      have h1 := IsScalarTower.algebraMap_apply Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r) a
      rw [MvPolynomial.algebraMap_eq] at h1
      rw [← h1]
      exact IntermediateField.algebraMap_mem K a
    · intro p q hp hq
      rw [map_add (f := _)]
      exact add_mem hp hq
    · intro p n hp
      rw [map_mul]
      exact mul_mem hp (hX n)
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial (GenIx r) Ω) z
  exact div_mem (hP a) (hP b)

theorem linearIndependent_one_tmul {ι : Type} {v : ι → E} (hv : LinearIndependent Ω v) :
    LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (v k) := by
  simpa only [TensorProduct.mk_apply] using
    Module.Flat.linearIndependent_one_tmul (S := GenField Ω r) hv

theorem genB_linearIndependent (c : ∀ s, Fin (r s) → E) (s : S)
    (h : LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c s k)) :
    LinearIndependent (GenField Ω r) (genB (Ω := Ω) c s) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have hz : ∀ l, ∑ k, genU Ω r s l k * g k = 0 := by
    refine h (fun l => ∑ k, genU Ω r s l k * g k) ?_
    rw [← hg]
    simp only [genB, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]
  have hv : Matrix.mulVec (genU Ω r s) g = 0 := by
    ext l
    exact hz l
  have hU : IsUnit (genU Ω r s).det := by
    rw [genU_det]
    exact isUnit_one
  have hg0 : g = 0 := by
    calc g = Matrix.mulVec ((genU Ω r s)⁻¹ * genU Ω r s) g := by
          rw [Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
      _ = Matrix.mulVec (genU Ω r s)⁻¹ (Matrix.mulVec (genU Ω r s) g) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  intro k
  simp [hg0]

theorem genB_isGenericFlag : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type)
    (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E),
    (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) →
    IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  intro Ω hΩ E hE hEm S r V c hc
  unfold IsGenericFlag
  have hli : ∀ σ, LinearIndependent (GenField Ω r)
      fun k => TensorProduct.mk Ω (GenField Ω r) E 1 (c σ k) :=
    fun σ => linearIndependent_one_tmul (r := r) (hc σ).1
  refine ⟨c, genU Ω r, hc, ?_, fun σ => hli σ, fun σ => genB_linearIndependent c σ (hli σ),
    fun σ k => genU_diag σ k, fun σ l k h => genU_above σ l k h, fun σ i => rfl, ?_, Nat.one_pos, ?_⟩
  · intro a e
    simp only [LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  · have hai : AlgebraicIndependent Ω (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q)) :=
      (MvPolynomial.algebraicIndependent_X (GenIx r) Ω).map'
        (f := IsScalarTower.toAlgHom Ω (MvPolynomial (GenIx r) Ω) (GenField Ω r))
        (IsFractionRing.injective (MvPolynomial (GenIx r) Ω) (GenField Ω r))
    have hfam : (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} =>
        genU Ω r q.1 q.2.1.1 q.2.1.2) =
        fun q => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q) :=
      funext fun q => genU_below q.1 q.2.1.1 q.2.1.2 q.2.2
    rw [hfam]
    exact hai
  · rw [genField_adjoin_eq_top]
    exact IntermediateField.finrank_top

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericFieldStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_over_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E), (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemRegAtOfCodimOne
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemRangeOfIntegralAtHeightOneOver
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_range_of_integral_at_heightOne_over :
    ∀ (B K : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
      [Field K] [Algebra B K] [IsFractionRing B K] (ϖ : B) (x : K), ϖ ≠ 0 →
      (∃ (N : ℕ) (b : B), algebraMap B K b = algebraMap B K ϖ ^ N * x) →
      (∀ P : Ideal B, P.IsPrime → P.height = 1 → ϖ ∈ P →
        ∃ (b c : B), c ∉ P ∧ algebraMap B K b = algebraMap B K c * x) →
      ∃ b : B, algebraMap B K b = x := by
  intro B K _ _ _ _ _ _ _ ϖ x _ hN hP
  obtain ⟨N, b, hb⟩ := hN
  obtain ⟨y, hy⟩ := GroundTheory.Arith.Toric.mem_range_of_forall_height_one (A := B) (K := K) x
    (fun p hp h1 => by
      by_cases hm : ϖ ∈ p
      · obtain ⟨b', c, hc, hbc⟩ := hP p hp h1 hm
        exact ⟨b', c, hc, by rw [hbc, mul_comm]⟩
      · exact ⟨b, ϖ ^ N, fun h => hm (hp.mem_of_pow_mem N h), by rw [hb, map_pow, mul_comm]⟩)
  exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_point_of_prime {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (p : Cpt ξ) (P : Ideal (regAt ξ p)) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ringKrullDim (X.presheaf.stalk q.1) = (P.height : WithBot ℕ∞) ∧
      ∀ a ∈ regAt ξ q, ∃ s t : regAt ξ p, s ∉ P ∧ a * s = t := by
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := p.1) (U := ⊤) trivial
  have hg : genPt ξ ∈ U := p.2.mem_open U.2 hp
  let e := RegAtRing.stalkEquiv h p
  let P' : Ideal (X.presheaf.stalk p.1) := P.comap (e : X.presheaf.stalk p.1 →+* regAt ξ p)
  have hP' : P'.IsPrime := Ideal.comap_isPrime _ _
  letI algP := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hp⟩ : U)
  have localization₂ := hU.isLocalization_stalk ⟨p.1, hp⟩
  let 𝔮 : Ideal Γ(X, U) := P'.comap (algebraMap Γ(X, U) (X.presheaf.stalk p.1))
  have h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  let y : PrimeSpectrum Γ(X, U) := ⟨𝔮, h𝔮⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this

  have hsp : hU.fromSpec y ⤳ p.1 := by
    have hle : y ≤ hU.primeIdealOf ⟨p.1, hp⟩ := by
      change 𝔮 ≤ (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal
      rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk p.1)
        (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP'.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this

  have hgy : genPt ξ ⤳ hU.fromSpec y := by
    have hle : hU.primeIdealOf ⟨genPt ξ, hg⟩ ≤ y := by
      change (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal ≤ 𝔮
      intro r hr
      letI algG := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, hg⟩ : U)
      have locG := hU.isLocalization_stalk ⟨genPt ξ, hg⟩
      have hnu : ¬ IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) r) := by
        rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (genPt ξ))
          (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal] at hr
        exact (IsLocalRing.mem_maximalIdeal _).1 hr
      have hz : (Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r) = 0 := by
        by_contra hne
        obtain ⟨w, hw⟩ := h.bij.2 ((Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r))⁻¹
        apply hnu
        refine IsUnit.of_mul_eq_one w (h.bij.1 ?_)
        erw [map_mul, hw, map_one]
        exact mul_inv_cancel₀ hne
      have hz' : X.presheaf.germ U p.1 hp r = 0 := by
        apply h.inj p
        rw [RegAtRing.genMap_germ p U hp hg, hz, map_zero]
      change algebraMap Γ(X, U) (X.presheaf.stalk p.1) r ∈ P'
      erw [hz']
      exact P'.zero_mem
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this
  letI algY : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec y, hyU⟩ : U)
  have locY : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hyU
  have locY' : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) 𝔮 := locY
  refine ⟨⟨hU.fromSpec y, hgy⟩, hsp, ?_, ?_⟩
  · have h1 : ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = (𝔮.height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (X.presheaf.stalk (hU.fromSpec y))
    have h2 : 𝔮.height = P'.height :=
      IsLocalization.height_under (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl P'
    have h3 : P'.height = P.height := RingEquiv.height_comap e P
    change ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = _
    rw [h1, h2, h3]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨⟨r, t⟩, he⟩ := IsLocalization.surj y.asIdeal.primeCompl
      (S := X.presheaf.stalk (hU.fromSpec y)) x
    have he' : x * (X.presheaf.germ U (hU.fromSpec y) hyU).hom t.1 =
        (X.presheaf.germ U (hU.fromSpec y) hyU).hom r := he
    have hgt := RegAtMono.genMap_germ_eq ξ p ⟨hU.fromSpec y, hgy⟩ hsp U hp hyU
    refine ⟨e ((X.presheaf.germ U p.1 hp).hom t.1), e ((X.presheaf.germ U p.1 hp).hom r), ?_, ?_⟩
    · exact t.2
    · change genMap ξ ⟨hU.fromSpec y, hgy⟩ x * genMap ξ p ((X.presheaf.germ U p.1 hp).hom t.1) =
        genMap ξ p ((X.presheaf.germ U p.1 hp).hom r)
      rw [← hgt, ← hgt, ← map_mul]
      exact congrArg _ he'

theorem mem_regAt_of_codim_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → NormalCpt ξ → ∀ (p : Cpt ξ) (a : Ω),
    (∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → a ∈ regAt ξ q) →
    a ∈ regAt ξ p := by
  intro X Ω _ ξ _ h hn p a ha
  obtain ⟨hfr, hno, -⟩ := RegAtRing.regAt_ring X Ω ξ h p
  have : IsFractionRing (regAt ξ p) Ω := hfr
  have : IsNoetherianRing (regAt ξ p) := hno inferInstance
  have : IsIntegrallyClosed (regAt ξ p) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, hn p x hx⟩, rfl⟩
  obtain ⟨t, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd1 : algebraMap (regAt ξ p) Ω d ≠ 0 := by
    simpa using hd0
  obtain ⟨b, hb⟩ := mem_range_of_integral_at_heightOne_over (regAt ξ p) Ω d
    (algebraMap (regAt ξ p) Ω t / algebraMap (regAt ξ p) Ω d) hd0
    ⟨1, t, by field_simp⟩
    (fun P hP h1 _ => by
      obtain ⟨q, hq, hdim, hiff⟩ := exists_point_of_prime h p P hP
      have hmem := ha q hq (by rw [hdim]; simp [h1])
      obtain ⟨s, u, hs, hsu⟩ := hiff _ hmem
      exact ⟨u, s, hs, by rw [mul_comm]; exact hsu.symm⟩)
  rw [← hb]
  exact b.2

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpan
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.IntClGens

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)

theorem twist_mem {c j : κ} (hc : x c ≠ 0) {b : Ω} (hb : b ∈ chRing o x c) :
    ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * b ∈ chRing o x j := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  induction hb using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have key : x c / x j * (x l / x c) = x l / x j := by
      rw [div_mul_div_comm, mul_comm (x j), mul_div_mul_left _ _ hc]
    have : (x c / x j) ^ (1 + k) * (x l / x c) = (x c / x j) ^ k * (x l / x j) := by
      rw [← key]; ring
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Algebra.subset_adjoin ⟨l, rfl⟩)
  | algebraMap r =>
    exact ⟨0, fun m _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Subalgebra.algebraMap_mem _ r)⟩
  | add y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    exact ⟨max e1 e2, fun m hm => by
      rw [mul_add]
      exact Subalgebra.add_mem _ (h1 m (le_of_max_le_left hm)) (h2 m (le_of_max_le_right hm))⟩
  | mul y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    refine ⟨e1 + e2, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : (x c / x j) ^ (e1 + e2 + k) * (y * z) =
        ((x c / x j) ^ (e1 + k) * y) * ((x c / x j) ^ e2 * z) := by ring
    rw [this]
    exact Subalgebra.mul_mem _ (h1 _ (by omega)) (h2 _ le_rfl)

theorem twist_integral {c j : κ} (hc : x c ≠ 0) {a : Ω} (ha : IsIntegral (chRing o x c) a) :
    ∃ e : ℕ, ∀ m, e ≤ m → IsIntegral (chRing o x j) ((x c / x j) ^ m * a) := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  obtain ⟨p, hmon, hp⟩ := ha
  have hE : ∀ i, ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * (p.coeff i : Ω) ∈ chRing o x j :=
    fun i => twist_mem x hc (p.coeff i).2
  choose E hE using hE
  obtain ⟨E0, hE0⟩ : ∃ E0, ∀ i ≤ p.natDegree, E i ≤ E0 :=
    ⟨(Finset.range (p.natDegree + 1)).sup E, fun i hi => Finset.le_sup (Finset.mem_range.2 (by omega))⟩
  have hn' : (p.map (algebraMap (chRing o x c) Ω)).natDegree = p.natDegree := hmon.natDegree_map _
  have hqm : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).Monic :=
    (Polynomial.monic_scaleRoots_iff _).2 (hmon.map _)
  have hq0 : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).eval
      ((x c / x j) ^ E0 * a) = 0 := by
    have h1 : (p.map (algebraMap (chRing o x c) Ω)).eval₂ (RingHom.id Ω) a = 0 := by
      rw [Polynomial.eval₂_map, RingHom.id_comp]; exact hp
    have := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id Ω) (s := (x c / x j) ^ E0) h1
    simpa [Polynomial.eval₂_id] using this
  have hlift : (p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0) ∈
      Polynomial.lifts (algebraMap (chRing o x j) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    have hmem : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).coeff i ∈
        chRing o x j := by
      rw [Polynomial.coeff_scaleRoots, hn', Polynomial.coeff_map]
      rcases lt_trichotomy i p.natDegree with hi | hi | hi
      · have h1 : E i ≤ E0 := hE0 i hi.le
        have h2 : 1 ≤ p.natDegree - i := by omega
        have hle : E i ≤ E0 * (p.natDegree - i) :=
          calc E i ≤ E0 := h1
            _ = E0 * 1 := (mul_one _).symm
            _ ≤ E0 * (p.natDegree - i) := Nat.mul_le_mul_left _ h2
        rw [← pow_mul, mul_comm]
        exact hE i _ hle
      · rw [hi, Nat.sub_self, pow_zero, mul_one, hmon.coeff_natDegree, map_one]
        exact Subalgebra.one_mem _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
        exact Subalgebra.zero_mem _
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q0, hq0map, -, hq0m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hqm
  have hint : IsIntegral (chRing o x j) ((x c / x j) ^ E0 * a) :=
    ⟨q0, hq0m, by rw [← Polynomial.eval_map, hq0map]; exact hq0⟩
  refine ⟨E0, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have : (x c / x j) ^ (E0 + k) * a = (x c / x j) ^ k * ((x c / x j) ^ E0 * a) := by ring
  rw [this]
  have htk : IsIntegral (chRing o x j) ((x c / x j) ^ k) :=
    isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _ ht k⟩ : chRing o x j))
  exact htk.mul hint

theorem exists_twisted_gens : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω), (∀ c, x c ≠ 0 → Module.Finite (chRing o x c) (integralClosure (chRing o x c) Ω)) →
    ∃ (d n : ℕ) (z : κ ⊕ Fin n → Ω), (∀ c, z (Sum.inl c) = x c ^ d) ∧ ∀ c, x c ≠ 0 → ∀ a : Ω,
      IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d) := by
  intro o _ Ω _ _ κ _ x hfin
  have hgen : ∀ c, ∃ (N : ℕ) (g : Fin N → Ω), (∀ k, x c ≠ 0 ∧ IsIntegral (chRing o x c) (g k)) ∧
      (x c ≠ 0 → ∀ a, IsIntegral (chRing o x c) a → a ∈ Submodule.span (chRing o x c) (Set.range g)) := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨0, Fin.elim0, fun k => k.elim0, fun h => absurd hc h⟩
    · haveI := hfin c hc
      obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin (R := chRing o x c) (M := integralClosure (chRing o x c) Ω)
      refine ⟨N, fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω),
        fun k => ⟨hc, (s k).2⟩, fun _ a ha => ?_⟩
      have hle : Submodule.map (integralClosure (chRing o x c) Ω).val.toLinearMap
          (Submodule.span (chRing o x c) (Set.range s)) ≤
          Submodule.span (chRing o x c) (Set.range fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω)) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨k, rfl⟩
        exact Submodule.subset_span ⟨k, rfl⟩
      rw [hs] at hle
      exact hle (Submodule.mem_map_of_mem (p := ⊤) (f := (integralClosure (chRing o x c) Ω).val.toLinearMap)
        (r := ⟨a, ha⟩) Submodule.mem_top)
  choose N g hg using hgen
  obtain ⟨M, ⟨eI⟩⟩ := Finite.exists_equiv_fin (Σ c, Fin (N c))
  have hD : ∀ (i : Σ c, Fin (N c)) (j : κ), ∃ e : ℕ, ∀ m, e ≤ m →
      IsIntegral (chRing o x j) ((x i.1 / x j) ^ m * g i.1 i.2) :=
    fun i j => twist_integral x ((hg i.1).1 i.2).1 ((hg i.1).1 i.2).2
  choose D hD using hD
  obtain ⟨d, hd⟩ := Finite.exists_le (fun q : (Σ c, Fin (N c)) × κ => D q.1 q.2)
  refine ⟨d, M, Sum.elim (fun c => x c ^ d) (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2),
    fun c => rfl, fun c hc a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · refine Submodule.span_mono ?_ ((hg c).2 hc a ha)
    rintro _ ⟨k, rfl⟩
    refine ⟨Sum.inr (eI ⟨c, k⟩), ?_⟩
    have he : eI.symm (eI ⟨c, k⟩) = ⟨c, k⟩ := eI.symm_apply_apply _
    simp only [Sum.elim_inr]
    rw [he]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hc)
  · have hsub : (Set.range fun k => (Sum.elim (fun c => x c ^ d)
        (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2) k : Ω) / x c ^ d) ⊆
        ((integralClosure (chRing o x c) Ω).toSubmodule : Set Ω) := by
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
      rcases k with j | k
      · simp only [Sum.elim_inl]
        rw [← div_pow]
        exact isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _
          (Algebra.subset_adjoin ⟨j, rfl⟩ : x j / x c ∈ chRing o x c) d⟩ : chRing o x c))
      · simp only [Sum.elim_inr]
        rw [mul_div_right_comm, ← div_pow]
        exact hD (eI.symm k) c d (hd (eI.symm k, c))
    have := Submodule.span_le.2 hsub ha
    rwa [Subalgebra.mem_toSubmodule, mem_integralClosure_iff] at this

end GlobalTheory.CompanionTheory.Ar.IntClGens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpanStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_closure_chart_span : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), (∀ c, x c ≠ 0 → Module.Finite (chRing o x c) (integralClosure (chRing o x c) Ω)) → ∃ (d n : ℕ) (z : κ ⊕ Fin n → Ω), (∀ c, z (Sum.inl c) = x c ^ d) ∧ ∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntClGens.exists_twisted_gens | exact GlobalTheory.CompanionTheory.Ar.IntClGens.exists_twisted_gens | (intros; apply GlobalTheory.CompanionTheory.Ar.IntClGens.exists_twisted_gens <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionDivisorEq
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionDivisorEq
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem length_localizedModule_quot_eq {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R}
    (h₁ : ∀ x ∈ J₁, ∃ s, s ∉ W ∧ s * x ∈ J₂) (h₂ : ∀ x ∈ J₂, ∃ s, s ∉ W ∧ s * x ∈ J₁) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₁)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₂)) := by
  have key : ∀ {A B : Ideal R}, (∀ x ∈ A, ∃ s, s ∉ W ∧ s * x ∈ B) →
      Submodule.localized W.primeCompl (M := R) A ≤ Submodule.localized W.primeCompl (M := R) B := by
    intro A B h y hy
    obtain ⟨m, hm, s, rfl⟩ := hy
    obtain ⟨t, ht, htm⟩ := h m hm
    refine ⟨t * m, htm, ⟨t, ht⟩ * s, ?_⟩
    exact IsLocalizedModule.mk'_cancel_left _ _ _ _
  have heq : Submodule.localized W.primeCompl (M := R) J₁ = Submodule.localized W.primeCompl (M := R) J₂ :=
    le_antisymm (key h₁) (key h₂)
  have e₁ := (localizedQuotientEquiv W.primeCompl (M := R) J₁).length_eq
  have e₂ := (localizedQuotientEquiv W.primeCompl (M := R) J₂).length_eq
  have e₃ := (Submodule.quotEquivOfEq _ _ heq).length_eq
  exact e₁.symm.trans (e₃.trans e₂)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem IsUnitSec.symm {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) : IsUnitSec P g f := by
  intro W hW hP hR
  obtain ⟨u, v, hu, hv, hm⟩ := h W hW hP hR
  refine ⟨v, u, hv, hu, ?_⟩
  have := P.neg_mem hm
  rwa [neg_sub] at this

theorem divSupp_subset_of_isUnitSec {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) :
    divSupp P f ⊆ divSupp P g := by
  rintro W ⟨hmin, hrel⟩
  have hWp : W.IsPrime := hmin.1.1
  have hP : P ≤ W := le_sup_left.trans hmin.1.2
  have hf : f ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨u, v, hu, hv, hm⟩ := h W hWp hP hrel
  have hvg : v * g ∈ W := by
    have e : v * g = u * f - (u * f - v * g) := by ring
    rw [e]
    exact W.sub_mem (W.mul_mem_left u hf) (hP hm)
  have hg : g ∈ W := (hWp.mem_or_mem hvg).resolve_left hv
  refine ⟨⟨⟨hWp, sup_le hP ((Ideal.span_singleton_le_iff_mem _).mpr hg)⟩, ?_⟩, hrel⟩
  rintro W' ⟨hW'p, hW'le⟩ hW'W
  have hP' : P ≤ W' := le_sup_left.trans hW'le
  have hg' : g ∈ W' := hW'le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have huf : u * f ∈ W' := by
    have e : u * f = (u * f - v * g) + v * g := by ring
    rw [e]
    exact W'.add_mem (hP' hm) (W'.mul_mem_left v hg')
  have hf' : f ∈ W' := (hW'p.mem_or_mem huf).resolve_left fun hu' => hu (hW'W hu')
  exact hmin.2 ⟨hW'p, sup_le hP' ((Ideal.span_singleton_le_iff_mem _).mpr hf')⟩ hW'W

theorem mul_mem_sup_span_of_sub_mem {R : Type*} [CommRing R] {P : Ideal R} {f g u v x : R}
    (hm : u * f - v * g ∈ P) (hx : x ∈ P ⊔ Ideal.span {f}) : u * x ∈ P ⊔ Ideal.span {g} := by
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have e : u * (p + a * f) = (u * p + a * (u * f - v * g)) + (a * v) * g := by ring
  rw [e]
  exact Ideal.add_mem _
    (Ideal.mem_sup_left (P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left a hm)))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))

theorem multAt_sup_span_eq_of_sub_mem {P W : Ideal (MRing ι)} (hW : W.IsPrime) {f g u v : MRing ι}
    (hu : u ∉ W) (hv : v ∉ W) (hm : u * f - v * g ∈ P) :
    multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  have hm' : v * g - u * f ∈ P := by
    have := P.neg_mem hm
    rwa [neg_sub] at this
  haveI := hW
  unfold multAt
  rw [dite_eq_left hW, dite_eq_left hW,
    length_localizedModule_quot_eq W
      (fun x hx => ⟨u, hu, mul_mem_sup_span_of_sub_mem hm hx⟩)
      (fun x hx => ⟨v, hv, mul_mem_sup_span_of_sub_mem hm' hx⟩)]

theorem cycles_eq_of_isUnitSec :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι),
      IsUnitSec P f g → divSupp P f = divSupp P g ∧
        (∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W) ∧
        ∀ (n : ℕ) (L : Fin n → HermLine ι), vertR P L f = vertR P L g := by
  intro K _ ι _ P f g h
  have hsupp : divSupp P f = divSupp P g :=
    Set.Subset.antisymm (divSupp_subset_of_isUnitSec h) (divSupp_subset_of_isUnitSec h.symm)
  have hmult : ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    rintro W ⟨hmin, hrel⟩
    have hWp : W.IsPrime := hmin.1.1
    obtain ⟨u, v, hu, hv, hm⟩ := h W hWp (le_sup_left.trans hmin.1.2) hrel
    exact multAt_sup_span_eq_of_sub_mem hWp hu hv hm
  refine ⟨hsupp, hmult, fun n L => ?_⟩
  unfold vertR
  rw [← hsupp]
  refine finsum_mem_congr rfl fun W hW => ?_
  rw [hmult W hW]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionDivisorEqStatement
alias GlobalTheory.T.unit_section_divisor_eq := GlobalTheory.CompanionTheory.Ar.Flat.cycles_eq_of_isUnitSec
end
end
