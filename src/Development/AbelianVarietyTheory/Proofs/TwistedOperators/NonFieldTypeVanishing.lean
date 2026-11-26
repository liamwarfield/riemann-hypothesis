module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermEqVolumeMulOrbitalIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentConstantTermVanish

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRa
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRa
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem factorIdem_mul (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (p : plusAlg σ J γ) :
    factorIdem e i * ((p : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      ((e.symm (Pi.single i (e p i)) : plusAlg σ J γ) : genAlg γ) := by
  have h : e.symm (Pi.single i 1) * p = e.symm (Pi.single i (e p i)) := by
    apply e.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [← h]; rfl

theorem factorIdem_mul_self (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    factorIdem e i * factorIdem e i = factorIdem e i := by
  have := factorIdem_mul e i (e.symm (Pi.single i 1))
  rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same] at this
  exact this

theorem factorIdem_ne_zero (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) : factorIdem e i ≠ 0 := by
  intro h
  have h1 : e.symm (Pi.single i 1) = 0 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) i
  simp at h2

theorem factorIdem_selfAdj (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (factorIdem e i) * J = J * factorIdem e i :=
  (e.symm (Pi.single i 1)).2

theorem factorIdem_orth (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (1 - factorIdem e i) * J * factorIdem e i = 0 := by
  have hq : cT (σ : E →+* E) (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) * J =
      J * (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) :=
    (1 - e.symm (Pi.single i 1)).2
  have hc : (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      1 - factorIdem e i := rfl
  rw [hc] at hq
  rw [hq, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, factorIdem_mul_self, sub_self, Matrix.mul_zero]

theorem factorIdem_comm (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    ∀ l ∈ genAlg γ, l * factorIdem e i = factorIdem e i * l := by
  intro l hl
  exact congrArg Subtype.val (mul_comm (⟨l, hl⟩ : genAlg γ) (e.symm (Pi.single i 1) : plusAlg σ J γ))

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem rank_factorIdem {γ : GL (Fin n) E} (hA : ClauseAlg σ J γ) (hP : ClausePlus σ J γ)
    (e : plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    (factorIdem e i).rank = Module.finrank E (E ⊗[F] K i) := by
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  obtain ⟨-, -, hbij⟩ := hP
  let L := genAlg (γ : Matrix (Fin n) (Fin n) E)
  let P := plusAlg σ J (γ : Matrix (Fin n) (Fin n) E)
  let φ : L →ₗ[E] (Fin n → E) :=
    { toFun := fun l => (l : Matrix (Fin n) (Fin n) E) *ᵥ v
      map_add' := fun a b => Matrix.add_mulVec _ _ _
      map_smul' := fun c a => Matrix.smul_mulVec _ _ _ }
  let incl : P →ₗ[F] L := P.val.toLinearMap
  let ψ : E ⊗[F] P →ₗ[E] L := LinearMap.liftBaseChange E incl
  let ι : K i →ₗ[F] P := e.symm.toLinearMap ∘ₗ LinearMap.single F K i
  let Φ : E ⊗[F] K i →ₗ[E] (Fin n → E) := φ ∘ₗ ψ ∘ₗ ι.baseChange E
  have hψ : ∀ t, ψ t = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) (TensorProduct.comm F E P t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      change ψ 0 = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) ((TensorProduct.comm F E P).toLinearMap 0)
      rw [map_zero, map_zero, map_zero]
    | tmul a p =>
      simp [ψ, incl, plusTensor, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def, mul_comm]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hψb : Function.Bijective ψ := by
    have : (ψ : E ⊗[F] P → L) = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) ∘ TensorProduct.comm F E P :=
      funext hψ
    rw [this]; exact hbij.comp (TensorProduct.comm F E P).bijective
  have hι : Function.Injective (ι.baseChange E) := by
    have h0 : Function.Injective ι := e.symm.injective.comp (Pi.single_injective i)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap ι h0
  have hΦ : Function.Injective Φ := hv.1.comp (hψb.1.comp hι)
  have hΦt : ∀ (a : E) (x : K i), Φ (a ⊗ₜ x) =
      a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v) := by
    intro a x
    simp [Φ, φ, ψ, ι, incl, LinearMap.liftBaseChange_tmul, Matrix.smul_mulVec]
  have hrange : LinearMap.range Φ = LinearMap.range (factorIdem e i).mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        refine ⟨a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v), ?_⟩
        rw [hΦt, Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
        simp
      | add x y hx hy => rw [map_add Φ]; exact add_mem hx hy
    · rintro _ ⟨w, rfl⟩
      obtain ⟨l, rfl⟩ := hv.2 w
      obtain ⟨s, rfl⟩ := hψb.2 l
      change (factorIdem e i).mulVecLin (φ (ψ s)) ∈ LinearMap.range Φ
      induction s using TensorProduct.induction_on with
      | zero => simp [φ]
      | tmul a p =>
        refine ⟨a ⊗ₜ (e p i), ?_⟩
        rw [hΦt]
        simp only [ψ, incl, LinearMap.liftBaseChange_tmul, Matrix.mulVecLin_apply]
        have hc : (((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) = a • ((p : L) : Matrix (Fin n) (Fin n) E) := rfl
        change _ = factorIdem e i *ᵥ ((((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v)
        rw [hc, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
      | add x y hx hy =>
        rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact add_mem hx hy
  rw [Matrix.rank, ← hrange, LinearMap.finrank_range_of_inj hΦ]

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem eq_zero_of_mulVec {M : Matrix (Fin n) (Fin n) E} (h : ∀ w, M *ᵥ w = 0) : M = 0 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.mulVec_single_one] using this

theorem rank_pos_of_ne_zero {M : Matrix (Fin n) (Fin n) E} (hM : M ≠ 0) : 0 < M.rank := by
  refine Nat.pos_of_ne_zero fun h => hM (eq_zero_of_mulVec fun w => ?_)
  rw [Matrix.rank, Submodule.finrank_eq_zero] at h
  have : M.mulVecLin w ∈ LinearMap.range M.mulVecLin := ⟨w, rfl⟩
  rw [h] at this
  exact (Submodule.mem_bot E).1 this

theorem eq_one_of_idem_rank {M : Matrix (Fin n) (Fin n) E} (hM : M * M = M) (hr : M.rank = n) : M = 1 := by
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hr, Module.finrank_fin_fun]
  have hu : ∀ u, M *ᵥ u = u := by
    intro u
    obtain ⟨w, hw⟩ : u ∈ LinearMap.range M.mulVecLin := htop ▸ Submodule.mem_top
    rw [← hw, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hM]
  have h0 := eq_zero_of_mulVec (M := M - 1) fun w => by rw [Matrix.sub_mulVec, hu, Matrix.one_mulVec, sub_self]
  exact sub_eq_zero.1 h0

theorem two_le_of_decomp {P : Type} [CommRing P] [Algebra F P] {k' : ℕ} {K' : Fin k' → Type}
    [∀ i, Field (K' i)] [∀ i, Algebra F (K' i)] (e' : P ≃ₐ[F] ∀ i, K' i) (hk' : 2 ≤ k')
    (e : P ≃ₐ[F] ∀ i, K i) (i : Fin k) : ∃ j, j ≠ i := by
  by_contra hne
  simp only [not_exists, ne_eq, not_not] at hne
  let a : Fin k' := ⟨0, by omega⟩
  let b : Fin k' := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  let q : P := e'.symm (Pi.single a 1)
  have hqq : q * q = q := by
    apply e'.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, ← Pi.single_mul, one_mul]
  have hq : IsIdempotentElem (e q i) := by
    show e q i * e q i = e q i
    rw [← Pi.mul_apply, ← map_mul, hqq]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hq with h | h
  · have : e q = 0 := funext fun j => by rw [hne j]; exact h
    have h2 := congrFun (e'.symm_apply_eq.1 (e.map_eq_zero_iff.1 this)) a
    simp at h2
  · have : e q = 1 := funext fun j => by rw [hne j]; exact h
    have h1 : q = 1 := by rw [← map_one e] at this; exact e.injective this
    have h2 := congrFun (e'.symm_apply_eq.1 h1) b
    simp [Pi.single_apply, hab.symm] at h2

theorem factorIdem_ne_one (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (hj : ∃ j, j ≠ i) :
    factorIdem e i ≠ 1 := by
  intro h
  obtain ⟨j, hj⟩ := hj
  have h1 : e.symm (Pi.single i 1) = 1 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) j
  simp [Pi.single_apply, hj] at h2

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

theorem factorIdem_orthSplit_rank : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)] (e : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) (i : Fin k), GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i).rank = Module.finrank D.host.E (TensorProduct D.host.F D.host.E (Kf i)) := by
  intro hRS D V γ hss k Kf _ _ e i hnf
  have hreg := GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS γ hss
  obtain ⟨hA, hP, -⟩ := hRS.1 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg
  obtain ⟨-, k', K', _, _, ⟨e'⟩, hk', -⟩ := hnf
  have hj := two_le_of_decomp e' hk' e i
  refine ⟨⟨factorIdem_mul_self e i, factorIdem_selfAdj e i, factorIdem_orth e i, factorIdem_comm e i,
    rank_pos_of_ne_zero (factorIdem_ne_zero e i), lt_of_le_of_ne (Matrix.rank_le_width _) fun h =>
      factorIdem_ne_one e i hj (eq_one_of_idem_rank (factorIdem_mul_self e i) h)⟩,
    rank_factorIdem hA hP e i⟩

end GlobalTheory.FactorSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRaStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfAdjointFactorIdempotent_orthogonal_splitting_rank : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)] (e : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) (i : Fin k), GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i).rank = Module.finrank D.host.E (TensorProduct D.host.F D.host.E (Kf i)) := by
  first | exact @GlobalTheory.FactorSplit.factorIdem_orthSplit_rank | exact GlobalTheory.FactorSplit.factorIdem_orthSplit_rank | (intros; apply GlobalTheory.FactorSplit.factorIdem_orthSplit_rank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTorusFundamentalDomainFiniteMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTorusFundamentalDomainFiniteMeasure
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.AnisoCovol

theorem exists_compact_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] :
    ∃ K : Set G, IsCompact K ∧ ∀ x : G, ∃ g ∈ Γ, g * x ∈ K := by
  classical
  choose K hK hK' using fun x : G => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : G => ((↑) : G → G ⧸ Γ) '' interior (K x))
    (fun x => QuotientGroup.isOpenMap_coe _ isOpen_interior) (fun q _ => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hK' x), rfl⟩)
  refine ⟨(⋃ x ∈ t, K x)⁻¹, (t.isCompact_biUnion fun x _ => hK x).inv, fun y => ?_⟩
  obtain ⟨x, hx, z, hz, e⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ((y⁻¹ : G) : G ⧸ Γ)))
  refine ⟨z⁻¹ * y⁻¹, QuotientGroup.eq.1 e, ?_⟩
  rw [Set.mem_inv, show (z⁻¹ * y⁻¹ * y)⁻¹ = z by group]
  exact Set.mem_iUnion₂.2 ⟨x, hx, interior_subset hz⟩

theorem measure_ne_top_of_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ g ∈ Γ, g * x ∈ K) (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 ≠ ⊤ := by
  have hsub : 𝓕 ⊆ ⋃ g : Γ, ((g • K) ∩ 𝓕) := by
    intro x hx
    obtain ⟨g, hg, hk⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨(⟨g, hg⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hk
  refine ne_of_lt ?_
  calc μ 𝓕 ≤ μ (⋃ g : Γ, ((g • K) ∩ 𝓕)) := measure_mono hsub
    _ ≤ ∑' g : Γ, μ ((g • K) ∩ 𝓕) := measure_iUnion_le _
    _ = μ K := (h𝓕.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

theorem bc_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (φ' : B →+* C) (g : GL n A) :
    Formalism.UG.bc φ' (Formalism.UG.bc φ g) = Formalism.UG.bc (φ'.comp φ) g := rfl

variable {D : D7} {V : HSp D}

abbrev tensFlip (D : D7) : D.host.E ⊗[D.host.F] AF D.host.F ≃+* AF D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.comm D.host.F D.host.E (AF D.host.F)).toRingEquiv

theorem tensFlip_inclE (e : D.host.E) :
    tensFlip D (Formalism.UG.inclE (F := D.host.F) (AF D.host.F) e) = inclR (F := D.host.F) (AF D.host.F) e := by
  simp [Formalism.UG.inclE, inclR]

theorem tensFlip_symm_inclR (e : D.host.E) :
    (tensFlip D).symm (inclR (F := D.host.F) (AF D.host.F) e) = Formalism.UG.inclE (F := D.host.F) (AF D.host.F) e := by
  simp [Formalism.UG.inclE, inclR]

theorem tensFlip_sig (x : D.host.E ⊗[D.host.F] AF D.host.F) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (tensFlip D x) =
      tensFlip D (Formalism.UG.sigR D.sp.cm.sig (AF D.host.F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [RingEquiv.map_add (e := _), RingHom.map_add (f := _), hx, hy]

theorem tensFlip_symm_sig (x : AF D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (AF D.host.F) ((tensFlip D).symm x) =
      (tensFlip D).symm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Formalism.UG.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [RingEquiv.map_add (e := _), RingHom.map_add (f := _), hx, hy]

variable {D : D7} (V : HSp D)

theorem tensFlip_gram :
    (V.gram.map (Formalism.UG.inclE (F := D.host.F) (AF D.host.F))).map (tensFlip D).toRingHom = JR (AF D.host.F) V.gram := by
  ext i j
  exact tensFlip_inclE _

theorem tensFlip_symm_gram :
    (JR (AF D.host.F) V.gram).map (tensFlip D).symm.toRingHom = V.gram.map (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) := by
  ext i j
  exact tensFlip_symm_inclR _

def uFlip : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F) →* GA D V :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU (Formalism.UG.sigR D.sp.cm.sig (AF D.host.F)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig)
    (tensFlip D).toRingHom tensFlip_sig _ _ (tensFlip_gram V)

def uFlipSymm : GA D V →* Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F) :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapU (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (Formalism.UG.sigR D.sp.cm.sig (AF D.host.F))
    (tensFlip D).symm.toRingHom tensFlip_symm_sig _ _ (tensFlip_symm_gram V)

theorem matHom_uFlip (g : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F)) :
    GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram (uFlip V g) = Formalism.UG.bc (tensFlip D).toRingHom g.1 := rfl

theorem val_uFlipSymm (g : GA D V) :
    ((uFlipSymm V g : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F)) : GL (Fin V.rank) (D.host.E ⊗[D.host.F] AF D.host.F)) =
      Formalism.UG.bc (tensFlip D).symm.toRingHom (GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram g) := rfl

theorem bc_inclR (γ : GF V) :
    Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ.1 =
      Formalism.UG.bc (tensFlip D).toRingHom (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1) := by
  rw [bc_bc]
  congr 1

theorem bc_symm_inclR (γ : GF V) :
    Formalism.UG.bc (tensFlip D).symm.toRingHom (Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ.1) =
      Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1 := by
  rw [bc_bc]
  congr 1

variable {D : D7} (V : HSp D)

theorem uFlip_mem (γ : GF V) (g : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F)) :
    uFlip V (Subgroup.inclusion inf_le_left g) ∈ cent (rat V γ) := by
  have h3 : Formalism.UG.bc (tensFlip D).toRingHom (g.1 * Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1) =
      Formalism.UG.bc (tensFlip D).toRingHom (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1 * g.1) :=
    congrArg _ (Subgroup.mem_centralizer_singleton_iff.1 g.2.2)
  rw [MonoidHom.map_mul, MonoidHom.map_mul, ← bc_inclR] at h3
  exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext h3)

def centFlip (γ : GF V) :
    GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F) →* cent (rat V γ) :=
  ((uFlip V).comp (Subgroup.inclusion inf_le_left)).codRestrict _ (uFlip_mem V γ)

theorem matHom_centFlip (γ : GF V) (g : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F)) :
    GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram (centFlip V γ g : GA D V) = Formalism.UG.bc (tensFlip D).toRingHom g.1 :=
  matHom_uFlip V _

theorem centFlip_surjective (γ : GF V) : Function.Surjective (centFlip V γ) := by
  intro y
  have hy : GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram y.1 * Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ.1 =
      Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ.1 * GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram y.1 :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2)
  have hx : ((uFlipSymm V y.1 : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F)) :
      GL (Fin V.rank) (D.host.E ⊗[D.host.F] AF D.host.F)) ∈
      Subgroup.centralizer {Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)) γ.1} := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have e := congrArg (Formalism.UG.bc (tensFlip D).symm.toRingHom) hy
    rw [MonoidHom.map_mul, MonoidHom.map_mul, bc_symm_inclR] at e
    rw [val_uFlipSymm]
    exact e
  refine ⟨⟨_, (uFlipSymm V y.1).2, hx⟩, Subtype.ext (GlobalTheory.AdelicU.matHom_injective (AF D.host.F) D.sp.cm.sig V.gram ?_)⟩
  rw [matHom_centFlip]
  show Formalism.UG.bc (tensFlip D).toRingHom ((uFlipSymm V y.1 : Formalism.UG.UPts D.sp.cm.sig V.gram (AF D.host.F)) :
      GL (Fin V.rank) (D.host.E ⊗[D.host.F] AF D.host.F)) = _
  rw [val_uFlipSymm, bc_bc]
  ext i j
  simp [Formalism.UG.bc]

theorem centFlip_rat (γ : GF V) (a : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F))
    (ha : a ∈ ((GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centRat D.sp.cm.sig V.gram γ.1).map
      (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)))).subgroupOf
        (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F))) :
    centFlip V γ a ∈ (GQ V).subgroupOf (cent (rat V γ)) := by
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 ha)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ, hδ.1, ?_⟩))
  show _ = GlobalTheory.AdelicU.matHom (AF D.host.F) D.sp.cm.sig V.gram (centFlip V γ a : GA D V)
  rw [matHom_centFlip, ← e, bc_bc]
  congr 1

variable {D : D7} (V : HSp D)

theorem continuous_tensFlip :
    letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
    Continuous (tensFlip D) := by
  letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
  letI : Algebra (AF D.host.F) (D.host.E ⊗[D.host.F] AF D.host.F) := Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (AF D.host.F) (D.host.E ⊗[D.host.F] AF D.host.F) := ⟨rfl⟩
  haveI : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  let L : D.host.E ⊗[D.host.F] AF D.host.F →ₗ[AF D.host.F] AF D.host.F ⊗[D.host.F] D.host.E :=
    { toFun := tensFlip D
      map_add' := fun x y => (tensFlip D).map_add x y
      map_smul' := fun a x => by
        rw [Algebra.smul_def, RingEquiv.map_mul, Algebra.smul_def]
        rfl }
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_centFlip (γ : GF V) :
    letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
    Continuous (centFlip V γ) := by
  letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have hf : Continuous (tensFlip D) := continuous_tensFlip
  have hbc : Continuous (Formalism.UG.bc (n := Fin V.rank) (tensFlip D).toRingHom) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩
  refine Continuous.subtype_mk ?_ _
  refine (GlobalTheory.AdelicU.isEmbedding_matHom (AF D.host.F) D.sp.cm.sig V.gram).continuous_iff.2 ?_
  exact hbc.comp continuous_subtype_val

theorem compactSpace_cent (γ : GF V) (hc : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.AdelicCompact D.sp.cm.sig V.gram γ.1) :
    CompactSpace (cent (rat V γ) ⧸ (GQ V).subgroupOf (cent (rat V γ))) := by
  letI := Formalism.BasicNotions.tensTopL (F := D.host.F) (E := D.host.E) (AF D.host.F)
  have hc' : CompactSpace (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F) ⧸
      ((GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centRat D.sp.cm.sig V.gram γ.1).map
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)))).subgroupOf
          (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F))) := hc
  let q := Quotient.map' (s₁ := QuotientGroup.leftRel (((GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centRat D.sp.cm.sig V.gram γ.1).map
        (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (AF D.host.F)))).subgroupOf
          (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.centPts D.sp.cm.sig V.gram γ.1 (AF D.host.F))))
      (s₂ := QuotientGroup.leftRel ((GQ V).subgroupOf (cent (rat V γ)))) (centFlip V γ) fun a b h => by
    refine QuotientGroup.leftRel_apply.2 ?_
    rw [← MonoidHom.map_inv, ← MonoidHom.map_mul]
    exact centFlip_rat V γ _ (QuotientGroup.leftRel_apply.1 h)
  have hq : Continuous q := (continuous_centFlip V γ).quotient_map' _
  have hs : Function.Surjective q := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨x, rfl⟩ := centFlip_surjective V γ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  exact hs.compactSpace hq

variable {D : D7}

theorem countable_GF (V : HSp D) : Countable (GF V) := by
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin V.rank → D.host.E))
  haveI : Countable (GL (Fin V.rank) D.host.E) := Units.val_injective.countable
  exact Subtype.countable

theorem countable_GQ (V : HSp D) : Countable (GQ V) := by
  haveI := countable_GF V
  refine Function.Surjective.countable (f := fun δ : GF V => (⟨rat V δ, Subgroup.mem_subgroupOf.2
    (Subgroup.mem_map.2 ⟨δ, δ.2, rfl⟩)⟩ : GQ V)) fun x => ?_
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 x.2)
  exact ⟨⟨δ, hδ⟩, Subtype.ext (Subtype.ext e)⟩

theorem covol_lt_top : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)], Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) → (∀ i, IsField (TensorProduct D.host.F (Kf i) D.host.E)) → ∀ (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure] (𝓣 : Set (cent (rat V γ))), IsFundamentalDomain ((GQ V).subgroupOf (cent (rat V γ))) 𝓣 dt → dt 𝓣 < ⊤ := by
  intro hR D V γ hγ k Kf _ _ he hf dt _ 𝓣 h𝓣
  have hreg := GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS γ hγ
  have hc := (hR.2 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg k Kf he).2 hf
  haveI := compactSpace_cent V γ hc
  haveI : LocallyCompactSpace (cent (rat V γ)) := (isClosed_cent (rat V γ)).locallyCompactSpace
  obtain ⟨K, hK, hcov⟩ := exists_compact_cover ((GQ V).subgroupOf (cent (rat V γ)))
  haveI := countable_GQ V
  haveI : Countable ((GQ V).subgroupOf (cent (rat V γ))) :=
    Function.Injective.countable (f := fun x : (GQ V).subgroupOf (cent (rat V γ)) => (⟨x.1.1, x.2⟩ : GQ V))
      fun a b h => by
        have e := Subtype.mk.inj h
        exact Subtype.ext (Subtype.ext e)
  exact lt_top_iff_ne_top.2 (measure_ne_top_of_cover _ hK hcov dt h𝓣)

end GlobalTheory.AnisoCovol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTorusFundamentalDomainFiniteMeasureStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropic_torus_fundamentalDomain_finite_measure : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)], Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) → (∀ i, IsField (TensorProduct D.host.F (Kf i) D.host.E)) → ∀ (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure] (𝓣 : Set (cent (rat V γ))), IsFundamentalDomain ((GQ V).subgroupOf (cent (rat V γ))) 𝓣 dt → dt 𝓣 < ⊤ := by
  first | exact @GlobalTheory.AnisoCovol.covol_lt_top | exact GlobalTheory.AnisoCovol.covol_lt_top | (intros; apply GlobalTheory.AnisoCovol.covol_lt_top <;> assumption)
end
end

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms (plusAlg genAlg)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH NoFixed radical)
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.NonFieldType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem localClause {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ} (hμf : ∀ v, (μf v).IsHaarMeasure) (hf : IsTestFin T U μf ff)
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) : LocalClause T μf ff γ := by
  intro k K _ _ e i
  obtain ⟨h1, h2⟩ := GlobalTheory.T.selfAdjointFactorIdempotent_orthogonal_splitting_rank GlobalTheory.T.regularSemisimple_unitaryGroup_concrete D V γ hγ.1 k K e i hγ
  refine ⟨h1, h2, fun v hv dt hdt => ?_⟩
  obtain ⟨hee, -, -, hcomm, hpos, hlt⟩ := h1
  have hγε : γ.1.1 * factorIdem e i = factorIdem e i * γ.1.1 :=
    hcomm _ (Algebra.self_mem_adjoin_singleton _ _)
  have h := GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish GlobalTheory.T.typeIdempotent_constantTerm_vanish D V T U μf ff hf v (hμf v) γ (factorIdem e i) hγ.1 hee hγε hpos hlt hv 1
    continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl) dt
  have e1 : (fun x => (1 : GLoc D.sp.cm.sig V.gram v → ℂ) x *
      ff v (x⁻¹ * proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ) * x)) = conjFn (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)) (ff v) := by
    funext x; exact one_mul _
  rw [e1] at h
  exact h

theorem isMulCommutative_cent_ratEmb {γ : GRat D.sp.cm.sig V.gram} (hγ : IsRegSS γ.1.1) :
    IsMulCommutative (cent (ratEmb D.sp.cm.sig V.gram γ)) := by
  refine ⟨⟨fun x y => Subtype.ext (GAd_ext _ _ (fun w => ?_) fun v => ?_)⟩⟩
  · have h := (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)).is_comm.comm
      (centMap (projArch D.sp.cm.sig V.gram w) _ x) (centMap (projArch D.sp.cm.sig V.gram w) _ y)
    have h' := congrArg Subtype.val h
    simpa [centMap] using h'
  · have h := (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)).is_comm.comm
      (centMap (proj D.sp.cm.sig V.gram v) _ x) (centMap (proj D.sp.cm.sig V.gram v) _ y)
    have h' := congrArg Subtype.val h
    simpa [centMap] using h'

theorem ratEmb_mem_GQ (γ : GRat D.sp.cm.sig V.gram) : ratEmb D.sp.cm.sig V.gram γ ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨γ, rfl⟩

theorem covol_lt_top {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1)
    (dt : Measure (cent (ratEmb D.sp.cm.sig V.gram γ))) [dt.IsHaarMeasure] (𝓣 : Set (cent (ratEmb D.sp.cm.sig V.gram γ)))
    (h𝓣 : IsFundamentalDomain ((GQ V).subgroupOf (cent (ratEmb D.sp.cm.sig V.gram γ))) 𝓣 dt) : dt 𝓣 < ⊤ := by
  obtain ⟨hreg, k, K, iF, iA, he, -, hK⟩ := hγ
  exact GlobalTheory.T.anisotropic_torus_fundamentalDomain_finite_measure GlobalTheory.T.regularSemisimple_unitaryGroup_concrete D V γ hreg k K he hK dt 𝓣 h𝓣


instance discreteTopology_subgroupOf_cent (γ : GA D V) : DiscreteTopology ((GQ V).subgroupOf (cent γ)) :=
  DiscreteTopology.of_continuous_injective (f := fun t : (GQ V).subgroupOf (cent γ) => (⟨t.1.1, t.2⟩ : GQ V))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun s t h => Subtype.ext (Subtype.ext (by have h' := congrArg Subtype.val h; exact h')))

set_option maxHeartbeats 4000000 in
theorem zeroClause {T : TypeDataG V} (hH : HypH (k := fun v : T.S => ResF v.1) T.τ)
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1)
    (hL : LocalClause T μf ff γ) (hP : ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ)) :
    ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (ratEmb D.sp.cm.sig V.gram γ) := by
  intro 𝓕 h𝓕
  haveI hla : ∀ w, LocallyCompactSpace (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun _ => (isClosed_cent _).locallyCompactSpace
  haveI hlf : ∀ v, LocallyCompactSpace (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun _ => (isClosed_cent _).locallyCompactSpace
  have hR := restrGroup_cent (frameLat V) (ratEmb D.sp.cm.sig V.gram γ)
  let K0 : ∀ v, TopologicalSpace.PositiveCompacts (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun v => ⟨⟨_, hR.isCompact_K v⟩, by
      simp only [(hR.isOpen_K v).interior_eq]; exact ⟨1, one_mem _⟩⟩
  let dta : ∀ w, Measure (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ))) := fun _ => Measure.haar
  let dtf : ∀ v, Measure (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ))) :=
    fun v => Measure.haarMeasure (K0 v)
  haveI : ∀ w, (dta w).IsHaarMeasure := fun _ => inferInstance
  haveI : ∀ v, (dtf v).IsHaarMeasure := fun _ => inferInstance
  have h1 : ∀ᶠ v in cofinite, dtf v ((stabLoc D.sp.cm.sig V.gram (frameLat V) v).subgroupOf
      (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)))) = 1 :=
    .of_forall fun v => Measure.haarMeasure_self (K₀ := K0 v)
  obtain ⟨dt, hdt, -⟩ := existsUnique_isCentProd (L := frameLat V) (ratEmb D.sp.cm.sig V.gram γ) dta dtf h1
  have h𝓣 := isFundamentalDomain_stdDom ((GQ V).subgroupOf (cent (ratEmb D.sp.cm.sig V.gram γ))) dt
  obtain ⟨-, oa, ob, -, hob, hone, -, hcls⟩ := hP dta dtf dt hdt _ h𝓣
  obtain ⟨-, k, K, iF, iA, ⟨e⟩, hk, -⟩ := hγ
  obtain ⟨hsplit, -, hloc⟩ := hL k K e ⟨0, by omega⟩
  obtain ⟨v, hv⟩ := hH _ hsplit.2.2.2.2.1 hsplit.2.2.2.2.2
  have h0 := hloc v hv (dtf v.1) inferInstance
  have hob0 : ob v.1 = 0 := (hob v.1).2.symm.trans h0.2
  have hfp : ∏ᶠ v, ob v = 0 := finprod_eq_zero ob v.1 hob0 (Filter.eventually_cofinite.1 hone)
  have h := hcls 𝓕 h𝓕
  rwa [hfp, mul_zero, mul_zero] at h


end GlobalTheory.NonFieldType
