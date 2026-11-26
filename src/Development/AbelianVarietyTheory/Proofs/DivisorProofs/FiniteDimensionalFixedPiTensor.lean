module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedPiTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCompactFixedVectorsPiTensorSmoo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCompactFixedVectorsPiTensorSmoo
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.PiTensorFixed

variable {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem exists_fixed_tprod (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a))) (v : ∀ a, X a) :
    ∃ u : ∀ a, X a, (∀ a, u a ∈ fixed (ρ a) (K a)) ∧
      (twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1).mkQ (PiTensorProduct.tprod ℂ u) =
        (twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1).mkQ (PiTensorProduct.tprod ℂ v) := by
  classical
  haveI := Fintype.ofFinite α
  set N := twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1
  have key : ∀ S : Finset α, ∃ u : ∀ a, X a, (∀ a ∈ S, u a ∈ fixed (ρ a) (K a)) ∧
      N.mkQ (PiTensorProduct.tprod ℂ u) = N.mkQ (PiTensorProduct.tprod ℂ v) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨v, by simp, rfl⟩
    | insert a S ha ih =>
      obtain ⟨u, hu, e⟩ := ih
      let f : X a →ₗ[ℂ] _ := N.mkQ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap u a
      obtain ⟨y, hy, hfy⟩ := IwahoriOnto.exists_fixed_map_eq (hρ a) (hK a) f (u a) fun h hh => by
        simp only [f, LinearMap.comp_apply, MultilinearMap.toLinearMap_apply, Submodule.mkQ_apply,
          Function.update_eq_self]
        rw [Submodule.Quotient.eq]
        refine Submodule.subset_span ⟨⟨Pi.mulSingle a h, fun b _ => ?_⟩, PiTensorProduct.tprod ℂ u, ?_⟩
        · by_cases hb : b = a
          · subst hb; simpa using hh
          · simp [Pi.mulSingle_eq_of_ne hb]
        · have : (fun b => ρ b (Pi.mulSingle (M := Γ) a h b) (u b)) = Function.update u a (ρ a h (u a)) := by
            funext b
            by_cases hb : b = a
            · subst hb; simp
            · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
          simp [this]
      refine ⟨Function.update u a y, fun b hb => ?_, ?_⟩
      · by_cases hba : b = a
        · subst hba; simpa using hy
        · rw [Function.update_of_ne hba]
          exact hu b ((Finset.mem_insert.1 hb).resolve_left hba)
      · rw [← e]
        simpa [f] using hfy
  obtain ⟨u, hu, e⟩ := key Finset.univ
  exact ⟨u, fun a => hu a (Finset.mem_univ a), e⟩

theorem fixed_le_range (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a))) :
    fixed (piTensor ρ) (Subgroup.pi Set.univ K) ≤
      LinearMap.range (PiTensorProduct.map fun a => (fixed (ρ a) (K a)).subtype) := by
  set N := twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1
  set R := LinearMap.range (PiTensorProduct.map fun a => (fixed (ρ a) (K a)).subtype)
  have hR : R ≤ fixed (piTensor ρ) (Subgroup.pi Set.univ K) := by
    rintro _ ⟨x, rfl⟩
    induction x using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | smul_tprod c x =>
      rw [map_smul]
      refine Submodule.smul_mem _ c (ContraRefl.mem_fix.2 fun h hh => ?_)
      rw [PiTensorProduct.map_tprod, piTensor_tprod]
      congr 1
      funext a
      exact ContraRefl.mem_fix.1 (x a).2 _ (hh a trivial)
  have hall : ∀ w, ∃ r ∈ R, N.mkQ r = N.mkQ w := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | add x y hx hy =>
      obtain ⟨r, hr, e⟩ := hx
      obtain ⟨s, hs, e'⟩ := hy
      exact ⟨r + s, add_mem hr hs, by rw [map_add (f := _), map_add (f := _), e, e']⟩
    | smul_tprod c x =>
      obtain ⟨u, hu, e⟩ := exists_fixed_tprod ρ hρ K hK x
      refine ⟨c • PiTensorProduct.tprod ℂ u, Submodule.smul_mem _ c
        ⟨PiTensorProduct.tprod ℂ fun a => ⟨u a, hu a⟩, by simp⟩, ?_⟩
      rw [map_smul, map_smul, e]
  intro w hw
  obtain ⟨r, hr, e⟩ := hall w
  have h0 : r - w = 0 := ContraRefl.eq_zero_of_fixed_twKer (isSmooth_piTensor hρ)
    (isCompact_univ_pi hK) (sub_mem (hR hr) hw) ((Submodule.Quotient.eq N).1 e)
  rw [← sub_eq_zero.1 h0]
  exact hr

theorem finiteDimensional_fixed_piTensor : ∀ {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)), (∀ a, IsSmooth (ρ a)) → ∀ (K : ∀ a, Subgroup (Γ a)), (∀ a, IsCompact (K a : Set (Γ a))) → (∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) → FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) := by
  intro α _ Γ X _ _ _ _ _ ρ hρ K hK hfin
  exact Submodule.finiteDimensional_of_le (fixed_le_range ρ hρ K hK)

end GlobalTheory.PiTensorFixed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCompactFixedVectorsPiTensorSmooStatement
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_compact_fixed_vectors_piTensor_smooth : ∀ {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)), (∀ a, IsSmooth (ρ a)) → ∀ (K : ∀ a, Subgroup (Γ a)), (∀ a, IsCompact (K a : Set (Γ a))) → (∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) → FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) := by
  first | exact @GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor | exact GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor | (intros; apply GlobalTheory.PiTensorFixed.finiteDimensional_fixed_piTensor <;> assumption)
end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ContraProd

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end General

end GlobalTheory.ContraProd

noncomputable section

namespace GlobalTheory.ContraProd

section Fixed

theorem finiteDimensional_fixed_piTensor {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a)))
    (hf : ∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) :
    FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) :=
  GlobalTheory.T.finiteDimensional_compact_fixed_vectors_piTensor_smooth ρ hρ K hK hf

end Fixed

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_compactOpen_GL (n : Type) [Fintype n] [DecidableEq n] (U : Set (GL n k)) (hU : U ∈ nhds 1) :
    ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ IsCompact (K : Set (GL n k)) ∧ (K : Set (GL n k)) ⊆ U := by
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k n U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem exists_pi_compactOpen {α : Type} [Finite α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (U : Set (Levi k m)) (hU : U ∈ nhds (1 : Levi k m)) :
    ∃ K : ∀ a, Subgroup (GL (m a) k), (∀ a, IsOpen (K a : Set (GL (m a) k))) ∧
      (∀ a, IsCompact (K a : Set (GL (m a) k))) ∧ ((Subgroup.pi Set.univ K : Subgroup (Levi k m)) : Set (Levi k m)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hts⟩ := hU
  choose K hKo hKc hKt using fun a => exists_compactOpen_GL (k := k) (m a) (t a) (ht a)
  refine ⟨K, hKo, hKc, ?_⟩
  rw [Subgroup.coe_pi]
  exact fun g hg => hts fun a _ => hKt a (hg a (Set.mem_univ a))

theorem isAdmissible_piTensor {α : Type} [Finite α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (hρ : ∀ a, IsAdmissible (ρ a)) :
    IsAdmissible (piTensor ρ : Representation ℂ (Levi k m) _) := by
  refine ⟨isSmooth_piTensor fun a => (hρ a).1, fun K hKo hKc => ?_⟩
  obtain ⟨K', hKo', hKc', hK'⟩ := exists_pi_compactOpen m (K : Set (Levi k m)) (hKo.mem_nhds K.one_mem)
  haveI := finiteDimensional_fixed_piTensor ρ (fun a => (hρ a).1) K' hKc'
    fun a => (hρ a).2 (K' a) (hKo' a) (hKc' a)
  exact Submodule.finiteDimensional_of_le (S₁ := fixed (piTensor ρ : Representation ℂ (Levi k m) _) K)
    (S₂ := fixed (piTensor ρ) (Subgroup.pi Set.univ K'))
    (fun v hv => GlobalTheory.ContraRefl.mem_fix.2 fun h hh => GlobalTheory.ContraRefl.mem_fix.1 hv h (hK' hh))

end GlobalTheory.ContraProd

noncomputable section

namespace GlobalTheory.ContraProd

section Pairing

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  (ρ : ∀ a, Representation ℂ (Γ a) (X a))

end Pairing

end GlobalTheory.ContraProd

noncomputable section

namespace GlobalTheory.ContraProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.ContraProd
end
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInert
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInert
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.UnitInert

section Local

variable {O : Type} [CommRing O] [IsNoetherianRing O] {r : ℕ}

theorem exists_unitary_conj (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] {σ : O →+* O}
    (hσ : ∀ a, σ (σ a) = a) (hI : ∀ x ∈ I, σ x ∈ I) (hω : ∃ ω, IsUnit (ω - σ ω))
    {g h : Matrix (Fin r) (Fin r) O} (hg : cT σ g * g = 1) (hh : cT σ h * h = 1)
    (hs : g.charpoly.Separable) (e : h.charpoly = g.charpoly) :
    ∃ u : GL (Fin r) O, cT σ u.1 * u.1 = 1 ∧ g * u = u * h := by
  have hjac := IsAdicComplete.le_jacobson_bot I
  obtain ⟨v, hv⟩ := GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := g) hs
  obtain ⟨w, hw⟩ := GlobalTheory.Orb.exists_cyclic_of_finite_quotient I hjac (g := h) (show h.charpoly.Separable by rwa [e])
  obtain ⟨a, ha⟩ := (isUnit_iff_isUnit_det _).2 hv
  obtain ⟨b, hb⟩ := (isUnit_iff_isUnit_det _).2 hw
  have hy : g * (a * b⁻¹ : GL (Fin r) O) = (a * b⁻¹ : GL (Fin r) O) * h := by
    have h1 := GlobalTheory.Orb.mul_krylov_eq g v
    have h2 := GlobalTheory.Orb.mul_krylov_eq h w
    rw [← ha] at h1
    rw [← hb, e] at h2
    rw [Units.val_mul, ← mul_assoc, h1, Units.mul_inv_eq_iff_eq_mul, mul_assoc, mul_assoc, h2,
      Units.inv_mul_cancel_left]
  generalize a * b⁻¹ = y at hy
  set s : Matrix (Fin r) (Fin r) O → Matrix (Fin r) (Fin r) O := cT σ with hsdef
  have hm : ∀ a b, s (a * b) = s b * s a := fun a b => cT_mul σ a b
  have hadd : ∀ a b, s (a + b) = s a + s b := fun a b => Matrix.ext fun i j => by simp [s, cT]
  have hss : ∀ a, s (s a) = a := fun a => Matrix.ext fun i j => by simp [s, cT, hσ]
  have hsc : ∀ c : O, s (algebraMap O _ c) = algebraMap O _ (σ c) := fun c => by
    ext i j
    simp only [s, cT, transpose_apply, map_apply, algebraMap_matrix_apply, eq_comm (a := j)]
    split_ifs <;> simp
  have h1 : s 1 = 1 := by simpa using hsc 1
  change s g * g = 1 at hg
  change s h * h = 1 at hh
  let C := Subalgebra.centralizer O ({h} : Set (Matrix (Fin r) (Fin r) O))
  have hC : ∀ {a}, a ∈ C ↔ a * h = h * a := by simp [C, Subalgebra.mem_centralizer_iff, eq_comm]
  let _ : CommRing C :=
    { (inferInstance : Ring C) with
      mul_comm := fun a b => Subtype.ext (by
        obtain ⟨p, hp⟩ := GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 a.2)
        obtain ⟨q, hq⟩ := GlobalTheory.Orb.exists_aeval_of_cyclic hw (hC.1 b.2)
        rw [C.coe_mul, C.coe_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]) }
  have : Module.Finite O (Matrix (Fin r) (Fin r) O) := inferInstanceAs (Module.Finite O (Fin r → Fin r → O))
  have : Module.Finite O C := Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite I C
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite I C
  have hsC : ∀ a ∈ C, s a ∈ C := fun a ha => hC.2 (by
    have h2 := congrArg s (hC.1 ha)
    rw [hm, hm] at h2
    calc s a * h = h * (s h * s a) * h := by rw [← mul_assoc, mul_eq_one_comm.1 hh, one_mul]
      _ = h * s a := by rw [h2, mul_assoc, mul_assoc, hh, mul_one])
  let t : C →+* C :=
    { toFun := fun a => ⟨s a, hsC _ a.2⟩
      map_one' := Subtype.ext h1
      map_mul' := fun a b => by rw [mul_comm a b]; exact Subtype.ext (hm _ _)
      map_zero' := Subtype.ext (by simpa using hsc 0)
      map_add' := fun a b => Subtype.ext (hadd _ _) }
  have hιR : ∀ c, t (algebraMap O C c) = algebraMap O C (σ c) := fun c => Subtype.ext (hsc c)
  have hl : s y * y ∈ C := hC.2 (by
    have h2 : s h * (s y * y) * h = s y * y := by
      rw [← mul_assoc, ← hm, mul_assoc, ← hy, hm, mul_assoc, ← mul_assoc (s g), hg, one_mul]
    conv_rhs => rw [← h2, ← mul_assoc, ← mul_assoc, mul_eq_one_comm.1 hh, one_mul])
  have hlu : (s y * y) * ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) = 1 := by
    rw [mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.inv_mul, h1]
  have hl' : ((y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O)) ∈ C := hC.2 (by
    have h2 := mul_eq_one_comm.1 hlu
    exact (Commute.units_inv_left (u := ⟨_, _, hlu, h2⟩) (hC.1 hl)).eq)
  obtain ⟨ω, hω⟩ := hω
  obtain ⟨z, hz⟩ := GlobalTheory.HenselianNorm.exists_norm_eq C (I.map (algebraMap O C)) t (fun a => Subtype.ext (hss _))
    (fun x hx => (show I.map (algebraMap O C) ≤ (I.map (algebraMap O C)).comap t from Ideal.map_le_iff_le_comap.2
      fun c hc => by
        rw [Ideal.mem_comap, Ideal.mem_comap, hιR]
        exact Ideal.mem_map_of_mem _ (hI c hc)) hx)
    ⟨algebraMap O C ω, by rw [hιR, ← map_sub]; exact hω.map _⟩ ⟨_, hl'⟩ (Subtype.ext (by
      change s _ = _
      rw [hm, hss])) (IsUnit.of_mul_eq_one_right ⟨_, hl⟩ (Subtype.ext hlu))
  have hz' : z.1 * s z.1 = (y⁻¹ : GL (Fin r) O) * s (y⁻¹ : GL (Fin r) O) := congrArg Subtype.val hz
  have h3 : (y * z.1) * s (y * z.1) = 1 := by
    rw [hm, mul_assoc, ← mul_assoc z.1, hz', mul_assoc, Units.mul_inv_cancel_left, ← hm, Units.mul_inv, h1]
  refine ⟨⟨_, _, h3, mul_eq_one_comm.1 h3⟩, mul_eq_one_comm.1 h3, ?_⟩
  change g * (y * z.1) = y * z.1 * h
  rw [← mul_assoc, hy, mul_assoc, mul_assoc, hC.1 z.2]

end Local

end GlobalTheory.BCT.UnitInert

namespace GlobalTheory.BCT.UnitInert

variable {E : Type} [Field E] [NumberField E]

theorem eventually_int (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

theorem eventually_lift (p : E[X]) : ∀ᶠ w : Pl E in cofinite, ∃ q : (w.adicCompletionIntegers E)[X],
    q.map (algebraMap _ (w.adicCompletion E)) = atPl w p := by
  have h : ∀ᶠ w : Pl E in cofinite, ∀ i ∈ p.support,
      algebraMap E (w.adicCompletion E) (p.coeff i) ∈ w.adicCompletionIntegers E := by
    rw [eventually_all_finset]
    exact fun i _ => eventually_int _
  filter_upwards [h] with w hw
  refine (Polynomial.mem_lifts _).1 ((Polynomial.lifts_iff_coeff_lifts _).2 fun i => ?_)
  rw [coeff_map]
  by_cases hi : i ∈ p.support
  · exact ⟨⟨_, hw i hi⟩, rfl⟩
  · rw [notMem_support_iff.1 hi, map_zero]
    exact ⟨0, map_zero _⟩

theorem eventually_separable (P : E[X]) (hP : P.Separable) : ∀ᶠ w : Pl E in cofinite,
    ∀ q : (w.adicCompletionIntegers E)[X], q.map (algebraMap _ (w.adicCompletion E)) = atPl w P → q.Separable := by
  obtain ⟨u, v, huv⟩ := hP
  filter_upwards [eventually_lift u, eventually_lift v] with w ⟨u', hu⟩ ⟨v', hv⟩ q hq
  refine ⟨u', v', Polynomial.map_injective (algebraMap _ (w.adicCompletion E)) Subtype.val_injective ?_⟩
  rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, hq, hu, hv,
    Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, huv,
    Polynomial.map_one, Polynomial.map_one]

theorem conj_of_charpoly_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w →
      γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  intro E _ _ _ hU n _ P hP
  filter_upwards [eventually_separable P hP.2.2.1] with w hsep hw γ γ' hγK hγ'K hγ hγ'
  let O := w.adicCompletionIntegers E
  let ι := algebraMap O (w.adicCompletion E)
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨y', hy'⟩ : ∃ y' : GL (Fin n) O, GeneralLinearGroup.map ι y' = γ.1 := (Subgroup.mem_subgroupOf.1 hγK)
  obtain ⟨z', hz'⟩ : ∃ z' : GL (Fin n) O, GeneralLinearGroup.map ι z' = γ'.1 := (Subgroup.mem_subgroupOf.1 hγ'K)
  obtain ⟨-, hcc, hv, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨ϖ, q, ⟨-, -, -, -, ⟨x₀, hx₀, hx₁⟩, hq2, hcard⟩, -⟩ := (h4 hw).2.1
  have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
  let c : O →+* O := (cj w).restrict _ _ (ThBasic.cj_mem_integers hU w)
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hcc _)
  have hmapc : ∀ M : Matrix (Fin n) (Fin n) O, (cT c M).map ι = cT (cj w) (M.map ι) := fun M => by
    ext i j; rfl
  have hUL : ∀ x : GLw n w, x ∈ UL n w ↔ cT (cj w) x.val * x.val = 1 := fun x => by
    rw [UL, if_neg hw]
    change cT (cj w) x.val * 1 * x.val = 1 ↔ _
    rw [mul_one]
  have hmv : ∀ x : GL (Fin n) O, (GeneralLinearGroup.map ι x).val = x.val.map ι := fun x => by
    ext i j; rfl
  have hunit : ∀ (x : GL (Fin n) O), GeneralLinearGroup.map ι x ∈ UL n w → cT c x.val * x.val = 1 := fun x hx => by
    refine Matrix.map_injective hι ?_
    show (cT c x.val * x.val).map ι = (1 : Matrix (Fin n) (Fin n) O).map ι
    rw [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι), ← hmv]
    exact (hUL _).1 hx
  have hch : ∀ x : GL (Fin n) O, x.val.charpoly.map ι = (GeneralLinearGroup.map ι x).val.charpoly := fun x =>
    (Matrix.charpoly_map _ _).symm
  have e1 : y'.val.charpoly.map ι = atPl w P := by rw [hch, hy', hγ]
  have e2 : z'.val.charpoly.map ι = atPl w P := by rw [hch, hz', hγ']
  obtain ⟨u, hu, hcu⟩ := exists_unitary_conj (IsLocalRing.maximalIdeal O) (σ := c) hc
    (fun x hx => by
      rw [GlobalTheory.InertUQ.mem_max_iff] at hx ⊢
      exact (hv _).trans_lt hx)
    ⟨⟨x₀, hx₀⟩, by
      rw [← IsLocalRing.notMem_maximalIdeal, GlobalTheory.InertUQ.mem_max_iff]
      change ¬ Valued.v (x₀ - cj w x₀) < 1
      rw [Valuation.map_sub_swap, hx₁]
      exact lt_irrefl _⟩
    (hunit y' (hy' ▸ γ.2)) (hunit z' (hz' ▸ γ'.2)) (hsep _ e1)
    (Polynomial.map_injective ι hι (e2.trans e1.symm))
  let g : GLw n w := GeneralLinearGroup.map ι u
  have hg : g ∈ UL n w := by
    rw [hUL]
    have := congrArg (fun M => M.map ι) hu
    simp only [Matrix.map_mul, hmapc, Matrix.map_one _ (map_zero ι) (map_one ι)] at this
    exact this
  have key : γ.1 * g = g * γ'.1 := by
    rw [← hy', ← hz', ← map_mul, ← map_mul]
    congr 1
    exact Units.ext hcu
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  change γ'.1 = g⁻¹ * γ.1 * g
  rw [mul_assoc, key, inv_mul_cancel_left]

end GlobalTheory.BCT.UnitInert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryConjOfSameEllipticCharpolyInertStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_unitary_conj_of_same_elliptic_charpoly_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w → γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  first | exact @GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert | exact GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert | (intros; apply GlobalTheory.BCT.UnitInert.conj_of_charpoly_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndex
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatIndexDeg
open NumberField IsDedekindDomain ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.FlatCM
open scoped nonZeroDivisors

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem ιMulti_ne_zero_of_li {m : ℕ} (v : Fin m → V) (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K m v ≠ 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Fintype.linearCombination K v)
    (LinearMap.ker_eq_bot.2 (LinearIndependent.fintypeLinearCombination_injective hv))
  intro h
  have := congrArg (exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).compLinearMap g)) h
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at this
  have hgv : ∀ i, g (v i) = Pi.single i 1 := by
    intro i
    have : v i = Fintype.linearCombination K v (Pi.single i 1) := by simp
    rw [this, ← LinearMap.comp_apply, hg, LinearMap.id_apply]
  have e : (fun i => g (v i)) = fun i => Pi.single i 1 := funext hgv
  change Matrix.det (Matrix.of fun i => g (v i)) = 0 at this
  rw [e, show (Matrix.of fun i : Fin m => (Pi.single i 1 : Fin m → K)) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one] at this
  exact one_ne_zero this


omit [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V] in
theorem colon_smul_cancel (𝔞 : Ideal (𝓞 K)) (D : Submodule (𝓞 K) K)
    (hD : IsFractional (𝓞 K)⁰ D) (h0 : D ≠ ⊥) : (𝔞 • D).colon (D : Set K) = 𝔞 := by
  ext r
  rw [Submodule.mem_colon]
  constructor
  · intro h
    set Df : FractionalIdeal (𝓞 K)⁰ K := ⟨D, hD⟩
    have hDf : Df ≠ 0 := fun e => h0 (by
      have := congrArg (fun I : FractionalIdeal (𝓞 K)⁰ K => (I : Submodule (𝓞 K) K)) e
      simpa [Df] using this)
    have hmem : ∀ x ∈ 𝔞 • D, x ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Df := by
      intro x hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha d hd
        rw [Algebra.smul_def]
        exact FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩) hd
      · intro x y hx hy
        exact Submodule.add_mem (((𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Df : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) hx hy
    have key : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r) * Df ≤
        (𝔞 : FractionalIdeal (𝓞 K)⁰ K) * Df := by
      rw [FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      have h1 := hmem _ (h j hj)
      rw [smul_mul_assoc]
      refine Submodule.smul_mem _ a ?_
      rwa [Algebra.smul_def] at h1
    have key2 := mul_le_mul_left key Df⁻¹
    rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hDf, mul_one, mul_one] at key2
    have hr := key2 (FractionalIdeal.mem_spanSingleton_self _ _)
    obtain ⟨x, hx, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 hr
    rwa [← (FaithfulSMul.algebraMap_injective (𝓞 K) K) e]
  · intro hr s hs
    exact Submodule.smul_mem_smul hr hs

variable {m : ℕ}


variable (K) in
def coordMap (v : Fin m → V) : (Fin m → K) →ₗ[𝓞 K] V :=
  (Fintype.linearCombination K v).restrictScalars (𝓞 K)

theorem coordMap_apply (v : Fin m → V) (x : Fin m → K) : coordMap K v x = ∑ i, x i • v i := by
  simp [coordMap, Fintype.linearCombination_apply]


variable (K) in
def lineMap (ω : ⋀[K]^m V) : K →ₗ[𝓞 K] ⋀[K]^m V :=
  (LinearMap.toSpanSingleton K _ ω).restrictScalars (𝓞 K)

theorem lineMap_apply (ω : ⋀[K]^m V) (t : K) : lineMap K ω t = t • ω := rfl

theorem detSpan_map_coord (v : Fin m → V) (M' : Submodule (𝓞 K) (Fin m → K)) :
    detSpan K m (M'.map (coordMap K v)) =
      (GlobalTheory.BetaEx.detSpan M').map (lineMap K (exteriorPower.ιMulti K m v)) := by
  unfold detSpan GlobalTheory.BetaEx.detSpan
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    choose x hx hxy using fun i => Submodule.mem_map.1 (hy i)
    refine ⟨(Matrix.of x).det, (GlobalTheory.BetaEx.mem_detSet M' _).2 ⟨Matrix.of x, hx, rfl⟩, ?_⟩
    have e : y = fun i => ∑ j, (Matrix.of x) i j • v j := funext fun i => by
      rw [← hxy i, coordMap_apply]; rfl
    rw [lineMap_apply, e, GlobalTheory.FlatCM.Model.ιMulti_comb]
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M' d).1 hd
    refine ⟨fun i => coordMap K v (x i), fun i => Submodule.mem_map_of_mem (hx i), ?_⟩
    have e : (fun i => coordMap K v (x i)) = fun i => ∑ j, x i j • v j := funext fun i => by
      rw [coordMap_apply]
    rw [lineMap_apply, e, GlobalTheory.FlatCM.Model.ιMulti_comb]


omit [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V] in
theorem colon_map_of_injective {A B : Type} [AddCommGroup A] [Module (𝓞 K) A] [AddCommGroup B] [Module (𝓞 K) B]
    (f : A →ₗ[𝓞 K] B) (hf : Function.Injective f) (P Q : Submodule (𝓞 K) A) :
    (P.map f).colon ((Q.map f : Submodule (𝓞 K) B) : Set B) = P.colon (Q : Set A) := by
  ext r
  simp only [Submodule.mem_colon]
  constructor
  · intro h q hq
    have := h (f q) (Submodule.mem_map_of_mem hq)
    rw [← map_smul] at this
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 this
    rwa [hf e] at hp
  · intro h b hb
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hb
    rw [← map_smul]
    exact Submodule.mem_map_of_mem (h q hq)


omit [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V] in
theorem bdd_of_fg {M : Submodule (𝓞 K) (Fin m → K)} (hM : M.FG) : GlobalTheory.BetaEx.Bdd M := by
  classical
  obtain ⟨s, rfl⟩ := hM
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 K)⁰
    (s.biUnion fun x => Finset.univ.image x)
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [GlobalTheory.BetaEx.mem_std]
    intro j
    obtain ⟨c, hc⟩ := hint (x j) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩⟩)
    exact ⟨c, hc⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem span_eq_of_latRank_eq [FiniteDimensional K V] {N L : Submodule (𝓞 K) V} (hNL : N ≤ L)
    (hr : latRank K L = latRank K N) :
    Submodule.span K (N : Set V) = Submodule.span K (L : Set V) :=
  Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono hNL) hr.symm


omit [IsScalarTower (𝓞 K) K V] in
theorem fg_of_le_fg' {N L : Submodule (𝓞 K) V} (hNL : N ≤ L) (hL : L.FG) : N.FG := by
  have : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  have hfg := IsNoetherian.noetherian (N.comap L.subtype)
  have e : (N.comap L.subtype).map L.subtype = N := by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hNL]
  exact e ▸ hfg.map _

theorem relIndex_eq_absNorm_idx [FiniteDimensional K V] {N L : Submodule (𝓞 K) V} (hNL : N ≤ L) (hL : L.FG)
    (hrL : latRank K L = m) (hrN : latRank K N = m) :
    idx K m L N ≠ ⊥ ∧ N.toAddSubgroup.relIndex L.toAddSubgroup = Ideal.absNorm (idx K m L N) := by
  have hN : N.FG := fg_of_le_fg' hNL hL
  obtain ⟨v, hv⟩ : ∃ v : Fin m → V, IsFrame K N v := hrN ▸ exists_isFrame N hN
  have hspanv : Submodule.span K (Set.range v) = Submodule.span K (N : Set V) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 hv.2.2)
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hv.1 i)
  have hLv : (L : Set V) ⊆ Submodule.span K (Set.range v) := by
    rw [hspanv, span_eq_of_latRank_eq hNL (hrL.trans hrN.symm)]
    exact Submodule.subset_span
  set ψ := coordMap K v with hψ
  have hinj : Function.Injective ψ := hv.2.1.fintypeLinearCombination_injective
  have hrange : L ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hLv hx)
    exact ⟨c, by rw [coordMap_apply]; exact hc⟩
  set L' := L.comap ψ with hL'def
  set N' := N.comap ψ with hN'def
  have hL' : L'.map ψ = L := Submodule.map_comap_eq_self hrange
  have hN' : N'.map ψ = N := Submodule.map_comap_eq_self (hNL.trans hrange)
  have hNL' : N' ≤ L' := Submodule.comap_mono hNL
  have hstd : ∀ x : Fin m → K, (∀ j, ∃ b : 𝓞 K, (b : K) = x j) → x ∈ N' := by
    intro x hx
    choose b hb using hx
    change ψ x ∈ N
    rw [coordMap_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← hb j, algebraMap_smul]
    exact N.smul_mem _ (hv.1 j)
  have hLfg : L'.FG := Submodule.fg_of_fg_map_injective ψ hinj (hL' ▸ hL)
  have hb : GlobalTheory.BetaEx.Bdd L' := bdd_of_fg hLfg
  have hb' : GlobalTheory.BetaEx.Bdd (N' ⊔ L') := by rwa [sup_eq_right.2 hNL']
  have ht : ∀ x ∈ L', ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ N' := by
    intro x hx
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk, hstd _ ((GlobalTheory.BetaEx.mem_std _).1 (h x hx))⟩
  obtain ⟨𝔞, h0, h1, -, h2⟩ := GlobalTheory.DetIdeal.exists_index_ideal_pair L' N' hLfg hb' ht
  rw [inf_eq_right.2 hNL'] at h1 h2
  have hω := ιMulti_ne_zero_of_li v hv.2.1
  have hℓ : Function.Injective (lineMap K (exteriorPower.ιMulti K m v)) :=
    fun s t e => smul_left_injective K hω e
  have hD0 : GlobalTheory.BetaEx.detSpan L' ≠ ⊥ := by
    intro e
    have h1m := GlobalTheory.BetaEx.det_mem (M := L') (1 : Matrix (Fin m) (Fin m) K) fun i => hNL' (hstd _ fun j =>
      ⟨if i = j then 1 else 0, by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]⟩)
    rw [e, Matrix.det_one] at h1m
    exact one_ne_zero ((Submodule.mem_bot _).1 h1m)
  have hidx : idx K m L N = 𝔞 := by
    unfold idx
    rw [← hL', ← hN', detSpan_map_coord, detSpan_map_coord, colon_map_of_injective _ hℓ, h1]
    exact colon_smul_cancel 𝔞 _ (GlobalTheory.BetaEx.frac_of_bdd hb) hD0
  refine ⟨hidx ▸ h0, ?_⟩
  rw [hidx, h2]
  have e : L'.toAddSubgroup.map ψ.toAddMonoidHom = L.toAddSubgroup := by
    ext x
    rw [← hL']
    simp [Submodule.mem_map]
  rw [← e]
  exact (AddSubgroup.relIndex_comap N.toAddSubgroup ψ.toAddMonoidHom L'.toAddSubgroup).symm

end GlobalTheory.LatIndexDeg

namespace GlobalTheory.LatIndexDeg
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

theorem deg_eq_deg_add_log_absNorm_idx : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (m : ℕ) (L N : Submodule (𝓞 K) V), N ≤ L → L.FG → latRank K L = m → latRank K N = m → idx K m L N ≠ ⊥ ∧ deg h L = deg h N + Real.log (Ideal.absNorm (idx K m L N)) / Module.finrank ℚ K := by
  intro K V _ _ _ _ _ _ _ h m L N hNL hL hrL hrN
  obtain ⟨hne, hidx⟩ := relIndex_eq_absNorm_idx hNL hL hrL hrN
  refine ⟨hne, ?_⟩
  have hN : N.FG := fg_of_le_fg' hNL hL
  have hspan : (L : Set V) ⊆ Submodule.span K (N : Set V) := by
    rw [span_eq_of_latRank_eq hNL (hrL.trans hrN.symm)]
    exact Submodule.subset_span
  rw [deg_of_le h hN hL hNL hspan, hidx]
  ring

end GlobalTheory.LatIndexDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndexStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_degree_eq_sublattice_degree_add_log_index : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (m : ℕ) (L N : Submodule (𝓞 K) V), N ≤ L → L.FG → latRank K L = m → latRank K N = m → idx K m L N ≠ ⊥ ∧ deg h L = deg h N + Real.log (Ideal.absNorm (idx K m L N)) / Module.finrank ℚ K := by
  first | exact @GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx | exact GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx | (intros; apply GlobalTheory.LatIndexDeg.deg_eq_deg_add_log_absNorm_idx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

theorem continuous_mixedSymm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_infAd : Continuous (infAd F) :=
  (continuous_mixedSymm F).prodMk continuous_const

theorem continuous_evI_arch : Continuous (evI F) := (continuous_mixed F).comp continuous_fst

@[simp] theorem evI_infAd (a : mixedEmbedding.mixedSpace F) : evI F (infAd F a) = a := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a) = a
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

theorem infAd_add (a b : mixedEmbedding.mixedSpace F) : infAd F (a + b) = infAd F a + infAd F b := by
  unfold infAd; rw [map_add (f := _), map_add (f := _)]

theorem infAd_zero : infAd F 0 = 0 := by unfold infAd; rw [map_zero, map_zero]

theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b := by
  exact map_add ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) a b

theorem evI_zero' : evI F 0 = 0 := by
  exact map_zero ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

abbrev dimA : ℕ := Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)

def ubasis : Module.Basis (Fin (dimA F κ)) ℝ (κ → mixedEmbedding.mixedSpace F) :=
  (Module.finBasis ℝ _).unitsSMul fun j =>
    Units.mk0 ‖Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F) j‖⁻¹
      (inv_ne_zero (norm_ne_zero_iff.2 ((Module.finBasis ℝ _).ne_zero j)))

theorem norm_ubasis (j : Fin (dimA F κ)) : ‖ubasis F κ j‖ = 1 := by
  have h := norm_ne_zero_iff.2 ((Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)).ne_zero j)
  simp [ubasis, Module.Basis.unitsSMul_apply, norm_smul, h]

def archIn : (Fin (dimA F κ) → ℝ) →+ (κ → AF F) where
  toFun t := fun i => infAd F ((ubasis F κ).equivFun.symm t i)
  map_zero' := by funext i; rw [map_zero]; exact infAd_zero F
  map_add' s t := by funext i; rw [map_add (f := _)]; exact infAd_add F _ _

def archOut : (κ → AF F) →+ (Fin (dimA F κ) → ℝ) where
  toFun x := (ubasis F κ).equivFun (arch F x)
  map_zero' := by
    have : arch F (0 : κ → AF F) = 0 := by funext i; exact evI_zero' F
    rw [this, map_zero]
  map_add' x y := by
    have : arch F (x + y) = arch F x + arch F y := by funext i; exact evI_add' F _ _
    rw [this, map_add (f := _)]

theorem archIn_apply (t : Fin (dimA F κ) → ℝ) (i : κ) :
    archIn F κ t i = infAd F ((ubasis F κ).equivFun.symm t i) := rfl

theorem archOut_apply (x : κ → AF F) : archOut F κ x = (ubasis F κ).equivFun (arch F x) := rfl

@[simp] theorem archOut_archIn (t : Fin (dimA F κ) → ℝ) : archOut F κ (archIn F κ t) = t := by
  have : arch F (archIn F κ t) = (ubasis F κ).equivFun.symm t := by funext i; simp [arch, archIn_apply]
  rw [archOut_apply, this, LinearEquiv.apply_symm_apply]

theorem continuous_archIn : Continuous (archIn F κ) := by
  refine continuous_pi fun i => ?_
  show Continuous fun t => infAd F ((ubasis F κ).equivFun.symm t i)
  exact (continuous_infAd F).comp ((continuous_apply i).comp
    (LinearMap.continuous_of_finiteDimensional (ubasis F κ).equivFun.symm.toLinearMap))

theorem continuous_archOut : Continuous (archOut F κ) := by
  show Continuous fun x => (ubasis F κ).equivFun (arch F x)
  exact (LinearMap.continuous_of_finiteDimensional (ubasis F κ).equivFun.toLinearMap).comp
    (continuous_pi fun i => (continuous_evI_arch F).comp (continuous_apply i))

def perSet (m : ℕ) : Set (κ → AF F) :=
  {z | ∀ i, ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧ z i = (m : AF F) * a}

def slab (m : ℕ) : Set (κ → AF F) := {w | w - archIn F κ (archOut F κ w) ∈ perSet F κ m}

def cube (N : ℕ) : Set (Fin N → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

end GlobalTheory.ArchDecay
end
end
