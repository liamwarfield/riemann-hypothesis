module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTri
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerRestrictedProductIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerRestrictedProductIff
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerAbs

theorem mem_twCent_iff_forall_comp : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → ∀ (δ x : X), x ∈ twCent θ δ ↔ ∀ v, pf v x ∈ twCent (θv v) (pf v δ) := by
  intro X V Y _ _ _ _ pf K hX θ θv hθ δ x
  simp only [twCent, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h v
    have := congrArg (pf v) h
    simpa [map_mul, hθ] using this
  · intro h
    apply hX.ext
    · intro w; exact Empty.elim w
    · intro v
      simpa [map_mul, hθ] using h v

end GlobalTheory.EulerAbs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerRestrictedProductIffStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_twistedCentralizer_restrictedProduct_iff : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → ∀ (δ x : X), x ∈ twCent θ δ ↔ ∀ v, pf v x ∈ twCent (θv v) (pf v δ) := by
  first | exact @GlobalTheory.EulerAbs.mem_twCent_iff_forall_comp | exact GlobalTheory.EulerAbs.mem_twCent_iff_forall_comp | (intros; apply GlobalTheory.EulerAbs.mem_twCent_iff_forall_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalTermEqFinprodLocalTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexRestrictedProductComponentwiseEqProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexRestrictedProductComponentwiseEqProd
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RelIdxRestr

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_iInf_comap {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (C H : ∀ v, Subgroup (Y v))
    (_hfin : ∀ v, (H v).relIndex (C v) ≠ 0) (hev : ∀ᶠ v in cofinite, C v ≤ H v) :
    (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  classical
  set S : Finset V := (Filter.eventually_cofinite.1 hev).toFinset with hS
  have hSm : ∀ v, v ∉ S → C v ≤ H v := fun v hv => by
    by_contra h; exact hv (by simpa [hS] using h)
  set Cg := ⨅ v, (C v).comap (pf v)
  set Hg := ⨅ v, (H v).comap (pf v)
  have hmemC : ∀ x : X, x ∈ Cg ↔ ∀ v, pf v x ∈ C v := fun x => by simp [Cg, Subgroup.mem_iInf]
  have hmemH : ∀ x : X, x ∈ Hg ↔ ∀ v, pf v x ∈ H v := fun x => by simp [Hg, Subgroup.mem_iInf]
  let φ : Cg →* ∀ v : S, C v := MonoidHom.pi fun v =>
    ((pf v).comp Cg.subtype).codRestrict (C v) fun x => (hmemC x).1 x.2 v
  have hφ : ∀ x (v : S), ((φ x v : C v) : Y v) = pf v x := fun _ _ => rfl
  have hsurj : Function.Surjective φ := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z
      (GlobalTheory.RestrMeas.eventually_of_finset S fun v hv => by simp [z, hv, one_mem])
    have hxC : x ∈ Cg := (hmemC x).2 fun v => by
      rw [hx v]
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    refine ⟨⟨x, hxC⟩, funext fun v => Subtype.ext ?_⟩
    rw [hφ]
    show pf v x = _
    rw [hx v]
    simp [z, v.2]
  have hcomap : Hg.subgroupOf Cg = (Subgroup.pi Set.univ fun v : S => (H v).subgroupOf (C v)).comap φ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, hmemH]
    constructor
    · intro h v; exact h v
    · intro h v
      by_cases hv : v ∈ S
      · exact h ⟨v, hv⟩
      · exact hSm v hv ((hmemC x).1 x.2 v)
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ,
    finprod_eq_prod_of_mulSupport_subset (s := S)]
  · exact (Finset.prod_coe_sort S fun v => (H v).relIndex (C v))
  · intro v hv
    by_contra h
    exact hv (Subgroup.relIndex_eq_one.2 (hSm v h))

end GlobalTheory.RelIdxRestr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexRestrictedProductComponentwiseEqProdStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (C H : ∀ v, Subgroup (Y v)), (∀ v, (H v).relIndex (C v) ≠ 0) → (∀ᶠ v in cofinite, C v ≤ H v) → (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  first | exact @GlobalTheory.RelIdxRestr.relIndex_iInf_comap | exact GlobalTheory.RelIdxRestr.relIndex_iInf_comap | (intros; apply GlobalTheory.RelIdxRestr.relIndex_iInf_comap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageRestrictedProductMaxCompactProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageRestrictedProductMaxCompactProd
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AvgRestr

theorem apply_out_mk {G : Type} [Group G] (u : G → ℂ) (x : G) :
    u ((QuotientGroup.mk x : G ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  exact k.2 x

theorem avg_pi_comp {H : Type} [Group H] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (π : H →* ∀ i, G i) (hπ : Function.Surjective π) (u : ∀ i, G i → ℂ) (hu : ∀ i, (rStab (u i)).index ≠ 0) :
    avg (fun k => ∏ i, u i (π k i)) = ∏ i, avg (u i) := by
  set P : Subgroup (∀ i, G i) := Subgroup.pi Set.univ fun i => rStab (u i) with hP
  set R : Subgroup H := P.comap π with hRdef
  have hPi : P.index = ∏ i, (rStab (u i)).index := by
    simp_rw [hP, Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  have hRi : R.index = ∏ i, (rStab (u i)).index := by
    rw [hRdef, Subgroup.index_comap_of_surjective _ hπ, hPi]
  have hR0 : R.index ≠ 0 := by rw [hRi]; exact Finset.prod_ne_zero_iff.2 fun i _ => hu i
  have hRle : R ≤ rStab (fun k => ∏ i, u i (π k i)) := by
    intro k hk x
    have hk' : ∀ i, π k i ∈ rStab (u i) := fun i => ((Subgroup.mem_pi _).1 hk) i (Set.mem_univ i)
    simp only [map_mul, Pi.mul_apply]
    exact Finset.prod_congr rfl fun i _ => hk' i (π x i)
  rw [avg_eq_of_le_rStab H _ R hRle hR0]
  haveI : R.FiniteIndex := ⟨hR0⟩
  haveI : ∀ i, (rStab (u i)).FiniteIndex := fun i => ⟨hu i⟩
  haveI : Fintype (H ⧸ R) := Fintype.ofFinite _
  haveI : ∀ i, Fintype (G i ⧸ rStab (u i)) := fun i => Fintype.ofFinite _
  let e : H ⧸ R → ∀ i, G i ⧸ rStab (u i) := fun q i => QuotientGroup.mk (π q.out i)
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      apply QuotientGroup.eq.2
      show π (q.out⁻¹ * q'.out) ∈ P
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      have := QuotientGroup.eq.1 (congrFun hq i)
      simpa [map_mul, map_inv] using this
    · intro x
      obtain ⟨k, hk⟩ := hπ fun i => (x i).out
      refine ⟨QuotientGroup.mk k, funext fun i => ?_⟩
      obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul R k
      have hr' : π r ∈ P := r.2
      show (QuotientGroup.mk (π (QuotientGroup.mk k : H ⧸ R).out i) : G i ⧸ rStab (u i)) = x i
      rw [hr, map_mul, Pi.mul_apply, hk]
      conv_rhs => rw [← QuotientGroup.out_eq' (x i)]
      apply QuotientGroup.eq.2
      simpa using ((Subgroup.mem_pi _).1 hr') i (Set.mem_univ i)
  have hsum : ∑ᶠ q : H ⧸ R, ∏ i, u i (π q.out i) = ∏ i, ∑ᶠ q : G i ⧸ rStab (u i), u i q.out := by
    rw [finsum_eq_sum_of_fintype]
    simp_rw [finsum_eq_sum_of_fintype]
    rw [Fintype.prod_sum]
    exact Fintype.sum_bijective e he _ _ fun q => Finset.prod_congr rfl fun i _ => (apply_out_mk (u i) _).symm
  rw [hsum, hRi]
  simp only [avg]
  rw [Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_inv_distrib]

end GlobalTheory.AvgRestr

namespace GlobalTheory.AvgRestr

theorem avg_restr_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)),
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ),
    (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) →
    avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      ∏ᶠ v, avg (u v) := by
  intro X V Y _ _ _ _ pf K hX u hu hev
  obtain ⟨S, hS⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually hev
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  let π : Kg →* ∀ v : S, K v.1 := MonoidHom.pi fun v =>
    ((pf v.1).comp Kg.subtype).codRestrict (K v.1) fun k => Subgroup.mem_iInf.1 k.2 v.1
  have hπ : Function.Surjective π := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    have hz : ∀ v, z v ∈ K v := fun v => by
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z (Eventually.of_forall hz)
    have hxK : x ∈ Kg := Subgroup.mem_iInf.2 fun v => by
      show pf v x ∈ K v
      rw [hx v]; exact hz v
    refine ⟨⟨x, hxK⟩, funext fun v => Subtype.ext ?_⟩
    show pf v.1 x = (y v : Y v.1)
    rw [hx v.1]
    simp [z, v.2]
  have hF : (fun k : Kg => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      fun k => ∏ v : S, u v.1 (π k v) := by
    funext k
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv (hS v h _),
      ← Finset.prod_coe_sort S]
    rfl
  have hA : ∏ᶠ v, avg (u v) = ∏ v : S, avg (u v.1) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv ?_,
      ← Finset.prod_coe_sort S]
    have hc : u v = fun _ => 1 := funext (hS v h)
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (fun _ : K v => (1 : ℂ)) (fun _ => 1) 1 1
      (by rw [← hc]; exact hu v) (by rw [← hc]; exact hu v)).2.2.2
  rw [hF, hA]
  exact avg_pi_comp π hπ (fun v : S => u v.1) fun v => hu v.1

end GlobalTheory.AvgRestr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageRestrictedProductMaxCompactProdStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAverage_restrictedProduct_maxCompact_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ), (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) → avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) = ∏ᶠ v, avg (u v) := by
  first | exact @GlobalTheory.AvgRestr.avg_restr_prod | exact GlobalTheory.AvgRestr.avg_restr_prod | (intros; apply GlobalTheory.AvgRestr.avg_restr_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalTermEqFinprodLocalTerms
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

open GlobalTheory.BCT

theorem mem_map_conj_iff_term {G : Type} [Group G] (K : Subgroup G) (y z : G) :
    z ∈ K.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem cptPart_le_self_term {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T :=
  Subgroup.closure_le _ |>.mpr fun _ ht => ht.1

theorem inf_relIndex_of_le_left_term {G : Type} [Group G] {A B C : Subgroup G} (h : C ≤ A) :
    (A ⊓ B).relIndex C = B.relIndex C := by
  unfold Subgroup.relIndex
  congr 1
  ext ⟨c, hc⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact and_iff_right (h hc)

theorem avg_eq_one_of_forall_term {H : Type} [Group H] (u : H → ℂ) (hu : ∀ k, u k = 1) : avg u = 1 := by
  have hs : rStab u = ⊤ := by
    ext k; simp only [Subgroup.mem_top, iff_true]; intro x; rw [hu, hu]
  have hi : (rStab u).index = 1 := Subgroup.index_eq_one.2 hs
  have hsub : Subsingleton (H ⧸ rStab u) := by
    have hc : Nat.card (H ⧸ rStab u) = 1 := hi
    exact (Nat.card_eq_one_iff_unique.1 hc).1
  unfold avg
  rw [hi, finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ rStab u) (fun q hq => absurd (Subsingleton.elim q _) hq), hu]
  simp

theorem twTerm_eq_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v) → ∀ x, GlobalTheory.EulerAbs.twTerm θ (⨅ v, (K v).comap (pf v)) δ f x = ∏ᶠ v, GlobalTheory.EulerAbs.twTerm (θv v) (K v) (pf v δ) (fv v) (pf v x) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX θ θv hθ hK δ f fv hf hcomm hstab hwt hev x
  have hT : ∀ y, y ∈ twCent θ δ ↔ ∀ v, pf v y ∈ twCent (θv v) (pf v δ) := fun y => GlobalTheory.T.mem_twistedCentralizer_restrictedProduct_iff pf K hX θ θv hθ δ y
  have hC : ∀ y, y ∈ cptPart (twCent θ δ) ↔ ∀ v, pf v y ∈ cptPart (twCent (θv v) (pf v δ)) :=
    GlobalTheory.T.mem_compactPart_restrictedProduct_iff_forall pf K hX (twCent θ δ) (fun v => twCent (θv v) (pf v δ)) hT hcomm
  have hgood := hev.and (hX.eventually_mem x)
  have hCg : cptPart (twCent θ δ) = ⨅ v, (cptPart (twCent (θv v) (pf v δ))).comap (pf v) := by
    ext y; rw [hC, Subgroup.mem_iInf]; rfl
  have hHg : (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom =
      ⨅ v, ((K v).map (MulAut.conj (pf v x)).toMonoidHom).comap (pf v) := by
    ext y
    simp only [mem_map_conj_iff_term, Subgroup.mem_iInf, Subgroup.mem_comap, map_mul, map_inv]
  have hloc : ∀ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) = ((K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := fun v => inf_relIndex_of_le_left_term (cptPart_le_self_term _)
  have hCH : ∀ᶠ v in cofinite, cptPart (twCent (θv v) (pf v δ)) ≤ (K v).map (MulAut.conj (pf v x)).toMonoidHom :=
    hgood.mono fun v hv c hc => by
      rw [mem_map_conj_iff_term]
      exact mul_mem (mul_mem (inv_mem hv.2) (hv.1.2.2 hc)) hv.2
  have hrel : (twCent θ δ ⊓ (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom).relIndex
      (cptPart (twCent θ δ)) = ∏ᶠ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := by
    rw [inf_relIndex_of_le_left_term (cptPart_le_self_term _), hHg, hCg]
    simp only [hloc]
    exact GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod pf K hX (fun v => cptPart (twCent (θv v) (pf v δ)))
      (fun v => (K v).map (MulAut.conj (pf v x)).toMonoidHom)
      (fun v => by rw [← hloc]; exact (hwt v (pf v x)).2) hCH
  let u : ∀ v, K v → ℂ := fun v k => fv v ((pf v x * k)⁻¹ * pf v δ * θv v (pf v x * k))
  have hfun : (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩ := by
    funext k; rw [hf]; congr 1; funext v; simp only [u, map_mul, map_inv, hθ]
  have hu1 : ∀ᶠ v in cofinite, ∀ k, u v k = 1 := hgood.mono fun v hv k => by
    have hk : pf v x * (k : Y v) ∈ K v := mul_mem hv.2 k.2
    simp only [u]
    rw [hv.1.1, Set.indicator_of_mem (show _ ∈ (K v : Set (Y v)) from
      mul_mem (mul_mem (inv_mem hk) hv.1.2.1) (hK v _ hk))]
    rfl
  have havg : avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      ∏ᶠ v, avg (u v) := by
    rw [hfun]; exact GlobalTheory.T.groupAverage_restrictedProduct_maxCompact_prod pf K hX u (fun v => hstab v (pf v x)) hu1
  have hfa : Function.HasFiniteMulSupport fun v => (((twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) : ℕ) : ℂ) :=
    (eventually_cofinite.1 hCH).subset fun v hv h => hv (by
      show ((_ : ℕ) : ℂ) = 1
      rw [hloc, Subgroup.relIndex_eq_one.2 h, Nat.cast_one])
  have hfb : Function.HasFiniteMulSupport fun v => avg (u v) :=
    (eventually_cofinite.1 hu1).subset fun v hv h => hv (avg_eq_one_of_forall_term _ h)
  unfold twTerm
  rw [hrel, havg, Nat.cast_finprod', ← finprod_mul_distrib hfa hfb]

end GlobalTheory.EulerAbs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalTermEqFinprodLocalTermsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalTerm_eq_finprod_localTerms : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v) → ∀ x, GlobalTheory.EulerAbs.twTerm θ (⨅ v, (K v).comap (pf v)) δ f x = ∏ᶠ v, GlobalTheory.EulerAbs.twTerm (θv v) (K v) (pf v δ) (fv v) (pf v x) := by
  first | exact @GlobalTheory.EulerAbs.twTerm_eq_finprod | exact GlobalTheory.EulerAbs.twTerm_eq_finprod | (intros; apply GlobalTheory.EulerAbs.twTerm_eq_finprod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermDoubleCosetInvari
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermDoubleCosetInvari
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

variable {G : Type} [Group G]

theorem twCent_mul_inv_conj (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (z : G) :
    (t * z)⁻¹ * δ * θ (t * z) = z⁻¹ * δ * θ z := by
  have htd : t * δ = δ * θ t := ht
  rw [map_mul, _root_.mul_inv_rev]
  calc z⁻¹ * t⁻¹ * δ * (θ t * θ z) = z⁻¹ * (t⁻¹ * (δ * θ t)) * θ z := by simp only [mul_assoc]
    _ = z⁻¹ * δ * θ z := by rw [← htd, inv_mul_cancel_left]

theorem twCent_inf_map_conj (θ : G →* G) (K : Subgroup G) (δ : G)
    (hcomm : ∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) {t : G} (ht : t ∈ twCent θ δ) (y : G) {k : G}
    (hk : k ∈ K) :
    twCent θ δ ⊓ K.map (MulAut.conj (t * y * k)).toMonoidHom = twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hxT, z, hz, rfl⟩
    refine ⟨hxT, k * z * k⁻¹, K.mul_mem (K.mul_mem hk hz) (K.inv_mem hk), ?_⟩
    have hx : t * y * k * z * (t * y * k)⁻¹ = t * (y * (k * z * k⁻¹) * y⁻¹) * t⁻¹ := by group
    rw [hx] at hxT ⊢
    have hlT : y * (k * z * k⁻¹) * y⁻¹ ∈ twCent θ δ := by
      have h := (twCent θ δ).mul_mem ((twCent θ δ).mul_mem ((twCent θ δ).inv_mem ht) hxT) ht
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
    rw [hcomm t ht _ hlT, mul_inv_cancel_right]
  · rintro ⟨hxT, z, hz, rfl⟩
    refine ⟨hxT, k⁻¹ * z * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hz) hk, ?_⟩
    have hx : t * y * k * (k⁻¹ * z * k) * (t * y * k)⁻¹ = t * (y * z * y⁻¹) * t⁻¹ := by group
    rw [hx, hcomm t ht _ hxT, mul_inv_cancel_right]

theorem twTerm_mul_mul [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hcomm : ∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a)
    (hidx : ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) :
    ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, twTerm θ K δ f (t * y * k) = twTerm θ K δ f y := by
  intro t ht y k hk
  unfold twTerm
  rw [twCent_inf_map_conj θ K δ hcomm ht y hk]
  congr 1
  have key := (GlobalTheory.AvgLin.avg_linear_translate_const K (fun k' : K => f ((y * k')⁻¹ * δ * θ (y * k'))) (fun k' : K => f ((y * k')⁻¹ * δ * θ (y * k')))
    0 ⟨k, hk⟩ (hidx y) (hidx y)).2.2.1
  rw [← key]
  congr 1
  funext k'
  congr 1
  rw [Subgroup.coe_mul, Subgroup.coe_mk, mul_assoc t y, mul_assoc t (y * k), ← mul_assoc y k]
  exact twCent_mul_inv_conj θ δ ht _

theorem twTerm_inv : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ),
    (∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) →
    (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) →
    ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, GlobalTheory.EulerAbs.twTerm θ K δ f (t * y * k) = GlobalTheory.EulerAbs.twTerm θ K δ f y :=
  fun θ K δ f hcomm hidx => twTerm_mul_mul θ K δ f hcomm hidx

end GlobalTheory.EulerAbs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermDoubleCosetInvariStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegralPointTerm_doubleCoset_invariant : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ), (∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) → (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) → ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, GlobalTheory.EulerAbs.twTerm θ K δ f (t * y * k) = GlobalTheory.EulerAbs.twTerm θ K δ f y := by
  first | exact @GlobalTheory.EulerAbs.twTerm_inv | exact GlobalTheory.EulerAbs.twTerm_inv | (intros; apply GlobalTheory.EulerAbs.twTerm_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZero
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

theorem exists_ne_zero_of_twTerm_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (δ : G) (f : G → ℂ) (y : G) (h : GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0) :
    ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  have hu : (fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))) = fun _ => 0 := by
    funext k
    exact hc k k.2
  unfold GlobalTheory.EulerAbs.twTerm
  rw [hu]
  simp [GlobalTheory.BCT.avg]

end GlobalTheory.EulerAbs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZeroStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G), GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0 → ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  first | exact @GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | exact GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | (intros; apply GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRestrictedProductEqProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRestrictedProductEqProd
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

open GlobalTheory.RestrMeas

theorem finsum_doubleCoset_restr {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X]
    [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (T : Subgroup X)
    (Tv : ∀ v, Subgroup (Y v)) (hT : ∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) (F : X → ℂ) (Fv : ∀ v, Y v → ℂ)
    (hF : ∀ x, F x = ∏ᶠ v, Fv v (pf v x))
    (hinv : ∀ v, ∀ t ∈ Tv v, ∀ y, ∀ k ∈ K v, Fv v (t * y * k) = Fv v y)
    (hfin : ∀ v, {q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)) | Fv v (Quotient.out q) ≠ 0}.Finite)
    (hev : ∀ᶠ v in cofinite, Fv v 1 = 1 ∧ ∀ y, Fv v y ≠ 0 → ∃ t ∈ Tv v, ∃ k ∈ K v, y = t * k) :
    ∑ᶠ q : DoubleCoset.Quotient (T : Set X) ((⨅ v, (K v).comap (pf v) : Subgroup X) : Set X), F (Quotient.out q) =
      ∏ᶠ v, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) := by
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  have memKg : ∀ x, x ∈ Kg ↔ ∀ v, pf v x ∈ K v := fun x => by simp [hKg, Subgroup.mem_iInf]
  obtain ⟨S0, hS0⟩ := exists_finset_of_eventually hev

  have L0 : ∀ v (z₁ z₂ : Y v), DoubleCoset.mk (Tv v) (K v) z₁ = DoubleCoset.mk (Tv v) (K v) z₂ →
      Fv v z₁ = Fv v z₂ := fun v z₁ z₂ h => by
    obtain ⟨t, ht, k, hk, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
    rw [e, hinv v t ht z₁ k hk]
  have L0' : ∀ v (z : Y v), Fv v (Quotient.out (DoubleCoset.mk (Tv v) (K v) z)) = Fv v z := fun v z =>
    L0 v _ _ (DoubleCoset.out_eq' _)

  have L1 : ∀ x y, DoubleCoset.mk T Kg x = DoubleCoset.mk T Kg y → ∀ v,
      DoubleCoset.mk (Tv v) (K v) (pf v x) = DoubleCoset.mk (Tv v) (K v) (pf v y) := fun x y h v => by
    obtain ⟨t, ht, k, hk, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
    exact (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨pf v t, (hT t).1 ht v, pf v k, (memKg k).1 hk v, by rw [e]; simp⟩

  have L1' : ∀ x y, (∀ v, DoubleCoset.mk (Tv v) (K v) (pf v x) = DoubleCoset.mk (Tv v) (K v) (pf v y)) →
      DoubleCoset.mk T Kg x = DoubleCoset.mk T Kg y := fun x y h => by
    have h' := fun v => (@DoubleCoset.eq _ _ _ _ _ _).1 (h v)
    choose t ht k hk e using h'
    let t' : ∀ v, Y v := fun v => if pf v x ∈ K v ∧ pf v y ∈ K v then 1 else t v
    have ht'T : ∀ v, t' v ∈ Tv v := fun v => by
      by_cases c : pf v x ∈ K v ∧ pf v y ∈ K v
      · simp only [t', if_pos c]; exact one_mem _
      · simp only [t', if_neg c]; exact ht v
    have ht'K : ∀ v, (pf v x)⁻¹ * (t' v)⁻¹ * pf v y ∈ K v := fun v => by
      by_cases c : pf v x ∈ K v ∧ pf v y ∈ K v
      · simp only [t', if_pos c, inv_one, mul_one]; exact mul_mem (inv_mem c.1) c.2
      · simp only [t', if_neg c]; rw [e v]; simpa [mul_assoc] using hk v
    have hev' : ∀ᶠ v in cofinite, t' v ∈ K v := ((hX.eventually_mem x).and (hX.eventually_mem y)).mono
      fun v c => by simp only [t', if_pos c]; exact one_mem _
    obtain ⟨g, -, hg⟩ := hX.exists_eq Empty.elim t' hev'
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨g, (hT g).2 fun v => hg v ▸ ht'T v, x⁻¹ * g⁻¹ * y,
      (memKg _).2 fun v => by simpa [hg v] using ht'K v, by group⟩

  have ProjectionSandwichLength : ∀ x, (Function.mulSupport fun v => Fv v (pf v x)).Finite := fun x => by
    have hE : ∀ᶠ v in cofinite, pf v x ∈ K v ∧ v ∉ S0 :=
      (hX.eventually_mem x).and (eventually_of_finset S0 fun v hv => hv)
    refine (eventually_cofinite.1 hE).subset fun v hv c => hv ?_
    show Fv v (pf v x) = 1
    have := hinv v 1 (one_mem _) 1 (pf v x) c.1
    rw [one_mul, one_mul] at this
    rw [this, (hS0 v c.2).1]
  have L2 : ∀ x, F x ≠ 0 → ∀ v, Fv v (pf v x) ≠ 0 := fun x hx v h0 =>
    hx (by rw [hF]; exact finprod_eq_zero _ v h0 (ProjectionSandwichLength x))
  have KernelIndexFullLattice : ∀ v ∉ S0, ∀ y : Y v, Fv v y ≠ 0 → DoubleCoset.mk (Tv v) (K v) y = DoubleCoset.mk (Tv v) (K v) 1 ∧
      Fv v y = 1 := fun v hv y hy => by
    obtain ⟨t, ht, k, hk, e⟩ := (hS0 v hv).2 y hy
    refine ⟨((@DoubleCoset.eq _ _ _ _ _ _).2 ⟨t, ht, k, hk, by rw [e, mul_one]⟩).symm, ?_⟩
    rw [e, ← (hS0 v hv).1, ← hinv v t ht 1 k hk, mul_one]
  have DegreeKernelLowerBound : ∀ x, (∀ v ∉ S0, Fv v (pf v x) ≠ 0) → F x = ∏ v ∈ S0, Fv v (pf v x) := fun x h => by
    rw [hF]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hS
    exact hv (KernelIndexFullLattice v hS _ (h v hS)).2

  have L3 : ∀ v ∉ S0, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) = 1 :=
    fun v hv => by
    rw [finsum_eq_single _ (DoubleCoset.mk (Tv v) (K v) 1), L0', (hS0 v hv).1]
    intro q hq
    by_contra h0
    apply hq
    rw [← DoubleCoset.out_eq' q]
    exact (KernelIndexFullLattice v hv _ h0).1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S0) fun v hv => by_contra fun h => hv (L3 v h),
    ← Finset.prod_coe_sort S0]
  let Q := fun v : S0 => DoubleCoset.Quotient (Tv v.1 : Set (Y v.1)) (K v.1 : Set (Y v.1))
  let Φ : DoubleCoset.Quotient (T : Set X) (Kg : Set X) → ∀ v : S0, Q v :=
    fun q v => DoubleCoset.mk (Tv v.1) (K v.1) (pf v.1 (Quotient.out q))
  let H : (∀ v : S0, Q v) → ℂ := fun b => ∏ v : S0, Fv v.1 (Quotient.out (b v))
  have hH : ∀ b, H b ≠ 0 → ∀ v : S0, Fv v.1 (Quotient.out (b v)) ≠ 0 := fun b hb v =>
    Finset.prod_ne_zero_iff.1 hb v (Finset.mem_univ _)
  have hval : ∀ q, F (Quotient.out q) ≠ 0 → F (Quotient.out q) = H (Φ q) := fun q hq => by
    rw [DegreeKernelLowerBound _ fun v _ => L2 _ hq v, ← Finset.prod_coe_sort S0]
    exact Finset.prod_congr rfl fun v _ => (L0' v.1 _).symm
  have hbij : Set.BijOn Φ (Function.support fun q => F (Quotient.out q)) (Function.support H) := by
    refine ⟨fun q hq => ?_, fun q₁ h₁ q₂ h₂ e => ?_, fun b hb => ?_⟩
    · show H (Φ q) ≠ 0
      rw [← hval q hq]; exact hq
    · rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂]
      refine L1' _ _ fun v => ?_
      by_cases hv : v ∈ S0
      · exact congrFun e ⟨v, hv⟩
      · rw [(KernelIndexFullLattice v hv _ (L2 _ h₁ v)).1, (KernelIndexFullLattice v hv _ (L2 _ h₂ v)).1]
    · have hb' := hH b hb
      let y : ∀ v, Y v := fun v => if h : v ∈ S0 then Quotient.out (b ⟨v, h⟩) else 1
      obtain ⟨x, -, hx⟩ := hX.exists_eq Empty.elim y
        (eventually_of_finset S0 fun v hv => by simp only [y, dif_neg hv]; exact one_mem _)
      have hq := L1 _ _ (DoubleCoset.out_eq' (DoubleCoset.mk T Kg x))
      have hxS : ∀ v : S0, DoubleCoset.mk (Tv v.1) (K v.1) (pf v.1 x) = b v := fun v => by
        rw [hx, show y v.1 = Quotient.out (b v) by simp [y, v.2]]
        exact DoubleCoset.out_eq' _
      have hΦ : Φ (DoubleCoset.mk T Kg x) = b := funext fun v => (hq v.1).trans (hxS v)
      refine ⟨DoubleCoset.mk T Kg x, ?_, hΦ⟩
      show F _ ≠ 0
      have hne : ∀ v ∉ S0, Fv v (pf v (Quotient.out (DoubleCoset.mk T Kg x))) ≠ 0 := fun v hv => by
        rw [L0 v _ _ (hq v), hx]; simp only [y, dif_neg hv, (hS0 v hv).1]; exact one_ne_zero
      rw [DegreeKernelLowerBound _ hne, Finset.prod_ne_zero_iff]
      intro v hv
      rw [L0 v _ _ (hq v), hx]
      simp only [y, dif_pos hv]
      exact hb' ⟨v, hv⟩
  refine ((finsum_mem_support _).symm.trans ((finsum_mem_eq_of_bijOn Φ hbij fun q hq => hval q hq).trans
    (finsum_mem_support H))).trans ?_
  have hsum : ∀ v : S0, ∑ᶠ q : Q v, Fv v.1 (Quotient.out q) =
      ∑ q ∈ (hfin v.1).toFinset, Fv v.1 (Quotient.out q) := fun v =>
    finsum_eq_sum_of_support_subset _ fun q hq => (hfin v.1).mem_toFinset.2 hq
  rw [Finset.prod_congr rfl fun v _ => hsum v, Finset.prod_univ_sum]
  refine finsum_eq_sum_of_support_subset H fun b hb => ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  exact fun v => by simpa using hH b hb v

end GlobalTheory.EulerAbs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetRestrictedProductEqProdStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_doubleCoset_restrictedProduct_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → ∀ (F : X → ℂ) (Fv : ∀ v, Y v → ℂ), (∀ x, F x = ∏ᶠ v, Fv v (pf v x)) → (∀ v, ∀ t ∈ Tv v, ∀ y, ∀ k ∈ K v, Fv v (t * y * k) = Fv v y) → (∀ v, {q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)) | Fv v (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ v in cofinite, Fv v 1 = 1 ∧ ∀ y, Fv v y ≠ 0 → ∃ t ∈ Tv v, ∃ k ∈ K v, y = t * k) → ∑ᶠ q : DoubleCoset.Quotient (T : Set X) ((⨅ v, (K v).comap (pf v) : Subgroup X) : Set X), F (Quotient.out q) = ∏ᶠ v, ∑ᶠ q : DoubleCoset.Quotient (Tv v : Set (Y v)) (K v : Set (Y v)), Fv v (Quotient.out q) := by
  first | exact @GlobalTheory.EulerAbs.finsum_doubleCoset_restr | exact GlobalTheory.EulerAbs.finsum_doubleCoset_restr | (intros; apply GlobalTheory.EulerAbs.finsum_doubleCoset_restr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermOneUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermOneUnramified
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerAbs

theorem avg_const_one {H : Type} [Group H] : avg (fun _ : H => (1 : ℂ)) = 1 := by
  have hs : rStab (fun _ : H => (1 : ℂ)) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
  rw [finsum_unique]
  simp

theorem twTerm_one_eq_one {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (hθ : ∀ k ∈ K, θ k ∈ K) (hδ : δ ∈ K) (hc : cptPart (twCent θ δ) ≤ K) :
    twTerm θ K δ ((K : Set G).indicator 1) 1 = 1 := by
  have hT : cptPart (twCent θ δ) ≤ twCent θ δ := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht; exact ht.1
  have hmap : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
    ext x; simp
  have hidx : ((twCent θ δ ⊓ K.map (MulAut.conj (1 : G)).toMonoidHom).relIndex (cptPart (twCent θ δ))) = 1 := by
    rw [hmap, Subgroup.relIndex_eq_one]
    exact le_inf hT hc
  have hf : (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((1 * (k : G))⁻¹ * δ * θ (1 * k))) = fun _ => 1 := by
    funext k
    rw [Set.indicator_of_mem]
    · rfl
    · simp only [one_mul, SetLike.mem_coe]
      exact K.mul_mem (K.mul_mem (K.inv_mem k.2) hδ) (hθ _ k.2)
  unfold twTerm
  rw [hidx, hf, avg_const_one]
  simp

end GlobalTheory.EulerAbs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermOneUnramifiedStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegralPointTerm_one_unramified : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G), (∀ k ∈ K, θ k ∈ K) → δ ∈ K → cptPart (twCent θ δ) ≤ K → GlobalTheory.EulerAbs.twTerm θ K δ ((K : Set G).indicator 1) 1 = 1 := by
  first | exact @GlobalTheory.EulerAbs.twTerm_one_eq_one | exact GlobalTheory.EulerAbs.twTerm_one_eq_one | (intros; apply GlobalTheory.EulerAbs.twTerm_one_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralRestrictedProductFinprod
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

theorem twOrb_restr_eq_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v, {q : DoubleCoset.Quotient (twCent (θv v) (pf v δ) : Set (Y v)) (K v : Set (Y v)) | ∃ k ∈ K v, fv v ((Quotient.out q * k)⁻¹ * pf v δ * θv v (Quotient.out q * k)) ≠ 0}.Finite) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v ∧ ∀ y, y⁻¹ * pf v δ * θv v y ∈ K v → ∃ t ∈ twCent (θv v) (pf v δ), ∃ k ∈ K v, y = t * k) → twOrb θ (⨅ v, (K v).comap (pf v)) δ f = ∏ᶠ v, twOrb (θv v) (K v) (pf v δ) (fv v) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX θ θv hθ hθK δ f fv hf hcomm hidx hfin hcpt hev
  rw [GlobalTheory.EulerAbs.twOrb_eq_finsum_twTerm]
  simp only [GlobalTheory.EulerAbs.twOrb_eq_finsum_twTerm]
  exact GlobalTheory.T.finsum_doubleCoset_restrictedProduct_eq_prod pf K hX (twCent θ δ) (fun v => twCent (θv v) (pf v δ)) (GlobalTheory.T.mem_twistedCentralizer_restrictedProduct_iff pf K hX θ θv hθ δ) _ _
    (GlobalTheory.T.twistedOrbitalTerm_eq_finprod_localTerms pf K hX θ θv hθ hθK δ f fv hf hcomm hidx hcpt (hev.mono fun v h => ⟨h.1, h.2.1, h.2.2.1⟩))
    (fun v t ht y k hk => GlobalTheory.T.twistedOrbitalIntegralPointTerm_doubleCoset_invariant _ _ _ _ (hcomm v) (hidx v) t ht y k hk)
    (fun v => (hfin v).subset fun q hq => GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero _ _ _ _ _ hq)
    (hev.mono fun v h => ⟨by rw [h.1]; exact GlobalTheory.T.twistedOrbitalIntegralPointTerm_one_unramified _ _ _ (hθK v) h.2.1 h.2.2.1, fun y hy => by
        obtain ⟨k, hk, hne⟩ := GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero _ _ _ _ _ hy
        rw [h.1] at hne
        have hm : (y * k)⁻¹ * pf v δ * θv v (y * k) ∈ K v := by
          by_contra hc; exact hne (Set.indicator_of_notMem hc _)
        obtain ⟨t, ht, k', hk', he⟩ := h.2.2.2 (y * k) hm
        exact ⟨t, ht, k' * k⁻¹, mul_mem hk' (inv_mem hk), by rw [← mul_assoc, ← he, mul_inv_cancel_right]⟩⟩)

end GlobalTheory.EulerAbs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralRestrictedProductFinprodStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_restrictedProduct_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v, {q : DoubleCoset.Quotient (twCent (θv v) (pf v δ) : Set (Y v)) (K v : Set (Y v)) | ∃ k ∈ K v, fv v ((Quotient.out q * k)⁻¹ * pf v δ * θv v (Quotient.out q * k)) ≠ 0}.Finite) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v ∧ ∀ y, y⁻¹ * pf v δ * θv v y ∈ K v → ∃ t ∈ twCent (θv v) (pf v δ), ∃ k ∈ K v, y = t * k) → twOrb θ (⨅ v, (K v).comap (pf v)) δ f = ∏ᶠ v, twOrb (θv v) (K v) (pf v δ) (fv v) := by
  first | exact @GlobalTheory.EulerAbs.twOrb_restr_eq_finprod | exact GlobalTheory.EulerAbs.twOrb_restr_eq_finprod | (intros; apply GlobalTheory.EulerAbs.twOrb_restr_eq_finprod <;> assumption)
end
