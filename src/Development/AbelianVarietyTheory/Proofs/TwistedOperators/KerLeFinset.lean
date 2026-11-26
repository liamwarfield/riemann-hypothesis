module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerLeFinset
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.Chain.IoLift.Factor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem kerLe_finset {A B Z₁ Z₂ σ : Type} [AddCommMonoid Z₁] [AddCommMonoid Z₂] {q₁ : A → B → Z₁} {q₂ : A → B → Z₂}
    (h : KerLe q₁ q₂) (s : Finset σ) (a : σ → A) (b : σ → B) (h0 : ∑ r ∈ s, q₁ (a r) (b r) = 0) :
    ∑ r ∈ s, q₂ (a r) (b r) = 0 := by
  have e := s.equivFin.symm
  rw [← Finset.sum_coe_sort s, ← e.sum_comp] at h0 ⊢
  exact h _ (fun k => a (e k)) (fun k => b (e k)) h0

theorem section_eq {ι : Type} [Fintype ι] {N K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (α : ∀ i, N i →ₗ[ℂ] K i) (s : ∀ i, K i →ₗ[ℂ] N i) (hs : ∀ i x, α i (s i x) = x)
    (M : (Π i, N i) →ₘₗ[ℂ] Z) (hM : ∀ n i z, α i z = 0 → M (Function.update n i z) = 0) (n : ∀ i, N i) :
    M (fun i => s i (α i (n i))) = M n := by
  have key : ∀ S : Finset ι, M (S.piecewise (fun i => s i (α i (n i))) n) = M n := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      rw [Finset.piecewise_insert, ← ih]
      have h1 := hM (S.piecewise (fun i => s i (α i (n i))) n) j (s j (α j (n j)) - n j) (by simp [hs])
      rw [MultilinearMap.map_update_sub, sub_eq_zero] at h1
      rw [h1]
      congr 1
      rw [Function.update_eq_self_iff, Finset.piecewise_eq_of_notMem _ _ _ hj]
  simpa using key Finset.univ

theorem factor :
    ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (P Y : ι → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (A : ∀ i, P i →ₗ[ℂ] Y i →ₗ[ℂ] K i), (∀ i, Submodule.span ℂ {x | ∃ p y, A i p y = x} = ⊤) → Submodule.span ℂ {x : ⨂[ℂ] i, K i | ∃ (p : ∀ i, P i) (y : ∀ i, Y i), PiTensorProduct.tprod ℂ (fun i => A i (p i) (y i)) = x} = ⊤ ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (B : (Π i, P i) →ₘₗ[ℂ] ((Π i, Y i) →ₘₗ[ℂ] Z)), (∀ i p y, KerLe (fun x z => A i x z) fun x z => B (Function.update p i x) (Function.update y i z)) → ∃ T : (⨂[ℂ] i, K i) →ₗ[ℂ] Z, ∀ p y, T (PiTensorProduct.tprod ℂ fun i => A i (p i) (y i)) = B p y := by
  intro ι _ K _ _ P Y _ _ _ _ A hA
  let α : ∀ i, (P i × Y i →₀ ℂ) →ₗ[ℂ] K i := fun i => Finsupp.linearCombination ℂ fun r => A i r.1 r.2
  have hα : ∀ i, LinearMap.range (α i) = ⊤ := by
    intro i
    rw [Finsupp.range_linearCombination, ← hA i]
    congr 1
    ext x
    simp
  choose s hs using fun i => (α i).exists_rightInverse_of_surjective (hα i)
  have hs' : ∀ i x, α i (s i x) = x := fun i x => LinearMap.congr_fun (hs i) x
  let b0 : ∀ i, Module.Basis (P i × Y i) ℂ (P i × Y i →₀ ℂ) := fun i => Finsupp.basisSingleOne
  have hb0 : ∀ i r, α i (b0 i r) = A i r.1 r.2 := by
    intro i r
    simp [α, b0]
  let b := Basis.piTensorProduct b0
  refine ⟨?_, ?_⟩
  · have hsurj : LinearMap.range (PiTensorProduct.map α) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro t
      refine ⟨PiTensorProduct.map s t, ?_⟩
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      simp [hs]
    rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span] at hsurj
    rw [eq_top_iff, ← hsurj]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨fun i => (q i).1, fun i => (q i).2, ?_⟩
    simp [b, hb0]
  · intro Z _ _ B hB
    let M : (Π i, P i × Y i →₀ ℂ) →ₘₗ[ℂ] Z :=
      (b.constr ℂ fun q => B (fun i => (q i).1) (fun i => (q i).2)).compMultilinearMap (PiTensorProduct.tprod ℂ)
    have hMb : ∀ q : ∀ i, P i × Y i, M (fun i => b0 i (q i)) = B (fun i => (q i).1) (fun i => (q i).2) := by
      intro q
      simp only [M, LinearMap.compMultilinearMap_apply]
      rw [← Basis.piTensorProduct_apply b0 q]
      exact b.constr_basis ℂ _ q
    have hM0 : ∀ (q : ∀ i, P i × Y i) i z, α i z = 0 → M (Function.update (fun i => b0 i (q i)) i z) = 0 := by
      intro q i z hz
      have h1 : ∀ r, M (Function.update (fun i => b0 i (q i)) i (b0 i r)) =
          B (Function.update (fun i => (q i).1) i r.1) (Function.update (fun i => (q i).2) i r.2) := by
        intro r
        have := hMb (Function.update q i r)
        convert this using 2 <;> [skip; congr 1; skip] <;> funext j <;> by_cases h : j = i <;>
          first | (subst h; simp) | simp [h]
      have h2 : M (Function.update (fun i => b0 i (q i)) i z) = ∑ r ∈ z.support,
          B (Function.update (fun i => (q i).1) i (z r • r.1)) (Function.update (fun i => (q i).2) i r.2) := by
        have hz' : z = ∑ r ∈ z.support, z r • b0 i r := by
          conv_lhs => rw [← Finsupp.sum_single z]
          simp [Finsupp.sum, b0]
        conv_lhs => rw [hz']
        rw [MultilinearMap.map_update_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [MultilinearMap.map_update_smul, MultilinearMap.map_update_smul, h1]
        rfl
      rw [h2]
      refine kerLe_finset (hB i (fun i => (q i).1) (fun i => (q i).2)) z.support (fun r => z r • r.1)
        (fun r => r.2) ?_
      simpa [α, Finsupp.linearCombination_apply, Finsupp.sum] using hz
    have hM : ∀ n i z, α i z = 0 → M (Function.update n i z) = 0 := by
      intro n i z hz
      let φ : (P i × Y i →₀ ℂ) →ₗ[ℂ] (P i × Y i →₀ ℂ) := Finsupp.linearCombination ℂ fun _ => z
      have hφ : ∀ r, φ (b0 i r) = z := by
        intro r
        simp [φ, b0]
      let f : ∀ j, (P j × Y j →₀ ℂ) →ₗ[ℂ] (P j × Y j →₀ ℂ) := Function.update (fun j => LinearMap.id) i φ
      have hf : ∀ m : ∀ j, (P j × Y j →₀ ℂ), (fun j => f j (m j)) = Function.update m i (φ (m i)) := by
        intro m
        funext j
        by_cases h : j = i
        · subst h; simp [f]
        · simp [f, h]
      have h0 : M.compLinearMap f = 0 := by
        refine Module.Basis.ext_multilinear b0 fun q => ?_
        rw [MultilinearMap.compLinearMap_apply, hf, hφ]
        exact hM0 q i z hz
      have := congrArg (fun F => F (Function.update n i (b0 i 0))) h0
      simpa [hf, hφ] using this
    refine ⟨PiTensorProduct.lift (M.compLinearMap s), fun p y => ?_⟩
    rw [PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply, ← hMb fun i => (p i, y i),
      ← section_eq α s hs' M hM fun i => b0 i (p i, y i)]
    simp only [hb0]

end GlobalTheory.Chain.IoLift.Factor

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRangeMapSubtypeOfContr
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdUpdateSelf
noncomputable section

open scoped TensorProduct Classical
open GlobalTheory.Chain.IoLift

namespace GlobalTheory.TensorContraction

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem prod_update_self [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∉ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = ∏ k ∈ s, φ k (v k) := by
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : k ≠ j := fun e => hj (e ▸ hk)
  rw [Function.update_of_ne hk']

theorem prod_update_mem [d : DecidableEq ι] (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (j : ι) (hj : j ∈ s)
    (v : ∀ k, K k) (x : K j) :
    ∏ k ∈ s, φ k (Function.update v j x k) = φ j x * ∏ k ∈ s.erase j, φ k (v k) := by
  rw [← Finset.mul_prod_erase s _ hj, Function.update_self,
    prod_update_self φ (s.erase j) j (Finset.notMem_erase j s) v x]

def contrM (φ : ∀ j, K j →ₗ[ℂ] ℂ) (s : Finset ι) (i : ι) (hi : i ∉ s) (hs : ∀ j, j ≠ i → j ∈ s) :
    (∀ j, K j) →ₘₗ[ℂ] K i where
  toFun v := (∏ k ∈ s, φ k (v k)) • v i
  map_update_add' v j x y := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self, smul_add]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_add (f := _), add_mul, add_smul]
  map_update_smul' v j c x := by
    by_cases h : j = i
    · subst h
      simp only [prod_update_self φ s j hi, Function.update_self, RingHom.id_apply]
      rw [smul_comm]
    · simp only [prod_update_mem φ s j (hs j h), Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul,
        RingHom.id_apply, mul_assoc, mul_smul]

def contrL (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) : (⨂[ℂ] j, K j) →ₗ[ℂ] K i :=
  PiTensorProduct.lift (contrM φ (Finset.univ.erase i) i (Finset.notMem_erase _ _)
    fun j h => Finset.mem_erase.2 ⟨h, Finset.mem_univ j⟩)

theorem contrL_tprod (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (v : ∀ j, K j) :
    contrL φ i (PiTensorProduct.tprod ℂ v) = (∏ k ∈ Finset.univ.erase i, φ k (v k)) • v i := by
  rw [contrL, PiTensorProduct.lift.tprod]
  rfl

theorem contrL_comp_mapFactor (φ : ∀ j, K j →ₗ[ℂ] ℂ) (i : ι) (f : Module.End ℂ (K i)) :
    contrL φ i ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ contrL φ i := by
  apply PiTensorProduct.ext
  refine MultilinearMap.ext fun v => ?_
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, position_tprod, contrL_tprod]
  rw [prod_update_self φ _ i (Finset.notMem_erase i _), Function.update_self, map_smul]

private theorem eq_zero_of_contrL_eq_zero (i : ι) (z : ⨂[ℂ] j, K j)
    (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i z = 0) : z = 0 := by
  let b : ∀ j, Module.Basis (Module.Basis.ofVectorSpaceIndex ℂ (K j)) ℂ (K j) :=
    fun j => Module.Basis.ofVectorSpace ℂ (K j)
  let B := Basis.piTensorProduct b
  refine B.forall_coord_eq_zero_iff.1 fun p => ?_
  let φ : ∀ j, K j →ₗ[ℂ] ℂ := fun j => (b j).coord (p j)
  have key : B.coord p = (b i).coord (p i) ∘ₗ contrL φ i := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext fun v => ?_
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contrL_tprod, map_smul, smul_eq_mul, Module.Basis.coord_apply, B,
      Basis.piTensorProduct_repr_tprod_apply, φ]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [key, LinearMap.comp_apply, h φ, map_zero]

theorem eq_of_contrL (i : ι) (x y : ⨂[ℂ] j, K j) (h : ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x = contrL φ i y) :
    x = y := by
  rw [← sub_eq_zero]
  exact eq_zero_of_contrL_eq_zero i (x - y) fun φ => by rw [map_sub, h φ, sub_self]

private theorem piTensorProduct_map_ite_eq_self_of_slot_fixed (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j)
    (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) (s : Finset ι) :
    PiTensorProduct.map (fun j => if j ∈ s then p j else LinearMap.id) x = x := by
  induction s using Finset.induction_on with
  | empty => simp [PiTensorProduct.map_id]
  | insert a s ha ih =>
    have e : (fun j => if j ∈ insert a s then p j else (LinearMap.id : Module.End ℂ (K j))) =
        fun j => Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) a (p a) j ∘ₗ
          (if j ∈ s then p j else LinearMap.id) := by
      funext j
      by_cases hj : j = a
      · subst hj
        simp [ha]
      · simp [hj]
    rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
    exact h a

theorem map_eq_self (p : ∀ j, Module.End ℂ (K j)) (x : ⨂[ℂ] j, K j) (h : ∀ i, intersection_update_fsHerm_neg_one i (p i) x = x) :
    PiTensorProduct.map p x = x := by
  simpa using piTensorProduct_map_ite_eq_self_of_slot_fixed p x h Finset.univ

theorem mem_range_map (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]
    (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ (i : ι) (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by

  have hN : ∀ i, ∀ φ : ∀ j, K j →ₗ[ℂ] ℂ, contrL φ i x ∈ N i :=
    fun i φ => h i (contrL φ i) (contrL_comp_mapFactor φ i)

  choose g hg using fun i => LinearMap.exists_leftInverse_of_injective (N i).subtype (N i).ker_subtype
  let P : ∀ i, Module.End ℂ (K i) := fun i => (N i).subtype ∘ₗ g i
  have hP : ∀ i, ∀ v ∈ N i, P i v = v := fun i v hv => by
    have := congrArg (fun f => (N i).subtype (f ⟨v, hv⟩)) (hg i)
    simpa [P] using this

  have hfix : ∀ i, intersection_update_fsHerm_neg_one i (P i) x = x := fun i =>
    eq_of_contrL i _ _ fun φ => by
      rw [← LinearMap.comp_apply (contrL φ i), contrL_comp_mapFactor, LinearMap.comp_apply, hP i _ (hN i φ)]
  rw [LinearMap.mem_range]
  refine ⟨PiTensorProduct.map g x, ?_⟩
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  exact map_eq_self P x hfix

end GlobalTheory.TensorContraction

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift

theorem mem_range_map_subtype_of_contr (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)]
    [∀ i, Module ℂ (K i)] (N : ∀ i, Submodule ℂ (K i)) (x : ⨂[ℂ] i, K i)
    (h : ∀ i (L : (⨂[ℂ] j, K j) →ₗ[ℂ] K i), (∀ f : Module.End ℂ (K i), L ∘ₗ intersection_update_fsHerm_neg_one i f = f ∘ₗ L) → L x ∈ N i) :
    x ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  first
  | exact @_root_.GlobalTheory.TensorContraction.mem_range_map
  | exact _root_.GlobalTheory.TensorContraction.mem_range_map
  | (apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorContraction.mem_range_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorContraction.mem_range_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorContraction.mem_range_map ..)

end GlobalTheory.Chain.IoLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingSkew
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.CuspL2

theorem exists_toLp_ext {G : Type} [MeasurableSpace G] (ν : Measure G) :
    ∃ E : (G → ℂ) →ₗ[ℂ] Lp ℂ 2 ν, ∀ φ, MemLp φ 2 ν → E φ =ᵐ[ν] φ := by
  classical
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {φ | MemLp φ 2 ν}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := by
        first
          | exact MemLp.zero
          | exact MemLp.zero'
          | exact zero_memLp
          | simp
      smul_mem' := fun c _ h => h.const_smul c }
  let f : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun φ => MemLp.toLp (φ : G → ℂ) φ.2
      map_add' := fun φ ψ => MemLp.toLp_add φ.2 ψ.2
      map_smul' := fun c φ => MemLp.toLp_const_smul c φ.2 }
  obtain ⟨E, hE⟩ := LinearMap.exists_extend f
  refine ⟨E, fun φ hφ => ?_⟩
  have hval : E φ = f ⟨φ, hφ⟩ := LinearMap.congr_fun hE ⟨φ, hφ⟩
  rw [hval]
  exact MemLp.coeFn_toLp hφ

theorem inner_eq {G : Type} [MeasurableSpace G] {ν : Measure G} {f f' : Lp ℂ 2 ν} {φ φ' : G → ℂ}
    (h : f =ᵐ[ν] φ) (h' : f' =ᵐ[ν] φ') : ⟪f, f'⟫_ℂ = ∫ g, (starRingEnd ℂ) (φ g) * φ' g ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h, h'] with g hg hg'
  rw [hg, hg']
  first
    | (rw [RCLike.inner_apply]; try ring)
    | simp [mul_comm]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bounded (hP : GlobalTheory.Published.CuspDecaySobolev) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsCuspGrow θ V φ) :
    ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B := by
  obtain ⟨ha, hs, hc, hg⟩ := h
  obtain ⟨-, -, hd⟩ := GlobalTheory.Size.rapidDec_of_cuspDecaySobolev hP hθ ha hs hg hc
  obtain ⟨C, hC⟩ := hd 0
  exact ⟨C, fun g => by simpa using hC g⟩

theorem conj_mul {G : Type} [TopologicalSpace G] {φ φ' : G → ℂ} (c : Continuous φ) (c' : Continuous φ')
    (b : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B) (b' : ∃ B : ℝ, ∀ g, ‖φ' g‖ ≤ B) :
    Continuous (fun g => (starRingEnd ℂ) (φ g) * φ' g) ∧ ∃ B : ℝ, ∀ g, ‖(starRingEnd ℂ) (φ g) * φ' g‖ ≤ B := by
  obtain ⟨B, hB⟩ := b
  obtain ⟨B', hB'⟩ := b'
  refine ⟨(Complex.continuous_conj.comp c).mul c', max B 0 * max B' 0, fun g => ?_⟩
  calc ‖(starRingEnd ℂ) (φ g) * φ' g‖ = ‖φ g‖ * ‖φ' g‖ := by simp [norm_mul]
    _ ≤ max B 0 * max B' 0 :=
      mul_le_mul ((hB g).trans (le_max_left _ _)) ((hB' g).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)

theorem exists_embedding_skew : GlobalTheory.Published.CuspDecaySobolev → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∃ E : (GA D V → ℂ) →ₗ[ℂ] Lp ℂ 2 (μ.restrict 𝓕), (∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) ∧ (E φ = 0 → φ = 0)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ φ', IsCuspGrow θ V φ → IsCuspGrow θ V φ' → IsCuspGrow θ V (Rder θ V τ X φ) → IsCuspGrow θ V (Rder θ V τ X φ') → ⟪E (Rder θ V τ X φ), E φ'⟫_ℂ + ⟪E φ, E (Rder θ V τ X φ')⟫_ℂ = 0 := by
  intro hP D θ V μ 𝓕 hθ hμ h𝓕
  haveI := hμ
  obtain ⟨-, -, -, iB, iT, -, iC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := iB
  haveI := iT
  haveI := iC
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ).1
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 (And.intro hμ h𝓕)).2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hmem : ∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) := by
    intro φ hφ
    obtain ⟨B, hB⟩ := bounded hP hθ hφ
    exact MemLp.of_bound hφ.1.cont.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hint : ∀ F : GA D V → ℂ, Continuous F → (∃ B : ℝ, ∀ g, ‖F g‖ ≤ B) → Integrable F (μ.restrict 𝓕) := by
    rintro F hF ⟨B, hB⟩
    exact memLp_one_iff_integrable.1 (MemLp.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall hB))
  obtain ⟨E, hE⟩ := exists_toLp_ext (μ.restrict 𝓕)
  refine ⟨E, fun φ hφ => ⟨hmem φ hφ, fun h0 => ?_⟩, ?_⟩
  · have h1 := hE φ (hmem φ hφ)
    rw [h0] at h1
    have hz : ⇑(0 : Lp ℂ 2 (μ.restrict 𝓕)) =ᵐ[μ.restrict 𝓕] (0 : GA D V → ℂ) := Lp.coeFn_zero ..
    have hae : ∀ᵐ g ∂(μ.restrict 𝓕), φ g = 0 := by
      filter_upwards [h1, hz] with g a b
      rw [← a, b]
      rfl
    have hopen : IsOpen {g | φ g ≠ 0} := isOpen_ne_fun hφ.1.cont continuous_const
    haveI : SMulInvariantMeasure (GQ V) (GA D V) μ := by
      first
        | exact inferInstance
        | exact ⟨fun γ s _ => measure_preimage_mul μ (γ : GA D V) s⟩
    open Pointwise in
    have hinv : ∀ γ : GQ V, γ • {g | φ g ≠ 0} = {g | φ g ≠ 0} := by
      intro γ
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      show φ ((γ⁻¹ : GQ V) * x) ≠ 0 ↔ φ x ≠ 0
      rw [hφ.1.left _ (γ⁻¹).2 x]
    have hnull : μ {g | φ g ≠ 0} = 0 := by
      refine h𝓕.measure_zero_of_invariant _ hinv ?_
      rw [← Measure.restrict_apply hopen.measurableSet]
      exact ae_iff.1 hae
    have hempty := (hopen.measure_eq_zero_iff μ).1 hnull
    funext g
    by_contra hne
    have hg : g ∈ {g | φ g ≠ 0} := hne
    rw [hempty] at hg
    exact hg
  · intro τ X hX φ φ' h1 h2 h3 h4
    rw [inner_eq (hE _ (hmem _ h3)) (hE _ (hmem _ h2)), inner_eq (hE _ (hmem _ h1)) (hE _ (hmem _ h4))]
    obtain ⟨c1, B1, b1⟩ := conj_mul h3.1.cont h2.1.cont (bounded hP hθ h3) (bounded hP hθ h2)
    obtain ⟨c2, B2, b2⟩ := conj_mul h1.1.cont h4.1.cont (bounded hP hθ h1) (bounded hP hθ h4)
    obtain ⟨c0, B0, b0⟩ := conj_mul h1.1.cont h2.1.cont (bounded hP hθ h1) (bounded hP hθ h2)
    rw [← integral_add (hint _ c1 ⟨B1, b1⟩) (hint _ c2 ⟨B2, b2⟩)]
    have key : ∀ ψ : GA D V → ℂ, ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V → ∀ g t,
        HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X s)) (Rder θ V τ X ψ (g * oneP θ V τ X t)) t := by
      intro ψ hψ g t
      have d0 : HasDerivAt (fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) 0 :=
        ((GlobalTheory.Mem.AutSpace.differentiable_oneP hψ hX (g * oneP θ V τ X t)) 0).hasDerivAt
      have d1 : HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t)))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) t :=
        HasDerivAt.comp_sub_const (f := fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u)) t t
          (by rw [sub_self]; exact d0)
      refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show ψ (g * oneP θ V τ X s) = ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t))
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, show t + (s - t) = s by ring]
    have hd : ∀ g t, HasDerivAt
        (fun s : ℝ => (starRingEnd ℂ) (φ (g * oneP θ V τ X s)) * φ' (g * oneP θ V τ X s))
        ((starRingEnd ℂ) (Rder θ V τ X φ (g * oneP θ V τ X t)) * φ' (g * oneP θ V τ X t) +
          (starRingEnd ℂ) (φ (g * oneP θ V τ X t)) * Rder θ V τ X φ' (g * oneP θ V τ X t)) t := by
      intro g t
      exact ((key φ h1.2.1 g t).star).mul (key φ' h2.2.1 g t)
    exact GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
      (Φ := fun g => (starRingEnd ℂ) (φ g) * φ' g)
      (Φ' := fun g => (starRingEnd ℂ) (Rder θ V τ X φ g) * φ' g + (starRingEnd ℂ) (φ g) * Rder θ V τ X φ' g)
      (fun γ hγ g => by
        show (starRingEnd ℂ) (φ (γ * g)) * φ' (γ * g) = (starRingEnd ℂ) (φ g) * φ' g
        rw [h1.1.left γ hγ g, h2.1.left γ hγ g])
      c0 (c1.add c2) b0
      (fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g)))
      (GlobalTheory.Mem.Lift.oneP_zero hθ) hd

end GlobalTheory.Chain.CuspL2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKtypeCoefficientExplicitPowerDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKtypeCoefficientExplicitPowerDecay
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal.PowDec

theorem hsn_sq_le {m : ℕ} (g : Mat m) : hsn g ^ 2 ≤ m * Real.exp (2 * GlobalTheory.Count.dHS g) := by
  have hA := Matrix.isHermitian_conjTranspose_mul_self g
  have h1 : hsn g ^ 2 = ∑ j, hA.eigenvalues j := by
    have e0 : hsn g = Real.sqrt (Formalism.REAL.hs g) := rfl
    rw [e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace,
      hA.trace_eq_sum_eigenvalues]
    simp [Complex.re_sum]
  rw [h1]
  have hle : ∀ j, hA.eigenvalues j ≤ Real.exp (2 * GlobalTheory.Count.dHS g) := by
    intro j
    have hx : |Real.log (hA.eigenvalues j) / 2| ≤ GlobalTheory.Count.dHS g := by
      unfold GlobalTheory.Count.dHS
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (f := fun i => (Real.log (hA.eigenvalues i) / 2) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    rcases le_or_gt (hA.eigenvalues j) 0 with h0 | h0
    · exact h0.trans (Real.exp_pos _).le
    · calc hA.eigenvalues j = Real.exp (2 * (Real.log (hA.eigenvalues j) / 2)) := by
            rw [show 2 * (Real.log (hA.eigenvalues j) / 2) = Real.log (hA.eigenvalues j) by ring,
              Real.exp_log h0]
        _ ≤ Real.exp (2 * GlobalTheory.Count.dHS g) := by
            apply Real.exp_le_exp.2
            linarith [le_abs_self (Real.log (hA.eigenvalues j) / 2)]
  calc ∑ j, hA.eigenvalues j ≤ ∑ _j : Fin m, Real.exp (2 * GlobalTheory.Count.dHS g) :=
        Finset.sum_le_sum fun j _ => hle j
    _ = m * Real.exp (2 * GlobalTheory.Count.dHS g) := by simp

theorem hsn_pos {m : ℕ} (hm : 1 ≤ m) {ε : Fin m → Bool} {g : Mat m} (hg : g ∈ UJset ε) : 0 < hsn g := by
  unfold hsn
  apply Real.sqrt_pos.2
  by_contra hle
  push_neg at hle
  have hsum : ∑ a, ∑ b, ‖g a b‖ ^ 2 = 0 := le_antisymm hle (by positivity)
  have hg0 : g = 0 := by
    ext a b
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hsum
    have h2 := hsum a (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at h2
    simpa using h2 b (Finset.mem_univ _)
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  rw [hg0] at hJ
  have := congrFun (congrFun hJ ⟨0, hm⟩) ⟨0, hm⟩
  simp [Jm] at this
  split_ifs at this <;> simp at this

theorem hsn_sq_definite {m : ℕ} {ε : Fin m → Bool} (hq : GlobalTheory.Count.rkR ε = 0) {g : Mat m} (hg : g ∈ UJset ε) :
    hsn g ^ 2 = m := by
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  have hJc : Jm ε = 1 ∨ Jm ε = -1 := by
    unfold GlobalTheory.Count.rkR at hq
    rcases Nat.min_eq_zero_iff.1 hq with h | h
    · right
      have hf : ∀ a, ε a = false := fun a => by
        by_contra ha
        have : a ∈ univ.filter fun a => ε a = true := by simpa using ha
        rw [Finset.card_eq_zero.1 h] at this
        simp at this
      ext a b
      by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]
    · left
      have hf : ∀ a, ε a = true := fun a => by
        by_contra ha
        have : a ∈ univ.filter fun a => ε a = false := by simpa using ha
        rw [Finset.card_eq_zero.1 h] at this
        simp at this
      ext a b
      by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]
  have hu : gᴴ * g = 1 := by
    rcases hJc with h | h
    · rw [h, Matrix.mul_one] at hJ; exact hJ
    · rw [h] at hJ
      have : -(gᴴ * g) = -1 := by simpa [Matrix.mul_neg, Matrix.neg_mul] using hJ
      exact neg_inj.1 this
  have e0 : hsn g = Real.sqrt (Formalism.REAL.hs g) := rfl
  rw [e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace, hu]
  simp

end GlobalTheory.SepReal.PowDec

namespace GlobalTheory.SepReal.PowDec

theorem rkR_le {m : ℕ} (ε : Fin m → Bool) : GlobalTheory.Count.rkR ε ≤ m := by
  unfold GlobalTheory.Count.rkR
  exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))

theorem gap_ok {m : ℕ} (hm : 1 ≤ m) (ε : Fin m → Bool) :
    120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1000 * (m : ℝ) ^ 3 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ≤ m := by exact_mod_cast rkR_le ε
  have h1 : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) hq (by norm_num)
  have h2 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  rw [Real.rpow_two] at h2
  have h3 : 0 ≤ (m : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0 : ℝ) ≤ 120 * m)]

end GlobalTheory.SepReal.PowDec

namespace GlobalTheory.SepReal


open GlobalTheory.SepReal.PowDec in
theorem decPow : DecPow := by
  intro m ε lam B hm hlam hgap _ H _ _ π hπ v₀ hv₀ g hg
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hdec := (GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap m ε lam H π hlam hπ
    (1000 * (m : ℝ) ^ 3) hgap (gap_ok (by omega) ε) g hg v₀ hv₀.2 v₀ hv₀.2).1
  rw [hv₀.1, mul_one, mul_one] at hdec
  unfold GlobalTheory.Dec.decHS at hdec
  set t := GlobalTheory.Count.dHS g with ht
  set q := GlobalTheory.Count.rkR ε with hqdef
  have hx := hsn_pos (by omega) hg
  set A : ℝ := 40 * (m : ℝ) ^ 2 with hA
  have hpow : hsn g ^ (-A) = Real.exp (Real.log (hsn g) * (-A)) := Real.rpow_def_of_pos hx _
  rw [hpow, ← Real.exp_add]
  refine hdec.trans (Real.exp_le_exp.2 ?_)
  have hlogm : Real.log m ≤ m := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ m := by positivity
  rcases Nat.eq_zero_or_pos q with hq | hq
  ·
    have hs2 := hsn_sq_definite hq hg
    have hL : 2 * Real.log (hsn g) = Real.log m := by
      rw [← Real.log_rpow hx, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hs2]
    have hM : min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) = 0 := by
      rw [hq]; simp; positivity
    rw [hM]
    nlinarith [mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]
  · have hs2 := hsn_sq_le g
    have hL : 2 * Real.log (hsn g) ≤ Real.log m + 2 * t := by
      have h1 : Real.log (hsn g ^ 2) ≤ Real.log (m * Real.exp (2 * t)) := Real.log_le_log (by positivity) hs2
      rw [Real.log_pow, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h1
      push_cast at h1; linarith
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqm : (q : ℝ) ≤ m := by exact_mod_cast rkR_le ε
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hsq : Real.sqrt (2 * (q : ℝ)) ≤ m := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have hsq0 : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by positivity)

    have hkey : t - 1 ≤ (m : ℝ) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := by
      rcases le_total t 1 with h1 | h1
      · have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := le_min (by positivity) (by positivity)
        nlinarith
      · have a1 : t ≤ (m : ℝ) * t ^ 2 := by nlinarith
        have a2 : t ≤ (m : ℝ) * (t / Real.sqrt (2 * (q : ℝ))) := by
          rw [mul_div_assoc', le_div_iff₀ hsq0]; nlinarith
        rcases min_choice (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) with e | e <;> rw [e] <;> linarith
    have hL' : Real.log (hsn g) * A ≤ 20 * (m : ℝ) ^ 3 + 40 * (m : ℝ) ^ 2 * t := by
      rw [hA]
      nlinarith [mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2),
        mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 20 * (m : ℝ) ^ 2)]
    have hk2 := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 125 * (m : ℝ) ^ 2)
    nlinarith

end GlobalTheory.SepReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKtypeCoefficientExplicitPowerDecayStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay : DecPow := by
  first | exact @GlobalTheory.SepReal.decPow | exact GlobalTheory.SepReal.decPow | (intros; apply GlobalTheory.SepReal.decPow <;> assumption)
end
end
