module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteMod
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.QuotMonic

variable {M : Type} [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M)

def stabAlg : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {f | ∀ x ∈ M', f x ∈ M' ∧ (x ∈ K → f x ∈ K)}
  mul_mem' := fun {f g} hf hg x hx => ⟨(hf _ (hg x hx).1).1, fun hk => (hf _ (hg x hx).1).2 ((hg x hx).2 hk)⟩
  add_mem' := fun {f g} hf hg x hx => ⟨M'.add_mem (hf x hx).1 (hg x hx).1, fun hk => K.add_mem ((hf x hx).2 hk) ((hg x hx).2 hk)⟩
  algebraMap_mem' := fun r x hx => ⟨by simpa [Module.algebraMap_end_apply] using M'.smul_mem r hx,
    fun hk => by simpa [Module.algebraMap_end_apply] using K.smul_mem r hk⟩

variable {M' K}

def restrictQ (f : stabAlg M' K) : Module.End ℂ (M' ⧸ K.comap M'.subtype) :=
  (K.comap M'.subtype).mapQ (K.comap M'.subtype) (f.1.restrict fun x hx => (f.2 x hx).1) fun x hx => by
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.restrict_apply] at hx ⊢
    exact (f.2 x x.2).2 hx


variable (M' K) in
def quotRep : stabAlg M' K →ₐ[ℂ] Module.End ℂ (M' ⧸ K.comap M'.subtype) where
  toFun := restrictQ
  map_one' := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_mul' f g := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_zero' := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_add' f g := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  commutes' r := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl


variable (M' K) in
def quotIncl : (M' ⧸ K.comap M'.subtype) →ₗ[ℂ] M ⧸ K :=
  (K.comap M'.subtype).liftQ (K.mkQ ∘ₗ M'.subtype) fun x hx => by simpa using hx

theorem quotIncl_injective : Function.Injective (quotIncl M' K) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => by simpa using hx

theorem quotIncl_quotRep (b : stabAlg M' K) (v : M) (hv : v ∈ M') :
    quotIncl M' K (quotRep M' K b (Submodule.Quotient.mk ⟨v, hv⟩)) = K.mkQ (b.1 v) := rfl

end GlobalTheory.LeviHC.QuotMonic

namespace GlobalTheory.LeviHC.QuotMonic


open Algebra in
theorem monicFactorFiniteMod_of (H : MonicFactorFinite) : MonicFactorFiniteMod := by
  intro M _ _ M' K c p q hp hq hpp hqq hpq hM hK hc v hv hfin
  classical
  set S := stabAlg M' K
  have hpB : ∀ u, p u ∈ S := fun u x hx => ⟨(hM u x hx).2.1, fun hk => (hK u x hk).1⟩
  have hqB : ∀ u, q u ∈ S := fun u x hx => ⟨(hM u x hx).2.2, fun hk => (hK u x hk).2⟩
  have hcB : ∀ u, c u ∈ S := fun u x hx => ⟨(hM u x hx).1, fun hk =>
    (K.sub_mem_iff_left (hK u _ (hK u x hk).2).1).1 (hc u x hx)⟩
  let pS : ℂ → S := fun u => ⟨p u, hpB u⟩
  let qS : ℂ → S := fun u => ⟨q u, hqB u⟩
  let cS : ℂ → S := fun u => ⟨c u, hcB u⟩
  let ρ := quotRep M' K

  have poly : ∀ (r : ℂ → Module.End ℂ M) (hr : ∀ u, r u ∈ S),
      (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, r u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
      ∃ (d : ℕ) (a : ℕ → Module.End ℂ (M' ⧸ K.comap M'.subtype)), a d = 1 ∧
        ∀ u, ρ ⟨r u, hr u⟩ = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
    intro r hr ⟨d, a, ha1, hra⟩
    have haB : ∀ i < d + 1, a i ∈ S := fun i hi =>
      (Subalgebra.mem_toSubmodule S).1 ((Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact hr u))
        (coeff_mem_span hra hi))
    let a' : ℕ → S := fun i => if h : a i ∈ S then ⟨a i, h⟩ else 0
    have ha' : ∀ i < d + 1, (a' i).1 = a i := fun i hi => by simp [a', haB i hi]
    refine ⟨d, fun i => ρ (a' i), ?_, fun u => ?_⟩
    · have : a' d = 1 := Subtype.ext ((ha' d (Nat.lt_succ_self d)).trans ha1)
      show ρ (a' d) = 1
      rw [this, map_one]
    · have e : (⟨r u, hr u⟩ : S) = ∑ i ∈ Finset.range (d + 1), u ^ i • a' i := by
        apply Subtype.ext
        change r u = _
        rw [hra u]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show ((∑ i ∈ Finset.range (d + 1), u ^ i • a' i : S) : Module.End ℂ M) = ∑ i ∈ Finset.range (d + 1), u ^ i • (a' i : Module.End ℂ M) from
          map_sum S.val.toLinearMap (fun i => u ^ i • a' i) _ |>.trans (Finset.sum_congr rfl fun i _ => map_smul S.val.toLinearMap _ _)]
        exact Finset.sum_congr rfl fun i hi => by rw [ha' i (Finset.mem_range.1 hi)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hcS : ∀ u, ρ (cS u) = ρ (pS u) * ρ (qS u) := fun u => by
    rw [← map_mul]
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    obtain ⟨x, hx⟩ := x
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    simpa using hc u x hx

  have hval : ∀ (r : ℂ → Module.End ℂ M) (hr : ∀ u, r u ∈ S),
      (adjoin ℂ (Set.range fun u => (⟨r u, hr u⟩ : S))).map S.val = adjoin ℂ (Set.range r) := by
    intro r hr
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hrho : ∀ (s : ℂ → S), adjoin ℂ (Set.range fun u => ρ (s u)) = (adjoin ℂ (Set.range s)).map ρ := by
    intro s
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  set v' : M' ⧸ K.comap M'.subtype := Submodule.Quotient.mk ⟨v, hv⟩
  have hj := quotIncl_injective (M' := M') (K := K)
  have key := H (M' ⧸ K.comap M'.subtype) (fun u => ρ (pS u)) (fun u => ρ (qS u)) (poly p hpB hp) (poly q hqB hq)
    (fun u u' => (show Commute (pS u) (pS u') from Subtype.ext (hpp u u').eq).map ρ)
    (fun u u' => (show Commute (qS u) (qS u') from Subtype.ext (hqq u u').eq).map ρ)
    (fun u u' => (show Commute (pS u) (qS u') from Subtype.ext (hpq u u').eq).map ρ) v' ?_
  ·
    haveI := key
    unfold FinMod
    refine Submodule.finiteDimensional_of_le (?_ : _ ≤ Submodule.map (quotIncl M' K)
      (Submodule.span ℂ {y | ∃ a ∈ adjoin ℂ (Set.range fun u => ρ (pS u)), y = a v'}))
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [← hval p hpB] at ha
    obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 ha
    refine Submodule.subset_span ⟨ρ b v', ⟨ρ b, ?_, rfl⟩, quotIncl_quotRep b v hv⟩
    rw [hrho pS]
    exact Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
  · haveI : FiniteDimensional ℂ (Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ adjoin ℂ (Set.range c), y = K.mkQ (a v)}) := hfin
    set T := Submodule.span ℂ {y | ∃ a ∈ adjoin ℂ (Set.range fun u => ρ (pS u) * ρ (qS u)), y = a v'}
    have hle : T.map (quotIncl M' K) ≤
        Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ adjoin ℂ (Set.range c), y = K.mkQ (a v)} := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have e : (fun u => ρ (pS u) * ρ (qS u)) = fun u => ρ (cS u) := funext fun u => (hcS u).symm
      rw [e, hrho cS] at ha
      obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 ha
      refine Submodule.subset_span ⟨b.1, ?_, quotIncl_quotRep b v hv⟩
      rw [← hval c hcB]
      exact Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hj T).symm

end GlobalTheory.LeviHC.QuotMonic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFinite
open scoped TensorProduct NNReal Matrix IsMulCommutative
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

theorem monicFactorFinite : MonicFactorFinite := by
  intro N _ _ p q hp hq hpp hqq hpq v hfin
  rcases subsingleton_or_nontrivial N with hN | hN
  · infer_instance
  obtain ⟨d, c₀, hcd, hpc₀⟩ := hp
  obtain ⟨e, b₀, hbe, hqb₀⟩ := hq
  set T := Algebra.adjoin ℂ (Set.range fun u => p u * q u) with hT
  set Wsp := Submodule.span ℂ {y | ∃ a ∈ T, y = a v} with hWsp
  let s : Set (Module.End ℂ N) := Set.range p ∪ Set.range q
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro a (⟨u, rfl⟩ | ⟨u, rfl⟩) b (⟨u', rfl⟩ | ⟨u', rfl⟩)
    · exact hpp u u'
    · exact hpq u u'
    · exact (hpq u' u).symm
    · exact hqq u u'
  let S := Algebra.adjoin ℂ s
  have : IsMulCommutative S := Algebra.isMulCommutative_adjoin ℂ fun a ha b hb _ => hcomm a ha b hb

  let c : ℕ → Module.End ℂ N := fun i => if i < d + 1 then c₀ i else 0
  let b : ℕ → Module.End ℂ N := fun i => if i < e + 1 then b₀ i else 0
  have hpc : ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • c i := fun u => by
    rw [hpc₀ u]; exact Finset.sum_congr rfl fun i hi => by
      show _ = u ^ i • (if i < d + 1 then c₀ i else 0); rw [ite_eq_left (Finset.mem_range.1 hi)]
  have hqb : ∀ u, q u = ∑ i ∈ Finset.range (e + 1), u ^ i • b i := fun u => by
    rw [hqb₀ u]; exact Finset.sum_congr rfl fun i hi => by
      show _ = u ^ i • (if i < e + 1 then b₀ i else 0); rw [ite_eq_left (Finset.mem_range.1 hi)]
  have hpS : Submodule.span ℂ (Set.range p) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.2 fun x hx => Algebra.subset_adjoin (Or.inl hx)
  have hqS : Submodule.span ℂ (Set.range q) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.2 fun x hx => Algebra.subset_adjoin (Or.inr hx)
  have hcS : ∀ i, c i ∈ S := fun i => by
    by_cases h : i < d + 1
    · show (if i < d + 1 then c₀ i else 0) ∈ S
      rw [ite_eq_left h]; exact hpS (coeff_mem_span hpc₀ h)
    · show (if i < d + 1 then c₀ i else 0) ∈ S
      rw [ite_eq_right h]; exact S.zero_mem
  have hbS : ∀ i, b i ∈ S := fun i => by
    by_cases h : i < e + 1
    · show (if i < e + 1 then b₀ i else 0) ∈ S
      rw [ite_eq_left h]; exact hqS (coeff_mem_span hqb₀ h)
    · show (if i < e + 1 then b₀ i else 0) ∈ S
      rw [ite_eq_right h]; exact S.zero_mem
  let c' : ℕ → S := fun i => ⟨c i, hcS i⟩
  let b' : ℕ → S := fun i => ⟨b i, hbS i⟩
  let P : Polynomial S := ∑ i ∈ Finset.range (d + 1), Polynomial.monomial i (c' i)
  let Q : Polynomial S := ∑ i ∈ Finset.range (e + 1), Polynomial.monomial i (b' i)
  have hPe : ∀ u, ((P.eval (algebraMap ℂ S u) : S) : Module.End ℂ N) = p u := fun u => by
    rw [hpc u]
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.commutes, map_pow]
  have hQe : ∀ u, ((Q.eval (algebraMap ℂ S u) : S) : Module.End ℂ N) = q u := fun u => by
    rw [hqb u]
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.commutes, map_pow]
  have hPc : ∀ i, i < d + 1 → P.coeff i = c' i := fun i hi => by
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 hi)]
  have hPm : P.Monic := by
    refine Polynomial.monic_of_degree_le d ?_ ?_
    · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
      exact (Polynomial.degree_monomial_le _ _).trans (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    · rw [hPc d (Nat.lt_succ_self d)]
      exact Subtype.ext (by simp [c', c, hcd])
  have hQm : Q.Monic := by
    refine Polynomial.monic_of_degree_le e ?_ ?_
    · refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
      exact (Polynomial.degree_monomial_le _ _).trans (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    · simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply]
      rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (Nat.lt_succ_self e))]
      exact Subtype.ext (by simp [b', b, hbe])

  let R : Subalgebra ℂ S :=
    Algebra.adjoin ℂ (Set.range fun u => P.eval (algebraMap ℂ S u) * Q.eval (algebraMap ℂ S u))
  have hRT : ∀ r ∈ R, ((r : S) : Module.End ℂ N) ∈ T := by
    intro r hr
    have hle : R ≤ Subalgebra.comap S.val T := Algebra.adjoin_le (by
      rintro _ ⟨u, rfl⟩
      show ((P.eval (algebraMap ℂ S u) * Q.eval (algebraMap ℂ S u) : S) : Module.End ℂ N) ∈ T
      rw [Subalgebra.coe_mul, hPe, hQe]
      exact Algebra.subset_adjoin ⟨u, rfl⟩)
    exact hle hr

  have hPQR : ∀ k, (P * Q).coeff k ∈ R := by
    intro k
    by_cases hk : k < (P * Q).natDegree + 1
    · have hf : ∀ u, (P * Q).eval (algebraMap ℂ S u) =
          ∑ i ∈ Finset.range ((P * Q).natDegree + 1), u ^ i • (P * Q).coeff i := fun u => by
        rw [Polynomial.eval_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, map_pow, mul_comm]
      have h1 := coeff_mem_span hf hk
      have h2 : Submodule.span ℂ (Set.range fun u => (P * Q).eval (algebraMap ℂ S u)) ≤ Subalgebra.toSubmodule R := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨u, rfl⟩
        show Polynomial.eval (algebraMap ℂ S u) (P * Q) ∈ R
        rw [Polynomial.eval_mul]
        exact Algebra.subset_adjoin ⟨u, rfl⟩
      exact h2 h1
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact R.zero_mem
  have hlift : P * Q ∈ Polynomial.lifts (algebraMap R S) :=
    (Polynomial.lifts_iff_coeff_lifts (f := algebraMap R S) (P * Q)).2 fun k => ⟨⟨_, hPQR k⟩, rfl⟩
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hPm.mul hQm)

  let C : Set S := c' '' (Finset.range (d + 1) : Set ℕ)
  have hCf : C.Finite := (Finset.range (d + 1)).finite_toSet.image c'
  have hCi : ∀ x ∈ C, IsIntegral R x := by
    rintro _ ⟨i, hi, rfl⟩
    have := Polynomial.isIntegral_coeff_of_dvd F P hFm hPm (by rw [hF]; exact dvd_mul_right P Q) i
    rwa [hPc i (Finset.mem_range.1 hi)] at this
  obtain ⟨G, hG⟩ := fg_adjoin_of_finite hCf hCi

  let B : Subalgebra ℂ S := (Algebra.adjoin R C).restrictScalars ℂ
  have hpB : Algebra.adjoin ℂ (Set.range fun u => P.eval (algebraMap ℂ S u)) ≤ B := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨u, rfl⟩
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    refine B.sum_mem fun i hi => B.mul_mem ?_ (B.pow_mem (B.algebraMap_mem u) _)
    exact (Subalgebra.mem_restrictScalars _).2 (Algebra.subset_adjoin ⟨i, hi, rfl⟩)
  have hmap : Algebra.adjoin ℂ (Set.range p) =
      (Algebra.adjoin ℂ (Set.range fun u => P.eval (algebraMap ℂ S u))).map S.val := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    exact congrArg (fun f => Algebra.adjoin ℂ (Set.range f)) (funext fun u => (hPe u).symm)

  let Xs : Submodule ℂ N := ⨆ g : (G : Set S), (Wsp.map ((g : S) : Module.End ℂ N) : Submodule ℂ N)
  have : FiniteDimensional ℂ Wsp := hfin
  have key : ∀ x ∈ Submodule.span R (G : Set S), ∀ t ∈ T, ((x : S) : Module.End ℂ N) (t v) ∈ Xs := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro t ht
      have h1 : t v ∈ Wsp := Submodule.subset_span ⟨t, ht, rfl⟩
      exact (le_iSup (fun g : (G : Set S) => (Wsp.map ((g : S) : Module.End ℂ N) : Submodule ℂ N)) ⟨g, hg⟩)
        (Submodule.mem_map_of_mem h1)
    | zero =>
      intro t _
      rw [Subalgebra.coe_zero, LinearMap.zero_apply]
      exact Xs.zero_mem
    | add x y _ _ ihx ihy =>
      intro t ht
      rw [Subalgebra.coe_add, LinearMap.add_apply]
      exact Xs.add_mem (ihx t ht) (ihy t ht)
    | smul a x _ ih =>
      intro t ht
      have e1 : (a • x : S) = x * (a : S) := by rw [Algebra.smul_def, mul_comm]; rfl
      rw [e1, Subalgebra.coe_mul, mul_apply_eq_comp]
      have := ih _ (T.mul_mem (hRT a a.2) ht)
      rwa [mul_apply_eq_comp] at this
  refine Submodule.finiteDimensional_of_le (S₂ := Xs) (Submodule.span_le.2 ?_)
  rintro _ ⟨a, ha, rfl⟩
  rw [hmap] at ha
  obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.1 ha
  have hx' : x ∈ Submodule.span R (G : Set S) := by
    rw [hG]; exact (Subalgebra.mem_restrictScalars _).1 (hpB hx)
  have := key x hx' 1 T.one_mem
  simpa using this

end GlobalTheory.LeviHC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixTrivialOffInertPlaceUnitaryAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixTrivialOffInertPlaceUnitaryAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBigCell

theorem idem_split_mul {R S : Type} [CommRing R] [Ring S] (e : R) (ι : S →+ R)
    (he : (1 - e) * (1 - e) = 1 - e) (hι : ∀ x, (1 - e) * ι x = 0) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    {l m n : Type} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) (X : Matrix l m S) (Y : Matrix m n S) :
    ((1 - e) • A + X.map ι) * ((1 - e) • B + Y.map ι) = (1 - e) • (A * B) + (X * Y).map ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmul]
  linear_combination (A i k * B k j) * he + A i k * hι (Y k j) + B k j * hι (X i k)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem iotaW_apply (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw x = GlobalTheory.InertLocField.liftT E v ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm x) := rfl

theorem iotaW_injective (hw : Formalism.UG.IsInertAt F E v w) : Function.Injective (iotaW hw) :=
  (GlobalTheory.InertLocField.liftT_injective v).comp (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.injective

theorem iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) (x y : w.adicCompletion E) :
    iotaW hw (x * y) = iotaW hw x * iotaW hw y := by
  rw [iotaW_apply, iotaW_apply, iotaW_apply, map_mul, GlobalTheory.InertLocField.liftT_mul]

theorem idem_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * iotaW hw x = iotaW hw x := by
  rw [← Algebra.smul_def, GlobalTheory.InertLocField.liftV_one_smul, iotaW_apply, GlobalTheory.InertLocField.evT_liftT]

theorem one_sub_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * iotaW hw x = 0 := by
  rw [sub_mul, one_mul, idem_mul_iotaW, sub_self]

theorem one_sub_idem (v : Pl (F := F)) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) =
      1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  have h : algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) =
      algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
    rw [← map_mul, ← GlobalTheory.InertLocField.liftV_mul, mul_one]
  linear_combination h

theorem complEquiv_symm_algebraMap' (hw : Formalism.UG.IsInertAt F E v w) (x : E) :
    (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (algebraMap E _ x) = (1 : Fv F v) ⊗ₜ[F] x := by
  rw [RingEquiv.symm_apply_eq]
  change _ = toCompl (under_eq_of_isInertAt hw) ((1 : Fv F v) ⊗ₜ[F] x)
  rw [toCompl_tmul, map_one, one_mul]

theorem iotaW_algebraMap (hw : Formalism.UG.IsInertAt F E v w) (x : E) :
    iotaW hw (algebraMap E _ x) = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) x := by
  rw [iotaW_apply, complEquiv_symm_algebraMap', GlobalTheory.InertLocField.liftT_tmul]
  change _ = (GlobalTheory.LatVac.liftV v 1 ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] x)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem iotaW_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw (conjW σ hw x) = cA σ (iotaW hw x) := by
  rw [iotaW_apply, iotaW_apply, ← GlobalTheory.InertLocField.liftT_sigR]
  congr 1
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply _

theorem incM_split (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} (J : Matrix l m E) :
    incM F J = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • incM F J +
      (J.map (algebraMap E (w.adicCompletion E))).map (iotaW hw) := by
  ext i j
  simp only [incM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, iotaW_algebraMap]
  ring

end GlobalTheory.InertBigCell

namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem iotaW_one (hw : Formalism.UG.IsInertAt F E v w) :
    iotaW hw 1 = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  rw [← map_one (algebraMap E (w.adicCompletion E)), iotaW_algebraMap]
  change _ * inclR (F := F) (AF F) 1 = _
  rw [(inclR (F := F) (AF F)).map_one, mul_one]

theorem diagCols_split (hw : Formalism.UG.IsInertAt F E v w) (ι : Type) [DecidableEq ι] :
    (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) =
      (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) +
        (diagCols ι : Matrix (ι ⊕ ι) ι (w.adicCompletion E)).map (iotaW hw) := by
  ext i j
  rcases i with i | i <;>
  · simp only [diagCols, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply]
    split_ifs
    · rw [iotaW_one]; ring
    · rw [map_zero]; ring

theorem invOf_two_smul_add_iotaW (hw : Formalism.UG.IsInertAt F E v w) (t : AE F E) (x : w.adicCompletion E) :
    ⅟(2 : AF F) • (t + t + iotaW hw x) = t + iotaW hw ((2 : w.adicCompletion E)⁻¹ * x) := by
  have h2 : (2 : w.adicCompletion E) ≠ 0 := by
    rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hx : iotaW hw x = iotaW hw (2⁻¹ * x) + iotaW hw (2⁻¹ * x) := by
    rw [← map_add (f := _), ← add_mul, ← two_mul, mul_inv_cancel₀ h2, one_mul]
  rw [hx, show t + t + (iotaW hw (2⁻¹ * x) + iotaW hw (2⁻¹ * x)) =
      (2 : AF F) • (t + iotaW hw (2⁻¹ * x)) by rw [two_smul]; abel, smul_smul, invOf_mul_self, one_smul]

theorem glueW_transpose (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : (glueW hw P)ᵀ = glueW hw Pᵀ := by
  rw [glueW, glueW, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_map]

theorem glueW_map_cA (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : (glueW hw P).map (cA σ) = glueW hw (P.map (conjW σ hw)) := by
  ext i j
  simp only [glueW, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub,
    map_one, AlgHom.commutes, iotaW_conjW]
  congr 2
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem glueW_read_at_place (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι] :
  (∀ (J : Matrix ι ι E) (P : Matrix ι ι (w.adicCompletion E)),
    (GlobalTheory.InertBigCell.glueW hw P)ᵀ * incM F J * (GlobalTheory.InertBigCell.glueW hw P).map (cA σ) = incM F J ↔
      Pᵀ * J.map (algebraMap E (w.adicCompletion E)) * P.map (GlobalTheory.InertBigCell.conjW σ hw) = J.map (algebraMap E (w.adicCompletion E))) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E), P * diagCols ι = diagCols ι →
    GlobalTheory.InertBigCell.glueW hw P * (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) = diagCols ι) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E),
    ⅟(2 : AF F) • ((GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₂ +
      (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₂) =
    GlobalTheory.InertBigCell.glueW hw ((2 : w.adicCompletion E)⁻¹ • (P.toBlocks₁₁ + P.toBlocks₁₂ + P.toBlocks₂₁ + P.toBlocks₂₂))) := by
  set e := algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) with he_def
  refine ⟨fun J P => ?_, fun P hP => ?_, fun P => ?_⟩
  · rw [glueW_transpose, glueW_map_cA, glueW, glueW, incM_split hw J, idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw), idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw), Matrix.one_mul, Matrix.mul_one,
      add_right_inj]
    exact (Matrix.map_injective (iotaW_injective hw)).eq_iff
  · rw [diagCols_split hw ι, glueW, idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.one_mul]
    exact congrArg (fun M => (1 - e) • (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) + M.map (iotaW hw)) hP
  · ext i j
    simp only [glueW, Matrix.smul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
      Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, add_zero]
    rw [← invOf_two_smul_add_iotaW hw, map_add (f := _), map_add (f := _), map_add (f := _)]
    congr 1
    abel

end GlobalTheory.InertBigCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixTrivialOffInertPlaceUnitaryAtPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ (J : Matrix ι ι E) (P : Matrix ι ι (w.adicCompletion E)),
    (GlobalTheory.InertBigCell.glueW hw P)ᵀ * incM F J * (GlobalTheory.InertBigCell.glueW hw P).map (cA σ) = incM F J ↔
      Pᵀ * J.map (algebraMap E (w.adicCompletion E)) * P.map (GlobalTheory.InertBigCell.conjW σ hw) = J.map (algebraMap E (w.adicCompletion E))) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E), P * diagCols ι = diagCols ι →
    GlobalTheory.InertBigCell.glueW hw P * (diagCols ι : Matrix (ι ⊕ ι) ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = diagCols ι) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E),
    ⅟(2 : AF F) • ((GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₂ +
      (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₂) =
    GlobalTheory.InertBigCell.glueW hw ((2 : w.adicCompletion E)⁻¹ • (P.toBlocks₁₁ + P.toBlocks₁₂ + P.toBlocks₂₁ + P.toBlocks₂₂))) := by
  first | exact @GlobalTheory.InertBigCell.glueW_read_at_place | exact GlobalTheory.InertBigCell.glueW_read_at_place | (intros; apply GlobalTheory.InertBigCell.glueW_read_at_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorIsometryMovedOrthonormal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open GlobalTheory.TriMove GlobalTheory.Mem.Isom
open Formalism.UG (cT cT_mul cT_one)
open scoped TensorProduct

private theorem opPow_comm {ι X X' : Type} (tr : (X → ℂ) →ₗ[ℂ] (X' → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (A' : ι → (X' → ℂ) → (X' → ℂ)) (h : ∀ k g, A' k (tr g) = tr (A k g)) (k : ι →₀ ℕ) (f : X → ℂ) :
    opPow A' k (tr f) = tr (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons]; rw [ih, h]

private theorem pure_comm {D : D7} {m n m' n' : ℕ} (hm : m = m') (hn : n = n') {X X' : Type}
    (tr : (X → ℂ) →ₗ[ℂ] (X' → ℂ)) (A : FVar D m n → (X → ℂ) → (X → ℂ))
    (A' : FVar D m' n' → (X' → ℂ) → (X' → ℂ))
    (h : ∀ (k : FVar D m n) g, A' (k.1, finCongr hm k.2.1, finCongr hn k.2.2) (tr g) = tr (A k g)) (f : X → ℂ)
    (P : MvPolynomial (FVar D m n) ℂ) :
    pureTensorL A' (tr f) (polMove hm hn P) = tr (pureTensorL A f P) := by
  subst hm hn
  have e : polMove (D := D) (rfl : m = m) (rfl : n = n) P = P := MvPolynomial.rename_id_apply P
  rw [e]
  have e2 : pureTensorL A' (tr f) = tr ∘ₗ pureTensorL A f := by
    refine (MvPolynomial.basisMonomials (FVar D m n) ℂ).ext fun k => ?_
    unfold pureTensorL
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]
    exact opPow_comm tr A A' h k f
  rw [e2]
  rfl

private theorem unitMap_move {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    (pS : Matrix (Fin n') (Fin n) ℂ) (qS : Matrix (Fin n) (Fin n') ℂ) (pq : pS * qS = 1)
    (pT : Matrix (Fin m') (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    unitMap (pS * B * (rdx hn : Matrix (Fin n) (Fin n') ℂ)) (pT * B' * (rdx hm : Matrix (Fin m) (Fin m') ℂ)) (finCongr hm i) (finCongr hn j) = pT * unitMap B B' i j * qS := by
  subst hm hn
  have e1 : rdx (K := ℂ) (rfl : m = m) = 1 := rfl
  have e2 : rdx (K := ℂ) (rfl : n = n) = 1 := rfl
  unfold unitMap
  rw [e1, e2, Matrix.mul_one, Matrix.mul_one, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv pq]
  simp only [Matrix.mul_assoc]
  rfl

private theorem cplxO_move {m n m' n' : ℕ} (ε : Bool)
    (pS : Matrix (Fin n') (Fin n) ℂ) (qS : Matrix (Fin n) (Fin n') ℂ) (qp : qS * pS = 1)
    (pT : Matrix (Fin m') (Fin m) ℂ) (qT : Matrix (Fin m) (Fin m') ℂ) (qp' : qT * pT = 1)
    (s : Matrix (Fin n) (Fin n) ℂ) (s' : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO (GlobalTheory.Grid.sgnM ε (pS * s * qS)) (pT * s' * qT) (pT * z * qS) = pT * cplxO (GlobalTheory.Grid.sgnM ε s) s' z * qS := by
  have e : GlobalTheory.Grid.sgnM ε (pS * s * qS) = pS * GlobalTheory.Grid.sgnM ε s * qS := by
    cases ε
    · rfl
    · show -(pS * s * qS) = pS * (-s) * qS
      rw [Matrix.mul_neg, Matrix.neg_mul]
  unfold cplxO
  rw [e, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = pT * s' * (qT * pT) * z * (qS * pS) * GlobalTheory.Grid.sgnM ε s * qS := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [qp, qp', Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private theorem trace_move {A : Type} [CommRing A] {m n m' n' : ℕ} (s : A →+* A)
    {H : Matrix (Fin n) (Fin n) A} {H' : Matrix (Fin n') (Fin n') A} {Q : Matrix (Fin n) (Fin n') A}
    (hH : Q * H' * cT s Q = H)
    {J : Matrix (Fin m) (Fin m) A} {J' : Matrix (Fin m') (Fin m') A} {P : Matrix (Fin m') (Fin m) A}
    (hJ : cT s P * J' * P = J) (x y : Matrix (Fin m) (Fin n) A) :
    Matrix.trace (H' * (cT s (P * y * Q) * J' * (P * x * Q))) = Matrix.trace (H * (cT s y * J * x)) := by
  rw [← hH, ← hJ, cT_mul, cT_mul]
  calc _ = Matrix.trace ((H' * cT s Q * (cT s y * (cT s P * J' * P) * x)) * Q) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

variable {D : D7}

private theorem hO_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (S.gram⁻¹.map (incA D) * (cT (cA D) y * T.gram.map (incA D) * x)) := by
  unfold hO
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact sum_form (cA D) (T.gram.map (incA D)) x y (incA D (S.gram⁻¹ a b)) a b

variable {S S' T T' : HSp D}

private theorem gram_inv_move (I : IsoMat S S') :
    I.Q * S'.gram⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q = S.gram⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← I.gram]
  calc _ = cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * (S'.gram * (I.P * I.Q) * S'.gram⁻¹) *
        cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q := by simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [I.PQ, Matrix.mul_one, Matrix.mul_nonsing_inv _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S'), Matrix.mul_one, ← cT_mul, I.QP,
        cT_one]

private theorem hO_homMap (IS : IsoMat S S') (IT : IsoMat T T') (x y : WO S T) :
    hO S' T' (homMap IS IT x) (homMap IS IT y) = hO S T x y := by
  rw [hO_trace, hO_trace]
  refine trace_move (cA D) ?_ (map_gram (incA D) _ (cA D) (fun _ => rfl) IT.gram) x y
  rw [← gram_inv_move IS, Matrix.map_mul, Matrix.map_mul]
  rfl

private theorem heisO_homMap (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (IS : IsoMat S S') (IT : IsoMat T T') (u : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ (GlobalTheory.Grid.sgn ε S') T' (homMap (S := S) (S' := S') IS IT u) (trH (S := S) (S' := S') IS IT f) = trH (S := S) (S' := S') IS IT (heisO ψ (GlobalTheory.Grid.sgn ε S) T u f) := by
  funext w
  obtain ⟨w, rfl⟩ := (homMap IS IT).surjective w
  have e : hO (GlobalTheory.Grid.sgn ε S') T' (homMap IS IT w) (homMap IS IT u) = hO (GlobalTheory.Grid.sgn ε S) T w u := by
    cases ε
    · exact hO_homMap IS IT w u
    · exact (GlobalTheory.Grid.hO_neg S' T' _ _).trans ((congrArg Neg.neg (hO_homMap IS IT w u)).trans (GlobalTheory.Grid.hO_neg S T _ _).symm)
  simp only [heisO, trH, ← map_add (f := _), AddEquiv.symm_apply_apply, symplOH, symplO, e]

private theorem lineAt_spec {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

private theorem lineAt_homMap {θ : InfFam D} (hθ : IsInfFam θ) (IS : IsoMat S S') (IT : IsoMat T T') (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (IT.pT τ * z * IS.qT τ) t = homMap IS IT (lineAt θ τ z t) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨h1, h2, h3⟩ := lineAt_spec hθ τ z
  have key : IsLineAt θ τ (IT.pT τ * z * IS.qT τ) ((homMap IS IT).toAddMonoidHom.comp (lineAt θ τ z)) := by
    refine ⟨(continuous_const.matrix_mul h1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (HMul.hMul (HMul.hMul IT.aP (lineAt θ τ z t)) IS.aQ).map (finPart D) = 0
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · let ρ : AE D →+* ℂ := (θ τ').comp (infPart D)
      have hρ : ∀ x : D.host.E, ρ (incA D x) = tauE D τ' x := fun x => by
        have := (hθ τ').1 x
        rw [← this]
        simp [ρ, incA, inclR, infPart]
      have e1 : IT.aP.map ρ = IT.pT τ' := by ext i j; exact hρ _
      have e2 : IS.aQ.map ρ = IS.qT τ' := by ext i j; exact hρ _
      have e3 : (lineAt θ τ z t).map ρ = _ := h3 t τ'
      show (HMul.hMul (HMul.hMul IT.aP (lineAt θ τ z t)) IS.aQ).map ρ = _
      rw [Matrix.map_mul, Matrix.map_mul, e1, e2, e3]
      split_ifs with c
      · subst c
        rw [Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (lineAt_spec hθ τ _) key]
  rfl

private theorem dRho_homMap (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (ε : Bool) (IS : IsoMat S S')
    (IT : IsoMat T T') (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ (GlobalTheory.Grid.sgn ε S') T') θ τ (IT.pT τ * z * IS.qT τ) (trH (S := S) (S' := S') IS IT f) =
      trH (S := S) (S' := S') IS IT (dRho (heisO ψ (GlobalTheory.Grid.sgn ε S) T) θ τ z f) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  simp only [lineAt_homMap hθ, heisO_homMap]
  rfl

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ → ∀ (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
  pureTensorO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (fun τ => GlobalTheory.TriMove.basMove (S' := S') IS τ (BS τ)) (fun τ => GlobalTheory.TriMove.basMove (S' := T') IT τ (BT τ)) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) (GlobalTheory.TriMove.polMove IT.rank_eq IS.rank_eq P) =
    GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT (pureTensorO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT BS BT f P) := by
  intro D ψ θ hθ ε S S' T T' IS IT sS BS sT BT f P
  refine pure_comm IT.rank_eq IS.rank_eq (GlobalTheory.TriMove.trLE IS IT).toLinearMap _ _ (fun k g => ?_) f P
  have e : ∀ g, (GlobalTheory.TriMove.trLE IS IT).toLinearMap g = GlobalTheory.TriMove.trH IS IT g := fun _ => rfl
  have e1 : unitMap (GlobalTheory.TriMove.basMove IS k.1 (BS k.1)) (GlobalTheory.TriMove.basMove IT k.1 (BT k.1)) (finCongr IT.rank_eq k.2.1)
      (finCongr IS.rank_eq k.2.2) = _ :=
    unitMap_move IT.rank_eq IS.rank_eq _ _ (IS.pT_qT k.1) (IT.pT k.1) (BS k.1) (BT k.1) k.2.1 k.2.2
  rw [e, e]
  unfold aPlusAll aPlus crea GlobalTheory.TriMove.cartMove
  dsimp only
  rw [e1, cplxO_move ε _ _ (IS.qT_pT k.1) _ _ (IT.qT_pT k.1), dRho_homMap ψ hθ, dRho_homMap ψ hθ]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDetPowCharacterSeparatesWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDetPowCharacterSeparatesWeights
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem GlobalTheory.MinorFrame.exists_unitary_detChar_ne : ∀ {ι : Type} [Fintype ι] (a : ℕ), 0 < a → ∀ n n₀ : ι → ℕ, n ≠ n₀ →
    ∃ g : ι → Matrix.unitaryGroup (Fin a) ℂ, GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) ≠ GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) := by
  intro ι _ a ha n n₀ hne
  classical
  obtain ⟨τ₀, hτ⟩ := Function.ne_iff.mp hne
  have hN : n τ₀ + n₀ τ₀ + 1 ≠ 0 := by omega
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ))) (n τ₀ + n₀ τ₀ + 1) :=
    Complex.isPrimitiveRoot_exp _ hN
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ)) with hzdef
  have hzn : ‖z‖ = 1 := hz.norm'_eq_one hN
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]; simp
  let d : Fin a → ℂ := Function.update 1 ⟨0, ha⟩ z
  have hU : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = ⟨0, ha⟩
    · subst i; simpa [d] using hzz
    · simp [d, hi]
  let g : ι → Matrix.unitaryGroup (Fin a) ℂ := fun τ => if τ = τ₀ then ⟨_, hU⟩ else 1
  refine ⟨g, ?_⟩
  have key : ∀ m : ι → ℕ, GlobalTheory.MinorFrame.detChar m (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = z ^ m τ₀ := by
    intro m
    unfold GlobalTheory.MinorFrame.detChar
    rw [Finset.prod_eq_single τ₀]
    · simp only [g, if_pos rfl, Matrix.det_diagonal, d]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    · intro b _ hb
      simp [g, hb]
    · simp
  rw [key, key]
  intro h
  exact hτ (hz.pow_inj (by omega) (by omega) h)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDetPowCharacterSeparatesWeightsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_detPowCharacter_separates_weights : ∀ {ι : Type} [Fintype ι] (a : ℕ), 0 < a → ∀ n n₀ : ι → ℕ, n ≠ n₀ →
    ∃ g : ι → Matrix.unitaryGroup (Fin a) ℂ, GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) ≠ GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) := by
  first | exact @GlobalTheory.MinorFrame.exists_unitary_detChar_ne | exact GlobalTheory.MinorFrame.exists_unitary_detChar_ne | (intros; apply GlobalTheory.MinorFrame.exists_unitary_detChar_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberHalfIsometryMoved
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriMove.StdFstMove

variable {D : D7}

private theorem rdi_mul_rdx {K : Type} [CommRing K] {m n m' n' : ℕ} (h : m = n) (h' : m' = n') (M : Matrix (Fin m) (Fin m') K) :
    HMul.hMul (HMul.hMul (rdi (K := K) h) M) (rdx (K := K) h') = M.submatrix (finCongr h).symm (finCongr h').symm := by
  subst h; subst h'
  ext i j
  simp [rdi, rdx, Matrix.mul_apply, Matrix.one_apply]

private theorem isIntM_re {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (M : Matrix (Fin b) (Fin a) (Formalism.IndefR.Datum.EAf D)) :
    Formalism.IndefR.Datum.IsIntM (D := D) (M.submatrix (finCongr hb).symm (finCongr ha).symm) ↔ Formalism.IndefR.Datum.IsIntM (D := D) M := by
  subst ha; subst hb; simp

private theorem inId_re (I : Ideal (𝓞 D.host.E)) {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (M : Matrix (Fin b) (Fin a) (Formalism.IndefR.Datum.EAf D)) :
    (∀ i j, a' ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (M.submatrix (finCongr hb).symm (finCongr ha).symm i j)) ↔
      ∀ i j, a ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (M i j) := by
  subst ha; subst hb; simp

private theorem unitChar_re (ν : (AE D)ˣ →* Circle) (e : AE D) {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    (M : Matrix (Fin b) (Fin a) (Formalism.IndefR.Datum.EAf D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (Formalism.IndefR.Datum.topL a' (M.submatrix (finCongr hb).symm (finCongr ha).symm)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (Formalism.IndefR.Datum.topL a M) := by
  subst ha; subst hb; simp

private theorem fixed_two {R : Type} [CommRing R] {p q r s : ℕ} (e : R) (M : Matrix (Fin p) (Fin q) R) (N : Matrix (Fin r) (Fin s) R)
    (x : Matrix (Fin q) (Fin r) R) (H : ∀ i j, e * x i j = x i j) (i : Fin p) (j : Fin s) :
    e * (M * x * N) i j = (M * x * N) i j := by
  have hx : e • x = x := by ext i j; exact H i j
  have : e • (M * x * N) = M * x * N := by rw [← Matrix.smul_mul, ← Matrix.mul_smul, hx]
  exact congrFun (congrFun this i) j

variable {S S' T T' : HSp D}

private theorem isHalf_homMap (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (e : AE D) (x : WO S T) :
    Formalism.IndefR.Datum.IsHalf e (homMap IS IT x) ↔ Formalism.IndefR.Datum.IsHalf e x := by
  constructor
  · intro h
    have hx : x = HMul.hMul (HMul.hMul IT.aQ (homMap IS IT x)) IS.aP := ((homMap IS IT).symm_apply_apply x).symm
    intro i j
    rw [hx]
    exact fixed_two e _ _ _ h i j
  · intro h i j
    exact fixed_two e _ _ _ h i j

private theorem map_aP (I : GlobalTheory.Mem.Isom.IsoMat S S') : I.aP.map (Formalism.IndefR.Datum.toEAf D) = fP I := by
  ext i j; rfl

private theorem map_aQ (I : GlobalTheory.Mem.Isom.IsoMat S S') : I.aQ.map (Formalism.IndefR.Datum.toEAf D) = fQ I := by
  ext i j; rfl

private theorem frMapO_homMap (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T')
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO S T) :
    frMapO S' T' (betaMove IS βS) (betaMove IT βT) (homMap IS IT x) =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IT.rank_eq) (frMapO S T βS βT x)) (rdx (K := Lev.EAf D) IS.rank_eq) := by
  unfold frMapO
  rw [homMap_apply]
  show HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IT.rank_eq) (βT⁻¹).val) (fQ IT))
      ((HMul.hMul (HMul.hMul IT.aP x) IS.aQ).map (Formalism.IndefR.Datum.toEAf D)))
      (HMul.hMul (HMul.hMul (fP IS) βS.val) (rdx (K := Lev.EAf D) IS.rank_eq)) = _
  rw [Matrix.map_mul, Matrix.map_mul, map_aP, map_aQ]
  calc _ = HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IT.rank_eq) (βT⁻¹).val) (HMul.hMul (fQ IT) (fP IT)))
            (x.map (Formalism.IndefR.Datum.toEAf D))) (HMul.hMul (fQ IS) (fP IS))) βS.val) (rdx (K := Lev.EAf D) IS.rank_eq) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [fQ_fP, fQ_fP, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc (rdi _), ← Matrix.mul_assoc (rdi _)]

private theorem stdFst_move : ∀ {D : D7} {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
  GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S' T' (GlobalTheory.TriMove.betaMove IS βS) (GlobalTheory.TriMove.betaMove IT βT) = GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT) := by
  intro D S S' T T' IS IT ν e I βS βT
  classical
  funext w
  obtain ⟨x, rfl⟩ := (homMap IS IT).surjective w
  unfold trH
  rw [AddEquiv.symm_apply_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [frMapO_homMap, rdi_mul_rdx]
  exact if_congr (and_congr (isHalf_homMap IS IT e x) (and_congr (isIntM_re _ _ _) (inId_re I _ _ _))) (unitChar_re ν e _ _ _) rfl

end GlobalTheory.TriMove.StdFstMove

end

theorem _root_.GlobalTheory.T.standardPairFirstMemberHalf_isometry_moved : ∀ {D : D7} {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
  GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S' T' (GlobalTheory.TriMove.betaMove IS βS) (GlobalTheory.TriMove.betaMove IT βT) = GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT) := @GlobalTheory.TriMove.StdFstMove.stdFst_move
end
