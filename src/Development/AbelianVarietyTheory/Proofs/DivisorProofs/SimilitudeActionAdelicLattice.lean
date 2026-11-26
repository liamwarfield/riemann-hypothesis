module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTermsTorusTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleAwayFromPEqZeroOfDivisibleCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleAwayFromPEqZeroOfDivisibleCoprime
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped RestrictedProduct

namespace GlobalTheory.AfPZero

theorem natCast_eq_algebraMap (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) (n : ℤ) :=
  (map_natCast (algebraMap ℤ (v.adicCompletion ℚ)) n).symm

theorem valued_natCast (v : HeightOneSpectrum ℤ) (n : ℕ) :
    Valued.v (n : v.adicCompletion ℚ) = v.intValuation (n : ℤ) := by
  rw [natCast_eq_algebraMap]
  have := valuedAdicCompletion_eq_valuation (K := ℚ) v (n : ℤ)
  rw [← valuation_of_algebraMap (K := ℚ)]
  exact this

theorem eq_zero_of_dvd (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ)
    (h : ∀ k : ℕ, ∃ n : ℕ, (n : ℤ) ∈ v.asIdeal ^ k ∧
      ∃ y ∈ v.adicCompletionIntegers ℚ, x = (n : v.adicCompletion ℚ) * y) : x = 0 := by
  by_contra hx
  have hγ : Valued.v x ≠ 0 := by simpa using hx
  set L : ℤ := log (Valued.v x) with hL
  obtain ⟨n, hn, y, hy, hxe⟩ := h ((-L).toNat + 1)
  have h1 : Valued.v x ≤ exp (-(((-L).toNat + 1 : ℕ) : ℤ)) := by
    rw [hxe, map_mul]
    calc Valued.v (n : v.adicCompletion ℚ) * Valued.v y ≤ Valued.v (n : v.adicCompletion ℚ) * 1 :=
          by gcongr; exact (mem_adicCompletionIntegers ℤ ℚ v).1 hy
      _ = v.intValuation (n : ℤ) := by rw [_root_.mul_one, valued_natCast]
      _ ≤ _ := (intValuation_le_pow_iff_mem v _ _).2 hn
  rw [← exp_log hγ, ← hL] at h1
  have h2 := exp_le_exp.1 h1
  omega

open GlobalTheory.LKTrip GlobalTheory.LKGeo

theorem exists_prime (p : ℕ) [Fact p.Prime] (v : AwayP p) :
    ∃ l : ℕ, l.Prime ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
  set q : ℤ := Submodule.IsPrincipal.generator v.1.asIdeal with hq
  have hspan : v.1.asIdeal = Ideal.span {q} := (Submodule.IsPrincipal.span_singleton_generator v.1.asIdeal).symm
  have hq0 : q ≠ 0 := by
    intro h0
    apply v.1.ne_bot
    rw [hspan, h0, Ideal.span_singleton_eq_bot]
  have hqp : Prime q := by
    have := v.1.isPrime
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hq0).1 this
  have hl : q.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan' : v.1.asIdeal = Ideal.span {((q.natAbs : ℕ) : ℤ)} := by
    rw [hspan, Int.span_natAbs]
  refine ⟨q.natAbs, hl, (Nat.coprime_primes hl (Fact.out)).2 ?_, ?_⟩
  · intro he
    apply v.2
    rw [hspan', he]
  · rw [hspan']
    exact Ideal.subset_span rfl

theorem main : ∀ (p : ℕ) [Fact p.Prime] (α : AfP p),
    (∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = n • β) → α = 0 := by
  intro p _ α h
  have hloc : ∀ v : AwayP p, AfP.eval v α = 0 := by
    intro v
    obtain ⟨l, hl, hlp, hlv⟩ := exists_prime p v
    apply eq_zero_of_dvd v.1
    intro k
    obtain ⟨β, hβ, hαβ⟩ := h (l ^ k) (pow_pos hl.pos k) (Nat.Coprime.pow_left k hlp)
    refine ⟨l ^ k, by push_cast; exact Ideal.pow_mem_pow hlv k, AfP.eval v β, hβ v, ?_⟩
    rw [hαβ, map_nsmul, nsmul_eq_mul]
  exact Subtype.ext (funext fun v => hloc v)

end GlobalTheory.AfPZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleAwayFromPEqZeroOfDivisibleCoprimeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleAwayFromP_eq_zero_of_divisible_coprime : ∀ (p : ℕ) [Fact p.Prime] (α : AfP p), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = n • β) → α = 0 := by
  first | (exact @GlobalTheory.AfPZero.main) | (exact GlobalTheory.AfPZero.main) | (intros; apply GlobalTheory.AfPZero.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDivisibleInLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianLieLatticeAgree
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKGeo.ModZero

theorem repr_isIntAf {p : ℕ} [Fact p.Prime] (D : Datum p) {κ : Type} (b : Module.Basis κ ℤ D.La)
    (u : AfP p ⊗[ℚ] VQ D) (hu : u ∈ LaHat D) (i : κ) :
    IsIntAf ((Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)).repr u i) := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨a, x, ha, rfl⟩ := hu
    intro v
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, one_smul,
      eq_intCast (algebraMap ℤ ℚ), map_intCast, map_mul, map_intCast]
    exact mul_mem (ha v) (intCast_mem _ _)
  | zero => intro v; rw [map_zero, Finsupp.zero_apply, map_zero]; exact zero_mem _
  | add u u' _ _ hu hu' => intro v; rw [map_add (f := _), Finsupp.add_apply, map_add (f := _)]; exact add_mem (hu v) (hu' v)
  | neg u _ hu => intro v; rw [map_neg, Finsupp.neg_apply, map_neg]; exact neg_mem (hu v)

end GlobalTheory.LKGeo.ModZero


open GlobalTheory.LKGeo.ModZero in
theorem GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D),
    (∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) → z = 0 := by
  intro p _ D z hz
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bA := Algebra.TensorProduct.basis (AfP p) (Algebra.TensorProduct.basis ℚ b)
  refine bA.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine GlobalTheory.T.finiteAdeleAwayFromP_eq_zero_of_divisible_coprime p (bA.repr z i) fun n hn hc => ?_
  obtain ⟨w, hw, rfl⟩ := hz n hn hc
  exact ⟨bA.repr w i, repr_isIntAf D b w hw i, by rw [map_nsmul, Finsupp.smul_apply]⟩
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_divisible_in_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) → z = 0 := by
  first | (exact @GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat) | (exact GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat) | (intros; apply GlobalTheory.LKGeo.eq_zero_of_forall_nsmul_laHat <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfPairingVanishes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegenerateIntegralForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem det_gram_ne_zero {L : Type} [AddCommGroup L] {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ ℤ L) (B : LinearMap.BilinForm ℤ L) (hB : Function.Injective B) :
    (Matrix.of fun i j => B (b i) (b j)).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  apply hc0
  have hx : B (∑ i, c i • b i) = 0 := by
    apply b.ext
    intro j
    have := congrFun hc j
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Matrix.vecMul, dotProduct, map_sum, map_smul, mul_comm] using this
  have h1 : ∑ i, c i • b i = 0 := hB (hx.trans (map_zero B).symm)
  funext i
  exact Fintype.linearIndependent_iff.mp b.linearIndependent c h1 i

theorem nondeg_afP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D),
    (∀ v, (D.EF.baseChange ℚ).baseChange (AfP p) v z = 0) → z = 0 := by
  intro p _ D z hz
  classical
  haveI := D.freeLa; haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bQ := Algebra.TensorProduct.basis ℚ b
  let bA := Algebra.TensorProduct.basis (AfP p) bQ
  have hg : ∀ i j, (D.EF.baseChange ℚ).baseChange (AfP p) (bA i) (bA j) = ((D.EF (b i) (b j) : ℤ) : AfP p) := by
    intro i j
    simp [bA, bQ, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]
  set c := bA.repr z
  let M : Matrix _ _ (AfP p) := (Matrix.of fun i j => D.EF (b i) (b j)).map (Int.castRingHom (AfP p))
  have hzs : z = ∑ j, c j • bA j := (bA.sum_repr z).symm
  have hM : M.mulVec c = 0 := by
    funext i
    have := hz (bA i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hzs, map_sum] at this
    simpa [Matrix.mulVec, dotProduct, M, hg, mul_comm] using this
  have hdet : IsUnit M.det := by
    rw [show M.det = Int.castRingHom (AfP p) (Matrix.of fun i j => D.EF (b i) (b j)).det from
      (RingHom.map_det _ _).symm]
    have h0 := det_gram_ne_zero b D.EF D.nondeg
    have hq : IsUnit (((Matrix.of fun i j => D.EF (b i) (b j)).det : ℤ) : ℚ) :=
      isUnit_iff_ne_zero.mpr (by exact_mod_cast h0)
    have := hq.map (algebraMap ℚ (AfP p))
    simpa using this
  have hc : (⇑c : _ → AfP p) = 0 := by
    have := congrArg (M⁻¹).mulVec hM
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have hc' : ∀ j, c j = 0 := fun j => congrFun hc j
  rw [hzs]
  simp [hc']

end GlobalTheory.LKGeo
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_pairing_vanishes : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D), (∀ v, (D.EF.baseChange ℚ).baseChange (AfP p) v z = 0) → z = 0 := by
  first | (exact @GlobalTheory.LKGeo.nondeg_afP) | (exact GlobalTheory.LKGeo.nondeg_afP) | (intros; apply GlobalTheory.LKGeo.nondeg_afP  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingIntegral
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_pairing_integral : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (v w : AfP p ⊗[ℚ] VQ D), v ∈ LaHat D → w ∈ LaHat D → IsIntAf ((D.EF.baseChange ℚ).baseChange (AfP p) v w) := by
  first | (exact @GlobalTheory.LKGeo.formInt_laHat) | (exact GlobalTheory.LKGeo.formInt_laHat) | (intros; apply GlobalTheory.LKGeo.formInt_laHat  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingAdjointInvolution
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_adjoint_involution : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D), (D.EF.baseChange ℚ).baseChange (AfP p) (actOn L.rep (AfP p) x v) w = (D.EF.baseChange ℚ).baseChange (AfP p) v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := by
  first | (exact @GlobalTheory.LKGeo.adj_actOn_afP) | (exact GlobalTheory.LKGeo.adj_actOn_afP) | (intros; apply GlobalTheory.LKGeo.adj_actOn_afP  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupAlgebraActionOfCommuteOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupAlgebraActionOfCommuteOrder
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LKGeo.CommBC

theorem actOn_tmul_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (a b : R) (c : C) (v : V) :
    actOn rep R (a ⊗ₜ c) (b ⊗ₜ v) = (a * b) ⊗ₜ rep c v := by
  have : actOn rep R (a ⊗ₜ c) = Algebra.ofId R _ a * Module.End.baseChangeHom ℚ R V (rep c) :=
    Algebra.TensorProduct.lift_tmul _ _ _ a c
  rw [this, Module.End.mul_apply]
  simp only [Algebra.ofId_apply, Module.algebraMap_end_apply]
  change a • (LinearMap.baseChange R (rep c)) (b ⊗ₜ v) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

theorem exists_actOn_eq {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) {ι' : Type} (S : ι' → Module.End ℚ V)
    (hrange : ∀ B : Module.End ℚ V, (∀ b, B * S b = S b * B) → ∃ x, rep x = B)
    (R : Type) [CommRing R] [Algebra ℚ R] (A : Module.End R (R ⊗[ℚ] V))
    (hA : ∀ b, A * (S b).baseChange R = (S b).baseChange R * A) : ∃ y, actOn rep R y = A := by
  classical
  let r := Module.Free.chooseBasis ℚ R
  let e : R ⊗[ℚ] V ≃ₗ[ℚ] (Module.Free.ChooseBasisIndex ℚ R →₀ V) :=
    (LinearEquiv.rTensor V r.repr).trans (TensorProduct.finsuppScalarLeft ℚ V _)
  have he : ∀ (a : R) (v : V) k, e (a ⊗ₜ v) k = r.repr a k • v := by
    intro a v k
    simp [e, TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  let Ak : Module.Free.ChooseBasisIndex ℚ R → Module.End ℚ V := fun k =>
    (Finsupp.lapply k) ∘ₗ e.toLinearMap ∘ₗ (A.restrictScalars ℚ) ∘ₗ (TensorProduct.mk ℚ R V 1)
  have hAk : ∀ k v, Ak k v = e (A (1 ⊗ₜ v)) k := fun k v => rfl
  have heS : ∀ (s : Module.End ℚ V) (x : R ⊗[ℚ] V) k, e (s.baseChange R x) k = s (e x k) := by
    intro s x k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => simp [he]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  have hcomm : ∀ k b, Ak k * S b = S b * Ak k := by
    intro k b; ext v
    simp only [Module.End.mul_apply, hAk]
    have := congrArg (fun f => f ((1 : R) ⊗ₜ v)) (hA b)
    simp only [Module.End.mul_apply, LinearMap.baseChange_tmul] at this
    rw [this, heS]
  choose x hx using fun k => hrange (Ak k) (hcomm k)
  let bV := Module.finBasis ℚ V
  let F := Finset.univ.biUnion fun i => (e (A ((1 : R) ⊗ₜ bV i))).support
  have hzero : ∀ k ∉ F, Ak k = 0 := by
    intro k hk
    refine bV.ext fun i => ?_
    rw [hAk, LinearMap.zero_apply]
    by_contra h
    exact hk (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩)
  refine ⟨∑ k ∈ F, r k ⊗ₜ x k, ?_⟩
  have h1 : ∀ v, actOn rep R (∑ k ∈ F, r k ⊗ₜ x k) ((1 : R) ⊗ₜ v) = A ((1 : R) ⊗ₜ v) := by
    intro v
    apply e.injective
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
    simp_rw [actOn_tmul_tmul, _root_.mul_one, hx, he, Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul,
      zero_smul]
    rw [Finset.sum_ite_eq', ← hAk]
    split_ifs with hj
    · rfl
    · rw [hzero j hj, LinearMap.zero_apply]
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  have : a ⊗ₜ[ℚ] v = a • ((1 : R) ⊗ₜ v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  rw [this, map_smul, map_smul, h1]

theorem exists_actOn_eq_of_commute : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G)
    (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)),
    (∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) →
    ∃ y, actOn L.rep (AfP p) y = A := by
  intro p _ D G L A hA
  haveI := D.finLa
  exact exists_actOn_eq L.rep (actQ D) (fun B hB => (L.rep_range B).mpr hB) (AfP p) A hA

end GlobalTheory.LKGeo.CommBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupAlgebraActionOfCommuteOrderStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupAlgebra_action_of_commute_order : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) → ∃ y, actOn L.rep (AfP p) y = A := by
  first | (exact @GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute) | (exact GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute) | (intros; apply GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleInverseSystemLatticeMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleInverseSystemLatticeMaps
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

namespace GlobalTheory.InvSys

theorem exists_nsmul_of_basis {M κ : Type} [AddCommGroup M] (b : Module.Basis κ ℤ M) (f : M →ₗ[ℤ] M) (n : ℕ)
    (hb : ∀ i, ∃ z, f (b i) = n • z) (x : M) : ∃ z, f x = n • z := by
  have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hb i
  | zero => exact ⟨0, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨z1, h1⟩ := hy; obtain ⟨z2, h2⟩ := hw
    exact ⟨z1 + z2, by rw [map_add (f := _), h1, h2, smul_add]⟩
  | smul a y _ hy =>
    obtain ⟨z, h⟩ := hy
    exact ⟨a • z, by rw [map_smul, h, smul_comm]⟩

theorem invSys : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w) → ∃ g' : ℕ → D.La →+ D.La, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g' (n * m) x = g' n x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g' n (g n x) = x + n • z) := by
  intro p _ D g htow hsurj hinj
  haveI := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  choose y z hyz using hsurj
  let g' : ℕ → D.La →+ D.La := fun n =>
    if h : 0 < n ∧ n.Coprime p then (b.constr ℤ (fun i => y n h.1 h.2 (b i))).toAddMonoidHom else 0
  have sec : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z := by
    intro n hn hc x
    have hg' : g' n = (b.constr ℤ (fun i => y n hn hc (b i))).toAddMonoidHom := by
      simp only [g', dif_pos (And.intro hn hc)]
    obtain ⟨w, hw⟩ := exists_nsmul_of_basis b
      ((g n).toIntLinearMap ∘ₗ b.constr ℤ (fun i => y n hn hc (b i)) - LinearMap.id) n
      (fun i => ⟨z n hn hc (b i), by simp [Module.Basis.constr_basis, hyz]⟩) x
    refine ⟨w, ?_⟩
    rw [hg']
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply] at hw
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [← hw]; abel
  refine ⟨g', ?_, sec, ?_⟩
  · intro n m hn hm hc x
    have hcn : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hc
    obtain ⟨z1, h1⟩ := htow n m hn hm hc (g' (n * m) x)
    obtain ⟨z2, h2⟩ := sec (n * m) (Nat.mul_pos hn hm) hc x
    obtain ⟨z3, h3⟩ := sec n hn hcn x
    obtain ⟨w, hw⟩ := hinj n hn hcn (g' (n * m) x - g' n x) (m • z2 - z1 - z3) (by
      rw [map_sub, smul_sub, smul_sub]
      rw [h2] at h1
      have : g n (g' (n * m) x) = x + (n * m) • z2 - n • z1 := by rw [h1]; abel
      rw [this, h3]
      rw [mul_smul]; abel)
    exact ⟨w, by rw [← hw]; abel⟩
  · intro n hn hc x
    obtain ⟨z1, h1⟩ := sec n hn hc (g n x)
    obtain ⟨w, hw⟩ := hinj n hn hc (g' n (g n x) - x) z1 (by rw [map_sub, h1]; abel)
    exact ⟨w, by rw [← hw]; abel⟩

end GlobalTheory.InvSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleInverseSystemLatticeMapsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_inverseSystem_latticeMaps : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z) → (∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w) → ∃ g' : ℕ → D.La →+ D.La, (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g' (n * m) x = g' n x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z) ∧ (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g' n (g n x) = x + n • z) := by
  first | (exact @GlobalTheory.InvSys.invSys) | (exact GlobalTheory.InvSys.invSys) | (intros; apply GlobalTheory.InvSys.invSys  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGroupAlgebraActionInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGroupAlgebraActionInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo

theorem baseChangeAlgebraRepresentationAction_injective {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hrep : Function.Injective rep) (R : Type) [CommRing R] [Algebra ℚ R] :
    Function.Injective (actOn rep R) := by
  classical
  set b := Module.finBasis ℚ V
  let g : C →ₗ[ℚ] (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℚ) :=
    LinearMap.pi (fun ij => (b.coord ij.2).comp ((LinearMap.applyₗ (b ij.1)).comp rep.toLinearMap))
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hrep
    rw [map_zero]
    refine b.ext (fun i => b.ext_elem (fun j => ?_))
    have := congrFun hx (i, j)
    simpa [g] using this
  have hlg : Function.Injective (LinearMap.lTensor R g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g hg
  have key : ∀ (y : R ⊗[ℚ] C) (i j : Fin (Module.finrank ℚ V)),
      TensorProduct.piScalarRight ℚ R R _ (LinearMap.lTensor R g y) (i, j) =
        TensorProduct.rid ℚ R (LinearMap.lTensor R (b.coord j) (actOn rep R y ((1 : R) ⊗ₜ b i))) := by
    intro y i j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have h1 : actOn rep R (r ⊗ₜ x) ((1 : R) ⊗ₜ b i) = r ⊗ₜ (rep x (b i)) := by
        simp only [actOn, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply]
        change r • ((rep x).baseChange R ((1 : R) ⊗ₜ b i)) = _
        rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]
      simp [g, Algebra.smul_def]
    | add y z hy hz => simp only [map_add (f := _), Pi.add_apply, LinearMap.add_apply, hy, hz]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  apply hlg
  rw [map_zero]
  apply (TensorProduct.piScalarRight ℚ R R _).injective
  rw [map_zero]
  funext ij
  rw [key, hy]
  simp

theorem actOn_rep_afP_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G),
    Function.Injective (actOn L.rep (AfP p)) := by
  intro p _ D G L
  haveI := D.finLa
  exact baseChangeAlgebraRepresentationAction_injective L.rep L.rep_inj (AfP p)

end GlobalTheory.LKGeo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGroupAlgebraActionInjectiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGroupAlgebraAction_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G), Function.Injective (GlobalTheory.LKGeo.actOn L.rep (AfP p)) := by
  exact GlobalTheory.LKGeo.actOn_rep_afP_injective
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseAdeleAwayFromPOfUnitCongruences
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseAdeleAwayFromPOfUnitCongruences
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.AfUnit

variable {p : ℕ} [Fact p.Prime]

theorem exists_nat_mem (v : AwayP p) : ∃ l : ℕ, 0 < l ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hmax : v.1.asIdeal.IsMaximal := v.1.isMaximal
  have hmp : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hnle : ¬ v.1.asIdeal ≤ Ideal.span {(p : ℤ)} := fun hle => v.2 (hmax.eq_of_le hmp.ne_top hle)
  obtain ⟨x, hx, hxp⟩ := Set.not_subset.1 hnle
  have hxp' : ¬ (p : ℤ) ∣ x := fun hd => hxp (Ideal.mem_span_singleton.2 hd)
  refine ⟨x.natAbs, Int.natAbs_pos.2 (fun h0 => hxp' (h0 ▸ dvd_zero _)), ?_, ?_⟩
  · exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (fun hd => hxp' (Int.natCast_dvd.2 hd))).symm
  · rcases Int.natAbs_eq x with h1 | h1
    · rw [← h1]; exact hx
    · rw [← neg_eq_iff_eq_neg.2 h1]; exact neg_mem hx

theorem val_natCast (v : AwayP p) (m : ℕ) :
    Valued.v ((m : ℕ) : v.1.adicCompletion ℚ) = v.1.valuation ℚ (algebraMap ℤ ℚ (m : ℤ)) := by
  have e : ((m : ℕ) : v.1.adicCompletion ℚ) = algebraMap ℤ (v.1.adicCompletion ℚ) (m : ℤ) := by simp
  rw [e, IsScalarTower.algebraMap_apply ℤ ℚ (v.1.adicCompletion ℚ)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _

theorem val_eval_eq_one (c : AfP p) (u : ℕ → ℕ)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β)
    (v : AwayP p) : Valued.v (AfP.eval v c) = 1 := by
  obtain ⟨l, hl0, hlp, hlv⟩ := exists_nat_mem v
  obtain ⟨hcop, β, hβ, e⟩ := h l hl0 hlp
  have hlt : Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) < 1 := by
    rw [val_natCast, HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hlv
  have hu : Valued.v ((u l : ℕ) : v.1.adicCompletion ℚ) = 1 := by
    rw [val_natCast]
    refine le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.1 fun hlt' => ?_)
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem] at hlt'
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    exact v.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ a hlt') (Ideal.mul_mem_left _ b hlv)))
  have hsmall : Valued.v (AfP.eval v (l • β)) < 1 := by
    rw [map_nsmul, nsmul_eq_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hβ v)) hlt
  rw [e, map_add (f := _), map_natCast]
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [hu]; exact hsmall), hu]

theorem exists_mul_eq_one : ∀ (p : ℕ) [Fact p.Prime] (c : AfP p) (u : ℕ → ℕ),
    (∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β) →
    ∃ c' : AfP p, c * c' = 1 := by
  intro p _ c u h
  have hv := val_eval_eq_one c u h
  have hint : ∀ v : AwayP p, (AfP.eval v c)⁻¹ ∈ v.1.adicCompletionIntegers ℚ := fun v => by
    show Valued.v (AfP.eval v c)⁻¹ ≤ 1
    rw [map_inv₀, hv v, inv_one]
  let c' : AfP p := ⟨fun v => (AfP.eval v c)⁻¹, Filter.Eventually.of_forall hint⟩
  refine ⟨c', Subtype.ext (funext fun v => ?_)⟩
  have hne : AfP.eval v c ≠ 0 := fun h0 => by simpa [h0] using hv v
  exact mul_inv_cancel₀ hne

end GlobalTheory.AfUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseAdeleAwayFromPOfUnitCongruencesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_adeleAwayFromP_of_unitCongruences : ∀ (p : ℕ) [Fact p.Prime] (c : AfP p) (u : ℕ → ℕ), (∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β) → ∃ c' : AfP p, c * c' = 1 := by
  first | (exact @GlobalTheory.AfUnit.exists_mul_eq_one) | (exact GlobalTheory.AfUnit.exists_mul_eq_one) | (intros; apply GlobalTheory.AfUnit.exists_mul_eq_one  <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AdelicSim

variable {p : ℕ} [Fact p.Prime]

abbrev formAf (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (D.EF.baseChange ℚ).baseChange (AfP p)

theorem lim (p : ℕ) [Fact p.Prime] (a : ℕ → ℤ)
    (ha : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) :
    ∃ α : AfP p, IsIntAf α ∧ ∀ n : ℕ, 0 < n → n.Coprime p →
      ∃ β : AfP p, IsIntAf β ∧ α = (a n : AfP p) + n • β := GlobalTheory.T.exists_integralAdeleLimit_compatibleIntSystem p a ha

theorem zero (p : ℕ) [Fact p.Prime] (α : AfP p)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = n • β) : α = 0 := GlobalTheory.T.finiteAdeleAwayFromP_eq_zero_of_divisible_coprime p α h

theorem unit (p : ℕ) [Fact p.Prime] (c : AfP p) (u : ℕ → ℕ)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β) :
    ∃ c' : AfP p, c * c' = 1 := GlobalTheory.T.exists_inverse_adeleAwayFromP_of_unitCongruences p c u h

theorem modZero (D : Datum p) (z : AfP p ⊗[ℚ] VQ D)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) : z = 0 := GlobalTheory.T.eq_zero_of_divisible_in_lattice p D z h

theorem modLim (D : Datum p) (g : ℕ → D.La →+ D.La)
    (hg : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) :
    ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧
      ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := GlobalTheory.T.exists_adelic_endomorphism_lattice p D g hg

theorem invSys (D : Datum p) (g : ℕ → D.La →+ D.La)
    (hg : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z)
    (hsurj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z)
    (hinj : ∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w) :
    ∃ g' : ℕ → D.La →+ D.La,
      (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g' (n * m) x = g' n x + n • z) ∧
      (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g n (g' n x) = x + n • z) ∧
      (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, g' n (g n x) = x + n • z) := GlobalTheory.T.exists_compatible_inverseSystem_latticeMaps p D g hg hsurj hinj

theorem comm {D : Datum p} {G : HTGroup p} (L : Link D G) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
    (hA : ∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) :
    ∃ y, actOn L.rep (AfP p) y = A := GlobalTheory.T.exists_groupAlgebra_action_of_commute_order p D G L A hA

theorem inj {D : Datum p} {G : HTGroup p} (L : Link D G) : Function.Injective (actOn L.rep (AfP p)) := GlobalTheory.T.adelicGroupAlgebraAction_injective p D G L

theorem nondeg (D : Datum p) (z : AfP p ⊗[ℚ] VQ D) (h : ∀ v, formAf D v z = 0) : z = 0 := GlobalTheory.T.eq_zero_of_pairing_vanishes p D z h

theorem adjAf {D : Datum p} {G : HTGroup p} (L : Link D G) (x : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D) :
    formAf D (actOn L.rep (AfP p) x v) w =
      formAf D v (actOn L.rep (AfP p) (starT G.star (AfP p) x).unop w) := GlobalTheory.T.pairing_adjoint_involution p D G L x v w

theorem formInt (D : Datum p) {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    IsIntAf (formAf D v w) := GlobalTheory.T.lattice_pairing_integral p D _ _ hv hw

theorem isInt_one : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _

theorem isInt_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

def inAfHom (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D :=
  ((TensorProduct.mk ℚ (AfP p) (VQ D) 1).toAddMonoidHom).comp ((TensorProduct.mk ℤ ℚ D.La 1).toAddMonoidHom)

theorem inAf_eq (D : Datum p) (x : D.La) : inAf D x = inAfHom D x := rfl

theorem inAf_add (D : Datum p) (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := by
  simp only [inAf_eq, map_add (f := _)]

theorem inAf_nsmul (D : Datum p) (n : ℕ) (x : D.La) : inAf D (n • x) = n • inAf D x := by
  simp only [inAf_eq, map_nsmul]

theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isInt_one, rfl⟩

theorem smul_mem_laHat (D : Datum p) {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', x, ha', rfl⟩ := hz
    rw [TensorProduct.smul_tmul']
    exact AddSubgroup.subset_closure ⟨a • a', x, isInt_mul ha ha', rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem span_inAf (D : Datum p) : Submodule.span (AfP p) (Set.range (inAf D)) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a m =>
    have : (1 : AfP p) ⊗ₜ[ℚ] m ∈ Submodule.span (AfP p) (Set.range (inAf D)) := by
      induction m using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact add_mem hx hy
      | tmul q x =>
        have e : (1 : AfP p) ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] x : VQ D) = q • inAf D x := by
          rw [inAf, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [e]
        exact Submodule.smul_of_tower_mem _ q (Submodule.subset_span ⟨x, rfl⟩)
    have e : a ⊗ₜ[ℚ] m = a • ((1 : AfP p) ⊗ₜ[ℚ] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e]; exact Submodule.smul_mem _ a this

theorem ext_inAf (D : Datum p) {f g : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)}
    (h : ∀ x, f (inAf D x) = g (inAf D x)) : f = g :=
  LinearMap.ext_on (span_inAf D) (by rintro _ ⟨x, rfl⟩; exact h x)

theorem bilinear_ext_adelic_inclusion (D : Datum p) {f g : AfP p ⊗[ℚ] VQ D →ₗ[AfP p] AfP p ⊗[ℚ] VQ D →ₗ[AfP p] AfP p}
    (h : ∀ x y, f (inAf D x) (inAf D y) = g (inAf D x) (inAf D y)) : f = g :=
  LinearMap.ext_on (span_inAf D) (by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.ext_on (span_inAf D) (by rintro _ ⟨y, rfl⟩; exact h x y))

theorem bc_inAf (D : Datum p) (b : D.O) (x : D.La) :
    (actQ D b).baseChange (AfP p) (inAf D x) = inAf D (b • x) := by
  simp only [inAf, actQ, LinearMap.baseChange_tmul]; rfl

theorem bc_mem (D : Datum p) (b : D.O) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    (actQ D b).baseChange (AfP p) v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, b • x, ha, ?_⟩
    simp only [actQ, LinearMap.baseChange_tmul]; rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem form_inAf (D : Datum p) (x y : D.La) : formAf D (inAf D x) (inAf D y) = (D.EF x y : AfP p) := by
  simp [formAf, inAf, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]

theorem congOne_of (D : Datum p) (f : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) (N : ℕ)
    (h : ∀ x, ∃ w ∈ LaHat D, f (inAf D x) = inAf D x + N • w) :
    ∀ v ∈ LaHat D, ∃ w ∈ LaHat D, f v = v + N • w := by
  intro v hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    obtain ⟨w, hw, e⟩ := h x
    have ez : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = a • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    refine ⟨a • w, smul_mem_laHat D ha hw, ?_⟩
    rw [ez, map_smul, e, smul_add, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, e⟩ := hx
    obtain ⟨w', hw', e'⟩ := hy
    exact ⟨w + w', add_mem hw hw', by rw [map_add (f := _), e, e', smul_add]; abel⟩
  | neg x _ hx =>
    obtain ⟨w, hw, e⟩ := hx
    exact ⟨-w, neg_mem hw, by rw [map_neg, e, smul_neg, neg_add]⟩

theorem isInt_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isInt_sub {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a - b) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

theorem isInt_intCast (k : ℤ) : IsIntAf (k : AfP p) := fun v => by rw [map_intCast]; exact intCast_mem _ k

theorem isInt_nsmul {a : AfP p} (ha : IsIntAf a) (n : ℕ) : IsIntAf (n • a) := fun v => by
  rw [map_nsmul]; exact nsmul_mem (ha v) n

theorem exists_mem_KN (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (N : ℕ)
    (hN : 0 < N) (hNp : N.Coprime p) (t : SimSys D N N) :
    ∃ h ∈ L.KN N, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x : D.La, ∃ w ∈ LaHat D,
      L.actG h (inAf D x) = inAf D (t.g n x) + n • w := by
  classical
  obtain ⟨g', htw', hgg', hg'g⟩ := invSys D t.g t.tower t.surj t.inj
  obtain ⟨h₀, h₀L, h₀c⟩ := modLim D t.g t.tower
  obtain ⟨h₁, h₁L, h₁c⟩ := modLim D g' htw'
  have inv_of : ∀ (f₀ f₁ : ℕ → D.La →+ D.La) (k₀ k₁ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)),
      (∀ v ∈ LaHat D, k₀ v ∈ LaHat D) →
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, k₀ (inAf D x) = inAf D (f₀ n x) + n • w) →
      (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, k₁ (inAf D x) = inAf D (f₁ n x) + n • w) →
      (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ z, f₀ n (f₁ n x) = x + n • z) → k₀ * k₁ = 1 := by
    intro f₀ f₁ k₀ k₁ hk₀L hk₀ hk₁ hf
    refine ext_inAf D fun x => ?_
    have := modZero D ((k₀ * k₁) (inAf D x) - inAf D x) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := hk₁ n hn hc x
      obtain ⟨w', hw', e'⟩ := hk₀ n hn hc (f₁ n x)
      obtain ⟨z, hz⟩ := hf n hn hc x
      refine ⟨inAf D z + w' + k₀ w, add_mem (add_mem (inAf_mem D z) hw') (hk₀L w hw), ?_⟩
      rw [Module.End.mul_apply, e, map_add (f := _), e', hz, inAf_add, inAf_nsmul, map_nsmul]
      simp only [smul_add]; abel
    rw [Module.End.one_apply]; exact sub_eq_zero.1 this
  have e01 : h₀ * h₁ = 1 := inv_of t.g g' h₀ h₁ h₀L h₀c h₁c hgg'
  have e10 : h₁ * h₀ = 1 := inv_of g' t.g h₁ h₀ h₁L h₁c h₀c hg'g
  have c0 : ∀ b : D.O, h₀ * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * h₀ := by
    intro b
    refine ext_inAf D fun x => ?_
    have := modZero D ((h₀ * (actQ D b).baseChange (AfP p)) (inAf D x) -
        ((actQ D b).baseChange (AfP p) * h₀) (inAf D x)) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := h₀c n hn hc (b • x)
      obtain ⟨w', hw', e'⟩ := h₀c n hn hc x
      obtain ⟨z, hz⟩ := t.lin n hn hc b x
      refine ⟨inAf D z + w - (actQ D b).baseChange (AfP p) w',
        sub_mem (add_mem (inAf_mem D z) hw) (bc_mem D b hw'), ?_⟩
      rw [Module.End.mul_apply, Module.End.mul_apply, bc_inAf, e, hz, e', map_add (f := _), bc_inAf, map_nsmul, inAf_add,
        inAf_nsmul]
      simp only [smul_add, smul_sub]; abel
    exact sub_eq_zero.1 this
  have c1 : ∀ b : D.O, h₁ * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * h₁ := by
    intro b
    calc h₁ * (actQ D b).baseChange (AfP p) = h₁ * ((actQ D b).baseChange (AfP p) * h₀) * h₁ := by
          rw [_root_.mul_assoc h₁, _root_.mul_assoc ((actQ D b).baseChange (AfP p)), e01, _root_.mul_one]
      _ = h₁ * (h₀ * (actQ D b).baseChange (AfP p)) * h₁ := by rw [c0]
      _ = _ := by rw [← _root_.mul_assoc h₁ h₀, e10, _root_.one_mul]
  obtain ⟨y, hy⟩ := comm L h₀ c0
  obtain ⟨y', hy'⟩ := comm L h₁ c1
  have yy' : y * y' = 1 := inj L (by rw [map_mul, hy, hy', e01, map_one])
  have y'y : y' * y = 1 := inj L (by rw [map_mul, hy, hy', e10, map_one])
  obtain ⟨c, hcI, hc⟩ := lim p (fun n => (t.u n : ℤ)) fun n m hn hm hnm => (t.u_tower n m hn hm hnm).symm.dvd
  obtain ⟨c', hcc'⟩ := unit p c t.u fun n hn hnp => ⟨t.u_cop n hn hnp, by
    obtain ⟨β, hβ, e⟩ := hc n hn hnp
    exact ⟨β, hβ, by rw [e, Int.cast_natCast]⟩⟩
  have key : ∀ x x', formAf D (h₀ (inAf D x)) (h₀ (inAf D x')) = c * formAf D (inAf D x) (inAf D x') := by
    intro x x'
    have := zero p (formAf D (h₀ (inAf D x)) (h₀ (inAf D x')) - c * formAf D (inAf D x) (inAf D x'))
      fun n hn hnp => by
      obtain ⟨w, hw, e⟩ := h₀c n hn hnp x
      obtain ⟨w', hw', e'⟩ := h₀c n hn hnp x'
      obtain ⟨β, hβ, eβ⟩ := hc n hn hnp
      obtain ⟨k, hk⟩ := t.sim n hn hnp x x'
      refine ⟨(k : AfP p) + formAf D (inAf D (t.g n x)) w' + formAf D w (inAf D (t.g n x')) +
        n • formAf D w w' - β * (D.EF x x' : AfP p), ?_, ?_⟩
      · exact isInt_sub (isInt_add (isInt_add (isInt_add (isInt_intCast k)
          (formInt D (inAf_mem D _) hw')) (formInt D hw (inAf_mem D _))) (isInt_nsmul (formInt D hw hw') n))
          (isInt_mul hβ (isInt_intCast _))
      · have hk' := congrArg (Int.cast : ℤ → AfP p) hk
        push_cast at hk'
        rw [e, e', eβ]
        simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, form_inAf, nsmul_eq_mul]
        push_cast
        linear_combination hk'
    exact sub_eq_zero.1 this
  have hsim : ∀ v w, formAf D (h₀ v) (h₀ w) = c * formAf D v w := by
    have e2 := bilinear_ext_adelic_inclusion D (f := (formAf D).compl₁₂ h₀ h₀) (g := c • formAf D) fun x x' => by
      simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul]; exact key x x'
    intro v w
    have := LinearMap.congr_fun₂ e2 v w
    simpa using this
  set s := (starT G.star (AfP p) y).unop with hsdef
  have hs : s * y = algebraMap (AfP p) _ c := by
    apply inj L
    refine LinearMap.ext fun w => sub_eq_zero.1 (nondeg D _ fun v => ?_)
    rw [map_sub, map_mul, Module.End.mul_apply, hy, AlgHom.commutes, Module.algebraMap_end_apply, hsdef,
      ← adjAf L y v (h₀ w), hy, hsim, map_smul, smul_eq_mul, sub_self]
  have hys : y * s = algebraMap (AfP p) _ c := by
    calc y * s = y * s * (y * y') := by rw [yy', _root_.mul_one]
      _ = y * (s * y) * y' := by simp only [_root_.mul_assoc]
      _ = y * algebraMap (AfP p) _ c * y' := by rw [hs]
      _ = algebraMap (AfP p) _ c * (y * y') := by rw [(Algebra.commutes c y).symm, _root_.mul_assoc]
      _ = _ := by rw [yy', _root_.mul_one]
  let yU : (AfP p ⊗[ℚ] G.C)ˣ := ⟨y, y', yy', y'y⟩
  let cU : (AfP p)ˣ := ⟨c, c', hcc', by rw [mul_comm]; exact hcc'⟩
  have hmem : (yU, cU) ∈ UPts G.star (AfP p) := mem_uGroup.2 hys
  let h : G.GAf := ⟨(yU, cU), hmem⟩
  have ha0 : L.actG h = h₀ := hy
  have ha1 : L.actG h⁻¹ = h₁ := hy'
  refine ⟨h, ⟨?_, ?_⟩, fun n hn hnp x => ?_⟩
  · intro v hv
    rw [ha0]
    refine congOne_of D h₀ N (fun x => ?_) v hv
    obtain ⟨w, hw, e⟩ := h₀c N hN hNp x
    obtain ⟨z, hz⟩ := t.one x
    exact ⟨inAf D z + w, add_mem (inAf_mem D z) hw, by rw [e, hz, inAf_add, inAf_nsmul, smul_add, add_assoc]⟩
  · intro v hv
    rw [ha1]
    refine congOne_of D h₁ N (fun x => ?_) v hv
    obtain ⟨w, hw, e⟩ := h₁c N hN hNp x
    obtain ⟨z₁, hz₁⟩ := hgg' N hN hNp x
    obtain ⟨z₂, hz₂⟩ := t.one (g' N x)
    have hx : g' N x = x + N • (z₁ - z₂) := by
      rw [hz₂] at hz₁
      rw [smul_sub, ← add_sub_assoc, ← hz₁, add_sub_cancel_right]
    exact ⟨inAf D (z₁ - z₂) + w, add_mem (inAf_mem D _) hw,
      by rw [e, hx, inAf_add, inAf_nsmul, smul_add, add_assoc]⟩
  · rw [ha0]; exact h₀c n hn hnp x

end GlobalTheory.AdelicSim
