module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory

namespace GlobalTheory

namespace PDiv

variable {p : ℕ} [hp : Fact p.Prime] {R A : Type} [CommRing R] [CommRing A]

theorem exists_dualSystem (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ s : Finset (CartierDual R M × M), ∀ a, ∑ i ∈ s, i.1 a • i.2 = a := by
  obtain ⟨u, hu⟩ :=
    (dualTensorHom_bijective_of_finite_projective_right (R := R) (M := M) (N := M)).2 LinearMap.id
  obtain ⟨u, rfl⟩ := (LinearEquiv.rTensor M (CartierDual.toDual R M)).surjective u
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset u
  exact ⟨s, fun a => by simpa [CartierDual.toDual] using LinearMap.congr_fun hu a⟩

variable [Bialgebra R A]

theorem dUnit_pow_prime (h : (p : R) = 0) (a : A) : dUnit (R := R) (a ^ p) = 0 := by
  have key : ∀ k : ℕ, dUnit (R := R) (a ^ (k + 1)) =
      ((k + 1 : ℕ) * counitAlgHom R A a ^ k : R) • dUnit (R := R) a := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, dUnit, AugCot.d_mul, ← dUnit, ← dUnit, ih, smul_smul, ← add_smul, map_pow]
      congr 1
      push_cast
      ring
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
  have := key k
  rwa [← Nat.succ_eq_add_one, ← hk, h, zero_mul, zero_smul] at this

variable [IsCocomm R A]

theorem convPow_prime_apply (h : (p : R) = 0) {B ι : Type} [CommRing B] [Algebra R B] (s : Finset ι)
    (φ : ι → CartierDual R A) (b : ι → B) (f : A →ₗ[R] B) (hf : ∀ a, f a = ∑ i ∈ s, φ i a • b i)
    (a : A) : (toConv f ^ p) a = ∑ i ∈ s, (φ i ^ p) a • b i ^ p := by
  let j : CartierDual R A →* WithConv (A →ₗ[R] B) :=
    { toFun := fun χ => toConv ((Algebra.ofId R B).toLinearMap ∘ₗ χ.ofConv)
      map_one' := rfl
      map_mul' := fun χ ψ => congrArg toConv (LinearMap.algHom_comp_convMul_distrib _ χ ψ) }
  have hj : ∀ (c : B) χ a, (c • j χ).ofConv a = χ a • c := fun c χ a =>
    (mul_comm _ _).trans (Algebra.smul_def _ _).symm
  have e : toConv f = ∑ i ∈ s, b i • j (φ i) := WithConv.ext (LinearMap.ext fun a => by
    rw [ofConv_toConv, hf, ofConv_sum, LinearMap.sum_apply]
    simp only [hj])
  have h0 := natCast_eq_zero_of_algebra h (WithConv (A →ₗ[R] B))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, ← frobRing_apply h0, map_sum, ofConv_sum, LinearMap.sum_apply]
  simp only [frobRing_apply, smul_pow, ← map_pow, hj]

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} [hp : Fact p.Prime] {R S : Type} [CommRing R] [CommRing S]

theorem prime_smul_id_app (G : PDivGroup p R) (n : ℕ) (a : G.A n) :
    Hom.app ((p : ℤ_[p]) • 𝟙 G) n a = mulBy R _ p a := by rw [natCast_smul_id_app]

theorem eq_zero_of_prime_smul_eq_zero {G H : PDivGroup p R} {f : G ⟶ H}
    (e : (p : ℤ_[p]) • f = 0) : f = 0 := by
  have e' : ((p : ℤ_[p]) • 𝟙 G) ≫ f = ((p : ℤ_[p]) • 𝟙 G) ≫ 0 := by
    rw [Linear.smul_comp, Category.id_comp, e, Limits.comp_zero]
  refine Hom.ext (funext fun n => BialgHom.ext fun a => Test.mulP_injective G n ?_)
  obtain ⟨b, rfl⟩ := H.res_surjective n a
  rw [← res_app, ← res_app, mulP_res, mulP_res, ← prime_smul_id_app, ← prime_smul_id_app]
  exact congrArg (fun g => Hom.app g (n + 1) b) e'

variable (h : (p : R) = 0) (G : PDivGroup p R)

theorem verschiebung_app_eq_sum (n : ℕ) {ι : Type} (s : Finset ι) (φ : ι → CartierDual R (G.A n))
    (e : ι → G.A n) (hs : ∀ a, ∑ i ∈ s, φ i a • e i = a) (a : G.A n) :
    (verschiebung h G).app n a = ∑ i ∈ s, (φ i ^ p) a • (frobProj h G).app n (e i) :=
  frobTwist_ext_dual h n fun χ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [frobTwistDual_verschiebung, map_sum]
    refine (convPow_prime_apply h s φ (fun i => χ (e i)) χ.ofConv
      (fun a => by simpa only [map_sum, map_smul] using congrArg χ.ofConv (hs a).symm) a).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul, frobTwistDual_frobProj]

theorem relFrob_app_verschiebung_app (n : ℕ) (a : G.A n) :
    (relFrob h G).app n ((verschiebung h G).app n a) = mulBy R _ p a := by
  obtain ⟨s, hs⟩ := exists_dualSystem R (G.A n)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [verschiebung_app_eq_sum h G n s Prod.fst Prod.snd hs, map_sum]
  simp only [map_smul, relFrob_app_frobProj]
  refine (convPow_prime_apply h s Prod.fst Prod.snd LinearMap.id (fun a => (hs a).symm) a).symm.trans ?_
  exact (congrArg (fun f => f.ofConv a)
    (BialgHom.toLinearMap_convPow (toConv (BialgHom.id R (G.A n))) p)).symm

theorem relFrob_comp_verschiebung : relFrob h G ≫ verschiebung h G = (p : ℤ_[p]) • 𝟙 G :=
  Hom.ext (funext fun n => BialgHom.ext fun a =>
    (relFrob_app_verschiebung_app h G n a).trans (prime_smul_id_app G n a).symm)

theorem frobProj_app_relFrob_app (n : ℕ) (x : (frobTwist h G).A n) :
    (frobProj h G).app n ((relFrob h G).app n x) = x ^ p := by
  rw [← absFrob_app h]
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add (f := _), hx, hy]
  | h1 r a =>
    rw [map_smul, SemiBialgHom.smul_map, SemiBialgHom.smul_map, relFrob_app_frobProj, map_pow,
      absFrob_app]

theorem verschiebung_comp_relFrob :
    verschiebung h G ≫ relFrob h G = (p : ℤ_[p]) • 𝟙 (frobTwist h G) :=
  frobTwist_hom_ext h fun n a => by
    rw [prime_smul_id_app, ← SemiBialgHom.map_mulBy, ← relFrob_app_verschiebung_app h,
      frobProj_app_relFrob_app, ← map_pow, ← relFrob_app_frobProj h]
    rfl

variable {G}

theorem epi_relFrob : Epi (relFrob h G) :=
  Preadditive.epi_of_cancel_zero _ fun g e => eq_zero_of_prime_smul_eq_zero (by
    rw [← Category.id_comp g, ← Linear.smul_comp, ← verschiebung_comp_relFrob, Category.assoc, e,
      Limits.comp_zero])

theorem eq_verschiebung_of_relFrob_comp {v : frobTwist h G ⟶ G}
    (e : relFrob h G ≫ v = (p : ℤ_[p]) • 𝟙 G) : v = verschiebung h G :=
  haveI := epi_relFrob h (G := G)
  (cancel_epi _).1 (e.trans (relFrob_comp_verschiebung h G).symm)

section Naturality

variable (h' : (p : S) = 0) {σ : R →+* S} {G' : PDivGroup p S} (s : SemiHom σ G' G)

theorem SemiHom.app_relFrob (n : ℕ) (x : (PDivGroup.frobTwist h G).A n) :
    s.app n ((relFrob h G).app n x) = (relFrob h' G').app n ((s.frobTwist h h').app n x) := by
  induction x using frobTwist_induction h n with
  | h0 => simp only [map_zero]
  | h2 x y hx hy => simp only [map_add (f := _), hx, hy]
  | h1 r a =>
    rw [map_smul, SemiBialgHom.smul_map, SemiBialgHom.smul_map, map_smul, relFrob_app_frobProj,
      SemiHom.frobTwist_app_frobProj, relFrob_app_frobProj, map_pow]

theorem SemiHom.app_verschiebung (n : ℕ) (a : G.A n) :
    (s.frobTwist h h').app n ((verschiebung h G).app n a) =
      (verschiebung h' G').app n (s.app n a) := by
  refine Test.mulP_injective (PDivGroup.frobTwist h' G') n ?_
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [← PDivGroup.res_app, ← SemiHom.res_app, ← SemiHom.res_app, ← PDivGroup.res_app, mulP_res,
    mulP_res, ← map_mulBy,
    ← SemiBialgHom.map_mulBy (s.app _), ← relFrob_app_verschiebung_app h, s.app_relFrob h h',
    ← prime_smul_id_app, ← verschiebung_comp_relFrob]
  rfl

variable {H : PDivGroup p R}

variable (G) [Algebra R S]

end Naturality

variable (G)

theorem dualHom_verschiebung :
    dualHom _ _ (verschiebung h G) ≫ (frobTwistDual h G).hom = relFrob h G.dual :=
  frobTwist_hom_ext h fun n χ => (CartierDual.ext_apply fun a =>
    frobTwistDual_verschiebung h n χ a).trans (relFrob_app_frobProj h (G := G.dual) n χ).symm

theorem dualHom_relFrob :
    (frobTwistDual h G).hom ≫ verschiebung h G.dual = dualHom _ _ (relFrob h G) := by
  rw [← Iso.eq_inv_comp]
  refine (eq_verschiebung_of_relFrob_comp h ?_).symm
  rw [← dualHom_verschiebung, Category.assoc, Iso.hom_inv_id_assoc, ← dualHom_comp,
    relFrob_comp_verschiebung, map_smul, dualHom_id]

theorem omegaMap_relFrob : omegaMap _ _ (relFrob h G) = 0 :=
  LinearMap.ext fun w => Subtype.ext (funext fun n => by
    obtain ⟨x, hx⟩ := AugCot.d_surjective _ (w.1 n)
    rw [omegaMap_val, ← hx, cotMap_d]
    change dUnit (R := R) _ = 0
    clear hx
    induction x using frobTwist_induction h n with
    | h0 => simp only [map_zero]
    | h2 x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    | h1 r a => rw [map_smul, relFrob_app_frobProj, dUnit, map_smul, ← dUnit, dUnit_pow_prime h, smul_zero])

theorem rigExtMap_relFrob_comp_rigOfOmega :
    rigExtMap (relFrob h G) ∘ₗ (frobTwist h G).rigOfOmega = 0 :=
  LinearMap.ext fun w => by
    rw [LinearMap.comp_apply, rigExtMap_rigOfOmega, omegaMap_relFrob, LinearMap.zero_apply, map_zero,
      LinearMap.zero_apply]

theorem verschiebung_app_eq_zero (n : ℕ) {b : G.A n} (hb : cobOne R _ b = 0) :
    (verschiebung h G).app n b = 0 :=
  frobTwist_ext_dual h n fun χ => by
    rw [frobTwistDual_verschiebung, map_zero, ← primTangent_d ⟨b, hb⟩, dUnit_pow_prime h, map_zero]

theorem vecExtMap_verschiebung : vecExtMap (verschiebung h G) = 0 :=
  LinearMap.ext fun x => ((frobTwist h G).extChar_bijective h).1 (Subtype.ext (by
    rw [extChar_vecExtMap h, verschiebung_app_eq_zero h G 1 (G.extChar h x).2, LinearMap.zero_apply,
      map_zero]
    rfl))

theorem range_rigExtMap_verschiebung_le :
    LinearMap.range (rigExtMap (verschiebung h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  rintro _ ⟨x, rfl⟩
  refine ((frobTwist h G).exact_rigOfOmega_rigToExt _).1 ?_
  rw [rigToExt_rigExtMap, vecExtMap_verschiebung, LinearMap.zero_apply]

theorem rigExtMap_relFrob_rig (x : G.RigExt) :
    rigExtMap (relFrob h G) ((frobProj h G).rig x) = (absFrob h G).rig x := by
  rw [← SemiHom.ofHom_rig]
  exact (frobProj h G).rig_rig _ _
    (fun n a => (absFrob_app h G n a).trans (relFrob_app_frobProj h n a).symm) x

section Perfect

variable {k : Type} [Field k] [CharP k p]

end Perfect

end PDivGroup

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockPolGK

theorem X_mul_pderiv_mem {σ : Type} (d : ℕ) (i j : σ) (P : MvPolynomial σ ℂ)
    (hP : P ∈ restrictTotalDegree σ ℂ d) :
    X i * pderiv j P ∈ restrictTotalDegree σ ℂ d := by
  classical
  rw [mem_restrictTotalDegree] at hP
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hd : (α.sum fun _ e => e) ≤ d := (le_totalDegree hα).trans hP
  rw [pderiv_monomial]
  by_cases h : α j = 0
  · simp [h]
  · rw [mem_restrictTotalDegree, X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)
    have hα : α = Finsupp.single j 1 + (α - Finsupp.single j 1) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp; omega
      · simp [hk]
    conv_rhs => rw [hα]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
    rfl

theorem omE_mem {p q r s : ℕ} (d : ℕ) (l l' : Ln p q r s) (h : linePos l = linePos l')
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omE l l' P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  unfold omE
  rw [LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · cases hl : linePos l
    · have hl' : linePos l' = false := h ▸ hl
      simp only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false]
      change -(pderiv l ((X l' : Pol p q r s) * P)) ∈ _
      refine Submodule.neg_mem _ ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Submodule.add_mem _ (X_mul_pderiv_mem d _ _ P hP) ?_
      by_cases e : l' = l
      · subst e; rw [pderiv_X_self, mul_one]; exact hP
      · rw [pderiv_X_of_ne e, mul_zero]; exact Submodule.zero_mem _
    · have hl' : linePos l' = true := h ▸ hl
      simp only [raiB, lowB, hl, hl', if_true]
      exact X_mul_pderiv_mem d _ _ P hP
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

theorem omAct_mem {p q r s : ℕ} (d : ℕ) (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (hZ : ∀ l l', linePos l ≠ linePos l' → Z l l' = 0)
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omAct p q r s Z P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  rw [LinearMap.smul_apply]
  by_cases h : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (omE_mem d l l' h P hP)
  · rw [hZ l l' h, zero_smul]; exact Submodule.zero_mem _

theorem kStable1 (p q r s d : ℕ) :
    KStable (fockAct1 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change Z a b * (1 : Mat r s) c e = 0
  by_cases hc : c = e
  · subst hc
    rw [hZ a b, zero_mul]
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, mul_zero]

theorem kStable2 (p q r s d : ℕ) :
    KStable (fockAct2 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change (1 : Mat p q) a b * Z c e = 0
  by_cases hc : a = b
  · subst hc
    rw [hZ c e, mul_zero]
    rcases a with a | a <;> rcases c with c | c <;> rcases e with e | e <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, zero_mul]

def signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) : ℚ := if linePos (a, c) then 1 else -1

theorem cast_signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) :
    ((signQ a c : ℚ) : ℂ) = lineSign a c := by
  rcases a with a | a <;> rcases c with c | c <;> simp [signQ, linePos, lineSign]

theorem mem_of_monomials {σ : Type} (N : Submodule ℂ (MvPolynomial σ ℂ))
    (h : ∀ α, monomial α (1 : ℂ) ∈ N) (P : MvPolynomial σ ℂ) : P ∈ N := by
  rw [P.as_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  have := N.smul_mem (AddMonoidAlgebra.coeff P α) (h α)
  rwa [smul_monomial, smul_eq_mul, mul_one] at this

theorem monomial_mem_weightSpace_fockAction_first {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct1 p q r s)
      (fun a => ∑ c, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan1, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

theorem monomial_mem_weightSpace_fockAction_second {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct2 p q r s)
      (fun c => ∑ a, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan2, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

theorem pol_locFin_weights : ∀ (p q r s : ℕ), (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct1 p q r s) W) ∧ P ∈ ⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ) ∧ (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct2 p q r s) W) ∧ P ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ) := by
  intro p q r s
  refine ⟨fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable1 _ _ _ _ _⟩, ?_⟩,
    fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable2 _ _ _ _ _⟩, ?_⟩⟩
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_first α)) P
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_second α)) P

end GlobalTheory.FockPolGK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeightsStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights : ∀ (p q r s : ℕ), (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct1 p q r s) W) ∧ P ∈ ⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ) ∧ (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct2 p q r s) W) ∧ P ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ) := by
  first | exact @GlobalTheory.FockPolGK.pol_locFin_weights | exact GlobalTheory.FockPolGK.pol_locFin_weights | (intros; apply GlobalTheory.FockPolGK.pol_locFin_weights <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.BadCount.Inh

variable {A : Type} [CommRing A] {n : ℕ}

theorem isUniUp_one : IsUniUp (1 : Matrix (Fin n) (Fin n) A) := by
  intro a b
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => ?_⟩
  subst h; exact Matrix.one_apply_eq a

theorem diag_mul_of_tri {M N : Matrix (Fin n) (Fin n) A} (hM : ∀ a c : Fin n, c < a → M a c = 0)
    (hN : ∀ a c : Fin n, c < a → N a c = 0) (a : Fin n) : (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hM a c h, zero_mul]
    · rw [hN c a h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem isUniUp_mul {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) : IsUniUp (M * N) := by
  intro a b
  constructor
  · intro hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [(hM a c).1 h, zero_mul]
    · rw [(hN c b).1 (lt_of_lt_of_le hba h), mul_zero]
  · rintro rfl
    rw [diag_mul_of_tri (fun a c h => (hM a c).1 h) (fun a c h => (hN a c).1 h), (hM a a).2 rfl, (hN a a).2 rfl, one_mul]

theorem isUniUp_inv (u : GL (Fin n) A) (hu : IsUniUp (u : Matrix (Fin n) (Fin n) A)) :
    IsUniUp ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  have hb : Matrix.BlockTriangular (u : Matrix (Fin n) (Fin n) A) id := fun i j h => (hu i j).1 h
  have hinv : Matrix.BlockTriangular ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) id := by
    rw [Matrix.coe_units_inv]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  intro a b
  refine ⟨fun h => hinv h, ?_⟩
  rintro rfl
  have h1 : (((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * (u : Matrix (Fin n) (Fin n) A)) a a = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [diag_mul_of_tri (fun a c h => hinv h) (fun a c h => hb h), (hu a a).2 rfl, mul_one] at h1
  exact h1

def uniUpGL : Subgroup (GL (Fin n) A) where
  carrier := {u | IsUniUp (u : Matrix (Fin n) (Fin n) A)}
  mul_mem' := fun {a b} ha hb => by
    rw [Set.mem_setOf_eq, Units.val_mul]; exact isUniUp_mul ha hb
  one_mem' := by rw [Set.mem_setOf_eq, Units.val_one]; exact isUniUp_one
  inv_mem' := fun {u} hu => isUniUp_inv u hu

theorem mem_uniUpGL (u : GL (Fin n) A) : u ∈ (uniUpGL : Subgroup (GL (Fin n) A)) ↔ IsUniUp (u : Matrix (Fin n) (Fin n) A) :=
  Iff.rfl

def sd (M : Matrix (Fin n) (Fin n) A) : A := ∑ i ∈ Finset.range (n - 1), entN M i (i + 1)

theorem entN_mul_super {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) {i : ℕ} (hi : i + 1 < n) :
    entN (M * N) i (i + 1) = entN M i (i + 1) + entN N i (i + 1) := by
  have h0 : i < n := by omega
  simp only [entN, dif_pos (And.intro h0 hi)]
  rw [Matrix.mul_apply, Fintype.sum_eq_add (⟨i, h0⟩ : Fin n) ⟨i + 1, hi⟩]
  · rw [(hM _ _).2 rfl, (hN _ _).2 rfl, one_mul, mul_one, add_comm]
  · simp [Fin.ext_iff]
  · rintro c ⟨h1, h2⟩
    have h1' : c.val ≠ i := fun h => h1 (Fin.ext h)
    have h2' : c.val ≠ i + 1 := fun h => h2 (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne h1' with h | h
    · rw [(hM ⟨i, h0⟩ c).1 (by change c.val < i; omega), zero_mul]
    · rw [(hN c ⟨i + 1, hi⟩).1 (by change i + 1 < c.val; omega), mul_zero]

theorem sd_mul {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) : sd (M * N) = sd M + sd N := by
  unfold sd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => entN_mul_super hM hN ?_
  have := Finset.mem_range.1 hi; omega

theorem sd_one : sd (1 : Matrix (Fin n) (Fin n) A) = 0 := by
  unfold sd
  refine Finset.sum_eq_zero fun i _ => ?_
  unfold entN
  split_ifs with h
  · exact Matrix.one_apply_ne (fun e => by simpa using congrArg Fin.val e)
  · rfl

variable (D : D7)

def whitP : Subgroup (G0g D.nd) := Subgroup.pi Set.univ fun _ => uniUpGL

theorem mem_whitP (g : G0g D.nd) :
    g ∈ whitP D ↔ ∀ kv, IsUniUp (g kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  rw [whitP, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_uniUpGL]

def whitChar (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) : whitP D →* ℂ where
  toFun g := ∏ kv, ψ kv (sd ((g : G0g D.nd) kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))
  map_one' := by
    refine Finset.prod_eq_one fun kv _ => ?_
    simp [sd_one]
  map_mul' g h := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [← AddChar.map_add_eq_mul, ← sd_mul ((mem_whitP D _).1 g.2 kv) ((mem_whitP D _).1 h.2 kv)]
    rfl

def halfH (k : Fin 2) : Subgroup (G0g D.nd) := Subgroup.pi {kv | kv.1 ≠ k} fun _ => uniUpGL

theorem isHalf_halfH (k : Fin 2) : IsHalf D k (halfH D k) := by
  intro g
  rw [halfH, Subgroup.mem_pi]
  simp only [Set.mem_setOf_eq, mem_uniUpGL]

theorem isWhit_whitP (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (hψ : ∀ kv, ψ kv ≠ 1) :
    IsWhit D (whitP D) (whitChar D ψ).toHomUnits ψ :=
  ⟨hψ, mem_whitP D, fun _ => rfl⟩

theorem exists_whit_half : ∀ (D : D7) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ),
    (∀ kv, ψ kv ≠ 1) → (∃ (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ), IsWhit D P lam ψ) ∧ ∀ k, ∃ H, IsHalf D k H :=
  fun D ψ hψ => ⟨⟨whitP D, _, isWhit_whitP D ψ hψ⟩, fun k => ⟨halfH D k, isHalf_halfH D k⟩⟩

end GlobalTheory.BadCount.Inh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembers
noncomputable section
namespace GlobalTheory.FockEmbExp
open Formalism.BasicNotions.TH Matrix
open scoped Kronecker

section general
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem exp_kron_left (Y : Matrix m m ℂ) :
    NormedSpace.exp (Y ⊗ₖ (1 : Matrix n n ℂ)) = NormedSpace.exp Y ⊗ₖ (1 : Matrix n n ℂ) := by
  let f : Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun Y := Y ⊗ₖ (1 : Matrix n n ℂ)
      map_one' := Matrix.one_kronecker_one
      map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      map_zero' := Matrix.zero_kronecker _
      map_add' A B := Matrix.add_kronecker _ _ _ }
  have hf : Continuous f := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    show Continuous fun Y : Matrix m m ℂ => Y a.1 b.1 * (1 : Matrix n n ℂ) a.2 b.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

theorem exp_kron_right (Z : Matrix n n ℂ) :
    NormedSpace.exp ((1 : Matrix m m ℂ) ⊗ₖ Z) = (1 : Matrix m m ℂ) ⊗ₖ NormedSpace.exp Z := by
  let f : Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun Z := (1 : Matrix m m ℂ) ⊗ₖ Z
      map_one' := Matrix.one_kronecker_one
      map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      map_zero' := Matrix.kronecker_zero _
      map_add' A B := Matrix.kronecker_add _ _ _ }
  have hf : Continuous f := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    show Continuous fun Y : Matrix n n ℂ => (1 : Matrix m m ℂ) a.1 b.1 * Y a.2 b.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Z).symm

theorem exp_reindex' (e : m ≃ n) (X : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e X) = Matrix.reindex e e (NormedSpace.exp X) := by
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X).symm

end general

variable {p q r s : ℕ}

theorem smul_mem {X : Mat p q} (hX : X ∈ upq p q) (t : ℝ) : t • X ∈ upq p q := by
  have h : Xᴴ * Jm p q + Jm p q * X = 0 := hX
  show (t • X)ᴴ * Jm p q + Jm p q * (t • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h,
    smul_zero]

theorem continuous_expt (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) :
    Continuous fun t : ℝ => T.expt (t • X) :=
  T.expt_cont.comp_continuous (by fun_prop) fun t => smul_mem hX t

theorem lift_unique (T : GrpData p q) {γ δ : ℝ → T.G} (hγ : Continuous γ) (hδ : Continuous δ)
    (hc : ∀ t, T.cov (γ t) = T.cov (δ t)) (h0 : γ 0 = δ 0) (t : ℝ) : γ t = δ t := by
  have hsq : Continuous T.sq := continuous_snd.comp T.emb.continuous
  have h := isPreconnected_univ.eq_of_sq_eq (α := ℝ)
    (f := fun t : ℝ => ((T.sq (γ t) : ℂˣ) : ℂ)) (g := fun t : ℝ => ((T.sq (δ t) : ℂˣ) : ℂ))
    (Units.continuous_val.comp (hsq.comp hγ)).continuousOn
    (Units.continuous_val.comp (hsq.comp hδ)).continuousOn (fun t _ => by
      simp only [Pi.pow_apply]
      rw [T.sq_sq, T.sq_sq, hc]) (fun _ => Units.ne_zero _) (Set.mem_univ 0) (by simp only [h0])
  exact T.emb.injective (Prod.ext (hc t) (Units.ext (h (Set.mem_univ t))))

theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal fun a => if a.isLeft then (1 : ℂ) else -1 := by
  ext (a | a) (b | b) <;> simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem Jm_eq (p q r s : ℕ) : Jm (p * r + q * s) (p * s + q * r) =
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Jm p q ⊗ₖ Jm r s) := by
  rw [Jm_diag, Jm_diag, Jm_diag, Matrix.diagonal_kronecker_diagonal, Matrix.reindex_apply,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨l, rfl⟩ := (lineEquiv p q r s).surjective x
  rw [lineEquiv_isLeft, Function.comp, Equiv.symm_apply_apply]
  rcases l with ⟨a | a, c | c⟩ <;> simp [linePos]

theorem left_mem {Y : Mat p q} (hY : Y ∈ upq p q) (r s : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Y ⊗ₖ (1 : Mat r s)) ∈
      upq (p * r + q * s) (p * s + q * r) := by
  have h : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
  show _ᴴ * _ + _ * _ = 0
  rw [Jm_eq, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun A : Mat p q => (A ⊗ₖ Jm r s).submatrix (lineEquiv p q r s).symm (lineEquiv p q r s).symm) h
  simpa [Matrix.add_kronecker, Matrix.submatrix_add] using this

theorem right_mem {Y : Mat r s} (hY : Y ∈ upq r s) (p q : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) ((1 : Mat p q) ⊗ₖ Y) ∈
      upq (p * r + q * s) (p * s + q * r) := by
  have h : Yᴴ * Jm r s + Jm r s * Y = 0 := hY
  show _ᴴ * _ + _ * _ = 0
  rw [Jm_eq, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun A : Mat r s => (Jm p q ⊗ₖ A).submatrix (lineEquiv p q r s).symm (lineEquiv p q r s).symm) h
  simpa [Matrix.kronecker_add, Matrix.submatrix_add] using this

variable {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}

theorem continuous_emb (F : FockData T0 T1 T2) : Continuous F.emb := by
  have h1 : Continuous T1.cov := continuous_fst.comp T1.emb.continuous
  have h2 : Continuous T2.cov := continuous_fst.comp T2.emb.continuous
  have s1 : Continuous T1.sq := continuous_snd.comp T1.emb.continuous
  have s2 : Continuous T2.sq := continuous_snd.comp T2.emb.continuous
  have hv : Continuous fun x : T1.G × T2.G =>
      ((T0.cov (F.emb x) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) := by
    have c1 := (Units.continuous_val.comp h1).comp (continuous_fst (X := T1.G) (Y := T2.G))
    have c2 := (Units.continuous_val.comp h2).comp (continuous_snd (X := T1.G) (Y := T2.G))
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have := (c1.matrix_elem ((lineEquiv p q r s).symm a).1 ((lineEquiv p q r s).symm b).1).mul
      (c2.matrix_elem ((lineEquiv p q r s).symm a).2 ((lineEquiv p q r s).symm b).2)
    refine this.congr fun x => ?_
    rw [show x = (x.1, x.2) from rfl, F.emb_cov]
    rfl
  rw [T0.emb.isInducing.continuous_iff]
  refine Continuous.prodMk (Units.continuous_iff.2 ⟨hv, ?_⟩) ?_
  · refine (hv.comp continuous_inv).congr fun x => ?_
    simp only [Function.comp, map_inv]
  · refine (((s1.comp continuous_fst).pow (r + s)).mul ((s2.comp continuous_snd).pow (p + q))).congr
      fun x => ?_
    exact (F.emb_sq x.1 x.2).symm

theorem emb_expt_left (F : FockData T0 T1 T2) {Y : Mat p q} (hY : Y ∈ upq p q) (t : ℝ) :
    F.emb (T1.expt (t • Y), 1) = T0.expt (t • Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Y ⊗ₖ (1 : Mat r s))) := by
  refine lift_unique T0 (γ := fun t : ℝ => F.emb (T1.expt (t • Y), 1))
    ((continuous_emb F).comp ((continuous_expt T1 hY).prodMk continuous_const))
    (continuous_expt T0 (left_mem hY r s)) (fun t => Units.ext ?_) ?_ t
  · rw [F.emb_cov, T0.expt_cov _ (smul_mem (left_mem hY r s) t), T1.expt_cov _ (smul_mem hY t),
      map_one, Units.val_one, ← exp_kron_left, ← exp_reindex']
    congr 1
    ext a b
    simp
    ring
  · simp only [zero_smul, T1.expt_zero, T0.expt_zero]
    exact map_one F.emb

theorem emb_expt_right (F : FockData T0 T1 T2) {Y : Mat r s} (hY : Y ∈ upq r s) (t : ℝ) :
    F.emb (1, T2.expt (t • Y)) = T0.expt (t • Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      ((1 : Mat p q) ⊗ₖ Y)) := by
  refine lift_unique T0 (γ := fun t : ℝ => F.emb (1, T2.expt (t • Y)))
    ((continuous_emb F).comp (continuous_const.prodMk (continuous_expt T2 hY)))
    (continuous_expt T0 (right_mem hY p q)) (fun t => Units.ext ?_) ?_ t
  · rw [F.emb_cov, T0.expt_cov _ (smul_mem (right_mem hY p q) t), T2.expt_cov _ (smul_mem hY t),
      map_one, Units.val_one, ← exp_kron_right, ← exp_reindex']
    congr 1
    ext a b
    simp
    ring
  · simp only [zero_smul, T2.expt_zero, T0.expt_zero]
    exact map_one F.emb

theorem fock_derived : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), Continuous F.emb ∧ (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P)) (F.ι (fockAct1 p q r s Y P)) 0) ∧ (∀ Y ∈ upq r s, ∀ P, HasDerivAt (fun t : ℝ => F.π (1, T2.expt (t • Y)) (F.ι P)) (F.ι (fockAct2 p q r s Y P)) 0) := by
  intro p q r s T0 T1 T2 F
  refine ⟨continuous_emb F, fun Y hY P => ?_, fun Y hY P => ?_⟩
  · have h := F.der _ (left_mem hY r s) P
    rw [← Matrix.reindex_symm, Equiv.symm_apply_apply] at h
    simp only [FockData.π, MonoidHom.comp_apply, emb_expt_left F hY]
    exact h
  · have h := F.der _ (right_mem hY p q) P
    rw [← Matrix.reindex_symm, Equiv.symm_apply_apply] at h
    simp only [FockData.π, MonoidHom.comp_apply, emb_expt_right F hY]
    exact h

end GlobalTheory.FockEmbExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembersStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_derived_actions_tensor_members : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), Continuous F.emb ∧ (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P)) (F.ι (fockAct1 p q r s Y P)) 0) ∧ (∀ Y ∈ upq r s, ∀ P, HasDerivAt (fun t : ℝ => F.π (1, T2.expt (t • Y)) (F.ι P)) (F.ι (fockAct2 p q r s Y P)) 0) := by
  first | exact @GlobalTheory.FockEmbExp.fock_derived | exact GlobalTheory.FockEmbExp.fock_derived | (intros; apply GlobalTheory.FockEmbExp.fock_derived <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheaf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSurjectiveSectionOfSH
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSurjectiveSectionOfSH
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_surjective_section_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f →
      ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  intro A _ hA Y f hf hs
  obtain ⟨hH, hsep⟩ := hA
  haveI := hH
  obtain ⟨y, hy⟩ := f.surjective (IsLocalRing.closedPoint A)
  let 𝒰 := Y.affineOpenCover
  let i := 𝒰.idx y
  obtain ⟨z, hz⟩ := 𝒰.covers y
  let g : Spec (𝒰.X i) ⟶ Spec (CommRingCat.of A) := 𝒰.f i ≫ f
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  haveI : Etale g := inferInstance
  let φ : CommRingCat.of A ⟶ 𝒰.X i := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hEt : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  letI : Algebra A (𝒰.X i) := φ.hom.toAlgebra
  haveI : Algebra.Etale A (𝒰.X i) := hEt
  have hq : z.asIdeal.comap (algebraMap A (𝒰.X i)) = IsLocalRing.maximalIdeal A := by
    have h1 : (Spec.map φ).base z = IsLocalRing.closedPoint A := by
      rw [hφ]; show f.base ((𝒰.f i).base z) = _; rw [hz, hy]
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    exact h2
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff A).2 ⟨hH, hsep⟩ (𝒰.X i) z.asIdeal hq
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ 𝒰.f i, ?_⟩
  rw [Category.assoc]
  change Spec.map (CommRingCat.ofHom s.toRingHom) ≫ g = _
  rw [← hφ, ← Spec.map_comp]
  have : φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _ := by
    ext a
    exact s.commutes a
  exact (congrArg Spec.map this).trans (Spec.map_id _)

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSurjectiveSectionOfSHStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_etale_surjective_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  first | exact @GlobalTheory.EtC.etale_surjective_section_of_SH | exact GlobalTheory.EtC.etale_surjective_section_of_SH | (intros; apply GlobalTheory.EtC.etale_surjective_section_of_SH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheaf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem heightFunctionalStatement_of_pairingProperties (hA5 : A5)
    (hsect : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
      Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _) : B2 := by
  intro R _ A _ hA F n hn
  have key : ∀ x : H R (sp A) F n, x = 0 := by
    intro x
    obtain ⟨Y, f, hf, hs, hx⟩ := hA5 R (Spec (CommRingCat.of A)) F n hn x
    obtain ⟨s, hsf⟩ := hsect A hA Y f hf hs
    calc x = pull R (𝟙 (sp A)) F n x := (pull_id R _ F n x).symm
      _ = pull R (sch.map (s ≫ f)) F n x := by rw [hsf, CategoryTheory.Functor.map_id]
      _ = pull R (sch.map s) F n (pull R (sch.map f) F n x) := by
          rw [CategoryTheory.Functor.map_comp, pull_comp]
      _ = 0 := by rw [hx, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem b2 : B2 := heightFunctionalStatement_of_pairingProperties GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.exists_section_of_etale_surjective_of_SH

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf : GlobalTheory.EtC.B2 := by
  first | (exact @GlobalTheory.EtC.b2) | (exact GlobalTheory.EtC.b2) | (intros; apply GlobalTheory.EtC.b2  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]

def ObjMap.comp {R : Type} [CommRing R] {D : Datum p} {b : Base D R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}}
    {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) :
    ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
    by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB m₁.φ₂) (pull_isLB o₃.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o₂.P m₁.φ₂ m₁.φ₂ rfl)
      (chartPullSame o₃.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
      m₂.pol)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

end GlobalTheory.UPel.HT

namespace GlobalTheory.RelTan

end GlobalTheory.RelTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamily
open Module

namespace GlobalTheory.BadCount

theorem finrank_iInf_ker_baseChange : ∀ (K L V W ι : Type) [Field K] [Field L] [Algebra K L]
    [Finite ι] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f →
    ∀ (a : ι → V →ₗ[K] V) (a' : ι → W →ₗ[L] W), (∀ i v, a' i (f v) = f (a i v)) →
      finrank L (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          finrank K (⨅ i, LinearMap.ker (a i) : Submodule K V) ∧
        (⨅ i, LinearMap.ker (a' i) : Submodule L W) =
          Submodule.span L (f '' ((⨅ i, LinearMap.ker (a i) : Submodule K V) : Set V)) := by
  intro K L V W ι _ _ _ _ _ _ _ _ _ _ _ f hf a a' ha
  refine ⟨GlobalTheory.finrank_iInf_ker_of_isBaseChange K L V W ι f a a' hf ha, ?_⟩
  rw [GlobalTheory.GaloisDescent.span_image_iInf hf]
  exact iInf_congr fun i =>
    (GlobalTheory.GaloisDescent.span_image_ker hf hf (a i) (a' i) (fun v => ha i v)).symm

end GlobalTheory.BadCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerEqOfIsBaseChangeFamilyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_iInf_ker_eq_of_isBaseChange_family : ∀ (K L V W ι : Type) [Field K] [Field L] [Algebra K L] [Finite ι] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (a : ι → V →ₗ[K] V) (a' : ι → W →ₗ[L] W), (∀ i v, a' i (f v) = f (a i v)) → finrank L (⨅ i, LinearMap.ker (a' i) : Submodule L W) = finrank K (⨅ i, LinearMap.ker (a i) : Submodule K V) ∧ (⨅ i, LinearMap.ker (a' i) : Submodule L W) = Submodule.span L (f '' ((⨅ i, LinearMap.ker (a i) : Submodule K V) : Set V)) := by
  first | exact @GlobalTheory.BadCount.finrank_iInf_ker_baseChange | exact GlobalTheory.BadCount.finrank_iInf_ker_baseChange | (intros; apply GlobalTheory.BadCount.finrank_iInf_ker_baseChange <;> assumption)
end
end
