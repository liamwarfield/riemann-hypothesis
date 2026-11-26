module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureClosedCompactDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAlgebraicRatFuncFractionRingDedekind
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevIteratedOneParameterSubgroups

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNormMulSeminormSliceRLe
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceWeight

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_inrL_le (κ κ' : Type) [Fintype κ] [Fintype κ'] : ‖(inrL (V := V) κ κ')‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simp [inrL]
  | inr j => simpa [inrL] using norm_le_pi_norm y j

theorem norm_le_norm_elim_left {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (y : κ' → V) :
    ‖x‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inl j)

theorem iteratedFDeriv_sliceR_norm_le {κ κ' : Type} [Fintype κ] [Fintype κ']
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (n : ℕ) (y : κ' → V) :
    ‖iteratedFDeriv ℝ n (sliceR f x) y‖ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
  have hfun : (sliceR f x : (κ' → V) → ℂ) = (fun z => f (Sum.elim x 0 + z)) ∘ (inrL (V := V) κ κ') := by
    funext y'
    simp only [sliceR_apply, Function.comp_apply]
    exact congrArg f (congrFun (elim_eq_add (V := V) (κ' := κ') x) y')
  have hg : ContDiff ℝ ∞ (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) :=
    (f.smooth ⊤).comp (contDiff_const.add contDiff_id)
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg _ (by exact_mod_cast le_top)]
  have h2 : iteratedFDeriv ℝ n (fun z : κ ⊕ κ' → V => f (Sum.elim x 0 + z)) (inrL κ κ' y)
      = iteratedFDeriv ℝ n f (Sum.elim x y) := by
    rw [iteratedFDeriv_comp_add_left]
    congr 1
    exact (congrFun (elim_eq_add (V := V) (κ' := κ') x) y).symm
  rw [h2]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖(inrL (V := V) κ κ')‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_inrL_le κ κ')
  calc _ ≤ ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem pow_norm_mul_seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (a k n : ℕ) (x : κ → V) :
    ‖x‖ ^ a * SchwartzMap.seminorm ℂ k n (sliceR f x) ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
  have hpt : ∀ y : κ' → V, ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
      ≤ SchwartzMap.seminorm ℂ (a + k) n f := by
    intro y
    have h1 := iteratedFDeriv_sliceR_norm_le f x n y
    have hx := norm_le_norm_elim_left x y
    have hy := norm_le_norm_elim x y
    calc ‖x‖ ^ a * (‖y‖ ^ k * ‖iteratedFDeriv ℝ n (sliceR f x) y‖)
        ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ a * (‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ k
            * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖) := by gcongr
      _ = ‖(Sum.elim x y : κ ⊕ κ' → V)‖ ^ (a + k) * ‖iteratedFDeriv ℝ n f (Sum.elim x y)‖ := by
          rw [pow_add, mul_assoc]
      _ ≤ _ := SchwartzMap.le_seminorm ℂ (a + k) n f _
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x) a) with h0 | hpos
  · rw [← h0, zero_mul]; exact apply_nonneg _ _
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ k n _ (div_nonneg (apply_nonneg _ _) hpos.le) fun y => ?_
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt y

end GlobalTheory.SliceWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorBasisCriterion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierInversionSchwartzBruhat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem GlobalTheory.tensorSum_bijective_iff (A B R S : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] [CommRing S] (κ : R ⊗[A] B →+* S) {r : ℕ} (v : Fin r → B) :
    Function.Bijective (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) ↔ (Function.Surjective κ ∧ LinearIndependent R (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) = ⊤) := by
  have hsum : ∀ c : Fin r → R, ∑ k, c k • Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)
      = Ideal.Quotient.mk (RingHom.ker κ) (∑ k, c k ⊗ₜ[A] v k) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : c k • ((1 : R) ⊗ₜ[A] v k) = c k ⊗ₜ[A] v k := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [← h1]
    exact (map_smul (Ideal.Quotient.mkₐ R (RingHom.ker κ)) (c k) ((1 : R) ⊗ₜ[A] v k)).symm
  have hker : ∀ x y : R ⊗[A] B, Ideal.Quotient.mk (RingHom.ker κ) x = Ideal.Quotient.mk (RingHom.ker κ) y ↔ κ x = κ y := by
    intro x y
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
  have hsub : ∀ c c' : Fin r → R, ∑ k, (c - c') k ⊗ₜ[A] v k = ∑ k, c k ⊗ₜ[A] v k - ∑ k, c' k ⊗ₜ[A] v k := by
    intro c c'
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.sub_apply, TensorProduct.sub_tmul]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun s => ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hsurj s
      exact ⟨_, hc⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm,
        hker] at hg
      have h0 : (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) g = (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) 0 := by
        simp only [Pi.zero_apply, TensorProduct.zero_tmul, Finset.sum_const_zero, map_zero]
        simpa using hg
      intro i
      rw [hinj h0]
      rfl
    · rw [eq_top_iff]
      intro x _
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc⟩ := hsurj (κ t)
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, by rw [hsum, hker]; exact hc⟩
  · rintro ⟨hsurj, hli, hspan⟩
    refine ⟨fun c c' h => ?_, fun s => ?_⟩
    · rw [Fintype.linearIndependent_iff] at hli
      have h2 := hli (c - c') (by
        rw [hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm,
          hker, hsub, map_sub, map_zero, sub_eq_zero]
        exact h)
      funext i
      exact sub_eq_zero.mp (h2 i)
    · obtain ⟨t, rfl⟩ := hsurj s
      have hm : Ideal.Quotient.mk (RingHom.ker κ) t ∈ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) := by
        rw [hspan]; trivial
      rw [Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨c, hc⟩ := hm
      rw [hsum, hker] at hc
      exact ⟨c, hc⟩
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_basis_criterion : ∀ (A B R S : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] [CommRing S] (κ : R ⊗[A] B →+* S) {r : ℕ} (v : Fin r → B), Function.Bijective (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) ↔ (Function.Surjective κ ∧ LinearIndependent R (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) = ⊤) := by
  first | (exact @GlobalTheory.tensorSum_bijective_iff) | (exact GlobalTheory.tensorSum_bijective_iff) | (intros; apply GlobalTheory.tensorSum_bijective_iff <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingMapFromAffineOpens
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorPowerSummable
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.AffGlue

end GlobalTheory.AffGlue

namespace GlobalTheory.AffGlue


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
open scoped TensorProduct in
theorem _root_.GlobalTheory.AffGlue.existsUnique_ringHom_of_affineOpens : ∀ (Z : Scheme.{0}) (R : Type) [CommRing R] (φ : ∀ U : Z.affineOpens, R →+* Γ(Z, U)), (∀ (U V : Z.affineOpens) (h : (U : Z.Opens) ≤ V), (Z.presheaf.map (homOfLE h).op).hom.comp (φ V) = φ U) → ∃! Φ : R →+* Γ(Z, ⊤), ∀ U : Z.affineOpens, (Z.presheaf.map (homOfLE (le_top : (U : Z.Opens) ≤ ⊤)).op).hom.comp Φ = φ U := by
  intro Z R _ φ hφ
  have hcomp : ∀ {A B C : Z.Opens} (f : A ⟶ B) (g : B ⟶ C) (s : Γ(Z, C)),
      (Z.presheaf.map f.op).hom ((Z.presheaf.map g.op).hom s) =
        (Z.presheaf.map (f ≫ g).op).hom s := by
    intro A B C f g s
    rw [op_comp, Functor.map_comp]
    rfl
  have hφ' : ∀ (U V : Z.affineOpens) (f : (U : Z.Opens) ⟶ V) (r : R),
      (Z.presheaf.map f.op).hom (φ V r) = φ U r := by
    intro U V f r
    rw [show f = homOfLE (leOfHom f) from Subsingleton.elim _ _]
    exact RingHom.congr_fun (hφ U V (leOfHom f)) r
  have hcov : ∀ V : Z.Opens,
      V ≤ ⨆ W : {W : Z.affineOpens // (W : Z.Opens) ≤ V}, (W.1 : Z.Opens) := by
    intro V x hx
    obtain ⟨W, hW, hxW, hWle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hxW⟩
  have hglue : ∀ r : R, ∃! s : Γ(Z, ⊤), ∀ W : Z.affineOpens,
      (Z.presheaf.map (homOfLE (le_top : (W : Z.Opens) ≤ ⊤)).op).hom s = φ W r := by
    intro r
    have htop : (⊤ : Z.Opens) ≤ ⨆ W : Z.affineOpens, (W : Z.Opens) := by
      intro x hx
      obtain ⟨W, hW, hxW, -⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, hxW⟩
    refine Z.sheaf.existsUnique_gluing' (fun W : Z.affineOpens => (W : Z.Opens)) ⊤
      (fun W => homOfLE le_top) htop (fun W => φ W r) ?_
    intro i j
    refine Z.sheaf.eq_of_locally_eq'
      (fun k : {W : Z.affineOpens // (W : Z.Opens) ≤ (i : Z.Opens) ⊓ j} => (k.1 : Z.Opens))
      _ (fun k => homOfLE k.2) (hcov _) _ _ fun k => ?_
    change (Z.presheaf.map _).hom ((Z.presheaf.map _).hom (φ i r)) =
      (Z.presheaf.map _).hom ((Z.presheaf.map _).hom (φ j r))
    rw [hcomp, hcomp, hφ', hφ']
  choose s hs hu using hglue
  let Φ : R →+* Γ(Z, ⊤) :=
    { toFun := s
      map_one' := (hu 1 1 fun W => by rw [map_one, map_one]).symm
      map_mul' := fun a b => (hu (a * b) (s a * s b) fun W => by
        rw [map_mul, hs a W, hs b W, map_mul]).symm
      map_zero' := (hu 0 0 fun W => by rw [map_zero, map_zero]).symm
      map_add' := fun a b => (hu (a + b) (s a + s b) fun W => by
        rw [map_add (f := _), hs a W, hs b W, map_add (f := _)]).symm }
  refine ⟨Φ, fun W => RingHom.ext fun r => hs r W,
    fun Ψ hΨ => RingHom.ext fun r => hu r (Ψ r) fun W => ?_⟩
  exact RingHom.congr_fun (hΨ W) r

end GlobalTheory.AffGlue
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_map_from_affine_opens : ∀ (Z : Scheme.{0}) (R : Type) [CommRing R] (φ : ∀ U : Z.affineOpens, R →+* Γ(Z, U)), (∀ (U V : Z.affineOpens) (h : (U : Z.Opens) ≤ V), (Z.presheaf.map (homOfLE h).op).hom.comp (φ V) = φ U) → ∃! Φ : R →+* Γ(Z, ⊤), ∀ U : Z.affineOpens, (Z.presheaf.map (homOfLE (le_top : (U : Z.Opens) ≤ ⊤)).op).hom.comp Φ = φ U := by
  first | (exact @GlobalTheory.AffGlue.existsUnique_ringHom_of_affineOpens) | (exact GlobalTheory.AffGlue.existsUnique_ringHom_of_affineOpens) | (intros; apply GlobalTheory.AffGlue.existsUnique_ringHom_of_affineOpens  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtDAlgebraMapPowCharMul
open GlobalTheory GlobalTheory.DI

set_option autoImplicit false

namespace GlobalTheory.DI

section

variable {K : Type} [CommRing K]

theorem kaehlerZ_span_induction {P : Ω[K⁄ℤ] → Prop} (v : Ω[K⁄ℤ]) (hD : ∀ a, P (KaehlerDifferential.D ℤ K a))
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (c : K) x, P x → P (c • x)) : P v := by
  have hv : v ∈ Submodule.span K (Set.range (KaehlerDifferential.D ℤ K)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hD a
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem kaehlerZ_D_pow_char (c : K) : KaehlerDifferential.D ℤ K (c ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

theorem extD_algebraMap_pow_char_mul {d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ]} (hd : IsExtD ℤ K d)
    (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]) :
    d (algebraMap K _ (c ^ p) * x) = algebraMap K _ (c ^ p) * d x := by
  rw [hd.mul, hd.alg, kaehlerZ_D_pow_char p, map_zero, zero_mul, zero_add]
  congr 1
  exact AlgHom.commutes _ _

end

end GlobalTheory.DI

namespace GlobalTheory.DI

theorem isDatum_of_frobenius_lifts {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ])
    (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (hπ : IsFlatLift p π)
    (hF : ∀ i, IsFrob p π (F i)) (hd : IsExtD ℤ K d) (hf : ∀ i, IsF p π (F i) (f i))
    (hh : ∀ i j, IsH p π (F i) (F j) (h i j)) : IsDatum p d f h := by

  have hw : ∀ i z, ∃ w, F i z = z ^ p + p * w := by
    intro i z
    obtain ⟨w, hw⟩ := (hπ.ker (F i z - z ^ p)).1 (by rw [map_sub, hF i, map_pow, sub_self])
    exact ⟨w, by rw [← hw]; ring⟩
  have hsm : ∀ (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]), d (c ^ p • x) = c ^ p • d x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, extD_algebraMap_pow_char_mul p hd]

  have hfD : ∀ i z w, F i z = z ^ p + p * w → ExteriorAlgebra.ι K (f i (KaehlerDifferential.D ℤ K (π z))) =
      algebraMap K _ (π z ^ (p - 1)) * ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K (π z)) +
        d (algebraMap K _ (π w)) := by
    intro i z w hz
    rw [(hf i).2 z w hz, map_add (f := _), map_smul, Algebra.smul_def, hd.alg]
  refine ⟨fun i c v => (hf i).1 c v, fun i j c v => (hh i j).1 c v, ?_, ?_, ?_⟩
  · intro i v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨w, hz⟩ := hw i z
      have h2 : d (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K (π z))) = 0 := by
        rw [← hd.alg, hd.sq]
      rw [hfD i z w hz, map_add (f := _), hd.sq, add_zero, hd.mul, h2, mul_zero, add_zero, hd.alg,
        Derivation.leibniz_pow, map_nsmul, map_smul, smul_mul_assoc, smul_mul_assoc,
        ExteriorAlgebra.ι_sq_zero, smul_zero, smul_zero]
    | h0 => simp
    | hadd x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, add_zero]
    | hsmul c x hx => rw [(hf i).1, map_smul, hsm, hx, smul_zero]
  · intro i j v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨wi, hzi⟩ := hw i z
      obtain ⟨wj, hzj⟩ := hw j z
      rw [(hh i j).2 z (wj - wi) (by rw [hzi, hzj]; ring), hfD i z wi hzi, hfD j z wj hzj, map_sub, map_sub,
        map_sub]
      abel
    | h0 => simp
    | hadd x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]; abel
    | hsmul c x hx =>
      rw [(hh i j).1, (hf i).1, (hf j).1, map_mul, ← Algebra.smul_def, hsm, hx, map_smul, map_smul, smul_sub]
  · intro i j l v
    induction v using kaehlerZ_span_induction with
    | hD a =>
      obtain ⟨z, rfl⟩ := hπ.surj a
      obtain ⟨wi, hzi⟩ := hw i z
      obtain ⟨wj, hzj⟩ := hw j z
      obtain ⟨wl, hzl⟩ := hw l z
      rw [(hh i j).2 z (wj - wi) (by rw [hzi, hzj]; ring), (hh j l).2 z (wl - wj) (by rw [hzj, hzl]; ring),
        (hh i l).2 z (wl - wi) (by rw [hzi, hzl]; ring), map_sub, map_sub, map_sub]
      ring
    | h0 => simp
    | hadd x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), ← hx, ← hy]; ring
    | hsmul c x hx => rw [(hh i j).1, (hh j l).1, (hh i l).1, ← hx]; ring

end GlobalTheory.DI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIndEtaleIsDomainIsIntegrallyClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleIsDomainIsIntegrallyClosed
open IsLocalRing

namespace GlobalTheory

namespace IndEtaleNormal

open Polynomial

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]

lemma exists_mem_of_finset (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (T : Finset S) : ∃ i, ∀ t ∈ T, t ∈ Si i := by
  classical
  choose idx hidx using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (T.image idx)
  exact ⟨M, fun t ht => hmono (hM _ (Finset.mem_image_of_mem idx ht)) (hidx t)⟩

lemma isDomain [Nontrivial S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (hdom : ∀ i, IsDomain (Si i)) : IsDomain S := by
  classical
  have : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov {x, y}
    have hx : x ∈ Si i := hi x (by simp)
    have hy : y ∈ Si i := hi y (by simp)
    haveI := hdom i
    have h0 : (⟨x, hx⟩ : Si i) * ⟨y, hy⟩ = 0 := Subtype.ext (by simpa using hxy)
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  exact NoZeroDivisors.to_isDomain S

lemma isIntegrallyClosed [IsDomain S] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i)
    (hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i)) : IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  obtain ⟨p, hpm, hp⟩ := hx
  obtain ⟨i, hi⟩ := exists_mem_of_finset Si hmono hcov (insert a (insert b p.coeffs))
  haveI := (hic i).1
  haveI := (hic i).2
  have ha : a ∈ Si i := hi a (by simp)
  have hb' : b ∈ Si i := hi b (by simp)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set g : Si i →+* FractionRing S := (algebraMap S (FractionRing S)).comp (algebraMap (Si i) S)
    with hg_def
  have hg : Function.Injective g :=
    (IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective
  let φ : FractionRing (Si i) →+* FractionRing S := IsFractionRing.lift hg
  have hφ : ∀ c : Si i, φ (algebraMap (Si i) (FractionRing (Si i)) c) = g c := fun c =>
    IsFractionRing.lift_algebraMap hg c
  have hlift : p ∈ Polynomial.lifts (algebraMap (Si i) S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : p.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨p.coeff n, hi _ (by simp [Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  set y : FractionRing (Si i) := algebraMap (Si i) (FractionRing (Si i)) ⟨a, ha⟩ /
    algebraMap (Si i) (FractionRing (Si i)) ⟨b, hb'⟩ with hy_def
  have hφy : φ y = algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b := by
    rw [hy_def, map_div₀, hφ, hφ]
    rfl
  have hyint : IsIntegral (Si i) y := by
    refine ⟨q, hqm, φ.injective ?_⟩
    rw [Polynomial.hom_eval₂, map_zero, hφy]
    have : φ.comp (algebraMap (Si i) (FractionRing (Si i))) = g :=
      RingHom.ext hφ
    rw [this, hg_def, ← Polynomial.eval₂_map, hq]
    exact hp
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (Si i))).mp (hic i).2 hyint
  refine ⟨(c : S), ?_⟩
  rw [← hφy, ← hc, hφ]
  rfl

end IndEtaleNormal

theorem indEtale_isDomain_isIntegrallyClosed :
    ∀ (R S : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Algebra R S]
      [Nontrivial S], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
        (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
        ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
          (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) →
      IsDomain S ∧ IsIntegrallyClosed S := by
  intro R S _ _ _ _ _ _ h
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩ := h
  have hic : ∀ i, IsDomain (Si i) ∧ IsIntegrallyClosed (Si i) := by
    intro i
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    obtain ⟨h1, h2⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R A q
    exact ⟨MulEquiv.isDomain (Localization.AtPrime q) e.symm.toMulEquiv,
      IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
  haveI := IndEtaleNormal.isDomain Si hmono hcov (fun i => (hic i).1)
  exact ⟨inferInstance, IndEtaleNormal.isIntegrallyClosed Si hmono hcov hic⟩

end GlobalTheory
end

open IsLocalRing

namespace GlobalTheory

namespace LocIndEtale

open Polynomial

lemma isIntegrallyClosed_of_forall_monic_root (T : Type) [CommRing T] [IsDomain T]
    (h : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  rintro x ⟨p, hpm, hp⟩
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have : p = 1 := hpm.natDegree_eq_zero.mp hn
      subst this
      simp at hp
    · obtain ⟨r, hr⟩ := h p hpm (hn ▸ hpos)
      have hroot : IsRoot p r := hr
      have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
      set q := p /ₘ (X - C r) with hq
      have hqm : q.Monic := by
        refine Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) ?_
        rw [hfac]; exact hpm
      have hqdeg : q.natDegree < n := by
        rw [hq, Polynomial.natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]
        omega
      rw [← hfac, eval₂_mul] at hp
      rcases mul_eq_zero.mp hp with h1 | h1
      · refine ⟨r, ?_⟩
        simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
        exact (sub_eq_zero.mp h1).symm
      · exact ih _ hqdeg q hqm h1 rfl

end LocIndEtale

theorem locIndEtale_isDomain_isIntegrallyClosed :
    ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ∧ IsIntegrallyClosed (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := by
  intro T O _ _ _ _ _ _ _ _ _ n hT _ _ hind
  haveI : IsIntegrallyClosed T := LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hT.2
  obtain ⟨hdom, hic⟩ := indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind

  have hinj : Function.Injective (algebraMap T O) := by
    obtain ⟨ι, _, _, _, Si, -, -, hloc⟩ := hind
    obtain ⟨A, _, _, _, P, _, ⟨e⟩⟩ := hloc (Classical.arbitrary ι)
    haveI : Module.Flat (Polynomial T) (Localization.AtPrime P) := inferInstance
    have hL : Function.Injective (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro f hf
      by_contra hne
      have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
        (M := Localization.AtPrime P) (mem_nonZeroDivisors_of_ne_zero hne)
      have h1 : f • (1 : Localization.AtPrime P) = f • 0 := by
        rw [Algebra.smul_def, hf, zero_mul, smul_zero]
      exact one_ne_zero (hreg h1)
    have hS : Function.Injective (algebraMap (Polynomial T) O) := by
      have : (algebraMap (Polynomial T) O) =
          (Si (Classical.arbitrary ι)).val.toRingHom.comp
            (e.toRingEquiv.toRingHom.comp (algebraMap (Polynomial T) (Localization.AtPrime P))) := by
        ext f
        · simp
        · simp
      rw [this]
      exact Subtype.val_injective.comp (e.injective.comp hL)
    rw [IsScalarTower.algebraMap_eq T (Polynomial T) O]
    exact hS.comp Polynomial.C_injective
  have hle : Algebra.algebraMapSubmonoid O (nonZeroDivisors T) ≤ nonZeroDivisors O := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ht (hinj ?_)
    rw [h, map_zero]
  exact ⟨IsLocalization.isDomain_localization hle,
    isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumIntegralCubeDerivatives
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumIntegralCubeDerivatives
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.CubeTaylor

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open MeasureTheory in
open scoped ContDiff in
private theorem integral_cube_succ_eq_iterated {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (N : ℕ) (s : ℝ) (F : (Fin (N + 1) → ℝ) → K)
    (hF : Continuous F) :
    ∫ t in Set.univ.pi (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), F t =
      ∫ t in Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) := by
  have hsnoc : Continuous fun p : (Fin N → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (N + 1) → ℝ) :=
    Continuous.finSnoc (A := fun _ => ℝ) continuous_fst continuous_snd
  have hF' : Continuous fun p : (Fin N → ℝ) × ℝ => F (Fin.snoc p.1 p.2) := hF.comp hsnoc
  have hG : Continuous fun t : Fin N → ℝ => ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) :=
    continuous_parametric_integral_of_continuous (f := fun t r => F (Fin.snoc t r)) hF'
      isCompact_Icc
  have hcube : IsCompact (Set.univ.pi fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcube' : IsCompact (Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) s) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  set X := ∫ t in Set.univ.pi (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), F t with hX
  set Y := ∫ t in Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) s),
    ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) with hY
  have key : ∀ e : K, (inner ℂ e X).re = (inner ℂ e Y).re := by
    intro e
    let L : K →L[ℝ] ℝ := Complex.reCLM.comp ((innerSL ℂ e).restrictScalars ℝ)
    have hL : ∀ x, L x = (inner ℂ e x).re := fun x => rfl
    rw [← hL, ← hL, hX, hY,
      ← L.integral_comp_comm (hF.continuousOn.integrableOn_compact hcube),
      ← L.integral_comp_comm (hG.continuousOn.integrableOn_compact hcube'),
      (_root_.GlobalTheory.integral_cube_succ_last N s (fun t => L (F t)) (L.continuous.comp hF)).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    exact L.integral_comp_comm
      ((hF.comp (Continuous.finSnoc (A := fun _ => ℝ) continuous_const continuous_id)).continuousOn.integrableOn_compact
        isCompact_Icc)
  have h := key (X - Y)
  have h2 : ‖X - Y‖ ^ 2 = 0 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sub_right, map_sub]
    simp only [RCLike.re_to_complex]
    rw [h, sub_self]
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2))

open MeasureTheory in
open scoped ContDiff in
private theorem eq_interval_average_sub_weighted_deriv
    {G : Type} [Group G] [TopologicalSpace G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (hcont : ∀ v, Continuous fun g => ρ g v)
    {s : ℝ} (hs : 0 < s) (c : ℝ → G) (hc : Continuous c) (hc0 : c 0 = 1)
    (hadd : ∀ a b, c (a + b) = c a * c b) (w w' : K)
    (hd : HasDerivAt (fun t : ℝ => ρ (c t) w) w' 0) :
    w = (∫ r in Set.Icc 0 s, ((1 / s : ℝ) : ℂ) • ρ (c r) w) -
      ∫ r in Set.Icc 0 s, (((s - r) / s : ℝ) : ℂ) • ρ (c r) w' := by
  have hg : ∀ r, HasDerivAt (fun t => ρ (c t) w) (ρ (c r) w') r := by
    intro r
    have h1 : HasDerivAt (fun t => ρ (c (t - r)) w) w' r := by
      have := hd
      rw [← sub_self r] at this
      exact this.comp_sub_const r r
    have h2 := ((ρ (c r)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← hadd, add_sub_cancel]
  have hb : ∀ r : ℝ, HasDerivAt (fun t : ℝ => (((s - t) / s : ℝ) : ℂ)) (((-(1 / s)) : ℝ) : ℂ) r := by
    intro r
    have : HasDerivAt (fun t : ℝ => (s - t) / s) (-(1 / s)) r := by
      simpa [neg_div] using ((hasDerivAt_id r).const_sub s).div_const s
    exact this.ofReal_comp
  have hh : ∀ r ∈ Set.uIcc 0 s, HasDerivAt (fun t => (((s - t) / s : ℝ) : ℂ) • ρ (c t) w)
      ((((s - r) / s : ℝ) : ℂ) • ρ (c r) w' + (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w) r :=
    fun r _ => (hb r).smul (hg r)
  have hgc : Continuous fun t => ρ (c t) w := (hcont w).comp hc
  have hg'c : Continuous fun t => ρ (c t) w' := (hcont w').comp hc
  have hA : Continuous fun r : ℝ => (((s - r) / s : ℝ) : ℂ) • ρ (c r) w' := by
    exact (Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).div_const s)).smul hg'c
  have hB : Continuous fun r : ℝ => (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w :=
    continuous_const.smul hgc
  have hE := intervalIntegral.integral_eq_sub_of_hasDerivAt hh
    ((hA.add hB).intervalIntegrable 0 s)
  rw [intervalIntegral.integral_add (hA.intervalIntegrable 0 s) (hB.intervalIntegrable 0 s),
    intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_of_le hs.le] at hE
  simp only [sub_self, zero_div, Complex.ofReal_zero, zero_smul, sub_zero, div_self hs.ne',
    Complex.ofReal_one, one_smul, hc0, map_one, ContinuousLinearMap.one_apply] at hE
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  have hneg : ∫ r in Set.Ioc 0 s, (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w =
      -∫ r in Set.Ioc 0 s, ((1 / s : ℝ) : ℂ) • ρ (c r) w := by
    rw [← integral_neg]
    congr 1
    funext r
    rw [Complex.ofReal_neg, neg_smul]
  rw [hneg] at hE
  have key : ∀ x A B : K, A + -B = 0 - x → x = B - A := by
    intro x A B h
    calc x = -(0 - x) := by abel
      _ = -(A + -B) := by rw [h]
      _ = B - A := by abel
  exact key _ _ _ hE


open MeasureTheory in
open scoped ContDiff in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem _root_.GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (s : ℝ), 0 < s → ∀ (N : ℕ) (c : Fin N → ℝ → G), (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ (J : Type) (_ : Fintype J) (κ : J → (Fin N → ℝ) → ℂ) (l : J → List (Fin N)), (∀ j, Continuous (κ j)) ∧ ∀ (d : Fin N → K → K) (S : Set K), (∀ v ∈ S, ∀ i, d i v ∈ S ∧ HasDerivAt (fun t : ℝ => ρ (c i t) v) (d i v) 0) → ∀ v ∈ S, v = ∑ j, ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), κ j t • ρ (List.ofFn fun i => c i (t i)).prod ((l j).foldr d v) := by
  intro G _ _ _ K _ _ _ ρ _ hcont s hs N
  induction N with
  | zero =>
    intro c hc
    refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => [], fun _ => continuous_const, ?_⟩
    intro d S hS v hv
    simp [Measure.real, Real.volume_Icc_pi]
  | succ N ih =>
    intro c hc
    obtain ⟨J, hJ, κ, l, hκ, hrep⟩ := ih (fun i => c (Fin.castSucc i)) (fun i => hc _)
    have hinit : Continuous (fun t : Fin (N + 1) → ℝ => Fin.init t) :=
      continuous_pi fun i => continuous_apply (Fin.castSucc i)
    refine ⟨J × Bool, inferInstance,
      fun p t => κ p.1 (Fin.init t) * (if p.2 then ((1 / s : ℝ) : ℂ)
        else -(((s - t (Fin.last N)) / s : ℝ) : ℂ)),
      fun p => if p.2 then (l p.1).map Fin.castSucc else Fin.last N :: (l p.1).map Fin.castSucc,
      ?_, ?_⟩
    · rintro ⟨j, _ | _⟩
      · simp only [Bool.false_eq_true, if_false]
        exact ((hκ j).comp hinit).mul (by fun_prop)
      · simp only [if_true]
        exact ((hκ j).comp hinit).mul continuous_const
    intro d S hS v hv
    have hS' : ∀ v ∈ S, ∀ i : Fin N, d (Fin.castSucc i) v ∈ S ∧
        HasDerivAt (fun t : ℝ => ρ (c (Fin.castSucc i) t) v) (d (Fin.castSucc i) v) 0 :=
      fun v hv i => hS v hv _
    have h1 := hrep (fun i => d (Fin.castSucc i)) S hS' v hv
    have hmem : ∀ l' : List (Fin N), l'.foldr (fun i => d (Fin.castSucc i)) v ∈ S := by
      intro l'
      induction l' with
      | nil => exact hv
      | cons a l' ihl => exact (hS _ ihl _).1
    have hfold : ∀ l' : List (Fin N),
        (l'.map Fin.castSucc).foldr d v = l'.foldr (fun i => d (Fin.castSucc i)) v := by
      intro l'
      rw [List.foldr_map]
    have hPc : ∀ x : K, Continuous fun t : Fin N → ℝ =>
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod x := fun x =>
      (hcont x).comp (_root_.GlobalTheory.continuous_prod_ofFn_curves N _ fun i => (hc _).1)
    have hcF : ∀ (f : (Fin (N + 1) → ℝ) → ℂ) (x : K), Continuous f →
        Continuous fun t => f t • ρ (List.ofFn fun i => c i (t i)).prod x := fun f x hf =>
      hf.smul ((hcont x).comp (_root_.GlobalTheory.continuous_prod_ofFn_curves _ c fun i => (hc i).1))
    have hprod : ∀ (t : Fin N → ℝ) (r : ℝ),
        (List.ofFn fun i => c i ((Fin.snoc t r : Fin (N + 1) → ℝ) i)).prod =
          (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod * c (Fin.last N) r := by
      intro t r
      rw [List.ofFn_succ', List.prod_concat]
      simp
    rw [Fintype.sum_prod_type]
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, List.foldr_cons, hfold]
    rw [integral_cube_succ_eq_iterated N s _ (hcF (fun t => κ j (Fin.init t) * ((1 / s : ℝ) : ℂ)) _
        (((hκ j).comp hinit).mul continuous_const)),
      integral_cube_succ_eq_iterated N s _
        (hcF (fun t => κ j (Fin.init t) * -(((s - t (Fin.last N)) / s : ℝ) : ℂ)) _
        (((hκ j).comp hinit).mul (by fun_prop)))]
    simp only [Fin.init_snoc, Fin.snoc_last, hprod, map_mul, ContinuousLinearMap.mul_apply]
    set u := (l j).foldr (fun i => d (Fin.castSucc i)) v with hu_def
    have hu : u ∈ S := hmem _
    set cl := c (Fin.last N) with hcl
    have hA := eq_interval_average_sub_weighted_deriv ρ hcont hs cl (hc _).1 (hc _).2.1
      (hc _).2.2 u (d (Fin.last N) u) (hS u hu _).2
    have hI1 : IntegrableOn (fun r => ((1 / s : ℝ) : ℂ) • ρ (cl r) u) (Set.Icc 0 s) :=
      (continuous_const.smul ((hcont u).comp (hc _).1)).continuousOn.integrableOn_compact
        isCompact_Icc
    have hI2 : IntegrableOn (fun r => (((s - r) / s : ℝ) : ℂ) • ρ (cl r) (d (Fin.last N) u))
        (Set.Icc 0 s) :=
      ((Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).div_const s)).smul
        ((hcont _).comp (hc _).1)).continuousOn.integrableOn_compact isCompact_Icc
    have e1 : ∀ t : Fin N → ℝ, ∫ r in Set.Icc (0 : ℝ) s, (κ j t * ((1 / s : ℝ) : ℂ)) •
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod (ρ (cl r) u) =
        κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod
          (∫ r in Set.Icc 0 s, ((1 / s : ℝ) : ℂ) • ρ (cl r) u) := by
      intro t
      rw [← ContinuousLinearMap.integral_comp_comm _ hI1, ← integral_smul]
      congr 1
      funext r
      rw [map_smul, smul_smul]
    have e2 : ∀ t : Fin N → ℝ, ∫ r in Set.Icc (0 : ℝ) s, (κ j t * -(((s - r) / s : ℝ) : ℂ)) •
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod (ρ (cl r) (d (Fin.last N) u)) =
        -(κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod
          (∫ r in Set.Icc 0 s, (((s - r) / s : ℝ) : ℂ) • ρ (cl r) (d (Fin.last N) u))) := by
      intro t
      rw [← ContinuousLinearMap.integral_comp_comm _ hI2, ← integral_smul, ← integral_neg]
      congr 1
      funext r
      rw [map_smul, smul_smul, mul_neg, neg_smul]
    simp only [e1, e2]
    have hcube : IsCompact (Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) s) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    have hi : ∀ x : K, IntegrableOn (fun t : Fin N → ℝ =>
        κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod x)
        (Set.univ.pi fun _ => Set.Icc (0 : ℝ) s) := fun x =>
      ((hκ j).smul (hPc x)).continuousOn.integrableOn_compact hcube
    rw [integral_neg, ← sub_eq_add_neg, ← integral_sub (hi _) (hi _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [← smul_sub, ← map_sub, ← hA]

end GlobalTheory.CubeTaylor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumIntegralCubeDerivativesStatement
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_integral_cube_derivatives_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (s : ℝ), 0 < s → ∀ (N : ℕ) (c : Fin N → ℝ → G), (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ (J : Type) (_ : Fintype J) (κ : J → (Fin N → ℝ) → ℂ) (l : J → List (Fin N)), (∀ j, Continuous (κ j)) ∧ ∀ (d : Fin N → K → K) (S : Set K), (∀ v ∈ S, ∀ i, d i v ∈ S ∧ HasDerivAt (fun t : ℝ => ρ (c i t) v) (d i v) 0) → ∀ v ∈ S, v = ∑ j, ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), κ j t • ρ (List.ofFn fun i => c i (t i)).prod ((l j).foldr d v) := by
  first | exact @GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives | exact GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives | (intros; apply GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives <;> assumption)
end
end
