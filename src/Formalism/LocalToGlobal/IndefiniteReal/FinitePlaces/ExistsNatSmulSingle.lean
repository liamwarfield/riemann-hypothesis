module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_nat_eq_mul {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c : 𝓞 K, (m : 𝓞 K) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
    omega
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

theorem exists_nat_mul_mem {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : K) * e ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) e
  obtain ⟨m, hm, c, hc⟩ := exists_nat_eq_mul (b : 𝓞 K) (nonZeroDivisors.ne_zero b.2)
  refine ⟨m, hm, a * c, ?_⟩
  have h1 : (m : K) = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K c := by
    rw [← map_mul, ← hc, map_natCast]
  simp only at h
  rw [map_mul, h1, ← h]
  ring

lemma uniform_nat {ι : Type*} [Fintype ι] (P : ι → ℕ → Prop) (hP : ∀ i k m, P i k → P i (m * k))
    (h : ∀ i, ∃ k, 0 < k ∧ P i k) : ∃ k, 0 < k ∧ ∀ i, P i k := by
  classical
  choose k hk hPk using h
  refine ⟨∏ i, k i, Finset.prod_pos fun i _ => hk i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP i _ _ (hPk i)

lemma selfDual_isFullLattice (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

lemma exists_nat_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : Fin n → D.host.E) :
    ∃ N : ℕ, 0 < N ∧ (N : D.host.E) • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_nat_smul_mem hΛ x

lemma exists_nat_smul_single {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    ∃ m : ℕ, 0 < m ∧ ∀ j, (m : D.host.E) • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ := by
  refine uniform_nat (fun j m => (m : D.host.E) • (Pi.single j 1 : Fin n → D.host.E) ∈ Λ) (fun j k m h => ?_)
    (fun j => exists_nat_smul_mem hΛ _)
  rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
  exact Λ.nsmul_mem h m

lemma exists_nat_denom {n : ℕ} (v : Fin n → D.host.E) :
    ∃ c : ℕ, 0 < c ∧ ∀ j, (c : D.host.E) * v j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  uniform_nat (fun j c => (c : D.host.E) * v j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (fun j k m h => by push_cast; rw [mul_assoc]; exact mul_mem (natCast_mem _ m) h)
    (fun j => by obtain ⟨m, hm, h⟩ := exists_nat_mul_mem (v j); exact ⟨m, hm, h⟩)

theorem lattice_projective {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) : Module.Projective (𝓞 D.host.E) Λ := by
  have : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.2 hΛ.fg
  have : Module.Flat (𝓞 D.host.E) Λ := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    rw [Submodule.mem_bot]
    rw [Submonoid.smul_def] at ha
    exact (smul_eq_zero.1 ha).resolve_left (nonZeroDivisors.coe_ne_zero a)
  have : Module.FinitePresentation (𝓞 D.host.E) Λ := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem hF_eq_dot (S : HSp D) (x y : Fin S.rank → D.host.E) :
    hF S x y = (fun a => star (x a)) ⬝ᵥ (S.gram *ᵥ y) := by
  simp only [hF, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hF_swap (S : HSp D) (x y : Fin S.rank → D.host.E) : hF S x y = star (hF S y x) := by
  unfold hF
  simp only [star_sum, star_mul', star_star, star_gram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

def repV (S : HSp D) (w : Fin S.rank → D.host.E) : Fin S.rank → D.host.E :=
  fun k => star ((w ᵥ* S.gram⁻¹) k)

theorem hF_repV (S : HSp D) (w v : Fin S.rank → D.host.E) : hF S (repV S w) v = w ⬝ᵥ v := by
  have h1 : S.gram⁻¹ * S.gram = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (Formalism.MainNotions.S.Inh.tie_gram_det_ne S))
  have h2 : (fun a => star (repV S w a)) = w ᵥ* S.gram⁻¹ := by
    funext a; simp [repV]
  rw [hF_eq_dot, h2, dotProduct_mulVec, vecMul_vecMul, h1, vecMul_one]


set_option maxHeartbeats 1600000 in
theorem selfDual_basis (S : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hS : IsSelfDualC S ΛS) :
    ∃ (N : ℕ) (g s' : Fin N → Fin S.rank → D.host.E), (∀ i, g i ∈ ΛS) ∧ (∀ i, s' i ∈ ΛS) ∧
      ∀ v : Fin S.rank → D.host.E, ∑ i, hF S (s' i) v • g i = v := by
  classical
  have := lattice_projective hS.1
  have : Module.Finite (𝓞 D.host.E) ΛS := Module.Finite.iff_fg.2 hS.1.fg
  obtain ⟨N, f, hf⟩ := Module.Finite.exists_fin' (𝓞 D.host.E) ΛS
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  let gg : Fin N → ΛS := fun i => f (fun j => if i = j then 1 else 0)
  have hrep : ∀ x : ΛS, ∑ i, σ x i • gg i = x := by
    intro x
    have h1 : f (σ x) = x := LinearMap.congr_fun hσ x
    have h2 : f (σ x) = ∑ i, σ x i • gg i := by
      conv_lhs => rw [pi_eq_sum_univ (σ x)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul, gg]
    rw [← h2, h1]
  let A := algebraMap (𝓞 D.host.E) D.host.E
  obtain ⟨m, hm, hmS⟩ := exists_nat_smul_single (selfDual_isFullLattice S ΛS hS)
  have hm0 : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  let em : Fin S.rank → ΛS := fun j => ⟨(m : D.host.E) • (Pi.single j 1 : Fin S.rank → D.host.E), hmS j⟩
  let w : Fin N → Fin S.rank → D.host.E := fun i j => A (σ (em j) i) / m
  have hw : ∀ i j, A (σ (em j) i) = m * w i j := by
    intro i j; simp only [w]; field_simp

  have hagree : ∀ (x : ΛS) (i : Fin N), A (σ x i) = w i ⬝ᵥ (x : Fin S.rank → D.host.E) := by
    intro x i
    obtain ⟨c, hc, hcx⟩ := exists_nat_denom (x : Fin S.rank → D.host.E)
    have hcx' : ∀ j, ∃ y, A y = (c : D.host.E) * (x : Fin S.rank → D.host.E) j := fun j => RingHom.mem_range.1 (hcx j)
    choose o ho using hcx'
    have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
    have hx : ((c * m : ℕ) : 𝓞 D.host.E) • x = ∑ j, o j • em j := by
      apply Subtype.ext
      funext k
      simp only [Submodule.coe_smul, Submodule.coe_sum, Finset.sum_apply, Pi.smul_apply, em]
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp only [Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def]
      have := ho k
      simp only [A] at this
      rw [map_natCast, this]
      push_cast; ring
    have h3 := congrArg (fun y => A (σ y i)) hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_natCast] at h3
    apply mul_left_cancel₀ (mul_ne_zero hc0 hm0)
    rw [dotProduct, Finset.mul_sum]
    have e1 : ((c * m : ℕ) : D.host.E) = (c : D.host.E) * m := by push_cast; ring
    rw [e1] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ho j, hw i j]; ring

  have hcol : ∀ j, ∑ i, w i j • (gg i : Fin S.rank → D.host.E) = Pi.single j 1 := by
    intro j
    have h := congrArg (fun y : ΛS => (y : Fin S.rank → D.host.E)) (hrep (em j))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    have h' : ∑ i, A (σ (em j) i) • (gg i : Fin S.rank → D.host.E) = (m : D.host.E) • Pi.single j 1 :=
      (Finset.sum_congr rfl fun i _ => algebraMap_smul D.host.E _ _).trans h
    simp only [hw, mul_smul, ← Finset.smul_sum] at h'
    exact smul_right_injective _ hm0 h'
  refine ⟨N, fun i => (gg i : Fin S.rank → D.host.E), fun i => repV S (w i), fun i => (gg i).2, fun i => ?_, fun v => ?_⟩
  · refine (hS.2 (repV S (w i))).2 fun x hx => ⟨starO (σ ⟨x, hx⟩ i), ?_⟩
    rw [coe_starO]
    show star (A (σ ⟨x, hx⟩ i)) = hF S x (repV S (w i))
    rw [hF_swap, hF_repV, hagree]
  · simp only [hF_repV, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, (w i j * v j) • (gg i : Fin S.rank → D.host.E)
        = ∑ j, v j • ∑ i, w i j • (gg i : Fin S.rank → D.host.E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, mul_comm]
      _ = ∑ j, v j • (Pi.single j 1 : Fin S.rank → D.host.E) := by simp only [hcol]
      _ = v := by
          funext k
          simp [Finset.sum_apply, Pi.single_apply]

end Formalism.IndefR.Fin.PDA

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatAnn
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


set_option maxHeartbeats 800000 in
theorem lat_ann (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {x : WO S T}
    (hx : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True))
    {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) :
    ψ (symplO S T x u) = 1 := by
  have inner : ∀ {α : Af D.host.F} {c : D.host.E} {s : Fin S.rank → D.host.E} {t : Fin T.rank → D.host.E},
      α ∈ intAf D.host.F → c ∈ D.host.AA → s ∈ ΛS → t ∈ ΛT →
      ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        ψ (symplO S T (pairA D.host.F 0 α • ratW T S (rk1 S T c s t)) u) = 1 := by
    intro α c s t hα hc hs ht u hu
    induction hu using AddSubgroup.closure_induction with
    | mem u' hu' =>
      obtain ⟨α', hα', -, c', hc', s', hs', t', ht', rfl⟩ := hu'
      rw [gen_eq]
      exact psi_gen hψ S T hS hT hα hα' hc hc' hs hs' ht ht'
    | zero => rw [symplO_zero_right, AddChar.map_zero_eq_one]
    | add u1 u2 _ _ h1 h2 => rw [symplO_add_right, AddChar.map_add_eq_mul, h1, h2, one_mul]
    | neg u' _ h => rw [symplO_neg_right, AddChar.map_neg_eq_inv, h, inv_one]
  induction hx using AddSubgroup.closure_induction with
  | mem x' hx' =>
    obtain ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩ := hx'
    rw [gen_eq]
    exact inner hα hc hs ht u hu
  | zero => rw [symplO_zero_left, AddChar.map_zero_eq_one]
  | add x1 x2 _ _ h1 h2 => rw [symplO_add_left, AddChar.map_add_eq_mul, h1, h2, one_mul]
  | neg x' _ h => rw [symplO_neg_left, AddChar.map_neg_eq_inv, h, inv_one]

end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceLatDualIiiOf
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualASt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PlaceLatDualIi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ y : WO S T, IsHalf (cA D e) y →
        ((∀ x ∈ latAll S T ΛS ΛT, IsHalf e x → ψ (symplO S T x y) = 1) ↔ y ∈ latAll S T ΛS ΛT))

def PlaceLatDualIii (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
      (∀ x : WO S T, IsHalf e x →
        ((∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) ↔ x ∈ latAll S T ΛS ΛT))

end Formalism.IndefR.Fin

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev fI (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

theorem pairA_mul_one (α : Af D.host.F) : pairA D.host.F 0 α * pairA D.host.F 0 1 = pairA D.host.F 0 α :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [mul_zero]) (by show α * 1 = α; rw [mul_one])

theorem splitIdem_mul_fI {e' : AE D} (h : IsSplitIdem D e') : e' * fI D = e' := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, h3⟩ := h
  have he : e' = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
    rw [← h3, mul_add, h1, h2, add_zero]
  calc e' * fI D = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * fI D := by rw [← he]
    _ = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α * pairA D.host.F 0 1) := by
        rw [map_mul, mul_assoc]
    _ = e' := by rw [pairA_mul_one, ← he]

theorem splitIdem_cA {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hv, by rw [cA_cA, add_comm, h3]⟩

theorem idemSum_mul_fI {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) :
    e * fI D = e ∧ cA D e * fI D = cA D e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  exact ⟨Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (hes PP hPP).1,
    Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (splitIdem_cA (hes PP hPP).1)⟩

theorem idemSum_int {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) :
    finPart D e ∈ intAE D ∧ finPart D (cA D e) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  refine ⟨?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (hes PP hPP).1
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, map_sum]
      exact AddSubgroup.sum_mem _ fun PP hPP => splitIdem_int (splitIdem_cA (hes PP hPP).1)

theorem infPart_fI : infPart D (fI D) = 0 := by
  show infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = 0
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
    (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (AlgHom.id D.host.F D.host.E) 1 = 0
  rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl, TensorProduct.zero_tmul]

theorem half_infPart {m n : ℕ} {f : AE D} (hf : f * fI D = f) {y : Mx D m n} (hy : IsHalf f y) :
    y.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  calc infPart D (y i j) = infPart D ((f * fI D) * y i j) := by rw [hf, hy i j]
    _ = 0 := by rw [map_mul, map_mul, infPart_fI, mul_zero, zero_mul]

variable (S T : HSp D)

theorem hO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    hO S T y u = hO S T y (f • u) := by
  unfold hO
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  conv_lhs => rw [← hy d a]
  ring

theorem symplO_half_right {f : AE D} {y : WO S T} (hy : IsHalf (cA D f) y) (u : WO S T) :
    symplO S T y u = symplO S T y (f • u) := by
  unfold symplO; rw [hO_half_right S T hy u]

variable {S T}

theorem placeLatDualIi_of (hL : LatSelfDual D) : PlaceLatDualIi D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he y hy
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, hfc⟩ := idemSum_mul_fI he
  have hie := (idemSum_int he).1
  have hee := idemSum_mul_self he
  have hy0 : y.map (infPart D) = 0 := half_infPart hfc hy
  constructor
  · intro hx
    refine (hL4 y hy0).2 fun u hu => ?_
    have hm : e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hie hu
    have hh : IsHalf e (e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hee]
    have h1 := hx _ hm hh
    rw [symplO_half_right S T hy u, symplO_swap S T (e • u) y, AddChar.map_neg_eq_inv, h1, inv_one]
  · intro hyL x hx hxh
    exact (hL4 x (half_infPart hfe hxh)).1 hx y hyL

theorem placeLatDualIii_of (hL : LatSelfDual D) : PlaceLatDualIii D := by
  intro ψ hψ S T ΛS ΛT hS hT P e he x hx
  have hL4 := (hL ψ hψ S T ΛS ΛT hS hT).2.2.2
  obtain ⟨hfe, -⟩ := idemSum_mul_fI he
  have hic := (idemSum_int he).2
  have hee := idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hx0 : x.map (infPart D) = 0 := half_infPart hfe hx
  have hxc : IsHalf (cA D (cA D e)) x := by rw [cA_cA]; exact hx
  constructor
  · intro hy
    refine (hL4 x hx0).2 fun u hu => ?_
    have hm : cA D e • u ∈ latAll S T ΛS ΛT := latO_smul_mem S T ΛS ΛT hic hu
    have hh : IsHalf (cA D e) (cA D e • u) := fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hcc]
    rw [symplO_half_right S T hxc u]
    exact hy _ hm hh
  · intro hxL y hy _
    exact (hL4 x hx0).1 hxL y hy

end Formalism.IndefR.Fin.PDA

end
end
