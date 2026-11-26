module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorDifferentiable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbability

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExistsHolds
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St.WittT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Witt

variable {D : D7}

abbrev Ix (D : D7) : Type := Fin D.R.rS ⊕ (Fin D.R.rS ⊕ Unit)

def mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) : Ix D → (VS D).V
  | Sum.inl a => e a
  | Sum.inr (Sum.inl a) => f a
  | Sum.inr (Sum.inr _) => z

def gstd (T : D.host.E) : Ix D → Ix D → D.host.E
  | Sum.inl a, Sum.inr (Sum.inl b) => if a = b then 1 else 0
  | Sum.inr (Sum.inl a), Sum.inl b => if a = b then 1 else 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => -T
  | _, _ => 0

def swp : Ix D → Ix D
  | Sum.inl a => Sum.inr (Sum.inl a)
  | Sum.inr (Sum.inl a) => Sum.inl a
  | Sum.inr (Sum.inr t) => Sum.inr (Sum.inr t)

def cstd (T : D.host.E) : Ix D → D.host.E
  | Sum.inr (Sum.inr _) => -T
  | _ => 1

theorem gram_mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) (T : D.host.E)
    (hee : ∀ a b, (VS D).hT (e a) (e b) = 0) (hff : ∀ a b, (VS D).hT (f a) (f b) = 0)
    (hef : ∀ a b, (VS D).hT (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, (VS D).hT (e a) z = 0) (hfz : ∀ a, (VS D).hT (f a) z = 0) (hzz : (VS D).hT z z = -T) :
    ∀ i j, (VS D).hT (mkFr e f z i) (mkFr e f z j) = gstd T i j := by
  rintro (a | a | ⟨⟩) (b | b | ⟨⟩)
  · exact hee a b
  · exact hef a b
  · exact hez a
  · show (VS D).hT (f a) (e b) = if a = b then 1 else 0
    rw [← (VS D).herm.eq (e b) (f a), hef b a]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · exact hff a b
  · exact hfz a
  · show (VS D).hT z (e b) = 0
    rw [← (VS D).herm.eq (e b) z, hez b, map_zero]
  · show (VS D).hT z (f b) = 0
    rw [← (VS D).herm.eq (f b) z, hfz b, map_zero]
  · exact hzz

theorem gstd_swp (T : D.host.E) (i j : Ix D) : gstd T (swp j) i = if i = j then cstd T j else 0 := by
  rcases i with a | a | ⟨⟩ <;> rcases j with b | b | ⟨⟩ <;>
    simp [gstd, swp, cstd, eq_comm]

theorem indep_of_dual {ι : Type} [Fintype ι] [DecidableEq ι] (v d : ι → (VS D).V) (c : ι → D.host.E)
    (hc : ∀ j, c j ≠ 0) (hd : ∀ i j, (VS D).hT (d j) (v i) = if i = j then c j else 0) :
    LinearIndependent D.host.E v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg ((VS D).hT (d j)) hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_zero, hd, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  exact (mul_eq_zero.1 h).resolve_right (hc j)

theorem indep_mkFr (e f : Fin D.R.rS → (VS D).V) (z : (VS D).V) (T : D.host.E) (hT : T ≠ 0)
    (hG : ∀ i j, (VS D).hT (mkFr e f z i) (mkFr e f z j) = gstd T i j) :
    LinearIndependent D.host.E (mkFr e f z) := by
  refine indep_of_dual (mkFr e f z) (fun j => mkFr e f z (swp j)) (cstd T) ?_ ?_
  · rintro (a | a | ⟨⟩) <;> simp [cstd, hT]
  · intro i j
    rw [hG, gstd_swp]

theorem witt_family {ι : Type} [Fintype ι] [DecidableEq ι] (v w : ι → (VS D).V)
    (hv : LinearIndependent D.host.E v) (hw : LinearIndependent D.host.E w)
    (hG : ∀ i j, (VS D).hT (v i) (v j) = (VS D).hT (w i) (w j)) :
    ∃ g : (VS D).V ≃ₗ[D.host.E] (VS D).V, (∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y) ∧ ∀ i, g (v i) = w i := by
  set U := Submodule.span D.host.E (Set.range v) with hU
  let b : Module.Basis ι D.host.E U := Module.Basis.span hv
  let f : U →ₗ[D.host.E] (VS D).V :=
    Finsupp.linearCombination D.host.E w ∘ₗ (b.repr : U →ₗ[D.host.E] (ι →₀ D.host.E))
  have hfb : ∀ i, f (b i) = w i := by
    intro i
    simp [f, Module.Basis.repr_self, Finsupp.linearCombination_single]
  have hbv : ∀ i, ((b i : U) : (VS D).V) = v i := by
    intro i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  have hinj : Function.Injective f := by
    have h2 : Function.Injective (Finsupp.linearCombination D.host.E w) := hw
    exact h2.comp b.repr.injective
  have hB : ((VS D).hT.comp f).compl₂ f = ((VS D).hT.comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hfb, Submodule.subtype_apply, hbv]
    exact (hG i j).symm
  have hiso : ∀ x y : U, (VS D).hT (f x) (f y) = (VS D).hT x y := by
    intro x y
    have h := congrArg (fun B => B x y) hB
    simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply] using h
  obtain ⟨g, hg, hgf⟩ := _root_.witt_extension_theorem D.host.E (VS D).V (VS D).hT
    (fun x y => (VS D).herm.eq x y) (fun x hx => (VS D).nondeg.1 x hx) U f hinj hiso
  refine ⟨g, hg, fun i => ?_⟩
  have h := hgf (b i)
  rw [hbv, hfb] at h
  exact h

theorem hypF_zmOf (u : D.what₂.Word) (a : Fin D.R.rS) : (VS D).hT (D.sp.hypF a) (D.zmOf u) = 0 := by
  unfold D7.zmOf
  rw [map_smul, ← (VS D).herm.eq D.sp.zm (D.sp.hypF a), (D.sp.hyp_orthz a).2, map_zero, smul_zero]

theorem wittExists_holds (D : D7) : WittExists D := by
  intro X u
  have hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hGX := gram_mkFr X.eX X.fY (X.zu u) (((D.mem u).A.T : ℕ) : D.host.E) X.ee X.ff X.ef
    (fun a => (X.zu_orth u a).1) (fun a => (X.zu_orth u a).2) (X.zu_norm u)
  have hGR := gram_mkFr D.sp.hypE D.sp.hypF (D.zmOf u) (((D.mem u).A.T : ℕ) : D.host.E) D.sp.hyp_ee D.sp.hyp_ff
    D.sp.hyp_ef (fun a => (Formalism.MainNotions.S.Inh.tie_flag0 D u).z_orth a) (hypF_zmOf u) (Formalism.MainNotions.S.Inh.tie_zmOf_norm D u)
  obtain ⟨g, hg, hgi⟩ := witt_family (mkFr X.eX X.fY (X.zu u)) (mkFr D.sp.hypE D.sp.hypF (D.zmOf u))
    (indep_mkFr _ _ _ _ hT hGX) (indep_mkFr _ _ _ _ hT hGR) (fun i j => by rw [hGX, hGR])
  exact ⟨g, hg, fun a => hgi (Sum.inl a), fun a => hgi (Sum.inr (Sum.inl a)), hgi (Sum.inr (Sum.inr ()))⟩

end Witt

theorem wittExists : ∀ D : D7, WittExists D := wittExists_holds

end GlobalTheory.St.WittT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicLatticeClosureIffSwapMemSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicLatticeClosureIffSwapMemSpan
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.AdelicLatticeSwap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))

private lemma mem_intAf_of_mem_intAd {a : Af F} (ha : a ∈ Formalism.UG.intAd F) : a ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  exact ha v

private lemma mem_intAd_of_mem_intAf {a : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) : a ∈ Formalism.UG.intAd F := by
  intro v
  exact ha v

private lemma intAf_mul_mem {a b : Af F} (ha : a ∈ Formalism.MainNotions.StandardLattice.intAf F) (hb : b ∈ Formalism.MainNotions.StandardLattice.intAf F) :
    a * b ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

private lemma one_mem_intAf_flag_measures : (1 : Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := by
  intro v
  rw [map_one]
  exact one_mem _


omit [NumberField E] in
theorem gen_smul_mem (a : Af F) (ha : a ∈ Formalism.UG.intAd F) (c : 𝓞 E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E))) :
    (a ⊗ₜ[F] (c : E) : Af F ⊗[F] E) • y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.StandardLattice.latHat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    refine ⟨a * b, intAf_mul_mem (mem_intAf_of_mem_intAd ha) hb, c • x, L.smul_mem c hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
  | neg u _ hu => rw [smul_neg]; exact neg_mem hu

theorem int_smul_mem (t : E ⊗[F] Af F) (ht : t ∈ Formalism.MainNotions.S.IntAf F E) :
    ∀ y : Fin n → Af F ⊗[F] E, y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) →
      (Algebra.TensorProduct.comm F (Af F) E).symm t • y ∈
        Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at ht
  induction ht using Subring.closure_induction with
  | mem s hs =>
    intro y hy
    rcases hs with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨c, rfl⟩ := he
      rw [Algebra.TensorProduct.comm_symm_tmul]
      exact gen_smul_mem L 1 (one_mem _) c y hy
    · rw [Algebra.TensorProduct.comm_symm_tmul]
      simpa using gen_smul_mem L b hb 1 y hy
  | zero => intro y _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro y hy; rw [map_one, one_smul]; exact hy
  | add s u _ _ hs hu => intro y hy; rw [map_add (f := _), add_smul]; exact add_mem (hs y hy) (hu y hy)
  | neg s _ hs => intro y hy; rw [map_neg, neg_smul]; exact neg_mem (hs y hy)
  | mul s u _ _ hs hu => intro y hy; rw [map_mul, mul_smul]; exact hs _ (hu y hy)

theorem symm_mem_of_mem (z : Fin n → E ⊗[F] Af F) (hz : z ∈ Formalism.MainNotions.S.lamAf (F := F) L) :
    (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (z i)) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) := by
  unfold Formalism.MainNotions.S.lamAf at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hw
    unfold Formalism.MainNotions.StandardLattice.latHat
    apply AddSubgroup.subset_closure
    refine ⟨1, one_mem_intAf_flag_measures, x, hx, ?_⟩
    funext i
    show (Algebra.TensorProduct.comm F (Af F) E).symm ((x i) ⊗ₜ[F] (1 : Af F)) = (1 : Af F) ⊗ₜ[F] x i
    simp
  | zero =>
    have h0 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((0 : Fin n → E ⊗[F] Af F) i)) = 0 := by
      funext i
      simp
    rw [h0]
    exact zero_mem _
  | add u w _ _ hu hw =>
    have h1 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((u + w) i)) =
        (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i)) +
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (w i) := by
      funext i
      simp
    rw [h1]
    exact add_mem hu hw
  | smul s u _ hu =>
    have h2 : (fun i => (Algebra.TensorProduct.comm F (Af F) E).symm ((s • u) i)) =
        (Algebra.TensorProduct.comm F (Af F) E).symm (s : E ⊗[F] Af F) •
          fun i => (Algebra.TensorProduct.comm F (Af F) E).symm (u i) := by
      funext i
      simp [Subring.smul_def]
    rw [h2]
    exact int_smul_mem L s s.2 _ hu

theorem mem_latHat_iff_comm_mem_lamAf (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E))
    (y : Fin n → Af F ⊗[F] E) :
    y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (Af F) E (y i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  constructor
  · intro hy
    unfold Formalism.MainNotions.StandardLattice.latHat at hy
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hw
      have hg : (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L :=
        Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      have hs : ((1 : E) ⊗ₜ[F] a : E ⊗[F] Af F) ∈ Formalism.MainNotions.S.IntAf F E :=
        Subring.subset_closure (Or.inr ⟨⟨a, mem_intAd_of_mem_intAf ha⟩, rfl⟩)
      convert Submodule.smul_mem _ (⟨_, hs⟩ : Formalism.MainNotions.S.IntAf F E) hg using 1
      funext i
      simp [Subring.smul_def, Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    | zero =>
      convert zero_mem (Formalism.MainNotions.S.lamAf (F := F) L) using 1
      funext i
      simp
    | add u w _ _ hu hw =>
      convert add_mem hu hw using 1
      funext i
      simp
    | neg u _ hu =>
      convert neg_mem hu using 1
      funext i
      simp
  · intro hz
    simpa using symm_mem_of_mem L _ hz

end GlobalTheory.AdelicLatticeSwap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicLatticeClosureIffSwapMemSpanStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicLatticeClosure_iff_swap_mem_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → Af F ⊗[F] E), y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔ (fun i => Algebra.TensorProduct.comm F (Af F) E (y i)) ∈ Formalism.MainNotions.S.lamAf (F := F) L := by
  first | exact @GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf | exact GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf | (intros; apply GlobalTheory.AdelicLatticeSwap.mem_latHat_iff_comm_mem_lamAf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSchwartzBruhatIndicatorLocalLatticeCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulEqInteger
namespace GlobalTheory.IntSmulIntegerEq

theorem exists_int_smul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers E,
      algebraMap (NumberField.RingOfIntegers E) E a = M • c := by
  have hQ : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hQ
  obtain ⟨M, hM, hint⟩ := hZ.exists_integral_multiple
  exact ⟨M, hM, ⟨M • c, hint⟩, rfl⟩

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, h₁, hx⟩ := hx
    obtain ⟨N₂, h₂, hy⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : (N₁ * N₂) • (x + y) = N₂ • (N₁ • x) + N₁ • (N₂ • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm N₂ N₁]
    rw [e]
    exact L.add_mem (zsmul_mem hx N₂) (zsmul_mem hy N₁)
  | smul c x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, a, ha⟩ := exists_int_smul_eq_integer c
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have e : (M * N) • (c • x) = a • (N • x) := by
      rw [← algebraMap_smul E a, ha, smul_assoc, mul_smul, smul_comm N c x]
    rw [e]
    exact L.smul_mem a hx

end GlobalTheory.IntSmulIntegerEq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSchwartzBruhatIndicatorLocalLatticeCompletion
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LatticeIndicator

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_int_generators (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ (k : ℕ) (x : Fin k → Fin n → E), (∀ j, x j ∈ L) ∧
      ∀ w ∈ L, ∃ m : Fin k → ℤ, w = ∑ j, m j • x j := by
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  refine ⟨k, fun j => s j, fun j => (s j).2, fun w hw => ?_⟩
  have : (⟨w, hw⟩ : L) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  exact ⟨m, by simpa using (congrArg Subtype.val hm).symm⟩

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (w : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  exact _root_.GlobalTheory.IntSmulIntegerEq.exists_int_smul_mem L hL w

theorem latLoc_compact_open (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) ∧
      IsOpen (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  haveI : CharZero (Fv F v) := charZero_of_injective_ringHom (algebraMap F (Fv F v)).injective
  obtain ⟨k, x, hxL, hx⟩ := exists_int_generators L hL.fg
  let f : (Fin k → Fv F v) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
    Fintype.linearCombination _ fun j i => (1 : Fv F v) ⊗ₜ[F] x j i
  have hfa : ∀ a i, f a i = ∑ j, a j ⊗ₜ[F] x j i := fun a i => by
    simp [f, Fintype.linearCombination_apply, TensorProduct.smul_tmul']
  have hm : ∀ (a : Fv F v) (m : Fin k → ℤ),
      f (fun j => m j • a) = fun i => a ⊗ₜ[F] (∑ j, m j • x j) i := fun a m => by
    funext i
    rw [hfa]
    simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _
  have hf : Function.Surjective f := by
    have h1 : ∀ (a : Fv F v) (w : Fin n → E), (fun i => a ⊗ₜ[F] w i) ∈ LinearMap.range f := by
      intro a w
      obtain ⟨N, hN, h⟩ := exists_int_smul_mem L hL w
      obtain ⟨m, e⟩ := hx _ h
      refine ⟨fun j => m j • ((N : Fv F v)⁻¹ * a), ?_⟩
      rw [hm, ← e]
      funext i
      rw [Pi.smul_apply, ← TensorProduct.smul_tmul, zsmul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (Int.cast_ne_zero.2 hN), one_mul]
    intro y
    rw [← LinearMap.mem_range, ← Finset.univ_sum_single y]
    refine sum_mem fun i _ => ?_
    generalize y i = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [Pi.single_add]; exact add_mem hp hq
    | tmul a e =>
      convert h1 a (Pi.single i e) using 1
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
  have hfo : IsOpenMap f := IsModuleTopology.isOpenMap_of_surjective (φ := f) hf
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have himg : (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) =
      f '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    constructor
    · refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => y ∈ f '' Set.pi Set.univ fun _ =>
        (v.adicCompletionIntegers F : Set (Fv F v))) ?_ ⟨0, fun _ _ => zero_mem _, map_zero _⟩ ?_ ?_
      · intro a ha w hw
        obtain ⟨m, rfl⟩ := hx w hw
        exact ⟨fun j => m j • a, fun j _ => zsmul_mem ha _, hm a m⟩
      · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun j _ => add_mem (s := v.adicCompletionIntegers F) (ha j trivial) (hb j trivial),
          map_add _ _ _⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun j _ => neg_mem (s := v.adicCompletionIntegers F) (ha j trivial), map_neg _ _⟩
    · rintro ⟨a, ha, rfl⟩
      have : f a = ∑ j, fun i => a j ⊗ₜ[F] x j i := funext fun i => by rw [hfa, Finset.sum_apply]
      rw [this]
      exact sum_mem (S := GlobalTheory.AdelicU.latLoc F L v) fun j _ =>
        GlobalTheory.AdelicU.tmul_mem_latLoc (ha j trivial) (hxL j)
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  rw [himg]
  exact ⟨(isCompact_univ_pi fun _ => hc).image hfc,
    hfo _ (isOpen_set_pi Set.finite_univ fun _ _ => ho)⟩

theorem isSB_indicator_latLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ v : HeightOneSpectrum (𝓞 F), IsSB ({X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ)) := by
  intro F E _ _ _ _ _ n L hL v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨hc, ho⟩ := latLoc_compact_open L hL v
  have hcl : IsClosed (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) :=
    (GlobalTheory.AdelicU.latLoc F L v).toAddSubgroup.isClosed_of_isOpen ho
  have e : {X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v} =
      Set.pi Set.univ fun _ : Fin 1 => (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext X
    simp [Fin.forall_fin_one]
  rw [e]
  have h1 := isCompact_univ_pi fun _ : Fin 1 => hc
  have h2 := isOpen_set_pi Set.finite_univ fun (_ : Fin 1) _ => ho
  have h3 := isClosed_set_pi (i := Set.univ) fun (_ : Fin 1) _ => hcl
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun X => ?_, ?_⟩
  · by_cases hX : X ∈ Set.pi Set.univ fun _ : Fin 1 =>
        (GlobalTheory.AdelicU.latLoc F L v : Set (Fin n → Fv F v ⊗[F] E))
    · exact ⟨_, h2, hX, fun Y hY => by rw [Set.indicator_of_mem hY, Set.indicator_of_mem hX]; rfl⟩
    · exact ⟨_, h3.isOpen_compl, hX, fun Y hY => by
        rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem hX]⟩
  · exact HasCompactSupport.intro' h1 h3 fun X hX => Set.indicator_of_notMem hX _

end GlobalTheory.LatticeIndicator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSchwartzBruhatIndicatorLocalLatticeCompletionStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhat_indicator_localLatticeCompletion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ v : HeightOneSpectrum (𝓞 F), IsSB ({X : Fin 1 → Fin n → Fv F v ⊗[F] E | X 0 ∈ GlobalTheory.AdelicU.latLoc F L v}.indicator (1 : (Fin 1 → Fin n → Fv F v ⊗[F] E) → ℂ)) := by
  first | exact @GlobalTheory.LatticeIndicator.isSB_indicator_latLoc | exact GlobalTheory.LatticeIndicator.isSB_indicator_latLoc | (intros; apply GlobalTheory.LatticeIndicator.isSB_indicator_latLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MiddleLatticeSelfDualAnisotropicPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MiddleLatticeSelfDualAnisotropicPairing
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.MidLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hconj (x y : S.V) : star (S.hT x y) = S.hT y x := by
  have h := S.herm.eq x y
  simpa [starRingEnd_apply] using h

def prj (e f : Fin r → S.V) : S.V →ₗ[E] S.V :=
  LinearMap.id - ∑ a, (S.hT (f a)).smulRight (e a) - ∑ a, (S.hT (e a)).smulRight (f a)

theorem prj_apply (e f : Fin r → S.V) (y : S.V) :
    prj e f y = y - ∑ a, S.hT (f a) y • e a - ∑ a, S.hT (e a) y • f a := by
  simp [prj, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

variable {e f : Fin r → S.V} (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hef in
theorem hfe (a b : Fin r) : S.hT (f a) (e b) = if b = a then 1 else 0 := by
  rw [← hconj, hef]; split_ifs <;> simp

include hee hef in
theorem prj_e (b : Fin r) : prj e f (e b) = 0 := by
  rw [prj_apply]; simp [hfe hef, hee]

include hff hef in
theorem prj_f (b : Fin r) : prj e f (f b) = 0 := by
  rw [prj_apply]; simp [hff, hef]

theorem prj_perp {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) : prj e f y = y := by
  rw [prj_apply]; simp [(hy _).1, (hy _).2]

theorem pair_prj {y : S.V} (hy : ∀ a, S.hT (e a) y = 0 ∧ S.hT (f a) y = 0) (x : S.V) :
    S.hT (prj e f x) y = S.hT x y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [prj_apply]; simp [map_sub, map_sum, (hy _).1, (hy _).2]

include hee hef in
theorem prj_spanE {s : S.V} (hs : s ∈ Submodule.span E (Set.range e)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range e) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_e hee hef b)
  exact h hs

include hff hef in
theorem prj_spanF {s : S.V} (hs : s ∈ Submodule.span E (Set.range f)) : prj e f s = 0 := by
  have h : Submodule.span E (Set.range f) ≤ LinearMap.ker (prj e f) :=
    Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact prj_f hff hef b)
  exact h hs

theorem latSpanS_le_span (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → S.V) :
    latSpanS aa v ≤ (Submodule.span E (Set.range v)).restrictScalars (𝓞 E) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, x, -, rfl⟩
  exact Submodule.smul_mem _ x (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.St.G.MidLat


open GlobalTheory.St.G.MidLat in
theorem GlobalTheory.St.G.midLat_selfDual_pairing : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧ ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb))) ∧ (∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = 1) ∧ ∀ y ∈ (VS D).L0, y - ∑ a, (VS D).hT (X.fY a) y • X.eX a - ∑ a, (VS D).hT (X.eX a) y • X.fY a ∈ X.Lb := by
  intro D X u
  have hprjL : ∀ y ∈ (VS D).L0, prj X.eX X.fY y ∈ X.Lb := by
    intro y hy
    rw [X.Lam_split] at hy
    obtain ⟨y1, hy1, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨s, hs, l, hl, rfl⟩ := Submodule.mem_sup.1 hy1
    have hs' := latSpanS_le_span _ _ hs
    have ht' := latSpanS_le_span _ _ ht
    rw [map_add (f := _), map_add (f := _), prj_spanE X.ee X.ef hs', prj_spanF X.ff X.ef ht', zero_add, add_zero,
      prj_perp (fun a => X.Lb_perp l hl a)]
    exact hl
  have hLbL : X.Lb ≤ (VS D).L0 := by
    rw [X.Lam_split]; exact le_sup_right.trans le_sup_left
  have h1 : ∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) →
      ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧
        ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb)) := by
    intro y hy
    refine ⟨⟨fun h => ?_, fun h => hLbL h⟩, fun hint => ?_⟩
    · have := hprjL y h; rwa [prj_perp hy] at this
    · have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
      have hyL : y ∈ (VS D).L0 := by
        rw [← hU]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply, Submodule.mem_one]
        intro x hx
        obtain ⟨o, ho⟩ := hint _ (hprjL x hx)
        exact ⟨o, by rw [ho, pair_prj hy]⟩
      have := hprjL y hyL; rwa [prj_perp hy] at this
  refine ⟨h1, ?_, fun y hy => ?_⟩

  · let σ : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (starRingEnd D.host.E)
    have hσ : ∀ o : 𝓞 D.host.E, ((σ o : 𝓞 D.host.E) : D.host.E) = star (o : D.host.E) := fun o => rfl
    let J : Ideal (𝓞 D.host.E) :=
      (LinearMap.range (((VS D).hT (X.zu u)).restrictScalars (𝓞 D.host.E) ∘ₗ X.Lb.subtype)).comap
        (Algebra.linearMap (𝓞 D.host.E) D.host.E)
    have hJ : ∀ o, o ∈ J ↔ ∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = (o : D.host.E) := by
      intro o
      simp only [J, Submodule.mem_comap, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, LinearMap.restrictScalars_apply, Algebra.linearMap_apply, Subtype.exists,
        exists_prop]
    by_cases hJt : J = ⊤
    · obtain ⟨x, hx, hx1⟩ := (hJ 1).1 (hJt ▸ Submodule.mem_top)
      exact ⟨x, hx, by rw [hx1]; simp⟩
    exfalso
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJt
    have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)
    obtain ⟨c, hc, hc1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := D.host.E) hM0 hM.ne_top
    have hc' := (FractionalIdeal.mem_inv_iff (by rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero])).1 hc
    have hU : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
    have hzL : X.zu u ∈ X.Lb := X.zu_Lb u
    have hwperp : ∀ a, (VS D).hT (X.eX a) (star c • X.zu u) = 0 ∧ (VS D).hT (X.fY a) (star c • X.zu u) = 0 := by
      intro a
      exact ⟨by rw [map_smul, smul_eq_mul, (X.zu_orth u a).1, mul_zero],
        by rw [map_smul, smul_eq_mul, (X.zu_orth u a).2, mul_zero]⟩
    have hwLb : star c • X.zu u ∈ X.Lb := by
      refine (h1 _ hwperp).2 ?_
      intro x hx
      have hxd : x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 := by rw [hU]; exact hLbL hx
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply, Submodule.mem_one] at hxd
      obtain ⟨o, ho⟩ := hxd (X.zu u) (hLbL hzL)
      have hoM : o ∈ M := hJM ((hJ o).2 ⟨x, hx, ho.symm⟩)
      obtain ⟨o', ho'⟩ := (FractionalIdeal.mem_one_iff _).1
        (hc' _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨o, hoM, rfl⟩))
      refine ⟨σ o', ?_⟩
      change ((σ o' : 𝓞 D.host.E) : D.host.E) = _
      rw [hσ]
      change star (algebraMap (𝓞 D.host.E) D.host.E o') = _
      rw [ho', map_smul, smul_eq_mul, ← hconj (X.zu u) x, ← ho, star_mul, mul_comm]
    have hprim := (X.Fu_fixed u).2.2.2.2 (star c)
    dsimp only at hprim
    rw [X.flagZVector u] at hprim
    have horth : star c • X.zu u ∈ Formalism.MainNotions.S.Lat.orth (Formalism.MainNotions.S.Lat.hS D)
        (Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))) := by
      simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      have hX : Formalism.MainNotions.S.Lat.Xsp (⟨X.Fu u, X.zu u⟩ : Formalism.MainNotions.S.Lat.LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
          = Submodule.span D.host.E (Set.range X.eX) := by
        show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
        rw [X.Fu_e u]
      rw [hX] at hx
      have hle : Submodule.span D.host.E (Set.range X.eX) ≤ LinearMap.ker ((VS D).hT (star c • X.zu u)) :=
        Submodule.span_le.2 (by
          rintro _ ⟨a, rfl⟩
          show (VS D).hT (star c • X.zu u) (X.eX a) = 0
          rw [← hconj, (hwperp a).1, star_zero])
      have := hle hx
      rw [LinearMap.mem_ker] at this
      rw [← hconj, this, star_zero]
    obtain ⟨o, ho⟩ := hprim ⟨Submodule.mem_sup_left ⟨hLbL hwLb, horth⟩, horth⟩
    apply hc1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨σ o, ?_⟩
    change ((σ o : 𝓞 D.host.E) : D.host.E) = c
    rw [hσ, ho, star_star]
  · have := hprjL y hy; rwa [prj_apply] at this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MiddleLatticeSelfDualAnisotropicPairingStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.middleLattice_selfDual_anisotropic_pairing : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), (∀ y : (VS D).V, (∀ a, (VS D).hT (X.eX a) y = 0 ∧ (VS D).hT (X.fY a) y = 0) → ((y ∈ (VS D).L0 ↔ y ∈ X.Lb) ∧ ((∀ x ∈ X.Lb, (VS D).hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → y ∈ X.Lb))) ∧ (∃ x ∈ X.Lb, (VS D).hT (X.zu u) x = 1) ∧ ∀ y ∈ (VS D).L0, y - ∑ a, (VS D).hT (X.fY a) y • X.eX a - ∑ a, (VS D).hT (X.eX a) y • X.fY a ∈ X.Lb := by
  first | exact @GlobalTheory.St.G.midLat_selfDual_pairing | exact GlobalTheory.St.G.midLat_selfDual_pairing | (intros; apply GlobalTheory.St.G.midLat_selfDual_pairing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContDiffFderivMul
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder ContDiff Topology Pointwise

namespace GlobalTheory.GardingStep

theorem hasDerivAt_orbit {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (ρ : G → H →L[ℂ] H) (w v : H) (hmul : ∀ a b, ρ (a * b) w = ρ a (ρ b w))
    (hc : Continuous fun y => ρ y w) (a : G → ℂ) (ha : Continuous a) (hs : HasCompactSupport a)
    (hw : ∫ y, a y • ρ y w ∂μ = v) (e : ℝ → G) (he : Continuous e) (he0 : e 0 = 1)
    (D : ℝ → G → ℂ) (hD : Continuous fun p : ℝ × G => D p.1 p.2)
    (hd : ∀ s y, HasDerivAt (fun t => a ((e t)⁻¹ * y)) (D s y) s) :
    HasCompactSupport (D 0) ∧ HasDerivAt (fun s => ρ (e s) v) (∫ y, D 0 y • ρ y w ∂μ) 0 := by
  have hint : Integrable (fun y => a y • ρ y w) μ :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hform : (fun s => ρ (e s) v) = fun s => ∫ y, a ((e s)⁻¹ * y) • ρ y w ∂μ := by
    funext s
    rw [← integral_mul_left_eq_self (fun y => a ((e s)⁻¹ * y) • ρ y w) (e s)]
    conv_lhs => rw [← hw]
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    simp only [inv_mul_cancel_left, hmul, map_smul]
  have hzero : ∀ s y, (e s)⁻¹ * y ∉ tsupport a → D s y = 0 := by
    intro s y hy
    have h1 : ∀ᶠ t in 𝓝 s, (e t)⁻¹ * y ∈ (tsupport a)ᶜ :=
      (he.inv.mul continuous_const).continuousAt.preimage_mem_nhds
        ((isClosed_tsupport a).isOpen_compl.mem_nhds hy)
    have h2 : HasDerivAt (fun t => a ((e t)⁻¹ * y)) 0 s :=
      (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq
        (h1.mono fun t ht => image_eq_zero_of_notMem_tsupport ht)
    exact (hd s y).unique h2
  have hK : IsCompact ((fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a)) :=
    (isCompact_Icc.prod hs.isCompact).image ((he.comp continuous_fst).mul continuous_snd)
  set K := (fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a) with hKdef
  have hcD : Continuous fun p : ℝ × G => D p.1 p.2 • ρ p.2 w := hD.smul (hc.comp continuous_snd)
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
    hcD.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun s y => a ((e s)⁻¹ * y) • ρ y w) (F' := fun s y => D s y • ρ y w) (x₀ := 0)
    (bound := K.indicator fun _ => M) (s := Set.Icc (-1) 1) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun s =>
      ((ha.comp (continuous_const.mul continuous_id)).smul hc).aestronglyMeasurable)
    (by simpa [he0] using hint)
    (hcD.comp (Continuous.prodMk_right 0)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y s hs' => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy]; exact hM (s, y) ⟨hs', hy⟩
      · rw [Set.indicator_of_notMem hy, hzero s y, zero_smul, norm_zero]
        intro h
        exact hy ⟨(s, (e s)⁻¹ * y), ⟨hs', h⟩, by simp⟩)
    ((integrable_indicator_iff hK.isClosed.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun y s _ => (hd s y).smul_const _)
  refine ⟨HasCompactSupport.intro hs.isCompact fun y hy => hzero 0 y (by simpa [he0] using hy), ?_⟩
  rw [hform]
  exact key.2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smooth_coef (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} {s v : H}
    (hα : SmoothOnG ε α) (hαc : HasCompactSupport (fun g : UJ ε => α (umat g)))
    (hfix : ∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, v⟫_ℂ) (u : H) :
    SmoothOnG ε (fun g => ⟪u, σ g v⟫_ℂ) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := isClosedEmbeddingMatrix n ε
  obtain ⟨F, hF, hFα⟩ := GlobalTheory.smoothOnG_exists_contDiff_extension n ε α hα
  have hmem : ∀ g : UJ ε, inUJ ε (umat g) := fun g => g.2
  have hu : Continuous fun g : UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : UJ ε => ⟪u, σ (umat g) s⟫_ℂ :=
    continuous_const.inner ((hcont s).comp_continuous hu hmem)
  have hlift : ∀ x, inUJ ε x → ∃ z : UJ ε, umat z = x := fun x hx => by
    have : x ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [show Set.range (fun g : UJ ε => umat g) = _ from hrange]; exact hx
    exact this
  have hinv : ∀ z : UJ ε, Jm ε * (umat z)ᴴ * Jm ε = umat z⁻¹ := fun z => by
    have h : (umat z)ᴴ * Jm ε * umat z = Jm ε := hmem z
    have i2 : umat z * umat z⁻¹ = 1 := Units.mul_inv _
    calc Jm ε * (umat z)ᴴ * Jm ε = Jm ε * (umat z)ᴴ * Jm ε * (umat z * umat z⁻¹) := by rw [i2, Matrix.mul_one]
      _ = Jm ε * ((umat z)ᴴ * Jm ε * umat z) * umat z⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Jm_mul_self, Matrix.one_mul]
  have hform : ∀ z : UJ ε, ⟪u, σ (umat z) v⟫_ℂ
      = ∫ g : UJ ε, α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro z
    rw [← ContinuousLinearMap.adjoint_inner_left, ← hfix,
      ← integral_mul_left_eq_self (fun g : UJ ε => α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = umat z * umat g := rfl
    simp only [inv_mul_cancel_left, e]
    rw [hmul _ (hmem z) _ (hmem g), ContinuousLinearMap.adjoint_inner_left]
    rfl
  intro g₀ hg₀
  have hC : IsCompact ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) :=
    hemb.isCompact_preimage (isCompact_closedBall g₀ 1)
  have hK := hC.mul hαc
  set K := ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) * tsupport (fun g : UJ ε => α (umat g))
  have hΨ : ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
      F (fun i j => (Jm ε * z.1ᴴ * Jm ε * z.2.1) i j) * z.2.2 := by
    refine ContDiff.mul (hF.comp ?_) (contDiff_snd.comp contDiff_snd)
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    have e1 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        star (z.1 a b) := fun a b =>
      Complex.conjCLE.contDiff.comp ((contDiff_apply_apply ℝ a b).comp contDiff_fst)
    have e2 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        z.2.1 a b := fun a b =>
      (contDiff_apply_apply ℝ a b).comp (contDiff_fst.comp contDiff_snd)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiff.sum fun a _ => (ContDiff.sum fun b _ => (ContDiff.sum fun c _ =>
      contDiff_const.mul (e1 _ _)).mul contDiff_const).mul (e2 _ _)
  refine ⟨Metric.ball g₀ 1, fun x => ∫ g in K, F (fun i j => (Jm ε * xᴴ * Jm ε * umat g) i j) *
    ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε), Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_, ?_⟩
  · exact (contDiff_infty.2 fun m =>
      GlobalTheory.GardingVec.contDiff_setIntegral_nat (muG ε) hK (hu.prodMk hb) m _ hΨ).contDiffOn
  · intro x hx hxJ
    obtain ⟨z, rfl⟩ := hlift x hxJ
    have e : ∀ g : UJ ε, F (fun i j => (Jm ε * (umat z)ᴴ * Jm ε * umat g) i j) = α (umat (z⁻¹ * g)) := fun g => by
      rw [hinv]; exact hFα _ (hmem (z⁻¹ * g))
    simp only [e]
    rw [hform z]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra hne
    exact hg ⟨z, Metric.ball_subset_closedBall hx, z⁻¹ * g,
      subset_tsupport _ fun h => hne (by rw [show α (umat (z⁻¹ * g)) = 0 from h, zero_mul]),
      mul_inv_cancel_left z g⟩

theorem contDiff_fderiv_mul {F : (Fin n → Fin n → ℂ) → ℂ} (hF : ContDiff ℝ ∞ F) (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ => fderiv ℝ F y (X * y : Matrix _ _ ℂ) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ fun y : Fin n → Fin n → ℂ => fun i j => ∑ k, X i k * y k j :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply_apply ℝ k j)
  exact h1.clm_apply h2

theorem garding_step : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s v : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ) → (∀ y, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ)) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ (β : Matrix (Fin n) (Fin n) ℂ → ℂ) (v' : H), SmoothOnG ε β ∧ HasCompactSupport (fun g : UJ ε => β (umat g)) ∧ (∀ y : H, ∫ g : UJ ε, β (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v'⟫_ℂ) ∧ HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
  intro n ε H _ _ _ σ α w v hσ hα hs hw
  refine ⟨smooth_coef hσ hα hs hw, fun X hX => ?_⟩
  obtain ⟨F, hF, hFα⟩ := smoothOnG_exists_contDiff_extension n ε α hα
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hum : ∀ a b : UJ ε, umat (a * b) = umat a * umat b := fun _ _ => rfl
  have hmul : ∀ a b : UJ ε, σ (umat (a * b)) w = σ (umat a) (σ (umat b) w) := by
    intro a b
    rw [hum, hσ.1.2 _ (hmem a) _ (hmem b)]; rfl
  have hc : Continuous fun y : UJ ε => σ (umat y) w := (hσ.2.2 w).comp_continuous hu hmem
  have hFα' : ∀ g : UJ ε, α (umat g) = F (umat g) := fun g => (hFα _ g.2).symm
  have ha : Continuous fun g : UJ ε => α (umat g) := by
    simp only [hFα']; exact hF.continuous.comp hu
  have hint : Integrable (fun y : UJ ε => α (umat y) • σ (umat y) w) (muG ε) :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hw' : ∫ y : UJ ε, α (umat y) • σ (umat y) w ∂(muG ε) = v := by
    refine ext_inner_left ℂ fun u => ?_
    rw [← integral_inner hint, ← hw u]
    simp only [inner_smul_right]
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  let e : ℝ → UJ ε := fun t =>
    ⟨(Matrix.isUnit_exp ((t : ℂ) • X)).unit, exp_indefinite_unitary_holds n ε X hX t⟩
  have hev : ∀ t, umat (e t) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
  have hei : ∀ t, umat (e t)⁻¹ = NormedSpace.exp ((t : ℂ) • (-X)) := fun t => by
    rw [smul_neg, Matrix.exp_neg, ← hev]
    exact Matrix.coe_units_inv _
  have he : Continuous e := by
    rw [(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]
    exact GlobalTheory.GardingVec.continuous_exp_curve X
  have he0 : e 0 = 1 := by
    apply Subtype.ext; apply Units.ext
    show umat (e 0) = 1
    rw [hev]; simp
  have hcE := GlobalTheory.GardingVec.continuous_exp_curve (-X)
  have key := hasDerivAt_orbit (muG ε) (fun g => σ (umat g)) w v hmul hc _ ha hs hw' e he he0
    (fun s y => fderiv ℝ F (NormedSpace.exp ((s : ℂ) • (-X)) * umat y : Matrix _ _ ℂ)
      (NormedSpace.exp ((s : ℂ) • (-X)) * (-X) * umat y : Matrix _ _ ℂ))
    ((hfd.comp ((hcE.comp continuous_fst).matrix_mul (hu.comp continuous_snd))).clm_apply
      (((hcE.comp continuous_fst).matrix_mul continuous_const).matrix_mul (hu.comp continuous_snd)))
    (fun s y => by
      simp only [hFα']
      simp only [hum, hei]
      exact ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s
        (GlobalTheory.GardingVec.hasDerivAt_exp_mul (-X) (umat y) s))
  simp only [hev, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at key
  have hβ := contDiff_fderiv_mul hF (-X)
  refine ⟨fun y => fderiv ℝ F y (-X * y : Matrix _ _ ℂ), _,
    fun g _ => ⟨Set.univ, _, isOpen_univ, trivial, hβ.contDiffOn, fun _ _ _ => rfl⟩, key.1, fun u => ?_, key.2⟩
  have hβi : Integrable (fun y : UJ ε => fderiv ℝ F (umat y) (-X * umat y : Matrix _ _ ℂ) • σ (umat y) w)
      (muG ε) :=
    ((hβ.continuous.comp hu).smul hc).integrable_of_hasCompactSupport key.1.smul_right
  rw [← integral_inner hβi]
  simp only [inner_smul_right]

end GlobalTheory.GardingStep
end
