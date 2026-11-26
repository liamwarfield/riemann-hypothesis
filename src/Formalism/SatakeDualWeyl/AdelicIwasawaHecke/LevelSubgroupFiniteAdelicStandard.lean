module

public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport

@[expose] public section

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Lattice

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type} [Fintype n]
  [DecidableEq n] (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

theorem easyc_inclE_mem (e : E) (he : e ∈ intOE E) :
    inclE (F := F) R e ∈ tensInt (F := F) R (intOE E) S₂ := by
  apply Subring.subset_closure
  left
  exact ⟨⟨e, he⟩, rfl⟩

theorem easyc_single_mem (i : n) :
    (Pi.single i (1 : E) : n → E) ∈ stdLat (n := n) (A := E) (𝓞 E) := by
  rw [mem_stdLat_iff']
  intro k
  by_cases hk : k = i
  · subst hk; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [hk]⟩

theorem easyc_latS_std :
    latS (F := F) R (tensInt (F := F) R (intOE E) S₂) (stdLat (n := n) (A := E) (𝓞 E)) =
      stdLat (n := n) (A := E ⊗[F] R) ↥(tensInt (F := F) R (intOE E) S₂) := by
  apply le_antisymm
  · rw [latS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_stdLat_iff']
    intro i
    have hxi := (mem_stdLat_iff' (R := 𝓞 E) x).1 hx i
    have hm : x i ∈ intOE E := by
      obtain ⟨y, hy⟩ := hxi
      exact ⟨y, hy⟩
    exact ⟨⟨_, easyc_inclE_mem R S₂ (x i) hm⟩, rfl⟩
  · intro x hx
    rw [mem_stdLat_iff'] at hx
    choose s hs using hx
    have hx : x = ∑ i, s i • (fun j => inclE (F := F) R ((Pi.single i (1 : E) : n → E) j)) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single j]
      · simp [← hs j, Algebra.smul_def]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨_, easyc_single_mem i, rfl⟩

end Lattice

theorem level_subgroup_finite_adelic_standard : Formalism.UG.LevelAfLStd := by
  intro F E _ _ _ _ _ n _ _ σ J
  unfold levelAfL levelAf
  rw [easyc_latS_std]

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

section Gen

variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_coe_bc (f : R →+* A) (u : GL n R) :
    ((bc (n := n) f u : GL n A) : Matrix n n A) = (u : Matrix n n R).map f := by
  rfl

theorem levelvsplit_mem_range_iff (f : R →+* A) (hf : Function.Injective f) (g : GL n A) :
    g ∈ (bc (n := n) f).range ↔
      (∀ i j, (g : Matrix n n A) i j ∈ Set.range f) ∧
        ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ Set.range f := by
  constructor
  · intro hg
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hg
    refine ⟨fun i j => ⟨(u : Matrix n n R) i j, rfl⟩, fun i j => ⟨((u⁻¹ : GL n R) : Matrix n n R) i j, ?_⟩⟩
    rw [← map_inv (bc (n := n) f) u]
    rfl
  · rintro ⟨h1, h2⟩
    choose M hM using h1
    choose N hN using h2
    have hinj : Function.Injective (f.mapMatrix : Matrix n n R →+* Matrix n n A) := by
      intro X Y h
      ext i j
      have h' := congrArg (fun Z : Matrix n n A => Z i j) h
      exact hf h'
    have hMg : f.mapMatrix (Matrix.of M) = (g : Matrix n n A) := by
      ext i j
      exact hM i j
    have hNg : f.mapMatrix (Matrix.of N) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j
      exact hN i j
    have e1 : Matrix.of M * Matrix.of N = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.mul_inv])
    have e2 : Matrix.of N * Matrix.of M = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.inv_mul])
    exact MonoidHom.mem_range.mpr ⟨⟨Matrix.of M, Matrix.of N, e1, e2⟩, Units.ext hMg⟩

end Gen

section Split

variable {B K : Type} [CommRing B] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_unitary (τ : B →+* B) (φ : B ≃+* K × K)
    (hτ : ∀ x, φ (τ x) = swapR K (φ x)) (J' : Matrix n n B) (h : GL n B) (hh : h ∈ UJ τ J') :
    ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ *
        J'.map ((RingHom.fst K K).comp φ.toRingHom) *
        (h : Matrix n n B).map ((RingHom.fst K K).comp φ.toRingHom) =
      J'.map ((RingHom.fst K K).comp φ.toRingHom) := by
  have hh' : Formalism.UG.cT τ (h : Matrix n n B) * J' * (h : Matrix n n B) = J' := hh
  have key : (Formalism.UG.cT τ (h : Matrix n n B)).map ((RingHom.fst K K).comp φ.toRingHom) =
      ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ := by
    ext i j
    simp [Formalism.UG.cT, hτ, Formalism.UG.swapR]
  have h2 := congrArg (fun M : Matrix n n B => M.map ((RingHom.fst K K).comp φ.toRingHom)) hh'
  simp only [Matrix.map_mul] at h2
  rw [key] at h2
  exact h2

theorem levelvsplit_solve (A Ainv P1 P1i P2 : Matrix n n K) (hA : A * Ainv = 1)
    (hP : P1 * P1i = 1) (hrel : P2ᵀ * A * P1 = A) : P2 = (A * P1i * Ainv)ᵀ := by
  have h1 : P2ᵀ * A = A * P1i := by
    calc P2ᵀ * A = P2ᵀ * A * (P1 * P1i) := by rw [hP, Matrix.mul_one]
      _ = P2ᵀ * A * P1 * P1i := by simp only [Matrix.mul_assoc]
      _ = A * P1i := by rw [hrel]
  have h2 : P2ᵀ = A * P1i * Ainv := by
    calc P2ᵀ = P2ᵀ * (A * Ainv) := by rw [hA, Matrix.mul_one]
      _ = P2ᵀ * A * Ainv := by rw [Matrix.mul_assoc]
      _ = A * P1i * Ainv := by rw [h1]
  rw [← h2, Matrix.transpose_transpose]

end Split

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelv
noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem levelv_relIndex_ne_zero {G : Type*} [Group G] (H K : Subgroup G) {β : Type*} [Finite β]
    (f : G → β) (hf : ∀ a ∈ K, ∀ b ∈ K, f a = f b → a⁻¹ * b ∈ H) : H.relIndex K ≠ 0 := by
  classical
  have hfin : Finite (K ⧸ H.subgroupOf K) := by
    refine Finite.of_surjective
      (fun y : Set.range (fun k : K => f k) =>
        (QuotientGroup.mk (Set.mem_range.mp y.2).choose : K ⧸ H.subgroupOf K)) ?_
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨f k, k, rfl⟩, ?_⟩
    beta_reduce
    have hc := (Set.mem_range.mp (⟨k, rfl⟩ : f k ∈ Set.range (fun k : K => f k))).choose_spec
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hf _ (Set.mem_range.mp (⟨k, rfl⟩ : f k ∈ Set.range (fun k : K => f k))).choose.2 _ k.2 hc
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

section Local

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev lvS (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

theorem levelv_tmul_mem (e : E) (he : e ∈ intOE E) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : e ⊗ₜ[F] x ∈ lvS F E v := by
  have h1 : e ⊗ₜ[F] (1 : v.adicCompletion F) ∈ lvS F E v := by
    apply Subring.subset_closure
    exact Set.mem_union_left _ ⟨⟨e, he⟩, rfl⟩
  have h2 : (1 : E) ⊗ₜ[F] x ∈ lvS F E v := by
    apply Subring.subset_closure
    exact Set.mem_union_right _ ⟨⟨x, hx⟩, rfl⟩
  simpa using mul_mem h1 h2

def levelvPsi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) →+
      E ⊗[F] v.adicCompletion F :=
  AddMonoidHom.mk' (fun a => ∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
      ((a i : v.adicCompletionIntegers F) : v.adicCompletion F))
    (by intro a a'; simp [tmul_add, Finset.sum_add_distrib])

theorem levelv_tmul_mem_range (e : 𝓞 E) (x : v.adicCompletionIntegers F) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] (x : v.adicCompletion F) ∈ (levelvPsi F E v).range := by
  classical
  let φ : 𝓞 E →+ E ⊗[F] v.adicCompletion F :=
    AddMonoidHom.mk' (fun y => algebraMap (𝓞 E) E y ⊗ₜ[F] (x : v.adicCompletion F))
      (by intro a b; simp [TensorProduct.add_tmul])
  have hb : ∀ i, φ (RingOfIntegers.basis E i) ∈ (levelvPsi F E v).range := by
    intro i
    refine AddMonoidHom.mem_range.mpr ⟨Pi.single i x, ?_⟩
    simp only [levelvPsi, AddMonoidHom.mk'_apply, φ]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  show φ e ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (RingOfIntegers.basis E).sum_repr e, map_sum]
  exact sum_mem fun i _ => by rw [map_zsmul]; exact zsmul_mem (hb i) _

theorem levelv_mul_mem_range (y y' : E ⊗[F] v.adicCompletion F)
    (hy : y ∈ (levelvPsi F E v).range) (hy' : y' ∈ (levelvPsi F E v).range) :
    y * y' ∈ (levelvPsi F E v).range := by
  have hPsi : ∀ c, levelvPsi F E v c = ∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
      ((c i : v.adicCompletionIntegers F) : v.adicCompletion F) := fun c => rfl
  obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hy
  obtain ⟨a', rfl⟩ := AddMonoidHom.mem_range.mp hy'
  rw [hPsi, hPsi]
  simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  first
    | simpa using levelv_tmul_mem_range v (RingOfIntegers.basis E i * RingOfIntegers.basis E j) (a i * a' j)
    | simpa using levelv_tmul_mem_range v (RingOfIntegers.basis E j * RingOfIntegers.basis E i) (a j * a' i)

def levelvT (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) where
  carrier := (levelvPsi F E v).range
  mul_mem' := levelv_mul_mem_range v _ _
  one_mem' := by
    have h1 : (1 : E ⊗[F] v.adicCompletion F) = algebraMap (𝓞 E) E 1 ⊗ₜ[F]
        ((1 : v.adicCompletionIntegers F) : v.adicCompletion F) := by rw [map_one]; rfl
    rw [h1]
    exact levelv_tmul_mem_range v 1 1
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem

theorem levelv_S_le_range (y : E ⊗[F] v.adicCompletion F) (hy : y ∈ lvS F E v) :
    y ∈ (levelvPsi F E v).range := by
  have hle : lvS F E v ≤ levelvT F E v := by
    apply Subring.closure_le.mpr
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨x, hx⟩, rfl⟩)
    · obtain ⟨e', rfl⟩ := RingHom.mem_range.mp he
      show algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : v.adicCompletion F) ∈ (levelvPsi F E v).range
      simpa using levelv_tmul_mem_range v e' 1
    · show (1 : E) ⊗ₜ[F] x ∈ (levelvPsi F E v).range
      have h := levelv_tmul_mem_range (E := E) v 1 ⟨x, hx⟩
      first
        | exact h
        | (rw [map_one] at h; exact h)
        | simpa using h
  exact hle hy

theorem levelv_denom (y : E ⊗[F] v.adicCompletion F) : ∃ N : ℕ, N ≠ 0 ∧ N • y ∈ lvS F E v := by
  classical
  have h1 : ∀ (m : ℕ) (e : E) (x : v.adicCompletion F), m • (e ⊗ₜ[F] x) = (m • e) ⊗ₜ[F] x :=
    fun m e x => (map_nsmul ((TensorProduct.mk F E (v.adicCompletion F)).flip x) m e).symm
  have h2 : ∀ (m : ℕ) (e : E) (x : v.adicCompletion F), m • (e ⊗ₜ[F] x) = e ⊗ₜ[F] (m • x) :=
    fun m e x => (map_nsmul (TensorProduct.mk F E (v.adicCompletion F) e) m x).symm
  have hE : ∀ e : E, ∃ M : ℕ, M ≠ 0 ∧ M • e ∈ intOE E := by
    intro e
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
    refine ⟨Ideal.absNorm (Ideal.span {s}), ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hs0
    · refine RingHom.mem_range.mpr ⟨t * a, ?_⟩
      have hs' : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      rw [nsmul_eq_mul, ← map_natCast (algebraMap (𝓞 E) E), ← ht, map_mul, map_mul]
      field_simp <;> ring
  have hF : ∀ x : v.adicCompletion F, ∃ N : ℕ, N ≠ 0 ∧ N • x ∈ v.adicCompletionIntegers F := by
    intro x
    obtain ⟨b, hb, hbx⟩ :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hb0
    · have hcv : algebraMap (𝓞 F) (v.adicCompletion F) c ∈ v.adicCompletionIntegers F :=
        (algebraMap (𝓞 F) (v.adicCompletionIntegers F) c).2
      have key : Ideal.absNorm (Ideal.span {b}) • x = algebraMap (𝓞 F) (v.adicCompletion F) c *
          (x * algebraMap (𝓞 F) (v.adicCompletion F) b) := by
        rw [nsmul_eq_mul, ← map_natCast (algebraMap (𝓞 F) (v.adicCompletion F)), ← hc, map_mul]
        ring
      rw [key]
      exact mul_mem hcv hbx
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | tmul e x =>
    obtain ⟨M, hM0, hM⟩ := hE e
    obtain ⟨N, hN0, hN⟩ := hF x
    refine ⟨M * N, mul_ne_zero hM0 hN0, ?_⟩
    rw [mul_smul, h2, h1]
    exact levelv_tmul_mem v _ hM _ hN
  | add y z hy hz =>
    obtain ⟨M, hM0, hM⟩ := hy
    obtain ⟨N, hN0, hN⟩ := hz
    refine ⟨M * N, mul_ne_zero hM0 hN0, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hM _
    · rw [mul_smul]
      exact nsmul_mem hN _

theorem levelv_denom_family {ι : Type*} [Fintype ι] (a : ι → E ⊗[F] v.adicCompletion F) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ i, N • a i ∈ lvS F E v := by
  classical
  choose M hM0 hM using fun i => levelv_denom v (a i)
  refine ⟨∏ i, M i, Finset.prod_ne_zero_iff.mpr fun i _ => hM0 i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ M (Finset.mem_univ i), mul_smul]
  exact nsmul_mem (hM i) _

end Local

section Lattice

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]

end Lattice

section GLact

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

end GLact


end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem conv_mul_right {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₂ : IsBiInv K f₂) (g : G) (b : K) : conv K f₁ f₂ (g * b) = conv K f₁ f₂ g := by
  unfold conv
  congr 1
  funext x
  have h := hf₂ 1 b (x.out⁻¹ * g)
  simp only [OneMemClass.coe_one, one_mul] at h
  rw [← mul_assoc, h]

theorem conv_mul_left {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) (a : K) (g : G) :
    conv K f₁ f₂ ((a : G) * g) = conv K f₁ f₂ g := by
  have key : ∀ y : G ⧸ K, ∃ c : K, ((a : G) • y).out = (a : G) * y.out * c := by
    intro y
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * y.out)
    refine ⟨c, ?_⟩
    have e : (a : G) • y = (QuotientGroup.mk ((a : G) * y.out) : G ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [e, hc]
  unfold conv
  refine (finsum_comp_equiv (MulAction.toPerm (a : G) : Equiv.Perm (G ⧸ K))).symm.trans ?_
  congr 1
  funext y
  obtain ⟨c, hc⟩ := key y
  simp only [MulAction.toPerm_apply]
  rw [hc, hf₁ a c y.out]
  have e2 : ((a : G) * y.out * c)⁻¹ * ((a : G) * g) = ((c⁻¹ : K) : G) * (y.out⁻¹ * g) * ((1 : K) : G) := by
    simp only [InvMemClass.coe_inv, OneMemClass.coe_one, mul_one]
    group
  rw [e2, hf₂]

theorem conv_biInv {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : IsBiInv K (conv K f₁ f₂) := by
  intro a b g
  rw [conv_mul_right K f₁ f₂ hf₂ ((a : G) * g) b, conv_mul_left K f₁ f₂ hf₁ hf₂ a g]

theorem conv_finDosetSupp {k : Type} [CommRing k] {K : Subgroup G} (hK : IsCommensurated K)
    (f₁ f₂ : G → k) (hs₁ : FinDosetSupp K f₁) (hs₂ : FinDosetSupp K f₂) :
    FinDosetSupp K (conv K f₁ f₂) := by
  classical
  have hX := finite_support_cosets hK hs₁
  obtain ⟨S₂, hS₂⟩ := hs₂
  set T : Set G := ⋃ t ∈ (S₂ : Set G), ⋃ x ∈ {x : G ⧸ K | f₁ x.out ≠ 0},
    ⋃ y ∈ {y : G ⧸ K | ∃ a b : K, y.out = (a : G) * t * b}, {x.out * y.out} with hTdef
  have hT : T.Finite :=
    S₂.finite_toSet.biUnion fun t _ => hX.biUnion fun x _ =>
      (finite_cosets_in_doset hK t).biUnion fun y _ => Set.finite_singleton _
  refine ⟨hT.toFinset, fun g hg => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg (finsum_eq_zero_of_forall_eq_zero h)
  have h1 : f₁ x.out ≠ 0 := left_ne_zero_of_mul hx
  have h2 : f₂ (x.out⁻¹ * g) ≠ 0 := right_ne_zero_of_mul hx
  obtain ⟨t, ht, a, b, hab⟩ := hS₂ _ h2
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * t)
  refine ⟨x.out * (QuotientGroup.mk ((a : G) * t) : G ⧸ K).out, ?_, 1, c⁻¹ * b, ?_⟩
  · rw [Set.Finite.mem_toFinset, hTdef]
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨t, ht, x, h1, _, ⟨a, c, hc⟩, rfl⟩
  · rw [hc]
    have e : g = x.out * (x.out⁻¹ * g) := by group
    rw [e, hab]
    simp only [OneMemClass.coe_one, one_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
    group

theorem hecke_convolution_mem_holds : Formalism.UG.HeckeConvMem := by
  intro G _ K k _ hK f₁ hf₁ f₂ hf₂
  have h1 : IsBiInv K f₁ ∧ FinDosetSupp K f₁ := hf₁
  have h2 : IsBiInv K f₂ ∧ FinDosetSupp K f₂ := hf₂
  show IsBiInv K (conv K f₁ f₂) ∧ FinDosetSupp K (conv K f₁ f₂)
  exact ⟨conv_biInv K f₁ f₂ h1.1 h2.1, conv_finDosetSupp hK f₁ f₂ h1.2 h2.2⟩

theorem convolution_count_holds : Formalism.UG.ConvCount := by
  classical
  intro G _ K k _ hK a b g
  set S : Set (G ⧸ K) := {x : G ⧸ K | x.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ∧
    x.out⁻¹ * g ∈ DoubleCoset.doubleCoset b (K : Set G) K} with hSdef
  have hfin : S.Finite := by
    refine (finite_cosets_in_doset hK a).subset fun x hx => ?_
    obtain ⟨h, hh, c, hc, e⟩ := DoubleCoset.mem_doubleCoset.1 hx.1
    exact ⟨⟨h, hh⟩, ⟨c, hc⟩, e⟩
  have hterm : ∀ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) =
      if x ∈ S then 1 else 0 := by
    intro x
    simp only [dosetInd, Set.indicator_apply, Pi.one_apply, hSdef, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  show ∑ᶠ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) = _
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [Finset.sum_congr rfl (fun x hx => if_pos (hfin.mem_toFinset.1 hx))]
    simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hx (if_neg h)

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SphericalA
open NumberField IsDedekindDomain Formalism.UG

namespace Formalism.UG.P

section Upper

variable {L : Type} [Field L] {n : ℕ}

theorem spherical_upper_iff (b : GL (Fin n) L) :
    (∀ i j : Fin n, j < i → (b : Matrix (Fin n) (Fin n) L) i j = 0) ↔
      (b : Matrix (Fin n) (Fin n) L).BlockTriangular id :=
  ⟨fun h _ _ hij => h _ _ hij, fun h _ _ hij => h hij⟩

theorem spherical_diag_mul (A B : Matrix (Fin n) (Fin n) L) (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hji => ?_) (by simp)
  rcases lt_or_gt_of_ne hji with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem spherical_upper_inv (b : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  have : Invertible (b : Matrix (Fin n) (Fin n) L) := Units.invertible b
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem spherical_upper_mul (b c : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hc : (c : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((b * c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  rw [Units.val_mul]; exact hb.mul hc

theorem spherical_diag_ne_zero (b : GL (Fin n) L) (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (i : Fin n) : (b : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  have hd : (b : Matrix (Fin n) (Fin n) L).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
    exact this.ne_zero
  rw [Matrix.det_of_isUpperTriangular hb] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

end Upper

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem spherical_ordV_mul (x y : v.adicCompletion F)
    (hx : x ≠ 0) (hy : y ≠ 0) : ordV F v (x * y) = ordV F v x + ordV F v y := by
  unfold ordV
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hxy : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  rw [dite_eq_right hx', dite_eq_right hy', dite_eq_right hxy]
  have : WithZero.unzero hxy = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective; simp [WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]; ring

theorem spherical_ordV_unit (x y : v.adicCompletion F) (hx : x ∈ Ov F v) (hy : y ∈ Ov F v)
    (hxy : y * x = 1) : ordV F v x = 0 := by
  have hx1 : Valued.v x ≤ 1 := hx
  have hy1 : Valued.v y ≤ 1 := hy
  have hm : Valued.v y * Valued.v x = 1 := by rw [← map_mul, hxy, map_one]
  have h1 : Valued.v x = 1 := by
    refine le_antisymm hx1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v y * Valued.v x := hm.symm
      _ ≤ 1 * Valued.v x := mul_le_mul' hy1 le_rfl
      _ = Valued.v x := one_mul _
  unfold ordV
  have h0 : Valued.v x ≠ 0 := by rw [h1]; exact one_ne_zero
  rw [dite_eq_right h0]
  have : WithZero.unzero h0 = 1 := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, h1]; rfl
  rw [this]; rfl

theorem spherical_qV_ne_zero : (qV F v : ℂ) ≠ 0 := by
  unfold qV
  rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

theorem spherical_chiDelta_mul {n : ℕ} (α : Fin n → ℂ) (hα : ∀ i, α i ≠ 0) (b c : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hc : (c : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id) :
    chiDelta F v α (b * c) = chiDelta F v α b * chiDelta F v α c := by
  unfold chiDelta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_mul, spherical_diag_mul _ _ hb hc i,
    spherical_ordV_mul F v _ _ (spherical_diag_ne_zero b hb i) (spherical_diag_ne_zero c hc i)]
  have hq := spherical_qV_ne_zero F v
  rw [zpow_add₀ (hα i)]
  push_cast
  rw [show (-((ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) +
      (ordV F v ((c : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ)) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
      = (-(ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
        + (-(ordV F v ((c : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
      by ring, Complex.cpow_add _ _ hq]
  ring

theorem spherical_chiDelta_int {n : ℕ} (α : Fin n → ℂ) (b : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hk : b ∈ GLint (Fin n) (Ov F v)) : chiDelta F v α b = 1 := by
  obtain ⟨k, rfl⟩ := hk
  unfold chiDelta
  refine Finset.prod_eq_one fun i _ => ?_
  have hinv := spherical_upper_inv _ hb
  have hm : ((((bc (n := Fin n) (Ov F v).subtype) k)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i *
      (((bc (n := Fin n) (Ov F v).subtype) k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i = 1 := by
    rw [← spherical_diag_mul _ _ hinv hb, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  have h0 : ordV F v ((((bc (n := Fin n) (Ov F v).subtype) k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) = 0 := by
    refine spherical_ordV_unit F v _ _ ?_ ?_ hm
    · simp only [bc, Units.coe_map]
      exact ((k : Matrix (Fin n) (Fin n) (Ov F v)) i i).2
    · rw [← map_inv (bc (n := Fin n) (Ov F v).subtype) k]
      simp only [bc, Units.coe_map]
      exact (((k⁻¹ : GL (Fin n) (Ov F v)) : Matrix (Fin n) (Fin n) (Ov F v)) i i).2
  rw [h0]; simp

end Formalism.UG.P
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA
open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem fSatake_nontriv {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) :
    (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial := by
  obtain ⟨-, -, -, hv, -⟩ := hU
  refine ⟨ϖ, ?_, ?_⟩
  · rw [hv]; exact WithZero.coe_ne_zero
  · rw [hv]
    intro h1
    have := WithZero.coe_injective (h1.trans WithZero.coe_one.symm)
    exact absurd (Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)) (by norm_num)

theorem isCommensurated_integral_unitary_of_unramified {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    IsCommensurated (KU σ n) := by
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    fSatake_nontriv hU
  obtain ⟨-, -, -, hvϖ, -, hq2, hq⟩ := hU
  set A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring with hA
  haveI : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
    isCyclic_of_surjective (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).symm.toMonoidHom
      (MulEquiv.surjective _)
  haveI hD : IsDiscreteValuationRing ↥A.toSubring := Valuation.valuationSubring_isDiscreteValuationRing _
  have hRes : Finite (IsLocalRing.ResidueField ↥A.toSubring) := by
    apply Nat.finite_of_card_ne_zero
    rw [show Nat.card (IsLocalRing.ResidueField ↥A.toSubring) = q ^ 2 from hq]
    exact pow_ne_zero 2 (by omega)
  intro g
  obtain ⟨c, hc0, hg1, hg2⟩ := Formalism.UG.P.glint_exists_denom A (g : GL (Fin n) L)
  haveI : Finite (↥A.toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hRes _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact mul_ne_zero hc0 hc0)
  have hO : intL L = A.toSubring := rfl
  unfold KU
  rw [hO]
  have hK : intPts A.toSubring.subtype (GU σ n) = GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range := rfl
  rw [hK]
  have hmap : ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).subgroupOf (GU σ n)).map (MulAut.conj g).toMonoidHom =
      ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom).subgroupOf (GU σ n) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy.1⟩, hy, Subtype.ext (by simpa using hyx)⟩
  rw [hmap, Subgroup.relIndex_subgroupOf inf_le_left]
  have hPB := glint_princ_relIndex_ne_zero (n := Fin n) A.toSubring (Ideal.span {c * c})
  have h1 : (princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n).relIndex
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range) ≠ 0 := by
    rw [inf_comm (GU σ n) (bc (n := Fin n) A.toSubring.subtype).range]
    exact Subgroup.relIndex_inter_ne_zero hPB (GU σ n)
  have hle : princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n ≤
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom := by
    rintro h ⟨hP, hHh⟩
    obtain ⟨b, hb, hbh⟩ := glint_princ_le_map_conj A.toSubring (g : GL (Fin n) L) c hg1 hg2 hP
    refine ⟨b, ⟨?_, hb⟩, hbh⟩
    have hbe : b = (g : GL (Fin n) L)⁻¹ * h * g := by
      rw [← hbh]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hbe]
    exact (GU σ n).mul_mem ((GU σ n).mul_mem ((GU σ n).inv_mem g.2) hHh) g.2
  exact fun hz => h1 (Subgroup.relIndex_eq_zero_of_le_left hle hz)

theorem fSatake_v_eq {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

private lemma ordL_eq_of_valuation_eq {x : L} (hx : x ≠ 0) {k : ℤ}
    (h : Valued.v x = ((Multiplicative.ofAdd (-k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = k := by
  rw [fSatake_v_eq hx] at h
  have h2 := WithZero.coe_injective h
  have h3 := Multiplicative.ofAdd.injective h2
  linarith

theorem fSatake_ord_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  apply ordL_eq_of_valuation_eq (mul_ne_zero hx hy)
  rw [map_mul, fSatake_v_eq hx, fSatake_v_eq hy, ← WithZero.coe_mul, ← ofAdd_add, neg_add]

theorem fSatake_ord_one : ordL (1 : L) = 0 := by
  apply ordL_eq_of_valuation_eq one_ne_zero
  simp

theorem fSatake_ord_of_v {x y : L} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

theorem fSatake_ord_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (k : ℤ) : ordL (ϖ ^ k) = k := by
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  apply ordL_eq_of_valuation_eq (zpow_ne_zero k h0)
  rw [map_zpow₀, hϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  simp

theorem fSatake_ord_nonneg {x : L} (hx : x ≠ 0) (hO : x ∈ intL L) : 0 ≤ ordL x := by
  have h1 : Valued.v x ≤ 1 := hO
  rw [fSatake_v_eq hx, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_le] at h1
  linarith

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitA
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace Formalism.UG.P
open Formalism.UG

section Adele
variable {F : Type} [Field F] [NumberField F]

theorem afsplit_add_apply (a b : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) : (a + b) w = a w + b w := rfl
theorem afsplit_mul_apply (a b : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) : (a * b) w = a w * b w := rfl
theorem afsplit_sub_apply (a b : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := rfl
theorem afsplit_one_apply (w : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸ᶠ[F]) w = 1 := rfl
theorem afsplit_zero_apply (w : HeightOneSpectrum (𝓞 F)) : (0 : 𝔸ᶠ[F]) w = 0 := rfl
theorem afsplit_smul_apply (c : F) (a : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) :
    (c • a) w = c • a w := by
  rw [Algebra.smul_def, afsplit_mul_apply, Algebra.smul_def]; rfl

def afsplitF (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : 𝔸ᶠ[F] := by
  classical
  exact ⟨Pi.single v x, by
    filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) ∈ Filter.cofinite by simp] with w hw
    rw [Set.mem_compl_singleton_iff] at hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _⟩

theorem afsplitF_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : afsplitF v x v = x := by
  classical
  show Pi.single v x v = x
  convert Pi.single_eq_same v x

theorem afsplitF_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) :
    afsplitF v x w = 0 := by
  classical
  show Pi.single v x w = 0
  convert Pi.single_eq_of_ne h x

def afsplitI (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →ₗ[F] 𝔸ᶠ[F] where
  toFun := afsplitF v
  map_add' x y := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_add_apply, afsplitF_self]
    · simp only [afsplit_add_apply, afsplitF_ne v w h, add_zero]
  map_smul' c x := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_smul_apply, afsplitF_self, RingHom.id_apply]
    · simp only [afsplit_smul_apply, afsplitF_ne v w h, smul_zero, RingHom.id_apply]

theorem afsplitI_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : afsplitI v x v = x :=
  afsplitF_self v x

theorem afsplitI_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) :
    afsplitI v x w = 0 := afsplitF_ne v w h x

theorem afsplitI_mul (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    afsplitI v (x * y) = afsplitI v x * afsplitI v y := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, mul_zero]

theorem afsplitI_eval (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸ᶠ[F]) :
    afsplitI v (a v) = afsplitI v 1 * a := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self, one_mul]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, zero_mul]

theorem afsplitI_mem_intAd (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : afsplitI v x ∈ intAd F := by
  intro w
  by_cases h : w = v
  · subst h; rw [afsplitI_self]; exact hx
  · rw [afsplitI_ne v w h]; exact zero_mem _

end Adele
end Formalism.UG.P
end
end
