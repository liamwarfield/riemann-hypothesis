module

public import Formalism.SatakeDualWeyl.StatementC

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.LevelCharts.AtGGlob
section -- merged from Formalism.LocalToGlobal.GroupLattices.LevelCharts.SignBlockDeterminant
noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Bar

variable {κ : Type} [CommRing κ] {N : ℕ} {a t : ℕ}

def entN (M : Matrix (Fin N) (Fin N) κ) (x y : ℕ) : κ := if h : x < N ∧ y < N then M ⟨x, h.1⟩ ⟨y, h.2⟩ else 0

end Bar

section Cong

variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem bc_injective (ι : R →+* A) (h : Function.Injective ι) : Function.Injective (bc (n := n) ι) := by
  intro x y hxy
  apply Units.ext
  have h2 : (x : Matrix n n R).map ι = (y : Matrix n n R).map ι := congrArg Units.val hxy
  exact Matrix.map_injective h h2

def congChar {Z : Type} [Group Z] (ι : R →+* A) (hι : Function.Injective ι) (I : Ideal R) (H : Subgroup (GL n (R ⧸ I)))
    (lam : H →* Z) : congPre ι I H →* Z :=
  (lam.comp ((redGL I).subgroupComap H)).comp
    ((H.comap (redGL I)).equivMapOfInjective (bc ι) (bc_injective ι hι)).symm.toMonoidHom

end Cong

section Loc

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev resV : Type := (v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)

theorem algMapV_injective :
    Function.Injective (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) :=
  fun _ _ h => Subtype.ext h

end Loc

section Uni

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (v : HeightOneSpectrum (𝓞 F))
  (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (fr : GL (Fin N) (v.adicCompletion F))

def toFr : GL (Fin N) (E ⊗[F] v.adicCompletion F) →* GL (Fin N) (v.adicCompletion F) :=
  (MulAut.conj fr⁻¹).toMonoidHom.comp (bc ((RingHom.fst _ _).comp spl.toRingHom))

theorem toFr_apply (x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
    toFr v spl fr x = fr⁻¹ * bc ((RingHom.fst _ _).comp spl.toRingHom) x * fr := by
  show (MulAut.conj fr⁻¹) (bc ((RingHom.fst _ _).comp spl.toRingHom) x) = _
  rw [MulAut.conj_apply, inv_inv]

end Uni

end Formalism.L2.G
end
end

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Places

variable (F : Type) [Field F] [NumberField F]

theorem finite_placesOver (g : ℕ) (hg : g ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ((g : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((g : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)


open Classical in
def placesOver (g : ℕ) : Finset (HeightOneSpectrum (𝓞 F)) := by
  classical
  exact if h : {v : HeightOneSpectrum (𝓞 F) | ((g : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite then
    h.toFinset else ∅

theorem mem_placesOver (g : ℕ) (hg : g ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ placesOver F g ↔ ((g : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [placesOver, dite_eq_left (finite_placesOver F g hg)]
  simp

end Places

section Prod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

def prodChar {Z : Type} [CommGroup Z] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (lam : ∀ v, v ∈ S → (Uloc v →* Z)) (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (h : ∀ v ∈ S, Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ v ∈ S.attach, (lam v.1 v.2).comp
    (((bc (prV (E := E) v.1)).subgroupComap (Uloc v.1)).comp (Subgroup.inclusion (h v.1 v.2)))

end Prod

end Formalism.L2.G
end
end

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem not_mem_of_coprime {p g : ℕ} (h : Nat.Coprime p g) (v : HeightOneSpectrum (𝓞 F))
    (hg : ((g : ℕ) : 𝓞 F) ∈ v.asIdeal) : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro hp
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have h1 : ((a * p + b * g : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hg)
  rw [hab, Int.cast_one] at h1
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

variable {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))} {k m t j : ℕ}

end Formalism.L2.G
