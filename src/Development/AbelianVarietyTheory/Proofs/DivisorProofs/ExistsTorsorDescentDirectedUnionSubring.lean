module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapCompAlgebraMap
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.GenFibMap

variable {A A' A'' X X' X'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [CommRing X]
  [CommRing X'] [CommRing X''] [Algebra A X] [Algebra A' X'] [Algebra A'' X'']

theorem submonoid_le (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors A) ≤
      (Algebra.algebraMapSubmonoid (Localization.AtPrime P') (nonZeroDivisors A')).comap
        (Localization.localRingHom P P' χ hP) := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨φ a, hφ a ha, ?_⟩
  simp only [IsScalarTower.algebraMap_apply A X (Localization.AtPrime P),
    IsScalarTower.algebraMap_apply A' X' (Localization.AtPrime P'),
    Localization.localRingHom_to_map, hc]

def genFibMap (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P') :=
  IsLocalization.map (S := GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))
    (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P')) (Localization.localRingHom P P' χ hP)
    (submonoid_le φ χ hc hφ P P' hP)

theorem genFibMap_comp_algebraMap (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) :
    (genFibMap φ χ hc hφ P P' hP).comp
        (algebraMap (Localization.AtPrime P) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))) =
      (algebraMap (Localization.AtPrime P') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P'))).comp
        (Localization.localRingHom P P' χ hP) :=
  IsLocalization.map_comp _

theorem genFibMap_apply (φ : A →+* A') (χ : X →+* X')
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A' X' (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (hP : P = P'.comap χ) (y : X) :
    genFibMap φ χ hc hφ P P' hP
        (algebraMap (Localization.AtPrime P) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P))
          (algebraMap X (Localization.AtPrime P) y)) =
      algebraMap (Localization.AtPrime P') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime P'))
          (algebraMap X' (Localization.AtPrime P') (χ y)) := by
  rw [genFibMap, IsLocalization.map_eq, Localization.localRingHom_to_map]

theorem ext {C : Type} [CommRing C] (P : Ideal X) [P.IsPrime]
    {u v : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime P) →+* C}
    (h : ∀ y : X, u (algebraMap (Localization.AtPrime P) _ (algebraMap X (Localization.AtPrime P) y)) =
      v (algebraMap (Localization.AtPrime P) _ (algebraMap X (Localization.AtPrime P) y))) : u = v := by
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (Localization.AtPrime P) (nonZeroDivisors A))
  apply IsLocalization.ringHom_ext P.primeCompl
  exact RingHom.ext h

theorem genFibMap_comp (φ₁ : A →+* A') (χ₁ : X →+* X')
    (hc₁ : ∀ a, χ₁ (algebraMap A X a) = algebraMap A' X' (φ₁ a))
    (hφ₁ : ∀ a ∈ nonZeroDivisors A, φ₁ a ∈ nonZeroDivisors A')
    (φ₂ : A' →+* A'') (χ₂ : X' →+* X'')
    (hc₂ : ∀ a, χ₂ (algebraMap A' X' a) = algebraMap A'' X'' (φ₂ a))
    (hφ₂ : ∀ a ∈ nonZeroDivisors A', φ₂ a ∈ nonZeroDivisors A'')
    (φ₃ : A →+* A'') (χ₃ : X →+* X'')
    (hc₃ : ∀ a, χ₃ (algebraMap A X a) = algebraMap A'' X'' (φ₃ a))
    (hφ₃ : ∀ a ∈ nonZeroDivisors A, φ₃ a ∈ nonZeroDivisors A'')
    (P : Ideal X) [P.IsPrime] (P' : Ideal X') [P'.IsPrime] (P'' : Ideal X'') [P''.IsPrime]
    (h₁ : P = P'.comap χ₁) (h₂ : P' = P''.comap χ₂) (h₃ : P = P''.comap χ₃)
    (hχ : ∀ y, χ₃ y = χ₂ (χ₁ y)) :
    (genFibMap φ₂ χ₂ hc₂ hφ₂ P' P'' h₂).comp (genFibMap φ₁ χ₁ hc₁ hφ₁ P P' h₁) =
      genFibMap φ₃ χ₃ hc₃ hφ₃ P P'' h₃ := by
  refine ext P (fun y => ?_)
  simp only [RingHom.comp_apply, genFibMap_apply, hχ]

theorem genFibMap_id (φ : A →+* A) (χ : X →+* X)
    (hc : ∀ a, χ (algebraMap A X a) = algebraMap A X (φ a))
    (hφ : ∀ a ∈ nonZeroDivisors A, φ a ∈ nonZeroDivisors A)
    (P : Ideal X) [P.IsPrime] (hP : P = P.comap χ) (hχ : ∀ y, χ y = y) :
    genFibMap φ χ hc hφ P P hP = RingHom.id _ := by
  refine ext P (fun y => ?_)
  simp only [RingHom.id_apply, genFibMap_apply, hχ]

end GlobalTheory.GenFibMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionSurjective
open IsLocalRing Polynomial

namespace GlobalTheory

theorem genFib_colim_surj : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ b : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q), ∃ k x, g k x = b := by
  intro T _ _ ι _ _ 𝒜 hmono hunion E _ _ Q _ Ek _ _ e h he hh hsurj g hg b
  classical
  obtain ⟨⟨z, ⟨m, hm⟩⟩, hb0⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) b
  obtain ⟨c, hc, hcm⟩ := hm
  subst hcm
  obtain ⟨⟨x, ⟨s, hs⟩⟩, hz0⟩ := IsLocalization.mk'_surjective Q.primeCompl z
  simp only at hb0 hz0
  subst hz0
  obtain ⟨k₁, y₁, hy₁⟩ := hsurj x
  obtain ⟨k₂, t₂, ht₂⟩ := hsurj s
  obtain ⟨k₃, hc₃⟩ := hunion c
  obtain ⟨k₁₂, h1, h2⟩ := directed_of (· ≤ ·) k₁ k₂
  obtain ⟨k, h12, h3⟩ := directed_of (· ≤ ·) k₁₂ k₃
  have hk1 : k₁ ≤ k := h1.trans h12
  have hk2 : k₂ ≤ k := h2.trans h12
  set y := h k₁ k hk1 y₁
  set t := h k₂ k hk2 t₂
  have hy : e k y = x := by rw [hh, hy₁]
  have ht : e k t = s := by rw [hh, ht₂]
  have htQ : t ∈ (Q.comap (e k)).primeCompl := by
    show t ∉ Q.comap (e k)
    rw [Ideal.mem_comap, ht]; exact hs
  set c' : 𝒜 k := ⟨c, hmono h3 hc₃⟩
  have hc' : c' ∈ nonZeroDivisors (𝒜 k) := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    apply nonZeroDivisors.ne_zero hc
    have := congrArg (fun a : 𝒜 k => (a : T)) h0
    simpa [c'] using this
  set z' : (Localization.AtPrime (Q.comap (e k))) := IsLocalization.mk' (Localization.AtPrime (Q.comap (e k))) y ⟨t, htQ⟩
  set m' : (Localization.AtPrime (Q.comap (e k))) := algebraMap (𝒜 k) (Localization.AtPrime (Q.comap (e k))) c'
  have hm' : m' ∈ Algebra.algebraMapSubmonoid (Localization.AtPrime (Q.comap (e k))) (nonZeroDivisors (𝒜 k)) := ⟨c', hc', rfl⟩
  refine ⟨k, IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩, ?_⟩
  have hu1 : IsUnit (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c)) :=
    IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
      (⟨algebraMap T (Localization.AtPrime Q) c, c, hc, rfl⟩ : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T))
  have hu2 : IsUnit (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) :=
    (IsLocalization.map_units (Localization.AtPrime Q) (⟨s, hs⟩ : Q.primeCompl)).map _
  have hgm : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) m') = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) := by
    have hm'e : m' = algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) (algebraMap (𝒜 k) (Ek k) c') :=
      IsScalarTower.algebraMap_apply (𝒜 k) (Ek k) (Localization.AtPrime (Q.comap (e k))) c'
    rw [hm'e, hg, he, ← IsScalarTower.algebraMap_apply]
    rfl
  have hgt : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) t)) =
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s) := by rw [hg, ht]
  have hgy : g k (algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by rw [hg, hy]
  have hz' : z' * algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) t = algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y :=
    IsLocalization.mk'_spec (Localization.AtPrime (Q.comap (e k))) y ⟨t, htQ⟩
  have hX : IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩ * algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) m' = algebraMap (Localization.AtPrime (Q.comap (e k))) (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' :=
    IsLocalization.mk'_spec (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩
  have hz : IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩ * algebraMap E (Localization.AtPrime Q) s = algebraMap E (Localization.AtPrime Q) x :=
    IsLocalization.mk'_spec (Localization.AtPrime Q) x ⟨s, hs⟩
  have hb : IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩)
      (⟨algebraMap T (Localization.AtPrime Q) c, c, hc, rfl⟩ : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) *
      algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (IsLocalization.mk' (Localization.AtPrime Q) x ⟨s, hs⟩) :=
    IsLocalization.mk'_spec (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) _ _
  have e1 : b * (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) * algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by
    rw [← hb0, ← mul_assoc, hb, ← map_mul, hz]
  have e2 : g k (IsLocalization.mk' (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))) z' ⟨m', hm'⟩) * (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap T (Localization.AtPrime Q) c) * algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) s)) = algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (algebraMap E (Localization.AtPrime Q) x) := by
    rw [← hgm, ← hgt, ← mul_assoc, ← map_mul, hX, ← map_mul, ← map_mul, hz', hgy]
  exact (hu1.mul hu2).mul_left_inj.mp (e2.trans e1.symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionSurjectiveStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibreLocalization_directedUnion_surjective : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ b : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q), ∃ k x, g k x = b := by
  first | (exact @GlobalTheory.genFib_colim_surj) | (exact GlobalTheory.genFib_colim_surj) | (intros; apply GlobalTheory.genFib_colim_surj  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionKernel
open IsLocalRing Polynomial

namespace GlobalTheory

theorem genFib_colim_ker : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ k, Function.Injective (e k)) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ (f : ∀ k l, k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l)))),
      (∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y))) →
    ∀ k (x : GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))), g k x = 0 →
      ∃ l, ∃ hkl : k ≤ l, f k l hkl x = 0 := by
  intro T _ _ ι _ _ 𝒜 hA hcov E _ _ Q _ Ek _ _ e h he hh heh hinj hsurj g hg f hf k x hx
  classical

  set L := Localization.AtPrime (Q.comap (e k)) with hL
  obtain ⟨⟨z, a'⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid L (nonZeroDivisors (𝒜 k))) x
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Q.comap (e k)).primeCompl z
  dsimp only at hx ⊢
  set G := GlobalTheory.LocAcyc.GenFib (𝒜 k) L
  set X := IsLocalization.mk' G (IsLocalization.mk' L y s) a' with hX
  set v : G := algebraMap L G (a' : L) * algebraMap L G (algebraMap (Ek k) L (s : Ek k)) with hv
  have hvu : IsUnit v := by
    refine (IsLocalization.map_units G a').mul ?_
    exact (IsLocalization.map_units L s).map _
  have hXv : X * v = algebraMap L G (algebraMap (Ek k) L y) := by
    rw [hv, ← mul_assoc, hX, IsLocalization.mk'_spec, ← map_mul, IsLocalization.mk'_spec]

  have hgy : g k (algebraMap L G (algebraMap (Ek k) L y)) = 0 := by
    rw [← hXv, map_mul, hx, zero_mul]
  rw [hg] at hgy

  obtain ⟨⟨m0, hm0⟩, hm0y⟩ := (IsLocalization.map_eq_zero_iff
    (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)) _ _).1 hgy
  obtain ⟨t, ht, rfl⟩ := Submonoid.mem_map.1 hm0
  simp only at hm0y
  rw [IsScalarTower.algebraMap_apply T E (Localization.AtPrime Q), ← map_mul] at hm0y
  obtain ⟨⟨u, hu⟩, huy⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ _).1 hm0y
  simp only at huy
  obtain ⟨m, u', rfl⟩ := hsurj u
  obtain ⟨m', htm'⟩ := hcov t
  obtain ⟨l1, hkl1, hml1⟩ := directed_of (· ≤ ·) k m
  obtain ⟨l, hl1, hm'l⟩ := directed_of (· ≤ ·) l1 m'
  have hkl : k ≤ l := hkl1.trans hl1
  have hml : m ≤ l := hml1.trans hl1
  let c : 𝒜 l := ⟨t, hA hm'l htm'⟩
  have hc0 : c ∈ nonZeroDivisors (𝒜 l) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have : (t : T) = 0 := congrArg Subtype.val h0
    exact nonZeroDivisors.ne_zero ht this
  have hprod : h m l hml u' * (algebraMap (𝒜 l) (Ek l) c * h k l hkl y) = 0 := by
    apply hinj l
    rw [map_mul, map_mul, heh, heh, he, map_zero]
    simpa [mul_assoc] using huy
  have hu'' : h m l hml u' ∈ (Q.comap (e l)).primeCompl := by
    change e l (h m l hml u') ∉ Q
    rw [heh]; exact hu
  set Ll := Localization.AtPrime (Q.comap (e l))
  have h1 : algebraMap (Ek l) Ll (algebraMap (𝒜 l) (Ek l) c * h k l hkl y) = 0 := by
    have := congrArg (algebraMap (Ek l) Ll) hprod
    rw [map_mul, map_zero] at this
    exact ((IsLocalization.map_units Ll ⟨_, hu''⟩).mul_right_eq_zero).1 this
  have h2 : algebraMap Ll (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll) (algebraMap (Ek l) Ll (h k l hkl y)) = 0 := by
    have hcm : algebraMap (𝒜 l) Ll c ∈ Algebra.algebraMapSubmonoid Ll (nonZeroDivisors (𝒜 l)) :=
      Submonoid.mem_map.2 ⟨c, hc0, rfl⟩
    have := congrArg (algebraMap Ll (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll)) h1
    rw [map_mul, map_zero, ← IsScalarTower.algebraMap_apply, map_mul] at this
    exact ((IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib (𝒜 l) Ll) ⟨_, hcm⟩).mul_right_eq_zero).1 this
  refine ⟨l, hkl, ?_⟩
  have hfy : f k l hkl (algebraMap L G (algebraMap (Ek k) L y)) = 0 := by
    rw [hf]; exact h2
  have := congrArg (f k l hkl) hXv
  rw [map_mul, hfy] at this
  exact ((hvu.map (f k l hkl)).mul_left_eq_zero).1 this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionKernelStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibreLocalization_directedUnion_kernel : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ k, Function.Injective (e k)) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ (f : ∀ k l, k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l)))),
      (∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y))) →
    ∀ k (x : GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))), g k x = 0 →
      ∃ l, ∃ hkl : k ≤ l, f k l hkl x = 0 := by
  first | (exact @GlobalTheory.genFib_colim_ker) | (exact GlobalTheory.genFib_colim_ker) | (intros; apply GlobalTheory.genFib_colim_ker  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtalePolynomialModelOfDirectedUnionStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleModelOfDirectedUnion
open IsLocalRing

namespace GlobalTheory.EtaleDescent

open TensorProduct

theorem exists_etale_model_of_directed_union :
    ∀ (R : Type) [CommRing R] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      (Ri : ι → Subring R), Monotone Ri → (∀ x, ∃ i, x ∈ Ri i) →
      ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A],
        ∃ (i : ι) (Ai : Type) (_ : CommRing Ai) (_ : Algebra (Ri i) Ai),
          Algebra.Etale (Ri i) Ai ∧ Nonempty (TensorProduct (Ri i) R Ai ≃ₐ[R] A) := by
  intro R _ ι _ _ _ Ri hmono hcov A _ _ _
  obtain ⟨κ, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := R) (S := A)).mp
      inferInstance |>.out

  have hfin := P.finite_coeffs
  have hex : ∃ i, P.coeffs ⊆ (Ri i : Set R) := by
    classical
    choose j hj using hcov
    obtain ⟨i, hi⟩ := Finset.exists_le (hfin.toFinset.image j)
    refine ⟨i, fun x hx ↦ hmono (hi _ (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hx))) (hj x)⟩
  obtain ⟨i, hi⟩ := hex
  letI : Algebra (Ri i) A := ((algebraMap R A).comp (algebraMap (Ri i) R)).toAlgebra
  haveI : IsScalarTower (Ri i) R A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (Ri i) := ⟨fun x hx ↦ ⟨⟨x, hi hx⟩, rfl⟩⟩
  let Q := P.ofHasCoeffs (Ri i)
  refine ⟨i, P.ModelOfHasCoeffs (Ri i), inferInstance, inferInstance, ?_,
    ⟨P.tensorModelOfHasCoeffsEquiv (Ri i)⟩⟩
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 (Ri i) (P.ModelOfHasCoeffs (Ri i)) :=
    Q.isStandardSmoothOfRelativeDimension (by rw [← hP]; rfl)
  infer_instance

end GlobalTheory.EtaleDescent
end

open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_polynomial_descent_of_directed_union : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra.Etale (Polynomial T) E],
    ∃ (i : ι) (E₀ : Type) (_ : CommRing E₀) (_ : Algebra (Polynomial (𝒜 i)) E₀),
      Algebra.Etale (Polynomial (𝒜 i)) E₀ ∧
      (letI : Algebra (Polynomial (𝒜 i)) (Polynomial T) :=
        (Polynomial.mapRingHom (𝒜 i).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) := by
  intro T _ ι _ _ _ 𝒜 hmono hcov E _ _ _
  let S : ι → Subring (Polynomial T) := fun i ↦ (Polynomial.mapRingHom (𝒜 i).subtype).range
  have hSmono : Monotone S := by
    intro i j hij p hp
    obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
    refine RingHom.mem_range.mpr ⟨q.map (Subring.inclusion (hmono hij)), ?_⟩
    simp only [coe_mapRingHom, Polynomial.map_map]
    rfl
  have hScov : ∀ p, ∃ i, p ∈ S i := by
    classical
    intro p
    choose j hj using hcov
    obtain ⟨i, hi⟩ := Finset.exists_le (p.support.image (fun n ↦ j (p.coeff n)))
    refine ⟨i, ?_⟩
    have hp : p ∈ Polynomial.lifts (𝒜 i).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : n ∈ p.support
      · exact ⟨⟨p.coeff n, hmono (hi _ (Finset.mem_image_of_mem _ hn)) (hj _)⟩, rfl⟩
      · rw [Polynomial.notMem_support_iff.mp hn]
        exact ⟨0, map_zero _⟩
    exact RingHom.mem_range.mpr hp
  obtain ⟨i, E₀, _, _, hE₀, ⟨φ⟩⟩ :=
    GlobalTheory.EtaleDescent.exists_etale_model_of_directed_union (Polynomial T) ι S hSmono hScov E
  let f : Polynomial (𝒜 i) →+* Polynomial T := Polynomial.mapRingHom (𝒜 i).subtype
  have hf : Function.Injective f := Polynomial.map_injective _ Subtype.val_injective
  let e : Polynomial (𝒜 i) ≃+* S i := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h ↦ hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let alg₀ : Algebra (Polynomial (𝒜 i)) E₀ := ((algebraMap (S i) E₀).comp e.toRingHom).toAlgebra
  let _ : Algebra (Polynomial (𝒜 i)) (Polynomial T) := f.toAlgebra
  have hEt : Algebra.Etale (Polynomial (𝒜 i)) E₀ := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.respectsIso.2 (algebraMap (S i) E₀) e
      (RingHom.etale_algebraMap.mpr hE₀)
  have hmapT (p : Polynomial (𝒜 i)) :
      algebraMap (S i) (Polynomial T) (e p) = algebraMap (Polynomial (𝒜 i)) (Polynomial T) p := rfl
  have hmapE (p : Polynomial (𝒜 i)) :
      algebraMap (S i) E₀ (e p) = algebraMap (Polynomial (𝒜 i)) E₀ p := rfl
  have : SMulCommClass (S i) (Polynomial (𝒜 i)) (Polynomial T) :=
    ⟨fun a b x ↦ by simp only [Algebra.smul_def]; ring⟩
  have : TensorProduct.CompatibleSMul (S i) (Polynomial (𝒜 i)) (Polynomial T) E₀ :=
    ⟨fun p m n ↦ by
      rw [Algebra.smul_def, Algebra.smul_def, ← hmapT, ← hmapE, ← Algebra.smul_def, ← Algebra.smul_def,
        TensorProduct.smul_tmul]⟩
  have : TensorProduct.CompatibleSMul (Polynomial (𝒜 i)) (S i) (Polynomial T) E₀ :=
    ⟨fun s m n ↦ by
      obtain ⟨p, rfl⟩ := e.surjective s
      rw [Algebra.smul_def, Algebra.smul_def, hmapT, hmapE, ← Algebra.smul_def, ← Algebra.smul_def,
        TensorProduct.smul_tmul]⟩
  refine ⟨i, E₀, inferInstance, alg₀, hEt, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.equivOfCompatibleSMul (S i) (Polynomial (𝒜 i)) (Polynomial T)
    (Polynomial T) E₀).trans φ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirectedSystemEtaleBaseChangePolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirectedSystemEtaleBaseChangePolynomial
open IsLocalRing Polynomial TensorProduct

namespace GlobalTheory

theorem tensor_directedSystem_of_flat (R : Type) [CommRing R] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] (k₀ : ι) (P : ι → Type) [∀ k, CommRing (P k)]
    [instP : ∀ k, Algebra R (P k)] (Q : Type) [CommRing Q] [Algebra R Q]
    (E₀ : Type) [CommRing E₀] [Algebra R E₀] [Module.Flat R E₀]
    (inc : ∀ k l, k ≤ l → P k →ₐ[R] P l) (sub : ∀ k, P k →ₐ[R] Q)
    (hinc_id : ∀ k (hkk : k ≤ k) (p : P k), inc k k hkk p = p)
    (hinc_comp : ∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (p : P k),
      inc k m hkm p = inc l m hlm (inc k l hkl p))
    (hsub_comp : ∀ k l (hkl : k ≤ l) (p : P k), sub l (inc k l hkl p) = sub k p)
    (hsub_inj : ∀ k, Function.Injective (sub k))
    (hcov : ∀ q : Q, ∃ k p, sub k p = q) :
    ∃ (h : ∀ k l, k ≤ l → P k ⊗[R] E₀ →+* P l ⊗[R] E₀) (e : ∀ k, P k ⊗[R] E₀ →+* Q ⊗[R] E₀),
      (∀ k l (hkl : k ≤ l) (p : P k) (y : E₀), h k l hkl (p ⊗ₜ y) = inc k l hkl p ⊗ₜ y) ∧
      (∀ k (p : P k) (y : E₀), e k (p ⊗ₜ y) = sub k p ⊗ₜ y) ∧
      (∀ k l (hkl : k ≤ l) (y : P k ⊗[R] E₀), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : P k ⊗[R] E₀), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : P k ⊗[R] E₀),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ z : Q ⊗[R] E₀, ∃ k y, e k y = z) := by
  let h : ∀ k l, k ≤ l → P k ⊗[R] E₀ →+* P l ⊗[R] E₀ := fun k l hkl =>
    (Algebra.TensorProduct.map (inc k l hkl) (AlgHom.id R E₀)).toRingHom
  let e : ∀ k, P k ⊗[R] E₀ →+* Q ⊗[R] E₀ := fun k =>
    (Algebra.TensorProduct.map (sub k) (AlgHom.id R E₀)).toRingHom
  have hh : ∀ k l (hkl : k ≤ l) (p : P k) (y : E₀), h k l hkl (p ⊗ₜ y) = inc k l hkl p ⊗ₜ y :=
    fun k l hkl p y => by simp [h]
  have he : ∀ k (p : P k) (y : E₀), e k (p ⊗ₜ y) = sub k p ⊗ₜ y :=
    fun k p y => by simp [e]
  have hcompat : ∀ k l (hkl : k ≤ l) (y : P k ⊗[R] E₀), e l (h k l hkl y) = e k y := by
    intro k l hkl y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, he, he, hsub_comp]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]
  refine ⟨h, e, hh, he, hcompat, ?_, ?_, ?_, ?_⟩
  · intro k hkk y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, hinc_id]
    | add a b ha hb => rw [map_add (f := _), ha, hb]
  · intro k l m hkl hlm hkm y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p z => rw [hh, hh, hh, hinc_comp k l m hkl hlm hkm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  · intro k
    have hfun : ⇑(e k) = ⇑(LinearMap.rTensor E₀ (sub k).toLinearMap) := by
      funext z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul p y => rw [he, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    rw [hfun]
    exact Module.Flat.rTensor_preserves_injective_linearMap _ (hsub_inj k)
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨k₀, 0, map_zero _⟩
    | tmul q y =>
      obtain ⟨k, p, rfl⟩ := hcov q
      exact ⟨k, p ⊗ₜ y, he k p y⟩
    | add a b ha hb =>
      obtain ⟨k₁, y₁, rfl⟩ := ha
      obtain ⟨k₂, y₂, rfl⟩ := hb
      obtain ⟨m, h₁, h₂⟩ := directed_of (· ≤ ·) k₁ k₂
      exact ⟨m, h k₁ m h₁ y₁ + h k₂ m h₂ y₂, by rw [map_add (f := _), hcompat, hcompat]⟩

theorem directedSystem_etaleBaseChange : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (i₀ : ι), (∀ k, i₀ ≤ k) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E]
      (E₀ : Type) [CommRing E₀] [Algebra (Polynomial (𝒜 i₀)) E₀] [Algebra.Etale (Polynomial (𝒜 i₀)) E₀],
      (letI : Algebra (Polynomial (𝒜 i₀)) (Polynomial T) :=
          (Polynomial.mapRingHom (𝒜 i₀).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i₀)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) →
    ∃ (Ek : ι → Type) (_ : ∀ k, CommRing (Ek k)) (_ : ∀ k, Algebra (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra (𝒜 k) (Ek k)) (_ : ∀ k, IsScalarTower (𝒜 k) (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra.Etale (Polynomial (𝒜 k)) (Ek k))
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k, (e k).comp (algebraMap (Polynomial (𝒜 k)) (Ek k)) =
          (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 k).subtype)) ∧
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) ∧
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : Ek k), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : Ek k),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ x : E, ∃ k y, e k y = x) := by
  intro T _ ι _ _ 𝒜 hA hcov i₀ h₀ E _ _ E₀ _ _ _ hφ
  obtain ⟨φ⟩ := hφ
  letI instA : ∀ k, Algebra (𝒜 i₀)[X] (𝒜 k)[X] := fun k =>
    (mapRingHom (Subring.inclusion (hA (h₀ k)))).toAlgebra
  letI instT : Algebra (𝒜 i₀)[X] T[X] := (mapRingHom (𝒜 i₀).subtype).toAlgebra
  have hincl : ∀ {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c),
      (Subring.inclusion (hA hbc)).comp (Subring.inclusion (hA hab)) =
        Subring.inclusion (hA (hab.trans hbc)) := by
    intro a b c hab hbc; ext x; rfl
  have hsub : ∀ {a b : ι} (hab : a ≤ b),
      (𝒜 b).subtype.comp (Subring.inclusion (hA hab)) = (𝒜 a).subtype := by
    intro a b hab; ext x; rfl
  let inc : ∀ k l, k ≤ l → (𝒜 k)[X] →ₐ[(𝒜 i₀)[X]] (𝒜 l)[X] := fun k l hkl =>
    { toRingHom := mapRingHom (Subring.inclusion (hA hkl))
      commutes' := fun p => by
        change Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hincl (h₀ k) hkl] }
  let sub : ∀ k, (𝒜 k)[X] →ₐ[(𝒜 i₀)[X]] T[X] := fun k =>
    { toRingHom := mapRingHom (𝒜 k).subtype
      commutes' := fun p => by
        change Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hsub (h₀ k)] }
  haveI : Module.Flat (𝒜 i₀)[X] E₀ := inferInstance
  have hcovT : ∀ q : T[X], ∃ k p, sub k p = q := by
    intro q
    have hq : ∃ k, ∀ n, q.coeff n ∈ 𝒜 k := by
      induction q using Polynomial.induction_on' with
      | add p q hp hq =>
        obtain ⟨k₁, h₁⟩ := hp
        obtain ⟨k₂, h₂⟩ := hq
        obtain ⟨m, hm₁, hm₂⟩ := directed_of (· ≤ ·) k₁ k₂
        exact ⟨m, fun n => by
          rw [coeff_add]; exact add_mem (hA hm₁ (h₁ n)) (hA hm₂ (h₂ n))⟩
      | monomial n c =>
        obtain ⟨j, hj⟩ := hcov c
        refine ⟨j, fun m => ?_⟩
        rw [coeff_monomial_apply]
        split_ifs
        · exact hj
        · exact zero_mem _
    obtain ⟨k, hk⟩ := hq
    have hsubset : (↑q.coeffs : Set T) ⊆ 𝒜 k := by
      intro c hc
      obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact hk n
    refine ⟨k, q.toSubring (𝒜 k) hsubset, ?_⟩
    show Polynomial.map (𝒜 k).subtype _ = q
    exact Polynomial.map_toSubring _ _ _
  obtain ⟨h, e', hh, he, hcompat, hid, hcomp, hinj, hcov'⟩ :=
    tensor_directedSystem_of_flat (𝒜 i₀)[X] i₀ (fun k => (𝒜 k)[X]) (instP := instA) T[X] E₀ inc sub
      (fun k hkk p => by
        have hid : Subring.inclusion (hA hkk) = RingHom.id _ := by ext; rfl
        show Polynomial.map _ p = p
        rw [hid, Polynomial.map_id])
      (fun k l m hkl hlm hkm p => by
        show Polynomial.map _ p = Polynomial.map _ (Polynomial.map _ p)
        rw [Polynomial.map_map, hincl hkl hlm])
      (fun k l hkl p => by
        show Polynomial.map _ (Polynomial.map _ p) = Polynomial.map _ p
        rw [Polynomial.map_map, hsub hkl])
      (fun k p q hpq => Polynomial.map_injective _ Subtype.val_injective hpq)
      hcovT
  let instC : ∀ k, Algebra (𝒜 k) (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀) := fun k =>
    ((algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)).comp (Polynomial.C)).toAlgebra
  have instS : ∀ k, @IsScalarTower (𝒜 k) (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀) _ _
      (instC k).toSMul := fun k =>
    letI := instC k
    IsScalarTower.of_algebraMap_eq (fun a => by
        change (algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)) (Polynomial.C a) =
          (algebraMap (𝒜 k)[X] (TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀)) (algebraMap (𝒜 k) (𝒜 k)[X] a)
        rw [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply])
  refine ⟨fun k => TensorProduct (𝒜 i₀)[X] (𝒜 k)[X] E₀, fun k => inferInstance,
    fun k => inferInstance, instC, instS, fun k => inferInstance,
    fun k => φ.toRingHom.comp (e' k), h, ?_, ?_, ?_, hid, hcomp, ?_, ?_⟩
  · intro k
    refine RingHom.ext fun p => ?_
    show φ (e' k (p ⊗ₜ 1)) = algebraMap T[X] E (Polynomial.map (𝒜 k).subtype p)
    rw [he, ← φ.commutes]
    rfl
  · intro k l hkl a
    show h k l hkl (C a ⊗ₜ 1) = C (Subring.inclusion (hA hkl) a) ⊗ₜ 1
    rw [hh]
    show Polynomial.map _ (C a) ⊗ₜ 1 = _
    rw [Polynomial.map_C]
  · intro k l hkl y
    exact congrArg φ (hcompat k l hkl y)
  · intro k
    exact φ.injective.comp (hinj k)
  · intro x
    obtain ⟨k, y, hy⟩ := hcov' (φ.symm x)
    refine ⟨k, y, ?_⟩
    show φ (e' k y) = x
    rw [hy, AlgEquiv.apply_symm_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DirectedSystemEtaleBaseChangePolynomialStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.directedSystem_etale_baseChange_polynomial : ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (i₀ : ι), (∀ k, i₀ ≤ k) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E]
      (E₀ : Type) [CommRing E₀] [Algebra (Polynomial (𝒜 i₀)) E₀] [Algebra.Etale (Polynomial (𝒜 i₀)) E₀],
      (letI : Algebra (Polynomial (𝒜 i₀)) (Polynomial T) :=
          (Polynomial.mapRingHom (𝒜 i₀).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i₀)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) →
    ∃ (Ek : ι → Type) (_ : ∀ k, CommRing (Ek k)) (_ : ∀ k, Algebra (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra (𝒜 k) (Ek k)) (_ : ∀ k, IsScalarTower (𝒜 k) (Polynomial (𝒜 k)) (Ek k))
      (_ : ∀ k, Algebra.Etale (Polynomial (𝒜 k)) (Ek k))
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k, (e k).comp (algebraMap (Polynomial (𝒜 k)) (Ek k)) =
          (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 k).subtype)) ∧
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) ∧
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) ∧
      (∀ k (hkk : k ≤ k) (y : Ek k), h k k hkk y = y) ∧
      (∀ k l m (hkl : k ≤ l) (hlm : l ≤ m) (hkm : k ≤ m) (y : Ek k),
          h k m hkm y = h l m hlm (h k l hkl y)) ∧
      (∀ k, Function.Injective (e k)) ∧
      (∀ x : E, ∃ k y, e k y = x) := by
  first | (exact @GlobalTheory.directedSystem_etaleBaseChange) | (exact GlobalTheory.directedSystem_etaleBaseChange) | (intros; apply GlobalTheory.directedSystem_etaleBaseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorDescentDirectedUnionSubring
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.TorsorUnionDescent

theorem exists_stage_torsor : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (q : ℕ), 0 < q →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E] (Q : Ideal E) [Q.IsPrime]
      (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (i : ι) (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial (𝒜 i)) EA) (_ : Algebra (𝒜 i) EA)
      (_ : IsScalarTower (𝒜 i) (Polynomial (𝒜 i)) EA) (_ : Algebra.Etale (Polynomial (𝒜 i)) EA) (e : EA →+* E),
      e.comp (algebraMap (Polynomial (𝒜 i)) EA) =
        (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 i).subtype) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)) →+*
          GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
        β.comp (algebraMap (Localization.AtPrime (Q.comap e))
            (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)))) =
          (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))).comp
            (Localization.localRingHom (Q.comap e) Q e rfl) ∧
      ∃ (D : Type) (_ : CommRing D) (_ : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D)
        (actA : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))] D)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D q actA ∧
        ∀ (C : Type) [CommRing C] (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* C) (σ : D →+* C),
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D) = ψ.comp β →
          ∃ σ₁ : D₁ →+* C, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  intro T _ _ ι _ _ _ 𝒜 hA hU q hq E _ _ _ _ _ Q _ D₁ _ _ act₁ htor
  obtain ⟨i₀, E₀, _, _, hE₀, ⟨iso₀⟩⟩ := GlobalTheory.T.exists_etale_polynomial_descent_of_directed_union T ι 𝒜 hA hU E

  let ι' := {k : ι // i₀ ≤ k}
  haveI : IsDirected ι' (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩⟩
  haveI : Nonempty ι' := ⟨⟨i₀, le_rfl⟩⟩
  let 𝒜' : ι' → Subring T := fun k => 𝒜 k.1
  have hA' : Monotone 𝒜' := fun a b hab => hA hab
  have hU' : ∀ x : T, ∃ k : ι', x ∈ 𝒜' k := fun x => by
    obtain ⟨j, hj⟩ := hU x
    obtain ⟨c, hjc, hic⟩ := directed_of (· ≤ ·) j i₀
    exact ⟨⟨c, hic⟩, hA hjc hj⟩
  obtain ⟨Ek, _, _, _, _, _, e, h, he, hh, heh, hid, hcomp, hinj, hsurj⟩ :=
    GlobalTheory.T.directedSystem_etale_baseChange_polynomial T ι' 𝒜' hA' hU' ⟨i₀, le_rfl⟩ (fun k => k.2) E E₀ ⟨iso₀⟩
  have he' : ∀ k (a : 𝒜' k), e k (algebraMap (𝒜' k) (Ek k) a) = algebraMap T E a := by
    intro k a
    have := congrArg (fun φ => φ (Polynomial.C a)) (he k)
    simpa [IsScalarTower.algebraMap_apply (𝒜' k) (Polynomial (𝒜' k)) (Ek k),
      IsScalarTower.algebraMap_apply T (Polynomial T) E] using this
  have hnz : ∀ (S S' : Subring T) (φ : S →+* S'), (∀ a, (φ a : T) = a) →
      ∀ a ∈ nonZeroDivisors S, φ a ∈ nonZeroDivisors S' := by
    intro S S' φ hφ a ha
    refine mem_nonZeroDivisors_of_ne_zero (fun h0 => nonZeroDivisors.ne_zero ha (Subtype.ext ?_))
    have := congrArg Subtype.val h0
    rw [hφ] at this
    exact this
  have hnzT : ∀ (S : Subring T), ∀ a ∈ nonZeroDivisors S, S.subtype a ∈ nonZeroDivisors T := by
    intro S a ha
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => nonZeroDivisors.ne_zero ha (Subtype.ext h0))
  let g : ∀ k : ι', GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))) →+*
      GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) := fun k =>
    GlobalTheory.GenFibMap.genFibMap (𝒜' k).subtype (e k) (he' k) (hnzT _) (Q.comap (e k)) Q rfl
  have hQ : ∀ k l (hkl : k ≤ l), Q.comap (e k) = (Q.comap (e l)).comap (h k l hkl) := by
    intro k l hkl
    rw [Ideal.comap_comap]
    congr 1
    ext y
    exact (heh k l hkl y).symm
  let f : ∀ k l : ι', k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))) →+*
      GlobalTheory.LocAcyc.GenFib (𝒜' l) (Localization.AtPrime (Q.comap (e l))) := fun k l hkl =>
    GlobalTheory.GenFibMap.genFibMap (Subring.inclusion (hA' hkl)) (h k l hkl) (hh k l hkl)
      (hnz _ _ _ (fun _ => rfl)) (Q.comap (e k)) (Q.comap (e l)) (hQ k l hkl)
  have hgc : ∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y)) := fun k y =>
    GlobalTheory.GenFibMap.genFibMap_apply _ _ _ _ _ _ _ y
  have hfc : ∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜' l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y)) := fun k l hkl y =>
    GlobalTheory.GenFibMap.genFibMap_apply _ _ _ _ _ _ _ y
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_torsor_model_filtered_colimit ι'
    (fun k => GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))) f
    (fun k hkk => GlobalTheory.GenFibMap.genFibMap_id _ _ _ _ _ _ (hid k hkk))
    (fun k l m hkl hlm => GlobalTheory.GenFibMap.genFibMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hcomp k l m hkl hlm (hkl.trans hlm)))
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) g
    (fun k l hkl => GlobalTheory.GenFibMap.genFibMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (fun y => (heh k l hkl y).symm))
    (GlobalTheory.T.genericFibreLocalization_directedUnion_surjective T ι' 𝒜' hA' hU' E Q Ek e h he' heh hsurj g hgc)
    (GlobalTheory.T.genericFibreLocalization_directedUnion_kernel T ι' 𝒜' hA' hU' E Q Ek e h he' hh heh hinj hsurj g hgc f hfc)
    q hq D₁ act₁ htor
  obtain ⟨Di, _, _, acti, htori, ⟨iso₂⟩⟩ := hk
  refine ⟨k.1, Ek k, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, e k, he k,
    g k, GlobalTheory.GenFibMap.genFibMap_comp_algebraMap _ _ _ _ _ _ _, Di, inferInstance, inferInstance, acti, htori, ?_⟩
  intro C _ ψ σ hσ
  letI : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k))))
      (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) := (g k).toAlgebra
  letI : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))) C :=
    (ψ.comp (g k)).toAlgebra
  let ψa : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →ₐ[GlobalTheory.LocAcyc.GenFib (𝒜' k)
      (Localization.AtPrime (Q.comap (e k)))] C := { ψ with commutes' := fun r => rfl }
  let σa : Di →ₐ[GlobalTheory.LocAcyc.GenFib (𝒜' k) (Localization.AtPrime (Q.comap (e k)))] C :=
    { σ with commutes' := fun r => (congrArg (fun φ => φ r) hσ : _) }
  refine ⟨(Algebra.TensorProduct.lift ψa σa (fun _ _ => Commute.all _ _)).toRingHom.comp
    iso₂.symm.toAlgHom.toRingHom, ?_⟩
  ext b
  simp [ψa]

end GlobalTheory.TorsorUnionDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorDescentDirectedUnionSubringStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsor_descent_directedUnion_subring : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (q : ℕ), 0 < q →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
      [Algebra.Etale (Polynomial T) E] (Q : Ideal E) [Q.IsPrime]
      (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (i : ι) (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial (𝒜 i)) EA) (_ : Algebra (𝒜 i) EA)
      (_ : IsScalarTower (𝒜 i) (Polynomial (𝒜 i)) EA) (_ : Algebra.Etale (Polynomial (𝒜 i)) EA) (e : EA →+* E),
      e.comp (algebraMap (Polynomial (𝒜 i)) EA) =
        (algebraMap (Polynomial T) E).comp (Polynomial.mapRingHom (𝒜 i).subtype) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)) →+*
          GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
        β.comp (algebraMap (Localization.AtPrime (Q.comap e))
            (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e)))) =
          (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))).comp
            (Localization.localRingHom (Q.comap e) Q e rfl) ∧
      ∃ (D : Type) (_ : CommRing D) (_ : Algebra (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D)
        (actA : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))] D)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D q actA ∧
        ∀ (C : Type) [CommRing C] (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* C) (σ : D →+* C),
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib (𝒜 i) (Localization.AtPrime (Q.comap e))) D) = ψ.comp β →
          ∃ σ₁ : D₁ →+* C, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  first | (exact @GlobalTheory.TorsorUnionDescent.exists_stage_torsor) | (exact GlobalTheory.TorsorUnionDescent.exists_stage_torsor) | (intros; apply GlobalTheory.TorsorUnionDescent.exists_stage_torsor  <;> assumption)
end
