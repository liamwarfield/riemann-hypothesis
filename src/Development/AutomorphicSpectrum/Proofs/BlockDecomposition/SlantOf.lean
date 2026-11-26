module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompat
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorSubRight

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem pr_res : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃) {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : CH.Cn (U₁.ι ⋙ E.F₁ a) i) (y : CH.Cn (U₂.ι ⋙ E.F₂ a') j), (resU (E.F₃ c) k₃).pullC n ((E.pr U₁ U₂ U₃ h₁ h₂ ha).μ hn x y) = (E.pr U₁' U₂' U₃' h₁' h₂' ha).μ hn ((resU (E.F₁ a) k₁).pullC i x) ((resU (E.F₂ a') k₂).pullC j y) := by
  intro K _ E U₁ U₁' U₂ U₂' U₃ U₃' h₁ h₂ h₁' h₂' k₁ k₂ k₃ a a' c ha i j n hn x y
  funext s
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_restrict_compat : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃) {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : CH.Cn (U₁.ι ⋙ E.F₁ a) i) (y : CH.Cn (U₂.ι ⋙ E.F₂ a') j), (resU (E.F₃ c) k₃).pullC n ((E.pr U₁ U₂ U₃ h₁ h₂ ha).μ hn x y) = (E.pr U₁' U₂' U₃' h₁' h₂' ha).μ hn ((resU (E.F₁ a) k₁).pullC i x) ((resU (E.F₂ a') k₂).pullC j y) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.pr_res | exact GlobalTheory.CompanionTheory.KunGlue.pr_res | (intros; apply GlobalTheory.CompanionTheory.KunGlue.pr_res <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem kun_res {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃) (b₁ : ∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n)) (b₂ : ∀ a n, Function.Bijective ((resU (E.F₂ a) k₂).pull n)) (b₃ : ∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n)) : (E.Kun U₁ U₂ U₃ h₁ h₂ ↔ E.Kun U₁' U₂' U₃' h₁' h₂') :=
  GlobalTheory.T.pairing_iso_of_component_isos (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (P' := fun a => CH.cx (U₁'.ι ⋙ E.F₁ a)) (Q' := fun a => CH.cx (U₂'.ι ⋙ E.F₂ a)) (T' := fun a => CH.cx (U₃'.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha) (fun {a a' c} ha => E.pr U₁' U₂' U₃' h₁' h₂' ha)
    (fun a => (resU (E.F₁ a) k₁).hom) (fun a => (resU (E.F₂ a) k₂).hom) (fun a => (resU (E.F₃ a) k₃).hom)
    b₁ b₂ b₃
    (fun ha _ _ _ h x y => GlobalTheory.T.pairing_restrict_compat E h₁ h₂ h₁' h₂' k₁ k₂ k₃ ha h x y)

end GlobalTheory.CompanionTheory.KunGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_of_restrict_bijective : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃), (∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n)) → (∀ a n, Function.Bijective ((resU (E.F₂ a) k₂).pull n)) → (∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n)) → (E.Kun U₁ U₂ U₃ h₁ h₂ ↔ E.Kun U₁' U₂' U₃' h₁' h₂') := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_res | exact GlobalTheory.CompanionTheory.KunGlue.kun_res | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_res <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEq
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEq
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem resU_self_pullC : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) (x : CH.Cn (U.ι ⋙ F) n), (resU F k).pullC n x = x := by
  intro R _ C _ F U k n x
  funext s
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEqStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_self_pullC_eq : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) (x : CH.Cn (U.ι ⋙ F) n), (resU F k).pullC n x = x := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC | exact GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC | (intros; apply GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductProperSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalGlobal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisLeft
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisLeft
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem glue_r : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₂) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → U₁ (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun U₁ (capU V S) (capU W S) (h₁ S) (h₂ S)) → E.Kun U₁ (capU V ∅) (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hM hC K _ E U₁ ι _ _ V W hV hW h₁ h₂ hK
  refine GlobalTheory.T.cosieve_pairing_family_compat hM hC E.F₂ E.F₃ (fun a => CH.cx (U₁.ι ⋙ E.F₁ a))
    (fun U U' => (∀ T, U' T → U₁ (E.L₁.obj T)) ∧ (∀ T, U' T → U (E.L₂.obj T)))
    (fun U U' r {a a' c} ha => E.pr U₁ U U' r.1 r.2 ha) ?_ V W hV hW (fun S => ⟨h₁ S, h₂ S⟩)
    (fun S hS => hK S hS)
  intro A B A' B' r₁ r₂ k k' a a' c ha i j n hn x y
  have h := GlobalTheory.T.pairing_restrict_compat E r₁.1 r₁.2 r₂.1 r₂.2 (le_refl U₁) k k' ha hn x y
  rw [GlobalTheory.T.restrict_self_pullC_eq] at h
  exact h

end GlobalTheory.CompanionTheory.KunGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisLeftStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_mayer_vietoris_left : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₂) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → U₁ (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun U₁ (capU V S) (capU W S) (h₁ S) (h₂ S)) → E.Kun U₁ (capU V ∅) (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_r | exact GlobalTheory.CompanionTheory.KunGlue.glue_r | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_r <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalCoords
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Aff

universe u w

section Algebra

variable {R : Type} [CommRing R]

theorem tensor_sub_left (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton M] :
    Subsingleton (M ⊗[R] N) := by
  have key : ∀ z : M ⊗[R] N, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem tensor_sub_right (M N : Type u) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) :=
  _root_.UpperTheory.Reformulated.B.Qn17.tensor_sub_right M N

variable {I A : Type} [DecidableEq I] [Fintype A] [DecidableEq A] (M : I → Type u) [∀ t, AddCommMonoid (M t)]
  [∀ t, Module R (M t)] (ι : A → I)

theorem component_lof_ne {i j : I} (h : j ≠ i) (x : M i) : DirectSum.component R I M j (DirectSum.lof R I M i x) = 0 := by
  rw [DirectSum.component.of]
  simp [h.symm]

def sumPi (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) :
    (⨁ t, M t) ≃ₗ[R] ∀ a, M (ι a) :=
  LinearEquiv.ofLinear (LinearMap.pi fun a => DirectSum.component R I M (ι a))
    (∑ a, (DirectSum.lof R I M (ι a)).comp (LinearMap.proj a))
    (by
      refine LinearMap.ext fun f => funext fun b => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply, map_sum]
      rw [Finset.sum_eq_single b]
      · exact DirectSum.component.lof_self R _ _
      · intro a _ hab
        exact component_lof_ne M (fun e => hab (hι e).symm) _
      · intro h
        exact absurd (Finset.mem_univ b) h)
    (by
      refine DirectSum.linearMap_ext R fun t => LinearMap.ext fun x => ?_
      by_cases ht : t ∈ Set.range ι
      · obtain ⟨b, rfl⟩ := ht
        simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.id_apply]
        rw [Finset.sum_eq_single b]
        · rw [DirectSum.component.lof_self]
        · intro a _ hab
          rw [component_lof_ne M (fun e => hab (hι e)) x, map_zero]
        · intro h
          exact absurd (Finset.mem_univ b) h
      · have := hz t ht
        rw [Subsingleton.elim x 0, map_zero, map_zero])

theorem sumPi_lof (hι : Function.Injective ι) (hz : ∀ t, t ∉ Set.range ι → Subsingleton (M t)) (b : A) (x : M (ι b)) :
    sumPi (R := R) M ι hι hz (DirectSum.lof R I M (ι b) x) = Pi.single b x := by
  refine funext fun a => ?_
  change DirectSum.component R I M (ι a) (DirectSum.lof R I M (ι b) x) = _
  by_cases h : a = b
  · subst h
    rw [DirectSum.component.lof_self, Pi.single_eq_same]
  · rw [component_lof_ne M (fun e => h (hι e)) x, Pi.single_eq_of_ne h]

end Algebra

variable {K : Type} [Field K]

def diag (c : ℕ) (a : Fin (c + 1)) : Idx c c :=
  ⟨a, a, c - a, c - a, by omega, by omega⟩

theorem diag_inj (c : ℕ) : Function.Injective (diag c) := by
  intro a b h
  exact Fin.ext (congrArg Idx.a h)

theorem kunE_of_diag {P Q T : ℕ → Cx.{w} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c))
    (hP : ∀ a j, j ≠ a → Subsingleton ((P a).H j)) (hQ : ∀ a j, j ≠ a → Subsingleton ((Q a).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((T a).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((P a).H a) ((Q (c - a)).H (c - a))) ≃ₗ[K] (T c).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (P a).X a) (y : (Q (c - a)).X (c - a))
        (hx : (P a).d a x = 0) (hy : (Q (c - a)).d (c - a) y = 0) (hz : (T c).d c ((pr hc).μ hc x y) = 0),
        e (Pi.single a ((P a).cls x hx ⊗ₜ (Q (c - a)).cls y hy)) = (T c).cls ((pr hc).μ hc x y) hz) :
    KunE pr := by
  intro c n
  have offL : ∀ t : Idx c n, t.i ≠ t.a → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hP t.a t.i h
    exact tensor_sub_left _ _
  have offR : ∀ t : Idx c n, t.j ≠ t.a' → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t h => by
    have := hQ t.a' t.j h
    exact tensor_sub_right _ _
  by_cases hn : n = c
  · subst hn
    obtain ⟨e, he⟩ := hE n
    have hz : ∀ t, t ∉ Set.range (diag n) → Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t ht => by
      refine offL t fun hi => ht ?_
      obtain ⟨a, i, a', j, ha, h⟩ := t
      simp only at hi
      subst hi
      obtain rfl : j = a' := by omega
      obtain rfl : j = n - i := by omega
      exact ⟨⟨i, by omega⟩, rfl⟩
    refine ⟨(sumPi (R := K) (fun t : Idx n n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) (diag n) (diag_inj n) hz).trans e, ?_⟩
    intro t x y hx hy hw
    by_cases ht : t ∈ Set.range (diag n)
    · obtain ⟨b, rfl⟩ := ht
      rw [LinearEquiv.trans_apply, sumPi_lof]
      exact he b (by omega) x y hx hy hw
    · have := hz t ht
      have hi : t.i ≠ t.a := fun hi => ht (by
        obtain ⟨a, i, a', j, ha, h⟩ := t
        simp only at hi
        subst hi
        obtain rfl : j = a' := by omega
        obtain rfl : j = n - i := by omega
        exact ⟨⟨i, by omega⟩, rfl⟩)
      have hB : x ∈ (P t.a).B t.i := by
        have := hP t.a t.i hi
        exact ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 x hx).1 (Subsingleton.elim _ _)
      set_option synthInstance.maxHeartbeats 200000 in
        rw [Subsingleton.elim ((P t.a).cls x hx ⊗ₜ[K] (Q t.a').cls y hy) 0, map_zero, map_zero]
      exact (((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ hw).2 (CrystallineSemistableComparison.Auxff.memB_left (pr t.ha) t.h x hB y hy)).symm
  · have : Subsingleton ((T c).H n) := hT c n hn
    have hs : ∀ t : Idx c n, Subsingleton ((P t.a).H t.i ⊗[K] (Q t.a').H t.j) := fun t => by
      by_cases hi : t.i = t.a
      · refine offR t fun hj => hn ?_
        have := t.ha
        have := t.h
        omega
      · exact offL t hi
    have : Subsingleton (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) := inferInstance
    exact ⟨LinearEquiv.ofSubsingleton _ _, fun _ _ _ _ _ _ => Subsingleton.elim _ _⟩

theorem xd_kun (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (hP : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₁.ι ⋙ E.F₁ a)).H j))
    (hQ : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₂.ι ⋙ E.F₂ a)).H j))
    (hT : ∀ a j, j ≠ a → Subsingleton ((CH.cx (U₃.ι ⋙ E.F₃ a)).H j))
    (hE : ∀ c : ℕ, ∃ e : (∀ a : Fin (c + 1), TensorProduct K ((CH.cx (U₁.ι ⋙ E.F₁ a)).H a) ((CH.cx (U₂.ι ⋙ E.F₂ (c - a))).H (c - a))) ≃ₗ[K] (CH.cx (U₃.ι ⋙ E.F₃ c)).H c,
      ∀ (a : Fin (c + 1)) (hc : (a : ℕ) + (c - a) = c) (x : (CH.cx (U₁.ι ⋙ E.F₁ a)).X a) (y : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).X (c - a))
        (hx : (CH.cx (U₁.ι ⋙ E.F₁ a)).d a x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).d (c - a) y = 0)
        (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d c ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) = 0),
        e (Pi.single a ((CH.cx (U₁.ι ⋙ E.F₁ a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ (c - a))).cls y hy)) =
          (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ hc).μ hc x y) hz) :
    E.Kun U₁ U₂ U₃ h₁ h₂ :=
  kunE_of_diag (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha) hP hQ hT hE

theorem cls_eq {R : Type} [CommRing R] (L : Cx.{w} R) {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0) (hy : L.d n y = 0) :
    L.cls x hx = L.cls y hy := by
  subst e
  rfl

section
variable {X X' P : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hw : p₂ ≫ q' = p₁ ≫ q)

theorem hodge_pr_eq (U₁ : ObjectProperty (Thick (smFun X q))) (U₂ : ObjectProperty (Thick (smFun X' q')))
    (U₃ : ObjectProperty (Thick (smFun P (p₁ ≫ q))))
    (h₁ : ∀ T, U₃ T → U₁ ((smS p₁ rfl).G.obj T)) (h₂ : ∀ T, U₃ T → U₂ ((smS p₂ hw).G.obj T)) {a a' c i j n : ℕ}
    (ha : a + a' = c) (h : i + j = n) (x : CH.Cn (U₁.ι ⋙ G q a) i) (y : CH.Cn (U₂.ι ⋙ G q' a') j) :
    ((hodgeXD q q' p₁ p₂ hw).pr U₁ U₂ U₃ h₁ h₂ ha).μ h x y =
      cupU (p₁ ≫ q) U₃ ha h ((morV p₁ rfl a h₁).pullC i x) ((morV p₂ hw a' h₂).pullC j y) := rfl

end


set_option maxHeartbeats 400000 in
theorem kun_aff : SiteLaws → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q' V' ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂  := by
  intro _ hA hK K _ _ X X' P q q' p₁ p₂ hP V V' d d' hc hc' h₁ h₂
  obtain ⟨hZ, hE⟩ := hK K X X' P q q' p₁ p₂ hP V V' d d' hc hc'
  refine xd_kun (hodgeXD q q' p₁ p₂ hP.w.symm) _ _ _ h₁ h₂ ?_ ?_ ?_ ?_
  · exact fun a j hj => (hA K X q V d hc a).1 j hj
  · exact fun a j hj => (hA K X' q' V' d' hc' a).1 j hj
  · exact fun a j hj => (hA K P (p₁ ≫ q) _ (d + d') hZ a).1 j hj
  · intro c
    obtain ⟨e, he⟩ := hE c h₁ h₂
    refine ⟨e, fun a hc x y hx hy hz => ?_⟩
    have eq := hodge_pr_eq q q' p₁ p₂ hP.w.symm (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂ hc hc x y
    have hz' : (CH.cx ((inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')).ι ⋙ G (p₁ ≫ q) c)).d c (cupU (p₁ ≫ q) _ hc hc ((morV p₁ rfl a h₁).pullC a x) ((morV p₂ hP.w.symm (c - a) h₂).pullC (c - a) y)) = 0 := by
      rw [← eq]
      exact hz
    exact (he a hc x y hx hy hz').trans (cls_eq _ eq.symm _ _)

end GlobalTheory.CompanionTheory.KunGlue.Aff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalCoordsStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_product_local_coords : SiteLaws → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (d d' : ℕ), Nonempty (Coord q V d) → Nonempty (Coord q' V' d') → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') T → inU q' V' ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' V') (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff | exact GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Aff.kun_aff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalGlobal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Right

variable {K : Type} [Field K]

theorem inU_pre (hs : SiteLaws) {Z Y : Scheme.{0}} {p : Z ⟶ Spec (CommRingCat.of K)} {r : Y ⟶ Spec (CommRingCat.of K)}
    (u : Y ⟶ Z) (hu : u ≫ p = r) (V : Z.Opens) (T) : inU r (u ⁻¹ᵁ V) T ↔ inU p V ((smS u hu).G.obj T) := by
  subst hu
  exact (hs K Z Z Y p (𝟙 Z) u).2.2.2.2.1 V T

theorem inU_biInf (hs : SiteLaws) {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) {κ : Type} (V : κ → Z.Opens)
    (S : Finset κ) (T) : inU q (⨅ α ∈ S, V α) T ↔ ∀ α ∈ S, inU q (V α) T := by
  classical
  obtain ⟨-, -, htop, hinf, -, -⟩ := hs K Z Z Z q (𝟙 Z) (𝟙 Z)
  rw [← Finset.inf_eq_iInf]
  induction S using Finset.induction_on with
  | empty => simpa using htop T
  | insert a s ha ih =>
    rw [Finset.inf_insert, hinf, ih]
    simp

theorem capU_of_forall {C : Type 1} [Category.{0} C] {ι : Type} [DecidableEq ι] (U : ι → ObjectProperty C)
    (Q : ObjectProperty C) (S : Finset ι) (hS : S.Nonempty) (h : ∀ T, Q T ↔ ∀ α ∈ S, U α T) : capU U S = Q := by
  funext T
  refine propext ⟨fun hT => (h T).2 hT.2, fun hT => ?_⟩
  obtain ⟨α, hα⟩ := hS
  exact ⟨⟨α, (h T).1 hT α hα⟩, (h T).1 hT⟩

theorem capU_empty_eq {C : Type 1} [Category.{0} C] {ι : Type} [DecidableEq ι] (U : ι → ObjectProperty C) :
    (fun T => ∃ α, U α T) = capU U ∅ := by
  funext T
  exact propext ⟨fun h => ⟨h, fun α hα => absurd hα (Finset.notMem_empty α)⟩, fun h => h.1⟩

theorem res_self_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C)
    (k : U ≤ U) (n : ℕ) : Function.Bijective ((resU F k).pull n) := by
  have h : ∀ x, (resU F k).pull n x = x := by
    intro x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  exact ⟨fun a b e => by rwa [h, h] at e, fun y => ⟨y, h y⟩⟩

theorem res_bij_of_eq {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U Q Q' : ObjectProperty C} (e : Q = Q') (h : Q ≤ U) (h' : Q' ≤ U) (n : ℕ)
    (hb : Function.Bijective ((resU F h).pull n)) : Function.Bijective ((resU F h').pull n) := by
  subst e
  exact hb

theorem kun_congr (E : XD K) {U₁ : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D}
    (e₂ : U₂ = U₂') (e₃ : U₃ = U₃') (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (h₁' : ∀ T, U₃' T → U₁ (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (h : E.Kun U₁ U₂ U₃ h₁ h₂) :
    E.Kun U₁ U₂' U₃' h₁' h₂' := by
  subst e₂ e₃
  exact h

theorem kun_right : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (d : ℕ), Nonempty (Coord q V d) → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  intro hs hmv hcd hz hA hK K _ _ X X' P q q' _ _ p₁ p₂ hP V d cV h₁ h₂
  classical
  obtain ⟨U⟩ := (cov_ex q').1 inferInstance
  have hw : p₂ ≫ q' = p₁ ≫ q := hP.w.symm
  obtain ⟨hcosP, -, htopP, hinfP, -, -⟩ := hs K P P P (p₁ ≫ q) (𝟙 P) (𝟙 P)
  obtain ⟨hcos', -, htop', -, -, -⟩ := hs K X' X' X' q' (𝟙 X') (𝟙 X')
  have l₁ : ∀ (D : X'.Opens) T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ D) T → inU q V ((smS p₁ rfl).G.obj T) :=
    fun D T hT => (inU_pre hs p₁ rfl V T).1 ((hinfP _ _ T).1 hT).1
  have l₂ : ∀ (D : X'.Opens) T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ D) T → inU q' D ((smS p₂ hw).G.obj T) :=
    fun D T hT => (inU_pre hs p₂ hw D T).1 ((hinfP _ _ T).1 hT).2
  let E := hodgeXD q q' p₁ p₂ hw
  let Vv : U.ι → ObjectProperty E.C₂ := fun α => inU q' (U.U α)
  let Ww : U.ι → ObjectProperty E.D := fun α => inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α)
  have g₁ : ∀ (S : Finset U.ι) T, capU Ww S T → inU q V (E.L₁.obj T) := by
    rintro S T ⟨⟨α, hα⟩, -⟩
    exact l₁ _ T hα
  have g₂ : ∀ (S : Finset U.ι) T, capU Ww S T → capU Vv S (E.L₂.obj T) := by
    rintro S T ⟨⟨α, hα⟩, hS⟩
    exact ⟨⟨α, l₂ _ T hα⟩, fun β hβ => l₂ _ T (hS β hβ)⟩
  have eV : ∀ S : Finset U.ι, S.Nonempty → capU Vv S = inU q' (⨅ α ∈ S, U.U α) := fun S hS =>
    capU_of_forall _ _ S hS fun T => inU_biInf hs q' U.U S T
  have eW : ∀ S : Finset U.ι, S.Nonempty →
      capU Ww S = inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⨅ α ∈ S, U.U α) := fun S hS =>
    capU_of_forall _ _ S hS fun T => by
      obtain ⟨α₀, hα₀⟩ := hS
      rw [hinfP, inU_pre hs p₂ hw, inU_biInf hs q' U.U S]
      refine ⟨fun h α hα => (hinfP _ _ T).2 ⟨h.1, (inU_pre hs p₂ hw _ T).2 (h.2 α hα)⟩, fun h => ⟨((hinfP _ _ T).1 (h α₀ hα₀)).1, fun α hα => (inU_pre hs p₂ hw _ T).1 ((hinfP _ _ T).1 (h α hα)).2⟩⟩
  have hS : ∀ S : Finset U.ι, S.Nonempty → E.Kun (inU q V) (capU Vv S) (capU Ww S) (g₁ S) (g₂ S) := by
    intro S hne
    obtain ⟨α₀, hα₀⟩ := id hne
    obtain ⟨c', -⟩ := coord_res (U.c α₀) (iInf₂_le α₀ hα₀) (U.inter S hne)
    exact kun_congr E (eV S hne).symm (eW S hne).symm (l₁ _) (l₂ _) _ _
      (GlobalTheory.T.kuenneth_product_local_coords hs hA hK K X X' P q q' p₁ p₂ hP V _ d _ cV ⟨c'⟩ (l₁ _) (l₂ _))
  have hglue := GlobalTheory.T.kuenneth_mayer_vietoris_left hmv hcd E (inU q V) Vv Ww (fun α => hcos' _) (fun α => hcosP _) g₁ g₂ hS
  have k₂ : capU Vv ∅ ≤ inU q' ⊤ := fun T _ => htop' T
  have k₃ : capU Ww ∅ ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨⟨α, hα⟩, -⟩
    exact (hinfP _ _ T).2 ⟨((hinfP _ _ T).1 hα).1, (inU_pre hs p₂ hw _ T).2 (htop' _)⟩
  have sup₃ : (⨆ α, p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α) = p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤ := by
    rw [← inf_iSup_eq, ← U.cover]
    congr 1
    ext x
    simp [TopologicalSpace.Opens.mem_iSup]
  refine (GlobalTheory.T.kuenneth_of_restrict_bijective E h₁ h₂ (g₁ ∅) (g₂ ∅) (le_refl _) k₂ k₃ ?_ ?_ ?_).2 hglue
  · exact fun a n => res_self_bij _ _ _ n
  · intro a n
    exact res_bij_of_eq (G q' a) (capU_empty_eq Vv) (fun _ _ => htop' _) k₂ n
      (hz K X' q' U.ι ⊤ U.U U.cover _ a n)
  · intro a n
    refine res_bij_of_eq (G (p₁ ≫ q) a) (capU_empty_eq Ww) (fun T hT => k₃ T ((capU_empty_eq Ww ▸ hT : capU Ww ∅ T))) k₃ n
      (hz K P (p₁ ≫ q) U.ι _ (fun α => p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α) sup₃ _ a n)

end GlobalTheory.CompanionTheory.KunGlue.Right
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalGlobalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_product_local_global : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (d : ℕ), Nonempty (Coord q V d) → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Right.kun_right | exact GlobalTheory.CompanionTheory.KunGlue.Right.kun_right | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Right.kun_right <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRight
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethSwap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethSwap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

universe w

variable {K : Type} [Field K]

abbrev Idx.swap {c n : ℕ} (t : Idx c n) : Idx c n :=
  ⟨t.a', t.j, t.a, t.i, by have := t.ha; omega, by have := t.h; omega⟩

def swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) :
    (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) →ₗ[K]
      (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) :=
  DirectSum.toModule K _ _ fun t =>
    ((-1 : ℤ) ^ (t.i * t.j)) •
      ((DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap).comp
        (TensorProduct.comm K ((P t.a).H t.i) ((Q t.a').H t.j)).toLinearMap)

theorem swapSum_lof (P Q : ℕ → Cx.{w} K) (c n : ℕ) (t : Idx c n) (u : (P t.a).H t.i) (v : (Q t.a').H t.j) :
    swapSum P Q c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t (u ⊗ₜ v)) =
      ((-1 : ℤ) ^ (t.i * t.j)) •
        DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t.swap (v ⊗ₜ u) := by
  unfold swapSum
  rw [DirectSum.toModule_lof]
  rfl

theorem swapSum_swapSum (P Q : ℕ → Cx.{w} K) (c n : ℕ) (z) :
    swapSum Q P c n (swapSum P Q c n z) = z := by
  have key : (swapSum Q P c n).comp (swapSum P Q c n) = LinearMap.id := by
    refine DirectSum.linearMap_ext K fun t => TensorProduct.ext' fun u v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, swapSum_lof, map_zsmul]
    have hs : ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.swap.i * t.swap.j)) = 1 := by
      change ((-1 : ℤ) ^ (t.i * t.j)) * ((-1 : ℤ) ^ (t.j * t.i)) = 1
      rw [Nat.mul_comm t.j t.i, ← mul_pow]
      simp
    refine (congrArg (fun w => ((-1 : ℤ) ^ (t.i * t.j)) • w) (swapSum_lof Q P c n t.swap v u)).trans ?_
    dsimp only
    rw [smul_smul, hs, one_smul]
  exact LinearMap.congr_fun key z

theorem kunE_swap {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (h : KunE pr) :
    KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  intro c n
  obtain ⟨e, he⟩ := h c n
  let σ : (⨁ t : Idx c n, (Q t.a).H t.i ⊗[K] (P t.a').H t.j) ≃ₗ[K]
      (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) :=
    LinearEquiv.ofLinear (swapSum Q P c n) (swapSum P Q c n)
      (LinearMap.ext fun z => swapSum_swapSum P Q c n z) (LinearMap.ext fun z => swapSum_swapSum Q P c n z)
  refine ⟨σ.trans e, fun t x y hx hy hz => ?_⟩
  have hz' : (T c).d n ((pr (show t.a' + t.a = c by have := t.ha; omega)).μ (show t.j + t.i = n by have := t.h; omega) y x) = 0 := by
    have e0 := (pr (show t.a' + t.a = c by have := t.ha; omega)).leib (show t.j + t.i = n by have := t.h; omega) y x
    rw [e0, hx, hy]
    simp
  have e1 := he t.swap y x hy hx hz'
  change e (swapSum Q P c n (DirectSum.lof K _ (fun t : Idx c n => (Q t.a).H t.i ⊗[K] (P t.a').H t.j) t
    ((Q t.a).cls x hx ⊗ₜ (P t.a').cls y hy))) = _
  rw [swapSum_lof]
  change e.toLinearMap (((-1 : ℤ) ^ (t.i * t.j)) •
    DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t.swap
      ((P t.a').cls y hy ⊗ₜ (Q t.a).cls x hx)) = _
  rw [map_zsmul e.toLinearMap]
  refine (congrArg _ e1).trans ?_
  rfl

end GlobalTheory.CompanionTheory.KunGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethSwapStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_swap : ∀ {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)), KunE pr → KunE (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kunE_swap | exact GlobalTheory.CompanionTheory.KunGlue.kunE_swap | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kunE_swap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRight
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem mapH_id_bij {K : Type} [Field K] (C : Cx.{1} K) (n : ℕ) :
    Function.Bijective ((Cx.Hom.id C).mapH n) := by
  have h : ∀ x : C.H n, (Cx.Hom.id C).mapH n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem swapPr_swapPr_apply {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K}
    (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) {a a' c : ℕ} (ha : a + a' = c)
    {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j) :
    (swapPr (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) ha).μ h x y = (pr ha).μ h x y := by
  simp only [swapPr, LinearMap.smul_apply, LinearMap.flip_apply, smul_smul]
  have s : ((-1 : ℤ) ^ (i * j) * (-1) ^ (j * i)) = 1 := by
    rw [mul_comm j i, ← mul_pow]
    simp
  rw [s, one_smul]

theorem glue_l : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hMV hCD K _ E U₂ ι _ _ V W hV hW h₁ h₂ hK
  let Rel : ObjectProperty E.C₁ → ObjectProperty E.D → Prop := fun U U' =>
    (∀ T, U' T → U (E.L₁.obj T)) ∧ (∀ T, U' T → U₂ (E.L₂.obj T))
  let prr : ∀ (U : ObjectProperty E.C₁) (U' : ObjectProperty E.D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c →
      CxPairing (CH.cx (U₂.ι ⋙ E.F₂ a)) (CH.cx (U.ι ⋙ E.F₁ a')) (CH.cx (U'.ι ⋙ E.F₃ c)) :=
    fun U U' r {a a' c} ha =>
      swapPr (P := fun a => CH.cx (U.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
        (T := fun c => CH.cx (U'.ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr U U₂ U' r.1 r.2 ha) ha
  have hnat : ∀ {U₁ U₂' : ObjectProperty E.C₁} {U₁' U₂'' : ObjectProperty E.D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂' U₂'')
      (k : U₂' ≤ U₁) (k' : U₂'' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n)
      (x : (CH.cx (U₂.ι ⋙ E.F₂ a)).X i) (y : CH.Cn (U₁.ι ⋙ E.F₁ a') j),
      (resU (E.F₃ c) k').pullC n ((prr U₁ U₁' r₁ ha).μ hn x y) = (prr U₂' U₂'' r₂ ha).μ hn x ((resU (E.F₁ a') k).pullC j y) := by
    intro U₁ U₂' U₁' U₂'' r₁ r₂ k k' a a' c ha i j n hn x y
    simp only [prr, swapPr, LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    rw [GlobalTheory.T.pairing_restrict_compat E r₁.1 r₁.2 r₂.1 r₂.2 k (le_refl U₂) k' (show a' + a = c by omega) (show j + i = n by omega) y x,
      GlobalTheory.T.restrict_self_pullC_eq (E.F₂ a) U₂ (le_refl U₂) i x]
  have key := GlobalTheory.T.cosieve_pairing_family_compat hMV hCD E.F₁ E.F₃ (fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) Rel prr hnat V W hV hW
    (fun S => ⟨h₁ S, h₂ S⟩) (fun S hS => GlobalTheory.T.kuenneth_swap _ (hK S hS))
  have k2 := GlobalTheory.T.kuenneth_swap _ key
  refine (GlobalTheory.T.pairing_iso_of_component_isos _ _ (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _)
    (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) ?_).1 k2
  intro a a' c ha i j n h x y
  exact swapPr_swapPr_apply (P := fun a => CH.cx ((capU V ∅).ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
    (T := fun c => CH.cx ((capU W ∅).ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) ha) ha h x y

end GlobalTheory.CompanionTheory.KunGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRightStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_mayer_vietoris_right : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_l | exact GlobalTheory.CompanionTheory.KunGlue.glue_l | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_l <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductProperSmooth
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem resU_self_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) : Function.Bijective ((resU F k).pull n) := by
  have h : ∀ x, (resU F k).pull n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem resU_bij_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U V V' : ObjectProperty C} (e : V = V') (k : V ≤ U) (k' : V' ≤ U) (n : ℕ)
    (h : Function.Bijective ((resU F k').pull n)) : Function.Bijective ((resU F k).pull n) := by
  subst e
  exact h

theorem kun_congr {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ : ObjectProperty E.C₂}
    {U₃ U₃' : ObjectProperty E.D} (e₁ : U₁ = U₁') (e₃ : U₃ = U₃')
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂ (E.L₂.obj T))
    (h : E.Kun U₁ U₂ U₃ h₁ h₂) : E.Kun U₁' U₂ U₃' h₁' h₂' := by
  subst e₁ e₃
  exact h

theorem glue_top (hMV : MVBij) (hCD : CovDesc) {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁)
    (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D) {ι : Type} [DecidableEq ι] [Fintype ι]
    (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D) (hV : ∀ α, Cosieve (V α)) (hW : ∀ α, Cosieve (W α))
    (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T))
    (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T))
    (hK : ∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S))
    (k₁ : capU V ∅ ≤ U₁) (k₃ : capU W ∅ ≤ U₃)
    (b₁ : ∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n))
    (b₃ : ∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n))
    (g₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (g₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) : E.Kun U₁ U₂ U₃ g₁ g₂ :=
  (GlobalTheory.T.kuenneth_of_restrict_bijective E g₁ g₂ (h₁ ∅) (h₂ ∅) k₁ (le_refl U₂) k₃ b₁ (fun a n => resU_self_bij _ _ _ n) b₃).2
    (GlobalTheory.T.kuenneth_mayer_vietoris_right hMV hCD E U₂ V W hV hW h₁ h₂ hK)

section Site

variable {K : Type} [CommRing K] {Z Y : Scheme.{0}}

theorem inU_pull (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {r : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z)
    (hu : u ≫ q = r) (A : Z.Opens) (T) : inU r (u ⁻¹ᵁ A) T ↔ inU q A ((smS u hu).G.obj T) := by
  subst hu
  exact (hS K Z Z Y q (𝟙 Z) u).2.2.2.2.1 A T

theorem inU_cos (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A : Z.Opens) : Cosieve (inU q A) :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).1 A

theorem inU_top (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (T) : inU q ⊤ T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.1 T

theorem inU_inf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A B : Z.Opens) (T) :
    inU q (A ⊓ B) T ↔ inU q A T ∧ inU q B T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.2.1 A B T

theorem inU_biInf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {ι : Type} [DecidableEq ι] (A : ι → Z.Opens)
    (S : Finset ι) (T) : inU q (⨅ α ∈ S, A α) T ↔ ∀ α ∈ S, inU q (A α) T := by
  induction S using Finset.induction_on with
  | empty => simpa using inU_top hS q T
  | insert a S _ ih =>
    rw [Finset.iInf_insert, inU_inf hS, ih]
    simp

end Site

theorem kun_left : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  intro hS hMV hCD hZ hA hKA K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP g₁ g₂
  classical
  obtain ⟨U⟩ := (cov_ex q).1 inferInstance
  have hw := hP.w.symm
  have inP : ∀ (A : X.Opens) (B : X'.Opens) (T),
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ A ⊓ p₂ ⁻¹ᵁ B) T ↔
        inU q A ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) ∧ inU q' B ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) := by
    intro A B T
    rw [inU_inf hS, inU_pull hS q p₁ rfl, inU_pull hS q' p₂ hw]
    rfl
  let V : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).C₁ := fun α => inU q (U.U α)
  let W : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).D := fun α => inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤)
  have h₁ : ∀ S : Finset U.ι, ∀ T, capU W S T → capU V S ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) := by
    rintro S T ⟨⟨α, hα⟩, h⟩
    exact ⟨⟨α, ((inP _ _ T).1 hα).1⟩, fun β hβ => ((inP _ _ T).1 (h β hβ)).1⟩
  have h₂ : ∀ S : Finset U.ι, ∀ T, capU W S T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) :=
    fun S T _ => inU_top hS q' _
  have eV : ∀ S : Finset U.ι, S.Nonempty → inU q (⨅ α ∈ S, U.U α) = capU V S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inU_biInf hS q U.U S T).trans ⟨fun h => ⟨⟨α₀, h α₀ h₀⟩, h⟩, fun h => h.2⟩)
  have eW : ∀ S : Finset U.ι, S.Nonempty →
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ (⨅ α ∈ S, U.U α) ⊓ p₂ ⁻¹ᵁ ⊤) = capU W S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inP _ _ T).trans ⟨fun h => ?_, fun h => ?_⟩)
    · have a : ∀ α ∈ S, W α T := fun α hα =>
        (inP _ _ T).2 ⟨(inU_biInf hS q U.U S _).1 h.1 α hα, h.2⟩
      exact ⟨⟨α₀, a α₀ h₀⟩, a⟩
    · exact ⟨(inU_biInf hS q U.U S _).2 fun α hα => ((inP _ _ T).1 (h.2 α hα)).1, inU_top hS q' _⟩
  have hK : ∀ S : Finset U.ι, S.Nonempty →
      (hodgeXD q q' p₁ p₂ hw).Kun (capU V S) (inU q' ⊤) (capU W S) (h₁ S) (h₂ S) := by
    intro S hSn
    obtain ⟨α₀, h₀⟩ := id hSn
    obtain ⟨c, -⟩ := coord_res (U.c α₀) (iInf₂_le α₀ h₀) (U.inter S hSn)
    exact kun_congr _ (eV S hSn) (eW S hSn) _ _ _ _
      (GlobalTheory.T.kuenneth_product_local_global hS hMV hCD hZ hA hKA K X X' P q q' p₁ p₂ hP _ _ ⟨c⟩
        (fun T h => ((inP _ _ T).1 h).1) (fun T h => ((inP _ _ T).1 h).2))
  have e₁ : capU V ∅ = fun T => ∃ α, inU q (U.U α) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have e₃ : capU W ∅ = fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have k₁ : capU V ∅ ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have k₃ : capU W ∅ ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨⟨α, hα⟩, -⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  have hc : (⨆ α, p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) = p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ := by
    refine le_antisymm (iSup_le fun α => inf_le_inf_right _ ((TopologicalSpace.Opens.map p₁.base).monotone le_top)) ?_
    intro x _
    have hx : p₁ x ∈ (⨆ α, U.U α) := by
      rw [U.cover]
      trivial
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨α, hα, trivial⟩
  have l₁ : (fun T => ∃ α, inU q (U.U α) T) ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have l₃ : (fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T) ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨α, hα⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  exact glue_top hMV hCD (hodgeXD q q' p₁ p₂ hw) (inU q ⊤) (inU q' ⊤) _ V W
    (fun α => inU_cos hS q _) (fun α => inU_cos hS _ _) h₁ h₂ hK k₁ k₃
    (fun a n => resU_bij_congr _ e₁ k₁ l₁ n (hZ K X q U.ι ⊤ U.U U.cover l₁ a n))
    (fun a n => resU_bij_congr _ e₃ k₃ l₃ n (hZ K P (p₁ ≫ q) U.ι _ _ hc l₃ a n)) g₁ g₂

end GlobalTheory.CompanionTheory.KunGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductProperSmoothStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_product_proper_smooth : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_left | exact GlobalTheory.CompanionTheory.KunGlue.kun_left | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_left <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethIsoProperSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethIsoProperSmooth
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

variable {K : Type} [Field K]

def topResEquiv (hT : TopRes) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C)
    (hU : ∀ T, U T) (n : ℕ) : CH.H F n ≃ₗ[K] CH.H (U.ι ⋙ F) n :=
  LinearEquiv.ofBijective ((CH.Mor.restrict F U.ι).pull n)
    (CrystallineSemistableComparison.P.mapH_bij (CH.Mor.restrict F U.ι).hom (fun m => (hT K C F U ⊥ hU m).1) n)

theorem cls_congr' {R : Type} [CommRing R] {L : Cx.{1} R} {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0)
    (hy : L.d n y = 0) : L.cls x hx = L.cls y hy := by
  subst e
  rfl

theorem XD.pr_restrict (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {a a' c p q n : ℕ} (ha : a + a' = c)
    (h : p + q = n) (x : CH.Cn (E.F₁ a) p) (y : CH.Cn (E.F₂ a') q) :
    (E.pr U₁ U₂ U₃ h₁ h₂ ha).μ h ((CH.Mor.restrict (E.F₁ a) U₁.ι).pullC p x)
        ((CH.Mor.restrict (E.F₂ a') U₂.ι).pullC q y) =
      (CH.Mor.restrict (E.F₃ c) U₃.ι).pullC n
        ((E.μ ha).cupC h ((E.m₁ a).pullC p x) ((E.m₂ a').pullC q y)) := by
  funext s
  rfl

theorem XD.kun_cup (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {c n : ℕ}
    (e : (⨁ t : Idx c n, (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) ≃ₗ[K]
      (CH.cx (U₃.ι ⋙ E.F₃ c)).H n)
    (he : ∀ (t : Idx c n) (x : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).X t.i) (y : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).X t.j)
      (hx : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).d t.i x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).d t.j y = 0)
      (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        ((CH.cx (U₁.ι ⋙ E.F₁ t.a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ t.a')).cls y hy)) =
        (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) hz)
    (t : Idx c n) (u : CH.H (E.F₁ t.a) t.i) (v : CH.H (E.F₂ t.a') t.j) :
    topResEquiv hT (E.F₃ c) U₃ hU₃ n
        ((E.μ t.ha).cup t.h ((E.m₁ t.a).pull t.i u) ((E.m₂ t.a').pull t.j v)) =
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        (topResEquiv hT (E.F₁ t.a) U₁ hU₁ t.i u ⊗ₜ topResEquiv hT (E.F₂ t.a') U₂ hU₂ t.j v)) := by
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj u
  obtain ⟨y, hy, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj v
  have hx₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₁ t.a).hom x hx
  have hy₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₂ t.a').hom y hy
  obtain ⟨hc, ec⟩ := CrystallineSemistableComparison.P.cup_cls (E.μ t.ha) t.h _ _ hx₁ hy₁
  have hx₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₁ t.a) U₁.ι).hom x hx
  have hy₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₂ t.a') U₂.ι).hom y hy
  have hc₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₃ c) U₃.ι).hom _ hc
  have hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h
      ((CH.Mor.restrict (E.F₁ t.a) U₁.ι).pullC t.i x) ((CH.Mor.restrict (E.F₂ t.a') U₂.ι).pullC t.j y)) = 0 := by
    rw [XD.pr_restrict]
    exact hc₂
  have key := he t _ _ hx₂ hy₂ hz
  refine Eq.trans ?_ key.symm |>.trans rfl
  change (CH.Mor.restrict (E.F₃ c) U₃.ι).pull n ((E.μ t.ha).cup t.h ((CH.cx _).cls _ hx₁) ((CH.cx _).cls _ hy₁)) = _
  rw [ec]
  exact cls_congr' (XD.pr_restrict E U₁ U₂ U₃ h₁ h₂ t.ha t.h x y).symm hc₂ hz

def sliceMap {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) :
    A ⊗[K] B →ₗ[K] B₀ :=
  (TensorProduct.lid K B₀).toLinearMap ∘ₗ TensorProduct.map (φ ∘ₗ r₁.symm.toLinearMap) r₂.symm.toLinearMap

theorem sliceMap_tmul {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) (u : A₀) (v : B₀) :
    sliceMap r₁ r₂ φ (r₁ u ⊗ₜ r₂ v) = φ u • v := by
  simp [sliceMap]

def compMap {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) : A →ₗ[K] W :=
  g ∘ₗ DirectSum.component K ι N t₀ ∘ₗ e.symm.toLinearMap ∘ₗ ρ.toLinearMap

theorem compMap_self {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (w : N t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t₀ w)) : compMap N ρ e t₀ g x = g w := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.lof_self]

theorem compMap_ne {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (t : ι) (w : N t) (ht : t ≠ t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t w)) : compMap N ρ e t₀ g x = 0 := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.of, dite_eq_right ht, map_zero]

theorem XD.slant (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (hK : E.Kun U₁ U₂ U₃ h₁ h₂)
    (a i a' j c n : ℕ) (ha : a + a' = c) (h : i + j = n) (φ : Module.Dual K (CH.H (E.F₁ a) i)) :
    ∃ sl : CH.H (E.F₃ c) n →ₗ[K] CH.H (E.F₂ a') j,
      (∀ u v, sl ((E.μ ha).cup h ((E.m₁ a).pull i u) ((E.m₂ a').pull j v)) = φ u • v) ∧
      ∀ (b i' b' j' : ℕ) (hb : b + b' = c) (h' : i' + j' = n), (b, i') ≠ (a, i) →
        ∀ (u : CH.H (E.F₁ b) i') (v : CH.H (E.F₂ b') j'),
          sl ((E.μ hb).cup h' ((E.m₁ b).pull i' u) ((E.m₂ b').pull j' v)) = 0 := by
  obtain ⟨e, he⟩ := hK c n
  have kc := XD.kun_cup hT E U₁ U₂ U₃ hU₁ hU₂ hU₃ h₁ h₂ e he
  refine ⟨compMap (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j)
    (topResEquiv hT (E.F₃ c) U₃ hU₃ n) e ⟨a, i, a', j, ha, h⟩
    (sliceMap (topResEquiv hT (E.F₁ a) U₁ hU₁ i) (topResEquiv hT (E.F₂ a') U₂ hU₂ j) φ), ?_, ?_⟩
  · intro u v
    exact (compMap_self _ _ e _ _ _ _ (kc ⟨a, i, a', j, ha, h⟩ u v)).trans (sliceMap_tmul _ _ φ u v)
  · intro b i' b' j' hb h' hne u v
    refine compMap_ne _ _ e _ _ _ ⟨b, i', b', j', hb, h'⟩ _ ?_ (kc ⟨b, i', b', j', hb, h'⟩ u v)
    intro hh
    exact hne (by rw [show b = a from congrArg Idx.a hh, show i' = i from congrArg Idx.i hh])

theorem slant_of_kun : TopRes → SiteLaws → (∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂) → Slant := by
  intro hT hS hK K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP a i a' j c n ha h φ
  have top₁ : ∀ T, inU q ⊤ T := fun T => (hS K X X X q (𝟙 X) (𝟙 X)).2.2.1 T
  have top₂ : ∀ T, inU q' ⊤ T := fun T => (hS K X' X' X' q' (𝟙 X') (𝟙 X')).2.2.1 T
  have topP : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    have e : p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ = ⊤ := by simp
    rw [e]
    exact fun T => (hS K P P P (p₁ ≫ q) (𝟙 P) (𝟙 P)).2.2.1 T
  have h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T) :=
    fun T _ => top₁ _
  have h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T) :=
    fun T _ => top₂ _
  exact XD.slant hT (hodgeXD q q' p₁ p₂ hP.w.symm) (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤))
    top₁ top₂ topP h₁ h₂ (hK K X X' P q q' p₁ p₂ hP h₁ h₂) a i a' j c n ha h φ

end GlobalTheory.CompanionTheory.KunGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethIsoProperSmoothStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slant_of_hodge_kuenneth : TopRes → SiteLaws → (∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂) → Slant := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.slant_of_kun | exact GlobalTheory.CompanionTheory.KunGlue.slant_of_kun | (intros; apply GlobalTheory.CompanionTheory.KunGlue.slant_of_kun <;> assumption)
end
end

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.KunGlue

theorem slantOf : CrystallineSemistableComparison.Onto.TopRes → CrystallineSemistableComparison.Onto.SlantOf :=
  fun hT hS hM hC hZ hA hK => GlobalTheory.T.slant_of_hodge_kuenneth hT hS (fun K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP h₁ h₂ =>
    GlobalTheory.T.kuenneth_product_proper_smooth hS hM hC hZ hA hK K X X' P q q' p₁ p₂ hP h₁ h₂)

end GlobalTheory.CompanionTheory.KunGlue
