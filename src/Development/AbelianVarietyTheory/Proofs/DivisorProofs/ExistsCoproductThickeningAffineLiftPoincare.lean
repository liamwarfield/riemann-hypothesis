module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeCrystallineThickeningOneElementLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningQuotientFreeThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeThickeningLevelFinitelyManyElements
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeThickeningLevelFinitelyManyElements
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.FreeFin

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}

theorem isFree_id (n : ℕ) (T : Thick κ t) (hT : IsLev T.δ n) :
    IsFree n (𝟙 T) (Fin.elim0 : Fin 0 → T.B) := by
  refine ⟨hT, fun i ↦ i.elim0, fun S _ a c _ ↦ ⟨a, ⟨Category.id_comp a, fun i ↦ i.elim0⟩, ?_⟩⟩
  rintro g ⟨hg, -⟩
  rw [← hg, Category.id_comp]

theorem isFree_cons (n m : ℕ) {T F F' : Thick κ t} (u : T ⟶ F) (τ : Fin m → F.B) (hu : IsFree n u τ)
    (u' : F ⟶ F') (τ' : Unit → F'.B) (hu' : IsFree n u' τ') :
    IsFree n (u ≫ u') (Fin.cons (τ' ()) (fun i ↦ u'.φ (τ i)) : Fin (m + 1) → F'.B) := by
  obtain ⟨-, hτ, hU⟩ := hu
  obtain ⟨hF', hτ', hU'⟩ := hu'
  refine ⟨hF', fun i ↦ Fin.cases (hτ' ()) (fun j ↦ Thick.Hom.mem u' (hτ j)) i, ?_⟩
  intro S hS a c hc
  obtain ⟨g₁, ⟨hg₁a, hg₁c⟩, hg₁u⟩ := hU S hS a (fun j ↦ c j.succ) (fun j ↦ hc j.succ)
  obtain ⟨g, ⟨hga, hgc⟩, hgu⟩ := hU' S hS g₁ (fun _ ↦ c 0) (fun _ ↦ hc 0)
  refine ⟨g, ⟨?_, fun i ↦ ?_⟩, ?_⟩
  · rw [Category.assoc, hga, hg₁a]
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using hgc ()
    · simp only [Fin.cons_succ]
      rw [← Thick.comp_φ, hga, hg₁c]
  · rintro g' ⟨hg'a, hg'c⟩
    have h1 : u' ≫ g' = g₁ := by
      refine hg₁u _ ⟨by rw [← Category.assoc, hg'a], fun j ↦ ?_⟩
      have := hg'c j.succ
      simp only [Fin.cons_succ] at this
      rw [Thick.comp_φ, this]
    refine hgu _ ⟨h1, fun _ ↦ ?_⟩
    simpa using hg'c 0

theorem exists_free : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (n m : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) →
    ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Fin m → F.B), IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  intro R _ I κ X t n m T hT
  induction m with
  | zero => exact ⟨T, 𝟙 T, Fin.elim0, isFree_id _ T hT, QAtFormal.qAt_ident _ T⟩
  | succ m ih =>
    obtain ⟨F, u, τ, hu, hq⟩ := ih
    obtain ⟨F', u', τ', hu', hq'⟩ := GlobalTheory.T.exists_freeCrystallineThickening_oneElement_level R I κ X t n F hu.1
    exact ⟨F', u ≫ u', _, isFree_cons (n + 1) m u τ hu u' τ' hu', QAtFormal.qAt_comp _ u u' hq hq'⟩

end GlobalTheory.PDForm.FreeFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeThickeningLevelFinitelyManyElementsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_freeThickening_level_finitelyMany_elements : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (n m : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) → ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Fin m → F.B), IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  first | exact @GlobalTheory.PDForm.FreeFin.exists_free | exact GlobalTheory.PDForm.FreeFin.exists_free | (intros; apply GlobalTheory.PDForm.FreeFin.exists_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientNilCrystallineThickeningOfSubDPIde
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientNilCrystallineThickeningOfSubDPIde
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.ThickQuot

section Ring

variable {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {𝔟 : Ideal B}
  (h𝔟 : δ.IsSubDPIdeal 𝔟)
include h𝔟

theorem isSubDPIdeal_inf : δ.IsSubDPIdeal (𝔟 ⊓ J) := by
  rw [inf_eq_left.mpr h𝔟.isSubideal]; exact h𝔟

def qdp : DividedPowers (J.map (Ideal.Quotient.mk 𝔟)) :=
  DividedPowers.Quotient.dividedPowers δ (isSubDPIdeal_inf δ h𝔟)

theorem qdp_apply {n : ℕ} {a : B} (ha : a ∈ J) :
    (qdp δ h𝔟).dpow n (Ideal.Quotient.mk 𝔟 a) = Ideal.Quotient.mk 𝔟 (δ.dpow n a) :=
  DividedPowers.Quotient.dpow_apply δ (isSubDPIdeal_inf δ h𝔟) ha

theorem qdp_isDPMorphism : IsDPMorphism δ (qdp δ h𝔟) (Ideal.Quotient.mk 𝔟) :=
  DividedPowers.Quotient.isDPMorphism δ (isSubDPIdeal_inf δ h𝔟)

theorem lift_list (l : List (ℕ × (B ⧸ 𝔟))) (hl : ∀ p ∈ l, p.2 ∈ J.map (Ideal.Quotient.mk 𝔟)) :
    ∃ l' : List (ℕ × B), (∀ p ∈ l', p.2 ∈ J) ∧ l'.map Prod.fst = l.map Prod.fst ∧
      Ideal.Quotient.mk 𝔟 ((l'.map fun p ↦ δ.dpow p.1 p.2).prod) =
        (l.map fun p ↦ (qdp δ h𝔟).dpow p.1 p.2).prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨a, ha, hpa⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (hl p List.mem_cons_self)
    refine ⟨(p.1, a) :: l', ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ha
      · exact h1 q hq
    · simp [h2]
    · simp only [List.map_cons, List.prod_cons, map_mul, h3]
      rw [← hpa, qdp_apply δ h𝔟 ha]

theorem isLev_qdp {n : ℕ} (hn : IsLev δ n) : IsLev (qdp δ h𝔟) n := by
  rw [isLev_iff_prod] at hn ⊢
  intro l hl hs
  obtain ⟨l', h1, h2, h3⟩ := lift_list δ h𝔟 l hl
  rw [← h3, hn l' h1 (h2 ▸ hs), map_zero]

theorem isDPNilpotent_quotient (hδ : IsNilDP δ) : IsNilDP (qdp δ h𝔟) := by
  rw [isDPNilpotent_iff_exists_isLevel] at hδ ⊢
  obtain ⟨n, hn⟩ := hδ
  exact ⟨n, isLev_qdp δ h𝔟 hn⟩

end Ring

section Thick

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  (T : Thick κ t) {𝔟 : Ideal T.B} (h𝔟 : T.δ.IsSubDPIdeal 𝔟)
include h𝔟

def quot : Thick κ t where
  B := T.B ⧸ 𝔟
  J := T.J.map (Ideal.Quotient.mk 𝔟)
  δ := qdp T.δ h𝔟
  nil := isDPNilpotent_quotient T.δ h𝔟 T.nil
  dp := by
    have : algebraMap R (T.B ⧸ 𝔟) = (Ideal.Quotient.mk 𝔟).comp (algebraMap R T.B) := rfl
    rw [this]
    exact (qdp_isDPMorphism T.δ h𝔟).comp _ T.dp
  B₀ := T.B₀
  π := Ideal.Quotient.lift 𝔟 T.π fun a ha ↦ (T.ker a).2 (h𝔟.isSubideal ha)
  surj := Ideal.Quotient.lift_surjective_of_surjective _ _ T.surj
  ker b := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.lift_mk, T.ker, Ideal.mem_quotient_iff_mem h𝔟.isSubideal]
  x := T.x
  w := by
    convert T.w using 2
    exact RingHom.ext fun _ ↦ rfl

def proj : T ⟶ quot T h𝔟 where
  φ := Ideal.Quotient.mkₐ R 𝔟
  φ₀ := RingHom.id T.B₀
  comm _ := rfl
  dp := qdp_isDPMorphism T.δ h𝔟
  pt := by
    show spMap (RingHom.id T.B₀) ≫ T.x = T.x
    rw [spMap_id, Category.id_comp]

def desc {S : Thick κ t} (a : T ⟶ S) (ha : ∀ b ∈ 𝔟, a.φ b = 0) : quot T h𝔟 ⟶ S where
  φ := Ideal.Quotient.liftₐ 𝔟 a.φ ha
  φ₀ := a.φ₀
  comm b := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact a.comm c
  dp := by
    refine ⟨?_, fun {n} y hy ↦ ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      obtain ⟨c, hc, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
      exact Thick.Hom.mem a hc
    · obtain ⟨c, hc, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
      have e1 : (quot T h𝔟).δ.dpow n (Ideal.Quotient.mk 𝔟 c) = Ideal.Quotient.mk 𝔟 (T.δ.dpow n c) :=
        qdp_apply T.δ h𝔟 hc
      rw [e1]
      exact a.dp.2 c hc
  pt := a.pt

end Thick

section Main

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem exists_quotient : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (T : Thick κ t) (𝔟 : Ideal T.B), T.δ.IsSubDPIdeal 𝔟 → ∃ (G : Thick κ t) (q : T ⟶ G), Function.Surjective q.φ ∧ (∀ b, q.φ b = 0 ↔ b ∈ 𝔟) ∧ G.J = T.J.map (q.φ : T.B →+* G.B) ∧ (∀ n, IsLev T.δ n → IsLev G.δ n) ∧ ∀ (S : Thick κ t) (a : T ⟶ S), (∀ b ∈ 𝔟, a.φ b = 0) → ∃! g : G ⟶ S, q ≫ g = a := by
  intro R _ I κ X t T 𝔟 h𝔟
  refine ⟨quot T h𝔟, proj T h𝔟, Ideal.Quotient.mkₐ_surjective R 𝔟, fun b ↦ Ideal.Quotient.eq_zero_iff_mem,
    rfl, fun n hn ↦ isLev_qdp T.δ h𝔟 hn, fun S a ha ↦
      ⟨desc T h𝔟 a ha, Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl), fun g hg ↦
        Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_)⟩⟩
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg (fun f : T ⟶ S ↦ f.φ c) hg

end Main

end GlobalTheory.ThickQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientNilCrystallineThickeningOfSubDPIdeStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_nilCrystallineThickening_of_subDPIdeal : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (T : Thick κ t) (𝔟 : Ideal T.B), T.δ.IsSubDPIdeal 𝔟 → ∃ (G : Thick κ t) (q : T ⟶ G), Function.Surjective q.φ ∧ (∀ b, q.φ b = 0 ↔ b ∈ 𝔟) ∧ G.J = T.J.map (q.φ : T.B →+* G.B) ∧ (∀ n, IsLev T.δ n → IsLev G.δ n) ∧ ∀ (S : Thick κ t) (a : T ⟶ S), (∀ b ∈ 𝔟, a.φ b = 0) → ∃! g : G ⟶ S, q ≫ g = a := by
  first | exact @GlobalTheory.ThickQuot.exists_quotient | exact GlobalTheory.ThickQuot.exists_quotient | (intros; apply GlobalTheory.ThickQuot.exists_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningQuotientFreeThickening
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CopEx

theorem exists_cop : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) →
    ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (F G : Thick D.κ D.t) (u : T ⟶ F) (q : F ⟶ G) (r : Λ.L.obj U ⟶ G),
      (KK D.κ D.t).QAt u ∧ IsLev F.δ (n + 1) ∧ Function.Surjective q.φ ∧ (∀ b, q.φ b ∈ G.J → b ∈ F.J) ∧
        IsCop (n + 1) (u ≫ q) r := by
  intro D Λ n U T hT hU
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.hom_spec_points_levels D Λ
  haveI : Algebra.Smooth D.R (Sec D.s U.unop.1) := (GlobalTheory.T.smooth_sections_mono_reduction_affine_inf D).1 U.unop
  obtain ⟨m, pres, hpres⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType D.R (Sec D.s U.unop.1))
  obtain ⟨g, hgx, hgR⟩ := h2 U T hU
  choose bl hbl using fun i : Fin m ↦ T.surj (g (pres (MvPolynomial.X i)))
  obtain ⟨F, u, τ, hfree, hQ⟩ := GlobalTheory.T.exists_freeThickening_level_finitelyMany_elements D.R D.I D.κ D.X₀ D.t n m T hT
  let ψ : MvPolynomial (Fin m) D.R →ₐ[D.R] F.B := MvPolynomial.aeval fun i ↦ u.φ (bl i) + τ i
  have hψX : ∀ i, ψ (MvPolynomial.X i) = u.φ (bl i) + τ i := fun i ↦ MvPolynomial.aeval_X _ _

  have hψπ : ∀ p, F.π (ψ p) = u.φ₀ (g (pres p)) := by
    have e : F.π.comp (ψ : MvPolynomial (Fin m) D.R →+* F.B) =
        u.φ₀.comp (g.comp (pres : MvPolynomial (Fin m) D.R →+* Sec D.s U.unop.1)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show F.π (ψ (MvPolynomial.C r)) = u.φ₀ (g (pres (MvPolynomial.C r)))
        have hC : MvPolynomial.C r = algebraMap D.R (MvPolynomial (Fin m) D.R) r := rfl
        rw [hC, AlgHom.commutes, AlgHom.commutes, hgR, u.comm, u.φ.commutes]
      · intro i
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hψX, map_add (f := _)]
        rw [(F.ker _).2 (hfree.2.1 i), add_zero, ← hbl i, u.comm]
    exact fun p ↦ RingHom.congr_fun e p
  have hker : ∀ k ∈ RingHom.ker pres, ψ k ∈ F.J := fun k hk ↦
    (F.ker _).1 (by rw [hψπ, (RingHom.mem_ker).1 hk, map_zero, map_zero])
  set 𝔟 : Ideal F.B := Ideal.span {y | ∃ j : ℕ, j ≠ 0 ∧ ∃ x ∈ ψ '' (RingHom.ker pres : Set _), y = F.δ.dpow j x}
    with h𝔟def
  have h𝔟 : F.δ.IsSubDPIdeal 𝔟 := (GlobalTheory.DPQuot.quotient_subDPIdeal F.B F.J F.δ).2 _ (by
    rintro _ ⟨k, hk, rfl⟩; exact hker k hk)
  obtain ⟨G, q, hqs, hq0, hGJ, hGlev, hquniv⟩ := GlobalTheory.T.exists_quotient_nilCrystallineThickening_of_subDPIdeal D.R D.I D.κ D.X₀ D.t F 𝔟 h𝔟
  have hψ𝔟 : ∀ k ∈ RingHom.ker pres, (q.φ.comp ψ) k = 0 := fun k hk ↦ (hq0 _).2
    (Ideal.subset_span ⟨1, one_ne_zero, ψ k, ⟨k, hk, rfl⟩, (F.δ.dpow_one (hker k hk)).symm⟩)

  let y : Sec D.s U.unop.1 →ₐ[D.R] G.B :=
    (Ideal.Quotient.liftₐ (RingHom.ker pres) (q.φ.comp ψ) hψ𝔟).comp
      (Ideal.quotientKerAlgEquivOfSurjective hpres).symm.toAlgHom
  have hy : ∀ p, y (pres p) = q.φ (ψ p) := by
    intro p
    have : (Ideal.quotientKerAlgEquivOfSurjective hpres).symm (pres p) = Ideal.Quotient.mk _ p :=
      (AlgEquiv.symm_apply_eq _).2 rfl
    change Ideal.Quotient.liftₐ (RingHom.ker pres) (q.φ.comp ψ) hψ𝔟
      ((Ideal.quotientKerAlgEquivOfSurjective hpres).symm (pres p)) = _
    rw [this]
    rfl
  have hyπ : G.π.comp (y : Sec D.s U.unop.1 →+* G.B) = (u ≫ q).φ₀.comp g := by
    ext a
    obtain ⟨p, rfl⟩ := hpres a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hy]
    rw [← q.comm, hψπ]
    rfl
  obtain ⟨r, hr⟩ := (h1 U G y).1 (by
    rw [hyπ, Cris.spMap_comp, Category.assoc, hgx, ← Category.assoc, (u ≫ q).pt])
  refine ⟨F, G, u, q, r, hQ, hfree.1, hqs, ?_, hGlev _ hfree.1, ?_⟩
  · intro b hb
    rw [hGJ] at hb
    obtain ⟨j, hj, hjb⟩ := (Ideal.mem_map_iff_of_surjective _ hqs).1 hb
    have : b - j ∈ 𝔟 := (hq0 _).1 (by rw [map_sub]; change q.φ b - q.φ j = 0; rw [← hjb]; exact sub_self _)
    have := F.J.add_mem hj (h𝔟.isSubideal this)
    rwa [add_sub_cancel] at this
  intro S hS a b

  have hsame : ∀ x, S.π (b.φ (Λ.e U x)) = a.φ₀ (g x) := by
    have e := h3 U S.B₀ (b.φ₀.comp ((Λ.L.obj U).π.comp (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B)))
      (a.φ₀.comp g) (by
        rw [Cris.spMap_comp, Category.assoc, Λ.pt U, ← Category.assoc, b.pt, Cris.spMap_comp, Category.assoc, hgx, ← Category.assoc, a.pt])
    intro x
    rw [← b.comm]
    exact RingHom.congr_fun e x
  let c : Fin m → S.B := fun i ↦ b.φ (Λ.e U (pres (MvPolynomial.X i))) - a.φ (bl i)
  have hc : ∀ i, c i ∈ S.J := by
    intro i
    refine (S.ker _).1 ?_
    simp only [c, map_sub, hsame, ← a.comm, hbl i, sub_self]
  obtain ⟨g', ⟨hg'u, hg'τ⟩, hg'uniq⟩ := hfree.2.2 S hS a c hc
  have hg'ψ : ∀ p, g'.φ (ψ p) = b.φ (Λ.e U (pres p)) := by
    have e : g'.φ.comp ψ = b.φ.comp ((Λ.e U).toAlgHom.comp pres) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, hψX, map_add (f := _), AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
      rw [hg'τ i, ← Thick.comp_φ, hg'u]
      simp only [c]
      abel
    exact fun p ↦ AlgHom.congr_fun e p
  have hkill : ∀ z ∈ 𝔟, g'.φ z = 0 := by
    intro z hz
    refine (Ideal.span_le (I := RingHom.ker (g'.φ : F.B →+* S.B))).2 ?_ hz
    rintro _ ⟨j, hj, _, ⟨k, hk, rfl⟩, rfl⟩
    change g'.φ (F.δ.dpow j (ψ k)) = 0
    have hdp := g'.dp.dpow_comp (n := j) _ (hker k hk)
    change S.δ.dpow j (g'.φ (ψ k)) = g'.φ (F.δ.dpow j (ψ k)) at hdp
    rw [← hdp, hg'ψ, (RingHom.mem_ker).1 hk, map_zero, map_zero, dpow_eval_zero _ hj]
  obtain ⟨c0, hc0, hc0u⟩ := hquniv S g' hkill
  refine ⟨c0, ⟨by rw [Category.assoc, hc0, hg'u], ?_⟩, ?_⟩
  · apply Thick.Hom.ext'
    apply AlgHom.ext
    intro z
    obtain ⟨x, rfl⟩ := (Λ.e U).surjective z
    obtain ⟨p, rfl⟩ := hpres x
    rw [Thick.comp_φ, hr, hy, ← Thick.comp_φ, hc0, hg'ψ]
  · rintro c1 ⟨hc1a, hc1b⟩
    refine hc0u c1 (hg'uniq (q ≫ c1) ⟨by rw [← Category.assoc, hc1a], fun i ↦ ?_⟩)
    have hτ : τ i = ψ (MvPolynomial.X i) - u.φ (bl i) := by rw [hψX]; abel
    rw [hτ, map_sub, Thick.comp_φ, Thick.comp_φ, ← hy, ← hr, ← Thick.comp_φ, hc1b, ← Thick.comp_φ q c1,
      ← Thick.comp_φ u, ← Category.assoc, hc1a]

end GlobalTheory.CopEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningQuotientFreeThickeningStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coproductThickening_quotient_freeThickening : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) → ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (F G : Thick D.κ D.t) (u : T ⟶ F) (q : F ⟶ G) (r : Λ.L.obj U ⟶ G), (KK D.κ D.t).QAt u ∧ IsLev F.δ (n + 1) ∧ Function.Surjective q.φ ∧ (∀ b, q.φ b ∈ G.J → b ∈ F.J) ∧ IsCop (n + 1) (u ≫ q) r := by
  first | exact @GlobalTheory.CopEx.exists_cop | exact GlobalTheory.CopEx.exists_cop | (intros; apply GlobalTheory.CopEx.exists_cop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningAffineLiftPoincare
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.CopPoincare

theorem isNilpotent_of_isNilDP {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) :
    IsNilpotent J := by
  obtain ⟨N, hN⟩ := (isDPNilpotent_iff_exists_isLevel δ).1 h
  have key : ∀ (m : ℕ), ∀ x ∈ J ^ m, ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) → N ≤ m + (l.map Prod.fst).sum →
      x * (l.map fun p ↦ δ.dpow p.1 p.2).prod = 0 := by
    intro m
    induction m with
    | zero =>
      intro x _ l hl hs
      rw [(isLev_iff_prod δ N).1 hN l hl (by simpa using hs), mul_zero]
    | succ m ih =>
      intro x hx l hl hs
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero])
      have := ih a ha ((1, b) :: l) (by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hb
        · exact hl p hp) (by simp only [List.map_cons, List.sum_cons]; omega)
      simpa [δ.dpow_one hb, mul_assoc] using this
  refine ⟨N, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  intro x hx
  simpa using key N x hx [] (by simp) (by simp)

theorem exists_cop_qAt : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) → ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (G : Thick D.κ D.t) (l : T ⟶ G) (r : Λ.L.obj U ⟶ G), IsCop (n + 1) l r ∧ (KK D.κ D.t).QAt l := by
  intro D Λ n U T hT hU
  obtain ⟨F, G, u, q, r, hu, hF, hq, hJ, hc⟩ := GlobalTheory.T.exists_coproductThickening_quotient_freeThickening D Λ n U T hT hU
  obtain ⟨h1, -, -, -⟩ := GlobalTheory.T.hom_spec_points_levels D Λ
  refine ⟨G, u ≫ q, r, hc, ?_⟩
  haveI := D.sec_smooth U.unop
  have hker : RingHom.ker (q.φ : F.B →+* G.B) ≤ F.J := fun b hb ↦ hJ b (by
    rw [show q.φ b = 0 from hb]; exact G.J.zero_mem)
  have hnil : IsNilpotent (RingHom.ker (q.φ : F.B →+* G.B)) := by
    obtain ⟨N, hN⟩ := isNilpotent_of_isNilDP F.nil
    refine ⟨N, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
    exact Ideal.pow_right_mono hker N
  let y : Sec D.s U.unop.1 →ₐ[D.R] G.B := r.φ.comp (Λ.e U : Sec D.s U.unop.1 →ₐ[D.R] (Λ.L.obj U).B)
  let y' : Sec D.s U.unop.1 →ₐ[D.R] F.B := Algebra.FormallySmooth.liftOfSurjective y q.φ hq hnil
  have hy' : ∀ a, q.φ (y' a) = y a := fun a ↦ Algebra.FormallySmooth.liftOfSurjective_apply y q.φ hq hnil a
  have hbij : Function.Bijective q.φ₀ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, fun c ↦ ?_⟩
    · obtain ⟨b, rfl⟩ := F.surj b
      rw [q.comm, G.ker] at hb
      exact (F.ker b).2 (hJ b hb)
    · obtain ⟨c, rfl⟩ := G.surj c
      obtain ⟨b, rfl⟩ := hq c
      exact ⟨F.π b, q.comm b⟩
  haveI : IsIso (spMap q.φ₀) :=
    (inferInstance : IsIso (Spec.map (RingEquiv.ofBijective q.φ₀ hbij).toCommRingCatIso.hom))
  have hy := (h1 U G y).2 ⟨r, fun _ ↦ rfl⟩
  have hpt : spMap (F.π.comp (y' : Sec D.s U.unop.1 →+* F.B)) ≫ affPt D.s U.unop = F.x ≫ D.i := by
    rw [← cancel_epi (spMap q.φ₀), ← Category.assoc, ← Cris.spMap_comp, ← Category.assoc, q.pt, ← hy]
    congr 2
    ext a
    exact (q.comm _).trans (congrArg G.π (hy' a))
  obtain ⟨b', hb'⟩ := (h1 U F y').1 hpt
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := hc.2 F hF u b'
  have hbq : b' ≫ q = r := by
    have hφ : (b' ≫ q).φ = r.φ := AlgHom.ext fun b ↦ by
      obtain ⟨a, rfl⟩ := (Λ.e U).surjective b
      change q.φ (b'.φ ((Λ.e U) a)) = r.φ ((Λ.e U) a)
      rw [hb', hy']; rfl
    have extHom : ∀ {f g : Thick.Hom (Λ.L.obj U) G}, f.φ = g.φ → f = g := by
      intro f g h
      rcases f with ⟨φ, φ₀, comm, dp, pt⟩
      rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
      obtain rfl : φ = ψ := h
      obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
        obtain ⟨b, rfl⟩ := (Λ.L.obj U).surj c
        rw [comm, comm']
      rfl
    exact extHom hφ
  have hsq : s ≫ q = 𝟙 G := by
    obtain ⟨c, -, huniq⟩ := hc.2 G hc.1 (u ≫ q) r
    refine (huniq _ ⟨?_, ?_⟩).trans (huniq _ ⟨Category.comp_id _, Category.comp_id _⟩).symm
    · rw [← Category.assoc, hs1]
    · rw [← Category.assoc, hs2, hbq]
  exact (GlobalTheory.CxCoh.QAtFormal.qAt_formal _ (KK D.κ D.t)).2.2 T G F (u ≫ q) s q hsq (by rw [hs1]; exact hu)

end GlobalTheory.PDForm.CopPoincare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningAffineLiftPoincareStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coproduct_thickening_affine_lift_poincare : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) → ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (G : Thick D.κ D.t) (l : T ⟶ G) (r : Λ.L.obj U ⟶ G), IsCop (n + 1) l r ∧ (KK D.κ D.t).QAt l := by
  first | exact @GlobalTheory.PDForm.CopPoincare.exists_cop_qAt | exact GlobalTheory.PDForm.CopPoincare.exists_cop_qAt | (intros; apply GlobalTheory.PDForm.CopPoincare.exists_cop_qAt <;> assumption)
end
