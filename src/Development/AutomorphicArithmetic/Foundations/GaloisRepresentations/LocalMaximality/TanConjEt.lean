module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.KaehlerVanishing.DerivationEqOfFormallyEtaleOfEvaluationEq
open KaehlerDifferential

namespace UpperTheory.EtaleExpansion

private abbrev D := TrivSqZeroExt ℂ ℂ

private noncomputable def tw {S : Type} [CommRing S] [Algebra ℂ S] (ev : S →ₐ[ℂ] ℂ) (η : S →ₗ[ℂ] ℂ)
    (h : ∀ a b : S, η (a * b) = ev a * η b + ev b * η a) : S →+* D where
  toFun a := TrivSqZeroExt.inl (ev a) + TrivSqZeroExt.inr (η a)
  map_one' := by
    have h1 : η 1 = 0 := by
      have := h 1 1
      simp only [mul_one, map_one, one_mul] at this
      linear_combination -this
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h1]
  map_zero' := by simp
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp <;> ring
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [h]; ring

private lemma tw_fst {S : Type} [CommRing S] [Algebra ℂ S] (ev : S →ₐ[ℂ] ℂ) (η : S →ₗ[ℂ] ℂ)
    (h : ∀ a b : S, η (a * b) = ev a * η b + ev b * η a) (a : S) : (tw ev η h a).fst = ev a := by
  simp [tw]

private lemma tw_snd {S : Type} [CommRing S] [Algebra ℂ S] (ev : S →ₐ[ℂ] ℂ) (η : S →ₗ[ℂ] ℂ)
    (h : ∀ a b : S, η (a * b) = ev a * η b + ev b * η a) (a : S) : (tw ev η h a).snd = η a := by
  simp [tw]

end UpperTheory.EtaleExpansion

private theorem exists_point_derivation_eq_on_image {A S : Type} [CommRing A] [CommRing S] [Algebra ℂ A] [Algebra ℂ S]
    [Algebra A S] [IsScalarTower ℂ A S] [Algebra.FormallySmooth A S] (a2 : A →ₐ[ℂ] S)
    (ev : S →ₐ[ℂ] ℂ) (hev : ∀ f : A, ev (algebraMap A S f) = ev (a2 f)) (η : S →ₗ[ℂ] ℂ)
    (hη : ∀ a b : S, η (a * b) = ev a * η b + ev b * η a) :
    ∃ η' : S →ₗ[ℂ] ℂ, (∀ a b : S, η' (a * b) = ev a * η' b + ev b * η' a) ∧
      ∀ f : A, η' (algebraMap A S f) = η (a2 f) := by
  classical
  let T : S →+* TrivSqZeroExt ℂ ℂ := UpperTheory.EtaleExpansion.tw ev η hη
  let χ : A →+* TrivSqZeroExt ℂ ℂ := T.comp a2.toRingHom
  let fs : TrivSqZeroExt ℂ ℂ →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
  letI iD : Algebra A (TrivSqZeroExt ℂ ℂ) := χ.toAlgebra
  letI iC : Algebra A ℂ := (fs.comp χ).toAlgebra
  have hT1 : ∀ s, (T s).fst = ev s := fun s => UpperTheory.EtaleExpansion.tw_fst ev η hη s
  have hT2 : ∀ s, (T s).snd = η s := fun s => UpperTheory.EtaleExpansion.tw_snd ev η hη s
  let f : S →ₐ[A] ℂ :=
    { ev.toRingHom with
      commutes' := fun x => by
        change ev (algebraMap A S x) = (T (a2 x)).fst
        rw [hT1, hev] }
  let g : TrivSqZeroExt ℂ ℂ →ₐ[A] ℂ :=
    { fs with commutes' := fun x => rfl }
  have hg : Function.Surjective g := fun z => ⟨TrivSqZeroExt.inl z, rfl⟩
  have hnil : IsNilpotent (RingHom.ker (g : TrivSqZeroExt ℂ ℂ →+* ℂ)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Submodule.zero_eq_bot, ← le_bot_iff]
    refine Ideal.mul_le.2 fun r hr s hs => ?_
    rw [RingHom.mem_ker] at hr hs
    change r.fst = 0 at hr
    change s.fst = 0 at hs
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [hr, hs]
    · simp [hr, hs]
  let L := Algebra.FormallySmooth.liftOfSurjective f g hg hnil
  have hL1 : ∀ s, (L s).fst = ev s := fun s =>
    Algebra.FormallySmooth.liftOfSurjective_apply f g hg hnil s
  have hL2 : ∀ x : A, L (algebraMap A S x) = T (a2 x) := fun x => L.commutes x
  have hη1 : η 1 = 0 := by
    have := hη 1 1
    simp only [mul_one, map_one, one_mul] at this
    linear_combination -this
  have hLc : ∀ c : ℂ, L (algebraMap ℂ S c) = TrivSqZeroExt.inl c := by
    intro c
    rw [IsScalarTower.algebraMap_apply ℂ A S, hL2, a2.commutes]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [hT1]
      simp
    · rw [hT2, Algebra.algebraMap_eq_smul_one, map_smul, hη1]
      simp
  refine ⟨{ toFun := fun s => (L s).snd
            map_add' := fun a b => by simp
            map_smul' := fun c s => by
              simp only [RingHom.id_apply, smul_eq_mul]
              rw [Algebra.smul_def, map_mul, hLc]
              simp }, ?_, ?_⟩
  · intro a b
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, TrivSqZeroExt.snd_mul, hL1]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring
  · intro x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, hL2, hT2]

theorem UpperTheory.derivation_eq_of_formallyEtale_of_evaluation_eq :
    ∀ {A S : Type} [CommRing A] [CommRing S] [Algebra ℂ A] [Algebra ℂ S] [Algebra A S] [IsScalarTower ℂ A S] [Algebra.FormallyEtale A S] (a2 : A →ₐ[ℂ] S) (ev : S →ₐ[ℂ] ℂ), (∀ f : A, ev (algebraMap A S f) = ev (a2 f)) → ∀ (d : ℕ) (δ δ' : S →ₗ[ℂ] (Fin d → ℂ)), (∀ a b : S, δ (a * b) = ev a • δ b + ev b • δ a) → (∀ a b : S, δ' (a * b) = ev a • δ' b + ev b • δ' a) → (∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) → ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (δ a)) → (∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) → ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (δ' a)) → ∀ (τ τ' : Fin d → A) (M M' : Matrix (Fin d) (Fin d) ℂ), (∀ l, δ (algebraMap A S (τ l)) = Pi.single l 1) → (∀ j, δ (a2 (τ j)) = fun l => M j l) → (∀ l, δ' (algebraMap A S (τ' l)) = Pi.single l 1) → (∀ j, δ' (a2 (τ' j)) = fun l => M' j l) → ∃ P : Matrix (Fin d) (Fin d) ℂ, IsUnit P.det ∧ M' = P * M * P⁻¹ := by
  intro A S _ _ _ _ _ _ _ a2 ev hev d δ δ' hδ hδ' uδ uδ' τ τ' M M' hτ hM hτ' hM'
  classical
  have F1 : ∀ (ε : S →ₗ[ℂ] (Fin d → ℂ)) (σ : Fin d → A),
      (∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) →
        ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (ε a)) →
      (∀ l, ε (algebraMap A S (σ l)) = Pi.single l 1) →
      ∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) →
        ∀ a, η a = ∑ l, η (algebraMap A S (σ l)) * ε a l := by
    intro ε σ uε hσ η hη a
    obtain ⟨r, hr⟩ := uε η hη
    have hsum : ε a = ∑ l, ε a l • (Pi.single l (1 : ℂ) : Fin d → ℂ) := by
      ext j
      simp [Pi.single_apply]
    simp only [hr, hσ]
    conv_lhs => rw [hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have Fδ := F1 δ τ uδ hτ
  have Fδ' := F1 δ' τ' uδ' hτ'
  have hproj : ∀ (ε : S →ₗ[ℂ] (Fin d → ℂ)), (∀ a b : S, ε (a * b) = ev a • ε b + ev b • ε a) →
      ∀ k : Fin d, ∀ a b : S, ((LinearMap.proj k).comp ε) (a * b) =
        ev a * ((LinearMap.proj k).comp ε) b + ev b * ((LinearMap.proj k).comp ε) a := by
    intro ε hε k a b
    simp [hε]
  let Q : Matrix (Fin d) (Fin d) ℂ := fun j l => δ (algebraMap A S (τ' j)) l
  let Q' : Matrix (Fin d) (Fin d) ℂ := fun j l => δ' (algebraMap A S (τ j)) l
  have hQQ' : Q * Q' = 1 := by
    ext j k
    have := Fδ ((LinearMap.proj k).comp δ') (hproj δ' hδ' k) (algebraMap A S (τ' j))
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, hτ'] at this
    have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) j k = (Pi.single j (1 : ℂ) : Fin d → ℂ) k := by
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [Matrix.mul_apply, h1, this]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Q, Q']
    ring
  have hQM : Q * M = M' * Q := by
    ext j k
    obtain ⟨η', hη', hη'a⟩ := exists_point_derivation_eq_on_image a2 ev hev ((LinearMap.proj k).comp δ) (hproj δ hδ k)
    have e1 := Fδ η' hη' (algebraMap A S (τ' j))
    have e2 := Fδ' ((LinearMap.proj k).comp δ) (hproj δ hδ k) (a2 (τ' j))
    rw [hη'a] at e1
    simp only [hη'a, LinearMap.comp_apply, LinearMap.proj_apply, hM, hM'] at e1 e2
    rw [Matrix.mul_apply, Matrix.mul_apply]
    calc ∑ l, Q j l * M l k = ∑ l, M l k * δ (algebraMap A S (τ' j)) l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [Q]
          ring
      _ = δ (a2 (τ' j)) k := e1.symm
      _ = ∑ l, M' j l * Q l k := by
          rw [e2]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [Q]
          ring
  refine ⟨Q, Matrix.isUnit_det_of_right_inverse hQQ', ?_⟩
  rw [Matrix.inv_eq_right_inv hQQ', hQM, Matrix.mul_assoc, hQQ', Matrix.mul_one]
end

section -- merged from Development.AutomorphicArithmetic.KaehlerVanishing.KaehlerFunctionalVanishingOfLocalizationAtPrime
open KaehlerDifferential

theorem UpperTheory.kaehler_functional_vanishing_of_localization_at_prime :
    ∀ {B S : Type} [CommRing B] [CommRing S] [Algebra ℂ B] [Algebra ℂ S] [Algebra B S] [IsScalarTower ℂ B S] (p : Ideal B) [p.IsPrime] [IsLocalization.AtPrime S p] (ev : S →ₐ[ℂ] ℂ), (∀ b : B, b ∈ p ↔ ev (algebraMap B S b) = 0) → ∀ (d : ℕ) (φ : Ω[B⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : B) (ω : Ω[B⁄ℂ]), φ (b • ω) = ev (algebraMap B S b) • φ ω) → (∀ ω : Ω[B⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → B) (ω' : Fin m → Ω[B⁄ℂ]), (∀ i, ev (algebraMap B S (b i)) = 0) ∧ ω = ∑ i, b i • ω' i) → ∃ δ : S →ₗ[ℂ] (Fin d → ℂ), (∀ a b : S, δ (a * b) = ev a • δ b + ev b • δ a) ∧ (∀ b : B, δ (algebraMap B S b) = φ (KaehlerDifferential.D ℂ B b)) ∧ ∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) → ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (δ a) := by
  intro B S _ _ _ _ _ _ p _ _ ev hp d φ hφ hker
  haveI : Algebra.FormallyEtale B S := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) p.primeCompl
  have hL : ∀ η : S →ₗ[ℂ] ℂ, (∀ a b : S, η (a * b) = ev a * η b + ev b * η a) →
      ∃ L : Ω[B⁄ℂ] →ₗ[ℂ] ℂ, (∀ b : B, L (KaehlerDifferential.D ℂ B b) = η (algebraMap B S b)) ∧
        ∀ (b : B) (ω : Ω[B⁄ℂ]), L (b • ω) = ev (algebraMap B S b) * L ω := by
    intro η hη
    have h1 : η 1 = 0 := by
      have := hη 1 1
      simp only [mul_one, map_one, one_mul] at this
      linear_combination -this
    letI : Module B ℂ := Module.compHom ℂ ((ev.toRingHom).comp (algebraMap B S))
    haveI : IsScalarTower ℂ B ℂ := ⟨fun c b z => by
      change ev (algebraMap B S (c • b)) * z = c * (ev (algebraMap B S b) * z)
      rw [Algebra.smul_def c b, map_mul, map_mul, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
      simp [mul_assoc]⟩
    let D' : Derivation ℂ B ℂ :=
      { toFun := fun b => η (algebraMap B S b)
        map_add' := fun a b => by simp only [map_add (f := _)]
        map_smul' := fun c b => by
          simp only [RingHom.id_apply]
          rw [Algebra.smul_def c b, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def,
            map_smul]
        map_one_eq_zero' := by simp only [LinearMap.coe_mk, AddHom.coe_mk, map_one, h1]
        leibniz' := fun a b => by
          change η (algebraMap B S (a * b)) = ev (algebraMap B S a) * η (algebraMap B S b) +
            ev (algebraMap B S b) * η (algebraMap B S a)
          rw [map_mul, hη] }
    refine ⟨D'.liftKaehlerDifferential.restrictScalars ℂ, fun b => ?_, fun b ω => ?_⟩
    · simp only [LinearMap.coe_restrictScalars, Derivation.liftKaehlerDifferential_comp_D]
      rfl
    · simp only [LinearMap.coe_restrictScalars, map_smul]
      rfl
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ B S
  letI iS : Module S (Fin d → ℂ) := Module.compHom (Fin d → ℂ) ev.toRingHom
  letI iB : Module B (Fin d → ℂ) :=
    Module.compHom (Fin d → ℂ) ((ev.toRingHom).comp (algebraMap B S))
  haveI : IsScalarTower B S (Fin d → ℂ) := ⟨fun b s v => by
    change ev (b • s) • v = ev (algebraMap B S b) • (ev s • v)
    rw [Algebra.smul_def b s, map_mul, mul_smul]⟩
  let g : Ω[B⁄ℂ] →ₗ[B] (Fin d → ℂ) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun b ω => by rw [RingHom.id_apply]; exact hφ b ω }
  let F : Ω[S⁄ℂ] →ₗ[S] (Fin d → ℂ) := g.liftBaseChange S ∘ₗ e.symm.toLinearMap
  let δ : S →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun s => F (KaehlerDifferential.D ℂ S s)
      map_add' := fun a b => by simp only [map_add (f := _)]
      map_smul' := fun c s => by
        rw [RingHom.id_apply, Derivation.map_smul,
          ← algebraMap_smul S c (KaehlerDifferential.D ℂ S s), map_smul]
        change ev (algebraMap ℂ S c) • F (KaehlerDifferential.D ℂ S s) =
          c • F (KaehlerDifferential.D ℂ S s)
        rw [AlgHom.commutes]
        rfl }
  have hδL : ∀ a b : S, δ (a * b) = ev a • δ b + ev b • δ a := fun a b => by
    change F (KaehlerDifferential.D ℂ S (a * b)) = _
    rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul]
    rfl
  have hδB : ∀ b : B, δ (algebraMap B S b) = φ (KaehlerDifferential.D ℂ B b) := fun b => by
    change g.liftBaseChange S (e.symm (KaehlerDifferential.D ℂ S (algebraMap B S b))) = _
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
      LinearMap.liftBaseChange_tmul]
    change ev 1 • φ (KaehlerDifferential.D ℂ B b) = _
    rw [map_one, one_smul]
  refine ⟨δ, hδL, hδB, fun η hη => ?_⟩
  obtain ⟨L, hLD, hLs⟩ := hL η hη
  have hker' : LinearMap.ker φ ≤ LinearMap.ker L := by
    intro ω hω
    rw [LinearMap.mem_ker] at hω ⊢
    obtain ⟨m, b, ω', hb, rfl⟩ := hker ω hω
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [hLs, hb, zero_mul]
  let φq := (LinearMap.ker φ).liftQ φ le_rfl
  have hinj : LinearMap.ker φq = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨ψ, hψ⟩ := φq.exists_leftInverse_of_injective hinj
  let r : (Fin d → ℂ) →ₗ[ℂ] ℂ := (LinearMap.ker φ).liftQ L hker' ∘ₗ ψ
  have hr : ∀ ω, L ω = r (φ ω) := fun ω => by
    have hq : ψ (φq (Submodule.Quotient.mk ω)) = Submodule.Quotient.mk ω := by
      simpa using LinearMap.congr_fun hψ (Submodule.Quotient.mk ω)
    change _ = (LinearMap.ker φ).liftQ L hker' (ψ (φq (Submodule.Quotient.mk ω)))
    rw [hq]
    rfl
  refine ⟨r, fun s => ?_⟩
  have hrδ : ∀ a b : S, r (δ (a * b)) = ev a * r (δ b) + ev b * r (δ a) := fun a b => by
    rw [hδL, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hδη : ∀ x : B, r (δ (algebraMap B S x)) = η (algebraMap B S x) := fun x => by
    rw [hδB, ← hr, hLD]
  obtain ⟨⟨b, t⟩, hs⟩ := IsLocalization.surj p.primeCompl s
  have ht : ev (algebraMap B S t) ≠ 0 := fun h => t.2 ((hp t).2 h)
  have h1 := hη s (algebraMap B S t)
  have h2 := hrδ s (algebraMap B S t)
  rw [hs] at h1 h2
  rw [hδη, hδη] at h2
  exact mul_left_cancel₀ ht (by linear_combination h2 - h1)
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

namespace UpperTheory.Gal.productCup_of_system

private theorem exists_stalk {Y : Scheme.{0}} (s' : Y ⟶ Sp ℂ) (y : CxPts s' (RingHom.id ℂ)) :
    ∃ (_ : Algebra ℂ (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))))
      (ev : (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) →ₐ[ℂ] ℂ),
      (∀ (W : Y.Opens) (h : y.1 (IsLocalRing.closedPoint ℂ) ∈ W) (c : ℂ),
        (Y.presheaf.germ W _ h).hom (algebraMap ℂ (Sec s' W) c) = algebraMap ℂ _ c) ∧
      (∀ (W : Y.Opens) (h : y.1 (IsLocalRing.closedPoint ℂ) ∈ W) (b : Γ(Y, W)),
        ev ((Y.presheaf.germ W _ h).hom b) = CxPts.ev s' (RingHom.id ℂ) W b y) := by
  have bridge : ∀ (W : Y.Opens) (hW : y.1 (IsLocalRing.closedPoint ℂ) ∈ W) (b : Γ(Y, W)),
      (Scheme.stalkClosedPointTo y.1).hom ((Y.presheaf.germ W _ hW).hom b) = valR y.1 W b := by
    intro W hW b
    have hh : ⊤ ≤ y.1 ⁻¹ᵁ W := (Points.le_preimage_iff y.1 W).mpr hW
    rw [valR, dite_eq_left hh]
    have := congrArg (fun g => g.hom b) (Scheme.germ_stalkClosedPointTo y.1 W hW)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp [Scheme.Hom.appLE]
    rfl
  have glue : ∀ (W : Y.Opens) (hW : y.1 (IsLocalRing.closedPoint ℂ) ∈ W) (c : ℂ),
      (Y.presheaf.germ W _ hW).hom (algebraMap ℂ (Sec s' W) c) =
        (Y.presheaf.germ ⊤ _ trivial).hom ((secMap s' ⊤).hom c) := by
    intro W hW c
    show (Y.presheaf.germ W _ hW).hom ((s'.appLE ⊤ W _).hom _) =
      (Y.presheaf.germ ⊤ _ trivial).hom ((s'.appLE ⊤ ⊤ _).hom _)
    rw [← Scheme.Hom.appLE_map (i := (homOfLE le_top).op), CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
    exact le_top
  letI alg : Algebra ℂ (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) :=
    ((Y.presheaf.germ ⊤ _ trivial).hom.comp (secMap s' ⊤).hom).toAlgebra
  have hev : ∀ c : ℂ, (Scheme.stalkClosedPointTo y.1).hom (algebraMap ℂ _ c) = c := by
    intro c
    have htop : ⊤ ≤ y.1 ⁻¹ᵁ (⊤ : Y.Opens) := Points.le_preimage_top y.1
    exact (bridge ⊤ trivial _).trans (Points.valR_constFn_of_over s' (RingHom.id ℂ) y.1 y.2 ⊤ htop c)
  refine ⟨alg, { toRingHom := (Scheme.stalkClosedPointTo y.1).hom, commutes' := hev }, ?_, ?_⟩
  · intro W hW c
    exact glue W hW c
  · intro W hW b
    exact bridge W hW b

end UpperTheory.Gal.productCup_of_system

namespace UpperTheory.Gal.productCup_of_system

private theorem mem_max_iff {S : Type} [CommRing S] [IsLocalRing S] [Algebra ℂ S] (ev : S →ₐ[ℂ] ℂ) (a : S) :
    a ∈ IsLocalRing.maximalIdeal S ↔ ev a = 0 := by
  have hs : Function.Surjective ev := fun c => ⟨algebraMap ℂ S c, by simp⟩
  rw [← IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ev hs), RingHom.mem_ker]

private theorem exists_der {Y : Scheme.{0}} (s' : Y ⟶ Sp ℂ) (y0 : Y)
    [Algebra ℂ (Y.presheaf.stalk y0)] (ev : (Y.presheaf.stalk y0) →ₐ[ℂ] ℂ)
    (V : Y.Opens) (hV : IsAffineOpen V) (h : y0 ∈ V)
    (halg : ∀ c : ℂ, (Y.presheaf.germ V y0 h).hom (algebraMap ℂ (Sec s' V) c) = algebraMap ℂ _ c)
    (d : ℕ) (φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)) (e : Sec s' V → ℂ)
    (he : ∀ b : Sec s' V, e b = ev ((Y.presheaf.germ V y0 h).hom b))
    (hs : ∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = e b • φ ω)
    (hk : ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
      (∀ i, e (b i) = 0) ∧ ω = ∑ i, b i • ω' i) :
    ∃ δ : (Y.presheaf.stalk y0) →ₗ[ℂ] (Fin d → ℂ),
      (∀ a b, δ (a * b) = ev a • δ b + ev b • δ a) ∧
      (∀ b : Sec s' V, δ ((Y.presheaf.germ V y0 h).hom b) = φ (KaehlerDifferential.D ℂ (Sec s' V) b)) ∧
      ∀ η : (Y.presheaf.stalk y0) →ₗ[ℂ] ℂ, (∀ a b, η (a * b) = ev a * η b + ev b * η a) →
        ∃ r : (Fin d → ℂ) →ₗ[ℂ] ℂ, ∀ a, η a = r (δ a) := by
  letI : Algebra (Sec s' V) (Y.presheaf.stalk y0) := (Y.presheaf.germ V y0 h).hom.toAlgebra
  haveI : IsScalarTower ℂ (Sec s' V) (Y.presheaf.stalk y0) :=
    IsScalarTower.of_algebraMap_eq (fun c => (halg c).symm)
  let p : Ideal (Sec s' V) := (hV.primeIdealOf ⟨y0, h⟩).asIdeal
  haveI : p.IsPrime := (hV.primeIdealOf ⟨y0, h⟩).isPrime
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y0) p := hV.isLocalization_stalk ⟨y0, h⟩
  have hp : ∀ b : Sec s' V, b ∈ p ↔ ev (algebraMap (Sec s' V) _ b) = 0 := by
    intro b
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Y.presheaf.stalk y0) p b).symm.trans
      (mem_max_iff ev _)
  obtain ⟨δ, h1, h2, h3⟩ := UpperTheory.kaehler_functional_vanishing_of_localization_at_prime (B := Sec s' V) (S := Y.presheaf.stalk y0) p ev hp d φ
    (fun b ω => (hs b ω).trans (by rw [he]; rfl))
    (fun ω hω => by
      obtain ⟨m, b, ω', hb, hω⟩ := hk ω hω
      exact ⟨m, b, ω', fun i => (he (b i)).symm.trans (hb i), hω⟩)
  exact ⟨δ, h1, h2, h3⟩

private noncomputable def pb {Z Y : Scheme.{0}} (c : Y ⟶ Z) (U : Z.Opens) (y0 : Y) (h : y0 ∈ c ⁻¹ᵁ U) :
    Γ(Z, U) →+* Y.presheaf.stalk y0 :=
  (Y.presheaf.germ (c ⁻¹ᵁ U) y0 h).hom.comp (c.app U).hom

private theorem pb_res {Z Y : Scheme.{0}} (c : Y ⟶ Z) {U U0 : Z.Opens} (e0 : U0 ≤ U) {W : Y.Opens}
    (e : W ≤ c ⁻¹ᵁ U) (y0 : Y) (hW : y0 ∈ W) (h : y0 ∈ c ⁻¹ᵁ U0) (f : Γ(Z, U)) :
    pb c U0 y0 h ((Z.presheaf.map (homOfLE e0).op).hom f) =
      (Y.presheaf.germ W y0 hW).hom ((c.appLE U W e).hom f) := by
  simp [pb, Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]

private theorem pb_const {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (c : Y ⟶ Z) (hc : c ≫ s = s')
    (U : Z.Opens) (y0 : Y) (h : y0 ∈ c ⁻¹ᵁ U) [Algebra ℂ (Y.presheaf.stalk y0)]
    (halg : ∀ (W : Y.Opens) (h : y0 ∈ W) (r : ℂ),
      (Y.presheaf.germ W y0 h).hom (algebraMap ℂ (Sec s' W) r) = algebraMap ℂ _ r) (r : ℂ) :
    pb c U y0 h (algebraMap ℂ (Sec s U) r) = algebraMap ℂ _ r := by
  have key := semiHom_appSec hc U
  unfold SemiHom at key
  have e1 : appSec s s' c U (algebraMap ℂ (Sec s U) r) = algebraMap ℂ (Sec s' (c ⁻¹ᵁ U)) r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, key r 1, map_one]
    rfl
  rw [← halg _ h r, ← e1]
  rfl

private theorem pb_etale {Z Y : Scheme.{0}} (c : Y ⟶ Z) (hc : Etale c) (U : Z.Opens) (hU : IsAffineOpen U)
    (y0 : Y) (h : y0 ∈ c ⁻¹ᵁ U) : (pb c U y0 h).FormallyEtale := by
  obtain ⟨V, hVa, hV, e⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens h
  have eq : pb c U y0 h = (Y.presheaf.germ V y0 hV).hom.comp (c.appLE U V e).hom := by
    ext f
    simp [pb, Scheme.Hom.appLE, TopCat.Presheaf.germ_res_apply]
  rw [eq]
  apply RingHom.FormallyEtale.comp
  · have := HasRingHomProperty.appLE @Etale c hc ⟨U, hU⟩ ⟨V, hVa⟩ e
    exact this.formallyEtale
  · letI := (Y.presheaf.germ V y0 hV).hom.toAlgebra
    haveI := (show IsAffineOpen V from hVa).isLocalization_stalk ⟨y0, hV⟩
    exact Algebra.FormallyEtale.of_isLocalization ((show IsAffineOpen V from hVa).primeIdealOf ⟨y0, hV⟩).asIdeal.primeCompl

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.tanConj_etale :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (d : ℕ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') (y : CxPts s' (RingHom.id ℂ)), Etale c1 → y.1 ≫ c1 = y.1 ≫ c2 → ∀ A A' : Matrix (Fin d) (Fin d) ℂ, IsTan d c1 c2 h1 h2 y A → IsTan d c1 c2 h1 h2 y A' → ∃ P : Matrix (Fin d) (Fin d) ℂ, IsUnit P.det ∧ A' = P * A * P⁻¹ := by
  intro Z Y s s' d c1 c2 h1 h2 y hc hcc A A' hA hA'
  obtain ⟨inst, ev, halg, hev⟩ := exists_stalk s' y
  obtain ⟨U, V, hV1, hV2, t, hyV, hU, hV, φ, hφs, hφ1, hφ2, hφk⟩ := hA
  obtain ⟨U', V', hV1', hV2', t', hyV', hU', hV', φ', hφs', hφ1', hφ2', hφk'⟩ := hA'
  have hy0V : y.1 (IsLocalRing.closedPoint ℂ) ∈ V := CxPts.mem_ptsIn.mp hyV
  have hy0V' : y.1 (IsLocalRing.closedPoint ℂ) ∈ V' := CxPts.mem_ptsIn.mp hyV'
  have hmU : c1 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ U ⊓ U' := ⟨hV1 hy0V, hV1' hy0V'⟩
  obtain ⟨U0, hU0a, hmem, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hmU
  have h1' : y.1 (IsLocalRing.closedPoint ℂ) ∈ c1 ⁻¹ᵁ U0 := hmem
  have hpt : c2 (y.1 (IsLocalRing.closedPoint ℂ)) = c1 (y.1 (IsLocalRing.closedPoint ℂ)) := by
    have := congrArg (fun g : Sp ℂ ⟶ Z => g (IsLocalRing.closedPoint ℂ)) hcc
    exact this.symm
  have h2' : y.1 (IsLocalRing.closedPoint ℂ) ∈ c2 ⁻¹ᵁ U0 := by
    show c2 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ U0
    rw [hpt]
    exact hmem
  letI : Algebra (Sec s U0) (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) :=
    (pb c1 U0 _ h1').toAlgebra
  haveI : Algebra.FormallyEtale (Sec s U0) (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) :=
    pb_etale c1 hc U0 hU0a _ h1'
  haveI : IsScalarTower ℂ (Sec s U0) (Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ))) :=
    IsScalarTower.of_algebraMap_eq (fun r => (pb_const c1 h1 U0 _ h1' halg r).symm)
  let a2 : Sec s U0 →ₐ[ℂ] Y.presheaf.stalk (y.1 (IsLocalRing.closedPoint ℂ)) :=
    { toRingHom := pb c2 U0 _ h2', commutes' := pb_const c2 h2 U0 _ h2' halg }
  have hval : ∀ f : Sec s U0, ev (algebraMap (Sec s U0) _ f) = ev (a2 f) := by
    intro f
    have e1 : ev (pb c1 U0 _ h1' f) = valR (y.1 ≫ c1) U0 f :=
      (hev _ h1' _).trans (Points.valR_comp y.1 c1 U0 f).symm
    have e2 : ev (pb c2 U0 _ h2' f) = valR (y.1 ≫ c2) U0 f :=
      (hev _ h2' _).trans (Points.valR_comp y.1 c2 U0 f).symm
    show ev (pb c1 U0 _ h1' f) = ev (pb c2 U0 _ h2' f)
    rw [e1, e2, hcc]
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ := exists_der s' _ ev V hV hy0V (halg V hy0V) d φ
    (fun b => CxPts.ev s' (RingHom.id ℂ) V b y) (fun b => (hev V hy0V b).symm) hφs hφk
  obtain ⟨δ', hδ1', hδ2', hδ3'⟩ := exists_der s' _ ev V' hV' hy0V' (halg V' hy0V') d φ'
    (fun b => CxPts.ev s' (RingHom.id ℂ) V' b y) (fun b => (hev V' hy0V' b).symm) hφs' hφk'
  have e0 : U0 ≤ U := hle.trans inf_le_left
  have e0' : U0 ≤ U' := hle.trans inf_le_right
  let τ : Fin d → Sec s U0 := fun l => (Z.presheaf.map (homOfLE e0).op).hom (t l)
  let τ' : Fin d → Sec s U0 := fun l => (Z.presheaf.map (homOfLE e0').op).hom (t' l)
  refine UpperTheory.derivation_eq_of_formallyEtale_of_evaluation_eq (A := Sec s U0) a2 ev hval d δ δ' hδ1 hδ1' hδ3 hδ3' τ τ' A A' ?_ ?_ ?_ ?_
  · intro l
    show δ (pb c1 U0 _ h1' (τ l)) = _
    rw [show pb c1 U0 _ h1' (τ l) = _ from pb_res c1 e0 hV1 _ hy0V h1' (t l)]
    exact (hδ2 _).trans (hφ1 l)
  · intro j
    show δ (pb c2 U0 _ h2' (τ j)) = _
    rw [show pb c2 U0 _ h2' (τ j) = _ from pb_res c2 e0 hV2 _ hy0V h2' (t j)]
    exact (hδ2 _).trans (hφ2 j)
  · intro l
    show δ' (pb c1 U0 _ h1' (τ' l)) = _
    rw [show pb c1 U0 _ h1' (τ' l) = _ from pb_res c1 e0' hV1' _ hy0V' h1' (t' l)]
    exact (hδ2' _).trans (hφ1' l)
  · intro j
    show δ' (pb c2 U0 _ h2' (τ' j)) = _
    rw [show pb c2 U0 _ h2' (τ' j) = _ from pb_res c2 e0' hV2' _ hy0V' h2' (t' j)]
    exact (hδ2' _).trans (hφ2' j)
