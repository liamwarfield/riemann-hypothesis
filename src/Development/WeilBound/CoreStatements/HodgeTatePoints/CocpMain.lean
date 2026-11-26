module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermJetLift
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerSeriesExpansionInDeltaUnique
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitsMulRelationRearrangeCommRing

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TruncatedExpansionPthPowerCoeff
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TruncatedExpansionPthPowerCoeff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.CoefAlg

theorem pow_frobenius_truncated {B : Type} [CommRing B] (δ : B) (p : ℕ) [Fact p.Prime]
    (hp0 : (p : B) = 0) (hδ : δ ^ (p + 1) = 0) (a : Fin (p + 1) → B) (ha0 : a 0 = 1)
    (h1 : 1 < p + 1) :
    (∑ i, a i * δ ^ (i : ℕ)) ^ p = 1 + a ⟨1, h1⟩ ^ p * δ ^ p := by
  have hpp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpp.two_le
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Subsingleton.elim _ _
  haveI : CharP B p := by
    have h := CharP.ringChar_of_prime_eq_zero hpp hp0
    rw [← h]
    exact ringChar.charP B
  rw [sum_pow_char p]
  have hterm : ∀ i : Fin (p + 1), (a i * δ ^ (i : ℕ)) ^ p =
      (if i = 0 then 1 else 0) + (if i = ⟨1, h1⟩ then a ⟨1, h1⟩ ^ p * δ ^ p else 0) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      have : (0 : Fin (p + 1)) ≠ ⟨1, h1⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [ha0, this]
    by_cases hi1 : i = ⟨1, h1⟩
    · subst hi1
      have : (⟨1, h1⟩ : Fin (p + 1)) ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [this, mul_pow]
    · have hv0 : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
      have hv1 : (i : ℕ) ≠ 1 := fun h => hi1 (Fin.ext h)
      have hv : 2 ≤ (i : ℕ) := by omega
      have hle : p + 1 ≤ (i : ℕ) * p := by nlinarith
      have hz : δ ^ ((i : ℕ) * p) = 0 := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
        rw [hk, pow_add, hδ, zero_mul]
      simp [hi0, hi1, mul_pow, ← pow_mul, hz]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem delta_pow_mul_truncated {B : Type} [CommRing B] (δ : B) (p : ℕ)
    (hδ : δ ^ (p + 1) = 0) (b : Fin (p + 1) → B) (hb0 : b 0 = 1) :
    δ ^ p * ∑ i, b i * δ ^ (i : ℕ) = δ ^ p := by
  rw [Fin.sum_univ_succ, mul_add, Finset.mul_sum]
  have hz : ∀ i : Fin p, δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) = 0 := by
    intro i
    have : δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) =
        b i.succ * (δ ^ (p + 1) * δ ^ (i : ℕ)) := by
      simp only [Fin.val_succ]
      ring
    rw [this, hδ]
    simp
  rw [Finset.sum_eq_zero (fun i _ => hz i)]
  simp [hb0]

theorem coeff_comparison : ∀ (A B : Type) [CommRing A] [CommRing B] (π : A →+* B) (δ : B) (p : ℕ) [Fact p.Prime], (p : B) = 0 → δ ^ (p + 1) = 0 → (∀ c c' : Fin (p + 1) → A, ∑ i, π (c i) * δ ^ (i : ℕ) = ∑ i, π (c' i) * δ ^ (i : ℕ) → c = c') → ∀ (u c₁ c₂ : Fin (p + 1) → A), u 0 = 1 → c₁ 0 = 1 → c₂ 0 = 1 → ∑ i, π (c₁ i) * δ ^ (i : ℕ) = (∑ i, π (u i) * δ ^ (i : ℕ)) ^ p * ∑ i, π (c₂ i) * δ ^ (i : ℕ) → c₁ (Fin.last p) = c₂ (Fin.last p) + u ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p := by
  intro A B _ _ π δ p _ hp0 hδ huniq u c₁ c₂ hu0 hc₁ hc₂ hmain
  have h1 : 1 < p + 1 := Nat.succ_lt_succ (Nat.Prime.pos Fact.out)
  have hfrob := pow_frobenius_truncated δ p hp0 hδ (fun i => π (u i)) (by simp [hu0]) h1
  have hdel := delta_pow_mul_truncated δ p hδ (fun i => π (c₂ i)) (by simp [hc₂])
  have hlast : ∀ i : Fin (p + 1),
      π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ) =
        π (c₂ i) * δ ^ (i : ℕ) +
          (if i = Fin.last p then π (u ⟨1, h1⟩) ^ p * δ ^ p else 0) := by
    intro i
    by_cases hi : i = Fin.last p
    · subst hi
      simp [add_mul]
    · simp [Function.update_of_ne hi, hi]
  have hsum : ∑ i, π (c₁ i) * δ ^ (i : ℕ) = ∑ i,
      π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ) := by
    simp only [hlast, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hmain, hfrob, add_mul, _root_.one_mul, _root_.mul_assoc, hdel]
  have := huniq _ _ hsum
  rw [this]
  simp

end GlobalTheory.CompanionTheory.Ar.CoefAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TruncatedExpansionPthPowerCoeffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_expansion_pth_power_coeff : ∀ (A B : Type) [CommRing A] [CommRing B] (π : A →+* B) (δ : B) (p : ℕ) [Fact p.Prime], (p : B) = 0 → δ ^ (p + 1) = 0 → (∀ c c' : Fin (p + 1) → A, ∑ i, π (c i) * δ ^ (i : ℕ) = ∑ i, π (c' i) * δ ^ (i : ℕ) → c = c') → ∀ (u c₁ c₂ : Fin (p + 1) → A), u 0 = 1 → c₁ 0 = 1 → c₂ 0 = 1 → ∑ i, π (c₁ i) * δ ^ (i : ℕ) = (∑ i, π (u i) * δ ^ (i : ℕ)) ^ p * ∑ i, π (c₂ i) * δ ^ (i : ℕ) → c₁ (Fin.last p) = c₂ (Fin.last p) + u ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoefAlg.coeff_comparison | exact GlobalTheory.CompanionTheory.Ar.CoefAlg.coeff_comparison | (intros; apply GlobalTheory.CompanionTheory.Ar.CoefAlg.coeff_comparison <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaExpansionRestriction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaExpansionRestriction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section Ring

variable (B : Type) [CommRing B] (p : ℕ)

theorem X_pow_dvd_of_mem {P : MvPolynomial Unit B} (hP : P ∈ orig B Unit ^ (p + 1)) :
    (Polynomial.X : Polynomial B) ^ (p + 1) ∣ MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P := by
  have h₁ : MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P ∈
      Ideal.map ((MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) :
        MvPolynomial Unit B →ₐ[B] Polynomial B) : MvPolynomial Unit B →+* Polynomial B) (orig B Unit ^ (p + 1)) :=
    Ideal.mem_map_of_mem _ hP
  rw [map_orig_pow] at h₁
  have h₂ : Ideal.span (Set.range fun i : Unit => ((MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) :
      MvPolynomial Unit B →ₐ[B] Polynomial B) : MvPolynomial Unit B →+* Polynomial B) (MvPolynomial.X i)) =
      Ideal.span {(Polynomial.X : Polynomial B)} := by
    congr 1
    ext a
    simp
  rw [h₂, Ideal.span_singleton_pow] at h₁
  exact Ideal.mem_span_singleton.1 h₁

variable {B p}

theorem top_coeff_eq (hp : 1 ≤ p) (b : Fin (p + 1) → B) (v : B)
    (h : ∑ i : Fin (p + 1), algebraMap B (Jet B Unit p) (b i) * dQ B p ^ (i : ℕ) =
      1 + dQ B p ^ p * algebraMap B (Jet B Unit p) v) : b (Fin.last p) = v := by
  set P : MvPolynomial Unit B := ∑ i : Fin (p + 1), MvPolynomial.C (b i) * MvPolynomial.X () ^ (i : ℕ) -
    (1 + MvPolynomial.X () ^ p * MvPolynomial.C v) with hPdef
  have hP : P ∈ orig B Unit ^ (p + 1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq_zero_iff_mem, hPdef, map_sub, map_add (f := _), map_sum, map_one, map_mul, map_pow, sub_eq_zero]
    simp only [map_mul, map_pow]
    exact h
  have hd := X_pow_dvd_of_mem B p hP
  have hc := Polynomial.X_pow_dvd_iff.1 hd p (Nat.lt_succ_self p)
  have hp0 : p ≠ 0 := by omega
  have e₁ : MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P =
      ∑ i : Fin (p + 1), Polynomial.C (b i) * Polynomial.X ^ (i : ℕ) -
        (1 + Polynomial.C v * Polynomial.X ^ p) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hPdef, map_sub, map_add (f := _), map_sum, map_mul, map_pow, map_one, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.algebraMap_eq]
    ring
  have e₂ : ∑ i : Fin (p + 1), (if p = (i : ℕ) then b i else 0) = b (Fin.last p) := by
    rw [Finset.sum_eq_single (Fin.last p)]
    · simp
    · intro i _ hi
      rw [if_neg]
      intro h'
      exact hi (Fin.ext (by simpa using h'.symm))
    · simp
  rw [e₁] at hc
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_one, if_neg hp0, e₂, if_true, zero_add] at hc
  exact sub_eq_zero.1 hc

end Ring

theorem appLE_top_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (W : Y.Opens) (h₁ : ⊤ ≤ f ⁻¹ᵁ W)
    (h₂ : ⊤ ≤ g ⁻¹ᵁ W) : f.appLE W ⊤ h₁ = g.appLE W ⊤ h₂ := by
  subst e
  rfl

theorem appTop_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appTop = f.appLE ⊤ ⊤ h := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

section Test

variable {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] {k : Type} [Field k] (x : Sp k ⟶ X0)
variable {B : Type} [CommRing B] [Algebra k B]

theorem rQ_appLE_prZ (p : ℕ) (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W)
    (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W)) (a : Γ(pullback G.hom x, W)) :
    ((rQ G x p z).appLE _ ⊤ hr).hom (((prZ G x p).app W).hom a) =
      ((spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p)).appTop).hom
        (((xkZ G x z).appLE W ⊤ hW).hom a) := by
  have h₁ : (prZ G x p).app W ≫ (rQ G x p z).appLE _ ⊤ hr = (rQ G x p z ≫ prZ G x p).appLE W ⊤ hr := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have h₂ : (xkZ G x z).appLE W ⊤ hW ≫
      (spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p)).appTop =
      (spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p) ≫ xkZ G x z).appLE W ⊤ (by
        rw [Scheme.Hom.comp_preimage]
        exact fun y _ => hW (show _ from trivial)) := by
    rw [← Scheme.Hom.appLE_comp_appLE _ _ W ⊤ ⊤ hW (by simp), appTop_eq_appLE _ (by simp)]
  have h₃ := h₁.trans ((appLE_top_congr (rQ_prZ G x p z) W _ _).trans h₂.symm)
  exact congrArg (fun q => q.hom a) h₃

theorem rQ_appLE_dltOn (p : ℕ) (z : overAt x B ⟶ G) (V : (Ym G x p).Opens) (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ V) :
    ((rQ G x p z).appLE V ⊤ hr).hom (dltOn G x p V) = toΓ _ (dQ B p) := by
  have h₁ : (Ym G x p).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ (rQ G x p z).appLE V ⊤ hr =
      (rQ G x p z).appTop := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h₂ : ((rQ G x p z).appLE V ⊤ hr).hom (dltOn G x p V) = ((rQ G x p z).appTop).hom (dlt G x p) :=
    congrArg (fun q => q.hom (dlt G x p)) h₁
  have h₃ := congrArg (fun q => (q.appTop).hom (toΓ (Jet k Unit p) (Ideal.Quotient.mk _ (MvPolynomial.X ()))))
    (rQ_fst G x p z)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h₃
  rw [h₂, dlt, h₃, spMap_toΓ]
  congr 1
  exact MvPolynomial.aeval_X (R := k) (fun _ : Unit => dQ B p) ()

theorem coef_at_test (p : ℕ) (hp : 1 ≤ p) (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens)
    (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B)
    (hf : f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ))
    (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W))
    (hv : ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v)) :
    ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  have hs : ∀ i, ∃ b : B, toΓ B b = ((xkZ G x z).appLE W ⊤ hW).hom (c i) := fun i =>
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2 _
  choose b hb using hs
  have key : ∑ i : Fin (p + 1), algebraMap B (Jet B Unit p) (b i) * dQ B p ^ (i : ℕ) =
      1 + dQ B p ^ p * algebraMap B (Jet B Unit p) v := by
    apply toΓ_inj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv, hf, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, rQ_appLE_prZ G x p z W hW hr, rQ_appLE_dltOn, ← hb, spMap_toΓ]
    rfl
  rw [← hb, top_coeff_eq hp b v key]

end Test

theorem coef_pull : ∀ (X0 : Scheme.{0}) (G : Over X0) [GrpObj G] (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (hp : 1 ≤ p) (B : Type) [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B), f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∀ hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W), ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v) → ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  intro X0 G _ k _ x p hp B _ _ z W hW c f v hf hr hv
  exact coef_at_test G x p hp z W hW c f v hf hr hv

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaExpansionRestrictionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_expansion_restriction : ∀ (X0 : Scheme.{0}) (G : Over X0) [GrpObj G] (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (hp : 1 ≤ p) (B : Type) [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B), f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∀ hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W), ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v) → ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.coef_pull | exact GlobalTheory.CompanionTheory.Ar.Coc.coef_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.coef_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZeroSectionSurjective
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZeroSectionSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem tensor_isPullback {X0 : Scheme.{0}} (A B : Over X0) :
    IsPullback (fst A B).left (snd A B).left A.hom B.hom :=
  IsPullback.of_hasPullback A.hom B.hom

theorem secZ_isPullback {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (m : ℕ) :
    IsPullback (secZ G x m) (pullback.snd G.hom x) (fst (Tm x m) G).left
      (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) := by
  have hR := (tensor_isPullback (Tm x m) G).flip
  have hO : IsPullback (secZ G x m ≫ (snd (Tm x m) G).left) (pullback.snd G.hom x) G.hom
      (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) ≫ (Tm x m).hom) := by
    rw [secZ_snd]
    have e : spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) ≫ (Tm x m).hom = x := by
      dsimp
      rw [← Category.assoc, spMap_comp_alg]
      simp [spMap]
    rw [e]
    exact IsPullback.of_hasPullback G.hom x
  exact IsPullback.of_right hO (secZ_fst G x m) hR

theorem secZ_surj (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ) :
    Function.Surjective (secZ G x m).base := by
  have hs : Surjective (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) := ⟨fun q =>
    ⟨IsLocalRing.closedPoint k, jet_pt m q _⟩⟩
  have := MorphismProperty.of_isPullback (P := @Surjective) (secZ_isPullback G x m).flip hs
  exact this.surj

end GlobalTheory.CompanionTheory.Ar.Coc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZeroSectionSurjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zero_section_surjective : ∀ (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ), Function.Surjective (secZ G x m).base := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.secZ_surj | exact GlobalTheory.CompanionTheory.Ar.Coc.secZ_surj | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.secZ_surj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleCocyclePullbackTransform
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleCocyclePullbackTransform
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem gm_appLE {X Y : Scheme.{0}} (a : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ a ⁻¹ᵁ U) (u : Γ(X, U)ˣ)
    {x : Y} (hx : x ∈ V) :
    gm (𝟙 Y) x V (Units.map (a.appLE U V h).hom.toMonoidHom u) = gm a x U u := by
  have e : Units.map (a.appLE U V h).hom.toMonoidHom u = res h (pullU a U u) := by
    apply Units.ext
    simp [res, pullU, Scheme.Hom.appLE]
  rw [e, gm_res _ x h hx, gm_pull (𝟙 Y) a x U (h hx) u, Category.id_comp]

theorem cob_group {G : Type} [CommGroup G] (p q r u v B T : G) (h₁ : p * q = v) (h₂ : r * u = v) :
    p * (q * B⁻¹ * T) = r * B⁻¹ * (u * T) := by
  calc p * (q * B⁻¹ * T) = p * q * (B⁻¹ * T) := by simp only [_root_.mul_assoc]
    _ = r * u * (B⁻¹ * T) := by rw [h₁, h₂]
    _ = r * B⁻¹ * (u * T) := mul_mul_mul_comm r u B⁻¹ T

theorem exists_gen_of_units (X Y : Scheme.{0}) (L : LB X) (hL : L.IsLB) (a b : Y ⟶ X) (hab : ∀ y, a y = b y)
    (t : ∀ j, Γ(Y, b ⁻¹ᵁ L.U j)ˣ)
    (ht : ∀ (j j' : L.ι) (h : b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')),
      res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j from fun _ hy => hy.1) (t j) =
        Units.map (a.appLE _ _ h).hom.toMonoidHom (L.g j j') * (pullU b _ (L.g j j'))⁻¹ *
          res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j' from fun _ hy => hy.2) (t j')) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]), c.IsGen := by
  have hA : ∀ i : Fin 2 → L.ι, ∀ y ∈ LB.wchart L ![a, b] i, a y ∈ L.U (i 0) := fun i y hy =>
    Set.mem_iInter.1 hy 0
  have hB : ∀ i : Fin 2 → L.ι, ∀ y ∈ LB.wchart L ![a, b] i, b y ∈ L.U (i 1) := fun i y hy =>
    Set.mem_iInter.1 hy 1
  have hle : ∀ i : Fin 2 → L.ι, LB.wchart L ![a, b] i ≤ a ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i 1)) := fun i y hy =>
    ⟨hA i y hy, by
      show a y ∈ L.U (i 1)
      rw [hab y]; exact hB i y hy⟩
  have hle' : ∀ i : Fin 2 → L.ι, LB.wchart L ![a, b] i ≤ b ⁻¹ᵁ L.U (i 1) := fun i y hy => hB i y hy
  let s : ∀ i : Fin 2 → L.ι, Γ(Y, LB.wchart L ![a, b] i)ˣ := fun i =>
    res (hle i) (pullU a _ (L.g (i 0) (i 1))) * res (hle' i) (t (i 1))
  have hs : ∀ (i : Fin 2 → L.ι) (x : Y), x ∈ LB.wchart L ![a, b] i →
      gm (𝟙 Y) x _ (s i) = gm a x _ (L.g (i 0) (i 1)) * gm (𝟙 Y) x _ (t (i 1)) := by
    intro i x hx
    have h₁ : gm (𝟙 Y) x _ (res (hle i) (pullU a _ (L.g (i 0) (i 1)))) = gm a x _ (L.g (i 0) (i 1)) := by
      rw [gm_res _ x _ hx, gm_pull (𝟙 Y) a x _ (hle i hx), Category.id_comp]
    rw [map_mul, h₁, gm_res _ x _ hx]
  refine ⟨⟨s⟩, fun i i' => unit_ext fun x hx => ?_⟩
  have hmem : b x ∈ L.U (i 1) ⊓ L.U (i' 1) := ⟨hB i x hx.1, hB i' x hx.2⟩
  have hh : b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) ≤ a ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) := fun y hy => by
    show a y ∈ L.U (i 1) ⊓ L.U (i' 1)
    rw [hab y]; exact hy
  have e := congrArg (gm (𝟙 Y) x (b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)))) (ht (i 1) (i' 1) hh)
  have hmem' : x ∈ b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) := hmem
  rw [map_mul, map_mul, map_inv, gm_res (𝟙 Y) x _ hmem', gm_res (𝟙 Y) x _ hmem', gm_appLE a hh _ hmem',
    gm_pull (𝟙 Y) b x _ hmem, Category.id_comp] at e
  have c₁ := gm_cocycle hL a x (hA i x hx.1) (show a x ∈ L.U (i 1) from (hle i hx.1).2)
    (show a x ∈ L.U (i' 1) from (hle i' hx.2).2)
  have c₂ := gm_cocycle hL a x (hA i x hx.1) (hA i' x hx.2) (show a x ∈ L.U (i' 1) from (hle i' hx.2).2)
  have hg := gm_linComb L ![a, b] ![1, -1] (𝟙 Y) x i i' hx.1 hx.2
  rw [gm_res _ x _ hx, map_mul, gm_res _ x _ hx]
  show gm (𝟙 Y) x (LB.wchart L ![a, b] i) (s i) =
    gm (𝟙 Y) x (LB.wchart L ![a, b] i ⊓ LB.wchart L ![a, b] i') ((LB.LinComb L ![a, b] ![1, -1]).g i i') *
      gm (𝟙 Y) x (LB.wchart L ![a, b] i') (s i')
  rw [hg, hs i x hx.1, hs i' x hx.2, e, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, zpow_one, zpow_neg]
  exact cob_group _ _ _ _ _ _ _ c₁ c₂

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleCocyclePullbackTransformStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_cocycle_pullback_transform : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (a b : Y ⟶ X), (∀ y, a y = b y) → ∀ (t : ∀ j, Γ(Y, b ⁻¹ᵁ L.U j)ˣ), (∀ (j j' : L.ι) (h : b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')), res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j from fun _ hy => hy.1) (t j) = Units.map (a.appLE _ _ h).hom.toMonoidHom (L.g j j') * (pullU b _ (L.g j j'))⁻¹ * res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j' from fun _ hy => hy.2) (t j')) → ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]), c.IsGen := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units | exact GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_of_units <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.QamCore
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace PositivityTheory.HtPt.Qam.CoreP

section Gen
variable {X Y Y' : Scheme.{0}}

def trU (L : LB X) (a b : Y ⟶ X) (j j' : L.ι) (V : Y.Opens)
    (hA : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB : V ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j')) : Γ(Y, V)ˣ :=
  Units.map (a.appLE _ V hA).hom.toMonoidHom (L.g j j') *
    (Units.map (b.appLE _ V hB).hom.toMonoidHom (L.g j j'))⁻¹

theorem trU_pull (L : LB X) (a b : Y ⟶ X) (j j' : L.ι) (V : Y.Opens)
    (hA : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB : V ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (h : Y' ⟶ Y) (V' : Y'.Opens) (hV : V' ≤ h ⁻¹ᵁ V)
    (hA' : V' ≤ (h ≫ a) ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB' : V' ≤ (h ≫ b) ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    Units.map (h.appLE V V' hV).hom.toMonoidHom (trU L a b j j' V hA hB) =
      trU L (h ≫ a) (h ≫ b) j j' V' hA' hB' := by
  have e : ∀ (c : Y ⟶ X) (hC : V ≤ c ⁻¹ᵁ (L.U j ⊓ L.U j')) (hC' : V' ≤ (h ≫ c) ⁻¹ᵁ (L.U j ⊓ L.U j')),
      Units.map (h.appLE V V' hV).hom.toMonoidHom (Units.map (c.appLE _ V hC).hom.toMonoidHom (L.g j j')) =
        Units.map ((h ≫ c).appLE _ V' hC').hom.toMonoidHom (L.g j j') := by
    intro c hC hC'
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    have := Scheme.Hom.appLE_comp_appLE h c _ V V' hC hV
    exact congrArg (fun q => q.hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) this
  rw [trU, trU, map_mul, map_inv, e a hA hA', e b hB hB']

theorem trU_pull' (L : LB X) (a b : Y ⟶ X) (j j' : L.ι) (V : Y.Opens)
    (hA : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB : V ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (h : Y' ⟶ Y) (V' : Y'.Opens) (hV : V' ≤ h ⁻¹ᵁ V) (a' b' : Y' ⟶ X) (ea : h ≫ a = a') (eb : h ≫ b = b')
    (hA' : V' ≤ a' ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB' : V' ≤ b' ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    Units.map (h.appLE V V' hV).hom.toMonoidHom (trU L a b j j' V hA hB) = trU L a' b' j j' V' hA' hB' := by
  subst ea eb
  exact trU_pull L a b j j' V hA hB h V' hV hA' hB'

theorem res_value_compose {U U₁ U₂ V : Y.Opens} (h₁ : U₁ ≤ U) (h₂ : V ≤ U₁) (h₃ : U₂ ≤ U) (h₄ : V ≤ U₂) (s : Γ(Y, U)ˣ) :
    (res h₂ (res h₁ s)).val =
      (Y.presheaf.map (homOfLE h₄).op).hom ((Y.presheaf.map (homOfLE h₃).op).hom s.val) := by
  have e : Y.presheaf.map (homOfLE h₁).op ≫ Y.presheaf.map (homOfLE h₂).op =
      Y.presheaf.map (homOfLE h₃).op ≫ Y.presheaf.map (homOfLE h₄).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact congrArg (fun q => q.hom s.val) e

theorem trU_congr (L : LB X) (a : Y ⟶ X) (j j' : L.ι) (V : Y.Opens)
    (hA hB : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) : trU L a a j j' V hA hB = 1 :=
  mul_inv_cancel _

theorem res_res_pull (c : Y ⟶ X) (O : X.Opens) (W V : Y.Opens) (h₂ : W ≤ c ⁻¹ᵁ O) (h₃ : V ≤ W)
    (hC : V ≤ c ⁻¹ᵁ O) (u : Γ(X, O)ˣ) :
    res h₃ (res h₂ (pullU c O u)) = Units.map (c.appLE O V hC).hom.toMonoidHom u := by
  have e : c.app O ≫ Y.presheaf.map (homOfLE h₂).op ≫ Y.presheaf.map (homOfLE h₃).op =
      c.appLE O V hC := by
    rw [← Functor.map_comp]
    rfl
  ext
  exact congrArg (fun q => q.hom (u : Γ(X, O))) e

theorem linComb_g (L : LB X) (a b : Y ⟶ X) (m : ℤ) (j j' : L.ι) (V : Y.Opens)
    (hV : V ≤ (LB.LinComb L (K := Fin 2) ![a, b] ![m, -m]).U (fun _ => j) ⊓
      (LB.LinComb L (K := Fin 2) ![a, b] ![m, -m]).U (fun _ => j'))
    (hA : V ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) (hB : V ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    res hV ((LB.LinComb L (K := Fin 2) ![a, b] ![m, -m]).g (fun _ => j) (fun _ => j')) =
      trU L a b j j' V hA hB ^ m := by
  show res hV (∏ k : Fin 2, (res _ (pullU (![a, b] k) _ (L.g j j'))) ^ (![m, -m] k)) = _
  rw [Fin.prod_univ_two, map_mul, map_zpow, map_zpow]
  have ea := res_res_pull a _ _ V (le_inf (inf_le_left.trans (LB.wchart_le L ![a, b] (fun _ => j) 0))
      (inf_le_right.trans (LB.wchart_le L ![a, b] (fun _ => j') 0)) :
        LB.wchart L ![a, b] (fun _ => j) ⊓ LB.wchart L ![a, b] (fun _ => j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')) hV hA (L.g j j')
  have eb := res_res_pull b _ _ V (le_inf (inf_le_left.trans (LB.wchart_le L ![a, b] (fun _ => j) 1))
      (inf_le_right.trans (LB.wchart_le L ![a, b] (fun _ => j') 1)) :
        LB.wchart L ![a, b] (fun _ => j) ⊓ LB.wchart L ![a, b] (fun _ => j') ≤ b ⁻¹ᵁ (L.U j ⊓ L.U j')) hV hB (L.g j j')
  erw [ea, eb]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [trU, mul_zpow, inv_zpow, zpow_neg]

end Gen

section Thick
variable {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0)

theorem dltOn_res (m : ℕ) {V V' : (Ym G x m).Opens} (h : V' ≤ V) :
    ((Ym G x m).presheaf.map (homOfLE h).op).hom (dltOn G x m V) = dltOn G x m V' := by
  rw [dltOn, dltOn, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem sum_res (m : ℕ) {W W' : (pullback G.hom x).Opens} (h : W' ≤ W) (h' : prZ G x m ⁻¹ᵁ W' ≤ prZ G x m ⁻¹ᵁ W)
    (c : Fin (m + 1) → Γ(pullback G.hom x, W)) :
    ((Ym G x m).presheaf.map (homOfLE h').op).hom (∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ)) =
      ∑ i, ((prZ G x m).app W').hom (((pullback G.hom x).presheaf.map (homOfLE h).op).hom (c i)) *
        dltOn G x m _ ^ (i : ℕ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, dltOn_res]
  congr 1
  have := (prZ G x m).naturality (homOfLE h).op
  exact (congrArg (fun q => q.hom (c i)) this).symm

theorem sum_pull (m : ℕ) {Y' : Scheme.{0}} (g : Y' ⟶ Ym G x m) (π' : Y' ⟶ pullback G.hom x)
    (e : g ≫ prZ G x m = π') (δ' : Γ(Y', ⊤)) (eδ : (g.appTop).hom (dlt G x m) = δ')
    (W : (pullback G.hom x).Opens) (V' : Y'.Opens) (hV : V' ≤ g ⁻¹ᵁ (prZ G x m ⁻¹ᵁ W)) (hV' : V' ≤ π' ⁻¹ᵁ W)
    (c : Fin (m + 1) → Γ(pullback G.hom x, W)) :
    (g.appLE (prZ G x m ⁻¹ᵁ W) V' hV).hom (∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ)) =
      ∑ i, (π'.appLE W V' hV').hom (c i) * ((Y'.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op).hom δ') ^ (i : ℕ) := by
  subst e
  subst eδ
  have e1 : ∀ i, (g.appLE (prZ G x m ⁻¹ᵁ W) V' hV).hom (((prZ G x m).app W).hom (c i)) =
      ((g ≫ prZ G x m).appLE W V' hV').hom (c i) := by
    intro i
    have := Scheme.Hom.appLE_comp_appLE g (prZ G x m) W _ V' (le_refl _) hV
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact congrArg (fun q => q.hom (c i)) this
  have e2 : (g.appLE (prZ G x m ⁻¹ᵁ W) V' hV).hom (dltOn G x m _) =
      (Y'.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op).hom ((g.appTop).hom (dlt G x m)) := by
    have h1 := Scheme.Hom.map_appLE g hV (homOfLE (le_top : prZ G x m ⁻¹ᵁ W ≤ ⊤)).op
    exact congrArg (fun q => q.hom (dlt G x m)) h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, e1, e2]

theorem id_appLE' {Z : Scheme.{0}} (W : Z.Opens) (h : W ≤ (𝟙 Z : Z ⟶ Z) ⁻¹ᵁ W) :
    (𝟙 Z : Z ⟶ Z).appLE W W h = 𝟙 _ := by
  exact (Category.id_comp _).trans ((congrArg Z.presheaf.map (Subsingleton.elim _ _)).trans (Z.presheaf.map_id _))

theorem sec_sum (m : ℕ) (W : (pullback G.hom x).Opens) (h : W ≤ secZ G x m ⁻¹ᵁ (prZ G x m ⁻¹ᵁ W))
    (c : Fin (m + 1) → Γ(pullback G.hom x, W)) :
    ((secZ G x m).appLE _ W h).hom (∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ)) = c 0 := by
  rw [sum_pull G x m (secZ G x m) (𝟙 _) (secZ_prZ G x m) 0 (secZ_dlt G x m) W W h le_rfl c]
  rw [Fin.sum_univ_succ]
  simp only [map_zero, ne_eq, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    mul_zero, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, _root_.mul_one]
  exact congrArg (fun q => q.hom (c 0)) (id_appLE' W _)

theorem sum_trunc {R : Type*} [CommRing R] (d : R) (hd : d ^ 2 = 0) (p : ℕ) (hp : 1 ≤ p) (c : Fin (p + 1) → R) :
    ∑ i, c i * d ^ (i : ℕ) = c 0 + c ⟨1, by omega⟩ * d := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have : ∀ i : Fin q, c i.succ.succ * d ^ ((i.succ.succ : Fin (q + 1 + 1)) : ℕ) = 0 := by
    intro i
    simp only [Fin.val_succ]
    rw [show (i : ℕ) + 1 + 1 = i + 2 from rfl, pow_add, hd, mul_zero, mul_zero]
  simp only [this, Finset.sum_const_zero, add_zero]
  simp

theorem dltOn_pow (m : ℕ) (V : (Ym G x m).Opens) : dltOn G x m V ^ (m + 1) = 0 := by
  rw [dltOn, ← map_pow, dlt_pow, map_zero]

theorem tr_sum (p : ℕ) (hp : 1 ≤ p) (W : (pullback G.hom x).Opens)
    (h : prZ G x 1 ⁻¹ᵁ W ≤ trY G x p hp ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W))
    (c : Fin (p + 1) → Γ(pullback G.hom x, W)) :
    ((trY G x p hp).appLE _ _ h).hom (∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ)) =
      ((prZ G x 1).app W).hom (c 0) + ((prZ G x 1).app W).hom (c ⟨1, by omega⟩) * dltOn G x 1 _ := by
  rw [sum_pull G x p (trY G x p hp) (prZ G x 1) (trY_prZ G x p hp) (dlt G x 1) (trY_dlt G x p hp) W _ h le_rfl c]
  have := sum_trunc (dltOn G x 1 (prZ G x 1 ⁻¹ᵁ W)) (dltOn_pow G x 1 _) p hp
    (fun i => ((prZ G x 1).app W).hom (c i))
  simp only [Scheme.Hom.app_eq_appLE] at this ⊢
  exact this

theorem cast_p (m : ℕ) (V : (Ym G x m).Opens) (p : ℕ) [CharP k p] : ((p : ℕ) : Γ(Ym G x m, V)) = 0 := by
  let ψ : k →+* Γ(Ym G x m, V) := ((Ym G x m).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp
    (((fst (Tm x m) G).left.appTop).hom.comp ((toΓ (Jet k Unit m)).comp (algebraMap k (Jet k Unit m))))
  have := map_natCast ψ p
  rw [CharP.cast_eq_zero k p, map_zero] at this
  exact this.symm

theorem base_eq (p : ℕ) (a : Ym G x p ⟶ G.left) (ha : secZ G x p ≫ a = pullback.fst G.hom x)
    (y : Ym G x p) : a y = (prZ G x p ≫ pullback.fst G.hom x) y := by
  obtain ⟨z, rfl⟩ := GlobalTheory.T.zero_section_surjective X0 G k x p y
  have e : secZ G x p ≫ prZ G x p ≫ pullback.fst G.hom x = pullback.fst G.hom x := by
    rw [← Category.assoc, secZ_prZ, Category.id_comp]
  have h1 := congrArg (fun q : pullback G.hom x ⟶ G.left => q z) (ha.trans e.symm)
  simpa using h1

end Thick

section Main
variable {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (p : ℕ)
  (L : LB G.left) (a : Ym G x p ⟶ G.left)

theorem le_pre (ha : secZ G x p ≫ a = pullback.fst G.hom x) (O : G.left.Opens) :
    prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ O) ≤ a ⁻¹ᵁ O := by
  intro y hy
  show a y ∈ O
  rw [base_eq G x p a ha]
  exact hy

theorem le_chart (ha : secZ G x p ≫ a = pullback.fst G.hom x) (m : ℤ) (j : L.ι) :
    prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j) ≤
      (LB.LinComb L (K := Fin 2) ![a, prZ G x p ≫ pullback.fst G.hom x] ![m, -m]).U (fun _ => j) := by
  intro y hy
  refine Set.mem_iInter.2 fun q => ?_
  fin_cases q
  · exact le_pre G x p a ha (L.U j) hy
  · exact hy

theorem le_sec (W : (pullback G.hom x).Opens) : W ≤ secZ G x p ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W) := by
  intro z hz
  show (secZ G x p ≫ prZ G x p) z ∈ W
  rw [secZ_prZ]
  exact hz

theorem chart_coef (ha : secZ G x p ≫ a = pullback.fst G.hom x)
    (C : LB.Gen (LB.LinComb L (K := Fin 2) ![a, prZ G x p ≫ pullback.fst G.hom x] ![(p : ℤ), -(p : ℤ)]))
    (hn : ∀ (j : L.ι) (h : pullback.fst G.hom x ⁻¹ᵁ L.U j ≤ secZ G x p ⁻¹ᵁ
        LB.wchart L (K := Fin 2) ![a, prZ G x p ≫ pullback.fst G.hom x] (fun _ => j)),
      ((secZ G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1) (j : L.ι) :
    ∃ c : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j),
      ((Ym G x p).presheaf.map (homOfLE (le_chart G x p L a ha (p : ℤ) j)).op).hom (C.s fun _ => j).val =
        ∑ i, ((prZ G x p).app _).hom (c i) * dltOn G x p _ ^ (i : ℕ) ∧ c 0 = 1 := by
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.power_series_expansion_in_delta_unique X0 G k x p _
    (((Ym G x p).presheaf.map (homOfLE (le_chart G x p L a ha (p : ℤ) j)).op).hom (C.s fun _ => j).val)
  refine ⟨c, hc, ?_⟩
  have hs := le_sec G x p (pullback.fst G.hom x ⁻¹ᵁ L.U j)
  rw [← sec_sum G x p _ hs c, ← hc]
  have h2 := Scheme.Hom.map_appLE (secZ G x p) hs (homOfLE (le_chart G x p L a ha (p : ℤ) j)).op
  exact (congrArg (fun q => q.hom (C.s fun _ => j).val) h2).trans (hn j _)

theorem tr_coef (ha : secZ G x p ≫ a = pullback.fst G.hom x) (j j' : L.ι)
    (hA : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (hB : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      (prZ G x p ≫ pullback.fst G.hom x) ⁻¹ᵁ (L.U j ⊓ L.U j')) :
    ∃ u : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j'),
      (trU L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ hA hB).val =
        ∑ i, ((prZ G x p).app _).hom (u i) * dltOn G x p _ ^ (i : ℕ) ∧ u 0 = 1 := by
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.power_series_expansion_in_delta_unique X0 G k x p _ (trU L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ hA hB).val
  refine ⟨u, hu, ?_⟩
  have hs := le_sec G x p (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j')
  rw [← sec_sum G x p _ hs u, ← hu]
  have e : secZ G x p ≫ prZ G x p ≫ pullback.fst G.hom x = pullback.fst G.hom x := by
    rw [← Category.assoc, secZ_prZ, Category.id_comp]
  have h1 := trU_pull' L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ hA hB (secZ G x p) _ hs
    (pullback.fst G.hom x) (pullback.fst G.hom x) ha e le_rfl le_rfl
  exact congrArg Units.val (h1.trans (trU_congr _ _ _ _ _ _ _))

theorem overlap [Fact p.Prime] [CharP k p] (ha : secZ G x p ≫ a = pullback.fst G.hom x)
    (C : LB.Gen (LB.LinComb L (K := Fin 2) ![a, prZ G x p ≫ pullback.fst G.hom x] ![(p : ℤ), -(p : ℤ)]))
    (hC : C.IsGen) (j j' : L.ι)
    (c₁ : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j))
    (c₂ : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j'))
    (h₁ : ((Ym G x p).presheaf.map (homOfLE (le_chart G x p L a ha (p : ℤ) j)).op).hom (C.s fun _ => j).val =
        ∑ i, ((prZ G x p).app _).hom (c₁ i) * dltOn G x p _ ^ (i : ℕ))
    (h₂ : ((Ym G x p).presheaf.map (homOfLE (le_chart G x p L a ha (p : ℤ) j')).op).hom (C.s fun _ => j').val =
        ∑ i, ((prZ G x p).app _).hom (c₂ i) * dltOn G x p _ ^ (i : ℕ))
    (e₁ : c₁ 0 = 1) (e₂ : c₂ 0 = 1)
    (hA : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (hB : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      (prZ G x p ≫ pullback.fst G.hom x) ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (u : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j'))
    (hu : (trU L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ hA hB).val =
        ∑ i, ((prZ G x p).app _).hom (u i) * dltOn G x p _ ^ (i : ℕ)) (u₀ : u 0 = 1) :
    ((pullback G.hom x).presheaf.map (homOfLE inf_le_left).op).hom (c₁ (Fin.last p)) =
      ((pullback G.hom x).presheaf.map (homOfLE inf_le_right).op).hom (c₂ (Fin.last p)) +
        u ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p := by
  have i₁ : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j) := fun _ hy => hy.1
  have i₂ : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j') := fun _ hy => hy.2
  have hV := le_inf (i₁.trans (le_chart G x p L a ha (p : ℤ) j)) (i₂.trans (le_chart G x p L a ha (p : ℤ) j'))
  have hg := congrArg (res hV) (hC (fun _ => j) (fun _ => j'))
  rw [map_mul, linComb_g L a _ (p : ℤ) j j' _ hV hA hB, zpow_natCast] at hg
  have hg' := congrArg Units.val hg
  rw [Units.val_mul, Units.val_pow_eq_pow_val,
    res_value_compose _ _ (le_chart G x p L a ha (p : ℤ) j) i₁, res_value_compose _ _ (le_chart G x p L a ha (p : ℤ) j') i₂, h₁, h₂, hu,
    sum_res G x p inf_le_left i₁, sum_res G x p inf_le_right i₂] at hg'
  refine GlobalTheory.T.truncated_expansion_pth_power_coeff _ _ ((prZ G x p).app _).hom (dltOn G x p _) p (cast_p G x _ _ p) (dltOn_pow G x p _)
    ?_ u _ _ u₀ ?_ ?_ hg'
  · intro c c' e
    exact (GlobalTheory.T.power_series_expansion_in_delta_unique X0 G k x p _ _).unique rfl e
  · rw [e₁, map_one]
  · rw [e₂, map_one]

def tU (W : (pullback G.hom x).Opens) (s : Γ(pullback G.hom x, W)) : Γ(Ym G x 1, prZ G x 1 ⁻¹ᵁ W)ˣ where
  val := 1 + dltOn G x 1 _ * ((prZ G x 1).app W).hom s
  inv := 1 - dltOn G x 1 _ * ((prZ G x 1).app W).hom s
  val_inv := by
    linear_combination (-(((prZ G x 1).app W).hom s) ^ 2) * dltOn_pow G x 1 (prZ G x 1 ⁻¹ᵁ W)
  inv_val := by
    linear_combination (-(((prZ G x 1).app W).hom s) ^ 2) * dltOn_pow G x 1 (prZ G x 1 ⁻¹ᵁ W)

theorem tU_res {W W' : (pullback G.hom x).Opens} (h : W' ≤ W) (h' : prZ G x 1 ⁻¹ᵁ W' ≤ prZ G x 1 ⁻¹ᵁ W)
    (s : Γ(pullback G.hom x, W)) :
    (res h' (tU G x W s)).val = 1 + dltOn G x 1 _ *
      ((prZ G x 1).app W').hom (((pullback G.hom x).presheaf.map (homOfLE h).op).hom s) := by
  show ((Ym G x 1).presheaf.map (homOfLE h').op).hom (1 + dltOn G x 1 _ * ((prZ G x 1).app W).hom s) = _
  rw [map_add (f := _), map_one, map_mul, dltOn_res]
  congr 2
  have := (prZ G x 1).naturality (homOfLE h).op
  exact (congrArg (fun q => q.hom s) this).symm

theorem pullU_eq {X Y : Scheme.{0}} (b : Y ⟶ X) (O : X.Opens) (u : Γ(X, O)ˣ) (h : b ⁻¹ᵁ O ≤ b ⁻¹ᵁ O) :
    pullU b O u = Units.map (b.appLE O _ h).hom.toMonoidHom u := by
  ext
  show (b.app O).hom u.val = (b.appLE O _ h).hom u.val
  rw [Scheme.Hom.app_eq_appLE]

theorem ring_step {R : Type*} [CommRing R] (d S S' : R) (h : d ^ (1 + 1) = 0) :
    1 + d * S = (1 + (S - S') * d) * (1 + d * S') := by
  linear_combination (-(S - S') * S') * h

theorem second (hp : 1 ≤ p) (hL : L.IsLB) (ha : secZ G x p ≫ a = pullback.fst G.hom x)
    (s : ∀ j, Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j))
    (cu : ∀ j j', Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j'))
    (hA : ∀ j j', prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (hB : ∀ j j', prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      (prZ G x p ≫ pullback.fst G.hom x) ⁻¹ᵁ (L.U j ⊓ L.U j'))
    (hcu : ∀ j j', (trU L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ (hA j j') (hB j j')).val =
        ∑ i, ((prZ G x p).app _).hom (cu j j' i) * dltOn G x p _ ^ (i : ℕ))
    (h0 : ∀ j j', cu j j' 0 = 1)
    (h1 : ∀ j j', cu j j' ⟨1, by omega⟩ =
      ((pullback G.hom x).presheaf.map (homOfLE (inf_le_left : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _)).op).hom (s j) -
      ((pullback G.hom x).presheaf.map (homOfLE (inf_le_right : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _)).op).hom (s j')) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![trY G x p hp ≫ a, trY G x p hp ≫ prZ G x p ≫ pullback.fst G.hom x] ![1, -1]),
      c.IsGen := by
  have e : trY G x p hp ≫ prZ G x p ≫ pullback.fst G.hom x = prZ G x 1 ≫ pullback.fst G.hom x := by
    rw [← Category.assoc, trY_prZ]
  rw [e]
  refine GlobalTheory.T.line_bundle_cocycle_pullback_transform _ _ L hL _ _ ?_ (fun j => tU G x _ (s j)) ?_
  · intro y
    have h := base_eq G x p a ha (trY G x p hp y)
    have h' := congrArg (fun q : Ym G x 1 ⟶ G.left => q y) e
    simp only [Scheme.Hom.comp_apply] at h h' ⊢
    rw [h, h']
  · intro j j' h
    have hs : prZ G x 1 ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
        trY G x p hp ⁻¹ᵁ (prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j')) := by
      intro y hy
      show (trY G x p hp ≫ prZ G x p) y ∈ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j')
      rw [trY_prZ]
      exact hy
    have hU := trU_pull' L a (prZ G x p ≫ pullback.fst G.hom x) j j' _ (hA j j') (hB j j') (trY G x p hp) _ hs
      (trY G x p hp ≫ a) (prZ G x 1 ≫ pullback.fst G.hom x) rfl e h le_rfl
    have hv := congrArg Units.val hU
    have hv' : (trU L (trY G x p hp ≫ a) (prZ G x 1 ≫ pullback.fst G.hom x) j j'
        (prZ G x 1 ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j')) h le_rfl).val =
        ((prZ G x 1).app _).hom (cu j j' 0) + ((prZ G x 1).app _).hom (cu j j' ⟨1, by omega⟩) * dltOn G x 1 _ := by
      rw [← hv, ← tr_sum G x p hp _ hs, ← hcu]
      rfl
    rw [h0, h1, map_one, map_sub] at hv'
    have hT : Units.map ((trY G x p hp ≫ a).appLE _ _ h).hom.toMonoidHom (L.g j j') *
        (pullU (prZ G x 1 ≫ pullback.fst G.hom x) _ (L.g j j'))⁻¹ =
        trU L (trY G x p hp ≫ a) (prZ G x 1 ≫ pullback.fst G.hom x) j j' _ h le_rfl := by
      rw [pullU_eq _ _ _ le_rfl]
      rfl
    rw [hT]
    have t₁ := tU_res G x (inf_le_left : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _) (fun _ hy => hy.1) (s j)
    have t₂ := tU_res G x (inf_le_right : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _) (fun _ hy => hy.2) (s j')
    ext
    refine t₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) hv'.symm t₂.symm))
    exact ring_step _ _ _ (dltOn_pow G x 1 _)

end Main
end PositivityTheory.HtPt.Qam.CoreP

namespace PositivityTheory.HtPt.Qam


open CoreP in
theorem core_firstOrder : ∀ (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) [IsIntegral (pullback G.hom x)] [CharP (pullback G.hom x).functionField p], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (pullback G.hom x) → ∀ (L : LB G.left), L.IsLB → ∀ (a b : Ym G x p ⟶ G.left), b = prZ G x p ≫ pullback.fst G.hom x → secZ G x p ≫ a = pullback.fst G.hom x → ∀ (C : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![(p : ℤ), -(p : ℤ)])), C.IsGen → (∀ (j : L.ι) (h : pullback.fst G.hom x ⁻¹ᵁ L.U j ≤ secZ G x p ⁻¹ᵁ LB.wchart L (K := Fin 2) ![a, b] (fun _ => j)), ((secZ G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1) → ∀ (j₀ : L.ι) [Nonempty (pullback.fst G.hom x ⁻¹ᵁ L.U j₀)], (∀ (c : Fin (p + 1) → Γ(pullback G.hom x, pullback.fst G.hom x ⁻¹ᵁ L.U j₀)) (h : prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j₀) ≤ LB.wchart L (K := Fin 2) ![a, b] (fun _ => j₀)), ((Ym G x p).presheaf.map (homOfLE h).op).hom (C.s fun _ => j₀).val = ∑ i, ((prZ G x p).app _).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∃ r : (pullback G.hom x).functionField, r ^ p = ((pullback G.hom x).germToFunctionField _).hom (c (Fin.last p))) → ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![trY G x p hp ≫ a, trY G x p hp ≫ b] ![1, -1]), c.IsGen := by
  intro X0 G k _ x p _ _ hp _ _ hZ L hL a b hb ha C hC hn j₀ _ hr
  subst hb
  choose cf hcf hcf0 using fun j => CoreP.chart_coef G x p L a ha C hn j
  have hA : ∀ j j', prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      a ⁻¹ᵁ (L.U j ⊓ L.U j') := fun j j' => CoreP.le_pre G x p a ha (L.U j ⊓ L.U j')
  have hB : ∀ j j', prZ G x p ⁻¹ᵁ (pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j') ≤
      (prZ G x p ≫ pullback.fst G.hom x) ⁻¹ᵁ (L.U j ⊓ L.U j') := fun _ _ _ hy => hy
  choose cu hcu hcu0 using fun j j' => CoreP.tr_coef G x p L a ha j j' (hA j j') (hB j j')
  have hnp : ∀ j j', cu j j' ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p =
      ((pullback G.hom x).presheaf.map (homOfLE (inf_le_left : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _)).op).hom (cf j (Fin.last p)) -
      ((pullback G.hom x).presheaf.map (homOfLE (inf_le_right : pullback.fst G.hom x ⁻¹ᵁ L.U j ⊓ pullback.fst G.hom x ⁻¹ᵁ L.U j' ≤ _)).op).hom (cf j' (Fin.last p)) := by
    intro j j'
    rw [CoreP.overlap G x p L a ha C hC j j' (cf j) (cf j') (hcf j) (hcf j') (hcf0 j) (hcf0 j') (hA j j') (hB j j')
      (cu j j') (hcu j j') (hcu0 j j')]
    ring
  obtain ⟨r, hr'⟩ := hr (cf j₀) (CoreP.le_chart G x p L a ha (p : ℤ) j₀) (hcf j₀)
  obtain ⟨s, hs⟩ := GlobalTheory.T.artin_schreier_cocycle_root (pullback G.hom x) p hZ L.ι (fun j => pullback.fst G.hom x ⁻¹ᵁ L.U j)
    (fun j j' => cu j j' ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩) (fun j => cf j (Fin.last p)) j₀ hnp ⟨r, hr'⟩
  exact CoreP.second G x p L a hp hL ha s cu hA hB hcu hcu0 hs

end PositivityTheory.HtPt.Qam
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cocp

theorem cocycle_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 1 ≤ p) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k), alpha g.B p (fun i => w i ^ p) = 0 → ∃ c : LB.Gen (Out.translDiff t.G t.PP.L (homAt x (toFirst k p hp) ≫ (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G))), c.IsGen := by
  intro E _ _ _ H _ hstar X0 t k _ _ p _ _ hp x d g w hα
  obtain ⟨hy0, hy1, -⟩ := PositivityTheory.HtPt.Ce.pt_of_vec E H hstar X0 t k p hp x d g w
  have hwv : (hw g.B p).mulVec (fun i => w i ^ p) = 0 := by
    have := congrArg Prod.fst hα
    rwa [alpha_apply] at this
  have hyp := hy1 hwv
  obtain ⟨gs, hax, hpow, -⟩ := GlobalTheory.T.pow_one_series_p_formula k p d (𝓞 E) g.B
  have hkill := GlobalTheory.T.alpha_kernel_derivative_vanishes k p d (𝓞 E) g.B (fun i => w i ^ p) gs hα hpow
  have hf : ∀ q, MvPowerSeries.pderiv (R := k) q (dSer gs fun i => w i ^ p) = 0 := by
    rintro ⟨i, j⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hkill j
  obtain ⟨hI, hN, hCh, hT⟩ := GlobalTheory.T.formal_germ_jet_lift E H hstar X0 t k p x d g (fun m => xkZ t.G x (g.x m))
    (fun m => xkZ_fst t.G x _) (fun m => xkZ_snd t.G x _)
  obtain ⟨C, hC, hnorm, hB⟩ := GlobalTheory.CompanionTheory.Ar.Coc.Pf.pfold E H hstar X0 t k p x d g w gs hax hpow _ rfl hy0 hyp
  have hL := t.PP.isLB
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨s⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ := by
    have hc := hL.cover
    have : (1 : overAt x k ⟶ t.G).left s ∈ (⊤ : t.G.left.Opens) := trivial
    rw [← hc] at this
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    refine ⟨j, fun s' _ => ?_⟩
    have e : s' = s := Subsingleton.elim (α := Sp k) _ _
    rw [e]
    exact hj
  have hU : ∀ m, ⊤ ≤ xkZ t.G x (g.x m) ⁻¹ᵁ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀) := by
    intro m q _
    have e : (homAt x (jetAug : Jet k (Fin 1 × Fin d) m →ₐ[k] k) ≫ g.x m).left = (1 : overAt x k ⟶ t.G).left :=
      congrArg (fun q => q.left) (g.chart.zero m)
    have e₁ : pullback.fst t.G.hom x (xkZ t.G x (g.x m) q) = (g.x m).left q := by
      rw [← Scheme.Hom.comp_apply, xkZ_fst]
    have e₂ : (g.x m).left q = (1 : overAt x k ⟶ t.G).left s := by
      rw [← jet_pt m q s, ← e]
      rfl
    change pullback.fst t.G.hom x (xkZ t.G x (g.x m) q) ∈ t.PP.L.U j₀
    rw [e₁, e₂]
    exact hj₀ trivial
  haveI : Nonempty (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀) :=
    ⟨⟨_, hU 0 (show (spMap ((jetAug : Jet k (Fin 1 × Fin d) 0 →ₐ[k] k) : Jet k (Fin 1 × Fin d) 0 →+* k) s) ∈ ⊤ from trivial)⟩⟩
  have main := PositivityTheory.HtPt.Qam.core_firstOrder X0 t.G k x p hp hN t.PP.L hL _ _ (prZ_fst t.G x p).symm (secZ_pa t.G x _ hy0) C hC hnorm j₀
    (fun c h hc => by
      obtain ⟨F, hF1, -, hF3⟩ := hT _ hU (c (Fin.last p))
      refine hF3 (GlobalTheory.T.pderiv_zero_of_jet_pth_power_diff k p d F _ hf fun m => ?_)
      obtain ⟨v, hv⟩ := hB j₀ hj₀ m
      refine ⟨v, ?_⟩
      have hr : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ (prZ t.G x p ⁻¹ᵁ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀)) := by
        intro q _
        have e : prZ t.G x p (rQ t.G x p (g.x m) q) = xkZ t.G x (g.x m)
            (spMap ((inR (k := k) (Jet k (Fin 1 × Fin d) m) p : Jet k (Fin 1 × Fin d) m →ₐ[k] Jet (Jet k (Fin 1 × Fin d) m) Unit p) : Jet k (Fin 1 × Fin d) m →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p) q) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, rQ_prZ]
        change prZ t.G x p (rQ t.G x p (g.x m) q) ∈ (pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j₀)
        rw [e]
        exact hU m trivial
      have hr' : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![_, _] (fun _ => j₀) :=
        hr.trans fun q hq => h hq
      have h2 := GlobalTheory.T.delta_expansion_restriction X0 t.G k x p hp _ (g.x m) _ (hU m) c _ (v ^ p - psJet m (dSer gs fun i => w i ^ p)) hc hr (by
        rw [← hv hr']
        exact congrArg (fun q => q.hom (C.s fun _ => j₀).val) (Scheme.Hom.map_appLE (rQ t.G x p (g.x m)) hr (homOfLE h).op))
      exact toΓ_inj _ ((hF1 m).symm.trans h2))
  rw [trY_pa, trY_pb] at main
  exact main

theorem tanpf_inj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), TanPF t x p → ConjInj g.B p :=
  PositivityTheory.HtPt.Ce.tanpf_inj_of cocycle_p

end PositivityTheory.HtPt.Cocp
