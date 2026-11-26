module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompF
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsAdj
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsAdjOne
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

section Push

variable (S : Thick (dp0 R) s) {A : Type} [CommRing A] (a : S.B →+* A) {JA : Ideal A} (θ : DividedPowers JA)
  (ha : IsDPMorphism S.δ θ a)

include ha in
theorem push_ker : RingHom.ker S.π ≤ RingHom.ker ((Ideal.Quotient.mk JA).comp a) := fun b hb ↦
  Ideal.Quotient.eq_zero_iff_mem.2 (ha.1 (Ideal.mem_map_of_mem _ ((S.ker b).1 hb)))

def pushRed : S.B₀ →+* A ⧸ JA := RingHom.liftOfSurjective S.π S.surj ⟨_, push_ker S a θ ha⟩

theorem pushRed_π (b : S.B) : pushRed S a θ ha (S.π b) = Ideal.Quotient.mk JA (a b) :=
  RingHom.liftOfSurjective_comp_apply S.π S.surj ⟨_, push_ker S a θ ha⟩ b

variable (hn : IsNilDP θ)

def push : Thick (dp0 R) s where
  B := A
  alg := (a.comp (algebraMap R S.B)).toAlgebra
  J := JA
  δ := θ
  nil := hn
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  B₀ := A ⧸ JA
  π := Ideal.Quotient.mk JA
  surj := Ideal.Quotient.mk_surjective
  ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem
  x := spMap (pushRed S a θ ha) ≫ S.x
  w := by
    rw [Category.assoc, S.w, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ pushRed_π S a θ ha _

def pushHom : S ⟶ push S a θ ha hn where
  φ := { a with commutes' := fun _ ↦ rfl }
  φ₀ := pushRed S a θ ha
  comm := pushRed_π S a θ ha
  dp := ha
  pt := rfl

def pushDesc {V : Thick (dp0 R) s} (φ : S ⟶ V) (G : A →+* V.B) (hG : IsDPMorphism θ V.δ G)
    (e : G.comp a = (φ.φ : S.B →+* V.B)) : push S a θ ha hn ⟶ V where
  φ := { G with commutes' := fun r ↦ (DFunLike.congr_fun e _).trans (φ.φ.commutes r) }
  φ₀ := Ideal.Quotient.lift JA (V.π.comp G) fun _ hc ↦ (V.ker _).2 (hG.1 (Ideal.mem_map_of_mem _ hc))
  comm := fun _ ↦ rfl
  dp := hG
  pt := by
    change spMap _ ≫ spMap (pushRed S a θ ha) ≫ S.x = V.x
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, ← φ.pt]
    congr 2
    refine RingHom.ext fun b ↦ ?_
    obtain ⟨b, rfl⟩ := S.surj b
    rw [RingHom.comp_apply, pushRed_π, φ.comm]
    exact congrArg V.π (DFunLike.congr_fun e b)

end Push

theorem exists_trunc (S : Thick (dp0 R) s) (hS : InN κ S) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P), InN κ P ∧ IsLev P.δ n ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V), ∃! ψ : P ⟶ V, i ≫ ψ = φ := by
  obtain ⟨A, _, a, JA, θ, ha, hlev, hext, hsurj, huniv⟩ := ring_trunc κ (algebraMap R S.B) S.δ hS n hn
  have hnil : IsNilDP θ := Fil.nil_of_lev hlev
  refine ⟨push S a θ ha hnil, pushHom S a θ ha hnil, hext, hlev, ?_⟩
  intro V hV φ
  obtain ⟨G, hG, hGa⟩ := huniv V.B V.J V.δ hV (φ.φ : S.B →+* V.B) φ.dp
  refine ⟨pushDesc S a θ ha hnil φ G hG hGa, ?_, ?_⟩
  · refine Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_)
    rw [Thick.comp_φ]
    exact DFunLike.congr_fun hGa b
  · intro ψ hψ
    refine Thick.Hom.ext' (AlgHom.ext fun x ↦ ?_)
    obtain ⟨b, rfl⟩ := hsurj x
    have h1 := Thick.comp_φ (pushHom S a θ ha hnil) ψ b
    rw [hψ] at h1
    have h2 : G (a b) = φ.φ b := DFunLike.congr_fun hGa b
    exact h1.symm.trans h2.symm

theorem exists_adj_one (S : Thick (dp0 R) s) (hS : InN κ S) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (y : P.B), InN κ P ∧ IsLev P.δ n ∧ y ∈ P.J ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (z : V.B), z ∈ V.J →
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ ψ.φ y = z := by
  obtain ⟨A, _, a, JA, θ, y, ha, hlev, hext, hy, huniv⟩ := ring_adj κ (algebraMap R S.B) S.δ hS n hn
  have hnil : IsNilDP θ := Fil.nil_of_lev hlev
  refine ⟨push S a θ ha hnil, pushHom S a θ ha hnil, y, hext, hlev, hy, ?_⟩
  intro V hV φ z hz
  obtain ⟨G, ⟨hG, hGa, hGy⟩, huniq⟩ := huniv V.B V.J V.δ hV (φ.φ : S.B →+* V.B) φ.dp z hz
  refine ⟨pushDesc S a θ ha hnil φ G hG hGa, ⟨?_, hGy⟩, ?_⟩
  · refine Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_)
    rw [Thick.comp_φ]
    exact DFunLike.congr_fun hGa b
  · rintro ψ ⟨hψ, hψy⟩
    let g : A →+* V.B := ψ.φ.toRingHom
    have hcomp : g.comp a = (φ.φ : S.B →+* V.B) := by
      refine RingHom.ext fun b ↦ ?_
      have h1 := Thick.comp_φ (pushHom S a θ ha hnil) ψ b
      rw [hψ] at h1
      exact h1.symm
    have heq : g = G := huniq g ⟨ψ.dp, hcomp, hψy⟩
    refine Thick.Hom.ext' (AlgHom.ext fun x ↦ ?_)
    exact DFunLike.congr_fun heq x

theorem exists_adj' (S : Thick (dp0 R) s) (hS : InN κ S) (d n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (y : Fin d → P.B), InN κ P ∧ IsLev P.δ n ∧ (∀ k, y k ∈ P.J) ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (z : Fin d → V.B), (∀ k, z k ∈ V.J) →
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ ∀ k, ψ.φ (y k) = z k := by
  induction d with
  | zero =>
    obtain ⟨P, i, hP, hlev, huniv⟩ := exists_trunc S hS n hn
    refine ⟨P, i, Fin.elim0, hP, hlev, fun k ↦ Fin.elim0 k, ?_⟩
    intro V hV φ z _
    obtain ⟨ψ, hψ, huniq⟩ := huniv V hV φ
    exact ⟨ψ, ⟨hψ, fun k ↦ Fin.elim0 k⟩, fun ψ' h ↦ huniq ψ' h.1⟩
  | succ d ih =>
    obtain ⟨P, i, y, hP, hlev, hy, huniv⟩ := ih
    obtain ⟨Q, j, w, hQ, hlevQ, hw, hunivQ⟩ := exists_adj_one P hP n hn
    refine ⟨Q, i ≫ j, Fin.cons w (fun k ↦ j.φ (y k)), hQ, hlevQ, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · simpa using hw
      · simp only [Fin.cons_succ]
        exact j.dp.ideal_comp (Ideal.mem_map_of_mem _ (hy k))
    · intro V hV φ z hz
      obtain ⟨ψ₁, ⟨hψ₁, hψ₁y⟩, huniq₁⟩ := huniv V hV φ (fun k ↦ z k.succ) (fun k ↦ hz k.succ)
      obtain ⟨ψ, ⟨hψ, hψw⟩, huniq⟩ := hunivQ V hV ψ₁ (z 0) (hz 0)
      refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
      · rw [Category.assoc, hψ, hψ₁]
      · intro k
        refine Fin.cases ?_ (fun k ↦ ?_) k
        · simpa using hψw
        · simp only [Fin.cons_succ]
          rw [← Thick.comp_φ, hψ]
          exact hψ₁y k
      · rintro ψ' ⟨hψ', hψ'y⟩
        have h1 : j ≫ ψ' = ψ₁ := by
          refine huniq₁ (j ≫ ψ') ⟨?_, fun k ↦ ?_⟩
          · rw [← Category.assoc]
            exact hψ'
          · rw [Thick.comp_φ]
            have := hψ'y k.succ
            simpa only [Fin.cons_succ] using this
        refine huniq ψ' ⟨h1, ?_⟩
        have := hψ'y 0
        simpa only [Fin.cons_zero] using this

end FubiniStudyChowHeightFormula₂.Adr
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

theorem exists_adj (S : Thick (dp0 R) s) (hS : InN κ S) (d n : ℕ) (hn : 1 ≤ n) :
    ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (y : Fin d → P.B), InN κ P ∧ IsLev P.δ n ∧ (∀ k, y k ∈ P.J) ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (z : Fin d → V.B), (∀ k, z k ∈ V.J) →
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ ∀ k, ψ.φ (y k) = z k :=
  exists_adj' S hS d n hn

end FubiniStudyChowHeightFormula₂.Adr
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

section Rings

variable {P A B C : Type} [CommRing P] [CommRing A] [CommRing B] [CommRing C]

theorem fe_lift (t : P →+* A) (ht : t.FormallyEtale) (π : B →+* C) (hπ : Function.Surjective π)
    (hn : IsNilpotent (RingHom.ker π)) (u : P →+* B) (f : A →+* C) (h : f.comp t = π.comp u) :
    ∃ g : A →+* B, g.comp t = u ∧ π.comp g = f := by
  letI := t.toAlgebra
  letI : Algebra P C := (π.comp u).toAlgebra
  letI : Algebra P B := u.toAlgebra
  haveI : Algebra.FormallyEtale P A := ht
  let fA : A →ₐ[P] C := { f with commutes' := fun r => RingHom.congr_fun h r }
  let πA : B →ₐ[P] C := { π with commutes' := fun r => rfl }
  let g := Algebra.FormallySmooth.liftOfSurjective fA πA hπ hn
  refine ⟨g.toRingHom, ?_, ?_⟩
  · ext r
    exact g.commutes r
  · ext x
    exact Algebra.FormallySmooth.liftOfSurjective_apply fA πA hπ hn x

theorem fe_uniq (t : P →+* A) (ht : t.FormallyEtale) (π : B →+* C) (hn : IsNilpotent (RingHom.ker π))
    (g₁ g₂ : A →+* B) (h : g₁.comp t = g₂.comp t) (h' : π.comp g₁ = π.comp g₂) : g₁ = g₂ := by
  letI := t.toAlgebra
  letI : Algebra P B := (g₁.comp t).toAlgebra
  haveI : Algebra.FormallyEtale P A := ht
  let a₁ : A →ₐ[P] B := { g₁ with commutes' := fun r => rfl }
  let a₂ : A →ₐ[P] B := { g₂ with commutes' := fun r => (RingHom.congr_fun h r).symm }
  have key := Algebra.FormallyUnramified.ext' π hn a₁ a₂ (fun x => RingHom.congr_fun h' x)
  ext x
  exact AlgHom.congr_fun key x

theorem fe_of_etale {t : P →+* A} (ht : t.Etale) : t.FormallyEtale := by
  letI := t.toAlgebra
  haveI : Algebra.Etale P A := ht
  show Algebra.FormallyEtale P A
  infer_instance

theorem isNilpotent_of_isNilDP {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) : IsNilpotent J := by
  obtain ⟨N, hN⟩ := h.exists_dpow_eq_zero
  have hexp : ∀ xs : List B, (∀ x ∈ xs, x ∈ J) → ∀ y ∈ J, ∀ n, N ≤ n →
      PowerSeries.coeff n ((xs.map fun x => δ.exp x - 1).prod * δ.exp y) = 0 := by
    intro xs
    induction xs with
    | nil =>
      intro _ y _ n hn
      simp [DividedPowers.exp, PowerSeries.coeff_mk, hN n hn]
    | cons x xs ih =>
      intro hxs y hy n hn
      have hx : x ∈ J := hxs x (by simp)
      have hxs' : ∀ z ∈ xs, z ∈ J := fun z hz => hxs z (by simp [hz])
      have e : (List.map (fun x => δ.exp x - 1) (x :: xs)).prod * δ.exp y
          = (xs.map fun x => δ.exp x - 1).prod * δ.exp (x + y)
            - (xs.map fun x => δ.exp x - 1).prod * δ.exp y := by
        rw [δ.exp_add hx hy, List.map_cons, List.prod_cons]
        ring
      rw [e, map_sub, ih hxs' (x + y) (J.add_mem hx hy) n hn, ih hxs' y hy n hn, sub_zero]
  have hone : δ.exp 0 = 1 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [DividedPowers.exp, δ.dpow_zero J.zero_mem]
    · simp [DividedPowers.exp, PowerSeries.coeff_one, δ.dpow_eval_zero hn.ne', hn.ne']
  have hfac : ∀ xs : List B, (∀ x ∈ xs, x ∈ J) → ∃ G : PowerSeries B,
      (xs.map fun x => δ.exp x - 1).prod = PowerSeries.X ^ xs.length * G ∧
        PowerSeries.constantCoeff G = xs.prod := by
    intro xs
    induction xs with
    | nil => exact fun _ => ⟨1, by simp, by simp⟩
    | cons x xs ih =>
      intro hxs
      have hx : x ∈ J := hxs x (by simp)
      obtain ⟨G, hG, hG0⟩ := ih (fun z hz => hxs z (by simp [hz]))
      refine ⟨PowerSeries.mk (fun n => δ.dpow (n + 1) x) * G, ?_, ?_⟩
      · have ex : δ.exp x - 1 = PowerSeries.X * PowerSeries.mk (fun n => δ.dpow (n + 1) x) := by
          ext n
          rcases n with _ | n
          · simp [DividedPowers.exp, δ.dpow_zero hx]
          · rw [PowerSeries.coeff_succ_X_mul]
            simp [DividedPowers.exp, PowerSeries.coeff_one]
        rw [List.map_cons, List.prod_cons, hG, ex, List.length_cons, pow_succ]
        ring
      · rw [map_mul, hG0, List.prod_cons, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_mk, zero_add, δ.dpow_one hx]
  have hprod : ∀ xs : List B, (∀ x ∈ xs, x ∈ J) → N ≤ xs.length → xs.prod = 0 := by
    intro xs hxs hlen
    obtain ⟨G, hG, hG0⟩ := hfac xs hxs
    have := hexp xs hxs 0 J.zero_mem xs.length hlen
    rw [hone, mul_one, hG] at this
    have e2 := PowerSeries.coeff_X_pow_mul G xs.length 0
    rw [zero_add] at e2
    rw [e2, PowerSeries.coeff_zero_eq_constantCoeff_apply, hG0] at this
    exact this
  have key : ∀ n, ∀ z ∈ J ^ n, ∀ xs : List B, (∀ x ∈ xs, x ∈ J) → N ≤ n + xs.length →
      z * xs.prod = 0 := by
    intro n
    induction n with
    | zero =>
      intro z _ xs hxs hlen
      rw [hprod xs hxs (by simpa using hlen), mul_zero]
    | succ n ih =>
      intro z hz xs hxs hlen
      rw [pow_succ'] at hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro a ha b hb
        have := ih b hb (a :: xs) (fun x hx' => by
          rcases List.mem_cons.1 hx' with rfl | hx'
          · exact ha
          · exact hxs x hx') (by simp; omega)
        rw [List.prod_cons] at this
        rw [← this]
        ring
      · intro u v hu hv
        rw [add_mul, hu, hv, add_zero]
  refine ⟨N, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  intro z hz
  have := key N z hz [] (by simp) (by simp)
  simpa using this

end Rings

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

instance (U : X.affineOpens) : IsOpenImmersion (affPt s U) := U.2.isOpenImmersion_fromSpec

theorem nil_ker {γ : DividedPowers I} (T : Thick γ s) : IsNilpotent (RingHom.ker T.π) := by
  have : RingHom.ker T.π = T.J := Ideal.ext T.ker
  rw [this]
  exact isNilpotent_of_isNilDP T.nil

theorem res_etale {U V : X.affineOpens} (h : V.1 ≤ U.1) : (Sec.res s h : Sec s U.1 →+* Sec s V.1).Etale := by
  have e : V.1 ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U.1 := h
  have H := (𝟙 X : X ⟶ X).etale_appLE U.2 V.2 e
  have key : ((𝟙 X : X ⟶ X).appLE U.1 V.1 e).hom = (Sec.res s h : Sec s U.1 →+* Sec s V.1) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    rfl
  rw [key] at H
  exact H

theorem sec_smooth (hs : Smooth s) (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have e : U.1 ≤ s ⁻¹ᵁ (⊤ : (Sp R).Opens) := le_top
  have H1 : (s.appLE ⊤ U.1 e).hom.Smooth := hs.smooth_appLE (isAffineOpen_top (Sp R)) U.2 e
  have H0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Smooth :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have H := H0.comp H1
  rw [← RingHom.smooth_algebraMap]
  exact H

theorem chart_cover (hs : Smooth s) : ⨆ U : Chart s, U.1.1 = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  rw [TopologicalSpace.Opens.mem_iSup]
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  letI algV : Algebra R Γ(X, V) := (secMap s V).hom.toAlgebra
  have hsmV : Algebra.Smooth R Γ(X, V) := by
    have e : V ≤ s ⁻¹ᵁ (⊤ : (Sp R).Opens) := le_top
    have H1 : (s.appLE ⊤ V e).hom.Smooth := hs.smooth_appLE (isAffineOpen_top (Sp R)) hV e
    have H0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Smooth :=
      RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact H0.comp H1
  obtain ⟨S, hS, hSt⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R Γ(X, V)
  have hcov := (hV.iSup_basicOpen_eq_self_iff (s := S)).2 hS
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hxV
  obtain ⟨⟨g, hgS⟩, hxg⟩ := hxV
  let W : X.affineOpens := ⟨X.basicOpen g, hV.basicOpen g⟩
  refine ⟨⟨W, ?_, ?_⟩, hxg⟩
  · exact RingHom.flat_algebraMap_iff.1
      (RingHom.Smooth.flat (RingHom.smooth_algebraMap.2 (sec_smooth hs W)))
  · haveI := hSt g hgS
    obtain ⟨d, g', hg'C, hg'e⟩ :=
      RingHom.IsStandardSmooth.exists_etale_mvPolynomial (RingHom.isStandardSmooth_algebraMap.2 this)
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) := hV.isLocalization_basicOpen g
    let e : Localization.Away g ≃ₐ[Γ(X, V)] Γ(X, X.basicOpen g) :=
      IsLocalization.algEquiv (Submonoid.powers g) _ _
    have he : (e : Localization.Away g →+* Γ(X, X.basicOpen g)).FormallyEtale := by
      letI := (e : Localization.Away g →+* Γ(X, X.basicOpen g)).toAlgebra
      show Algebra.FormallyEtale (Localization.Away g) Γ(X, X.basicOpen g)
      exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ => rfl))
    have hcompat : ∀ r, e (algebraMap R (Localization.Away g) r) = algebraMap R (Sec s W.1) r := by
      intro r
      rw [IsScalarTower.algebraMap_apply R Γ(X, V) (Localization.Away g), e.commutes]
      show (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom ((secMap s V).hom r) =
        (secMap s (X.basicOpen g)).hom r
      rw [← CommRingCat.comp_apply]
      have key := Scheme.Hom.appLE_map s (U := ⊤) (V := V) (V' := X.basicOpen g) le_top
        (homOfLE (X.basicOpen_le g)).op
      simp only [secMap, Category.assoc]
      exact congrArg (fun φ => ConcreteCategory.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ) r) key
    let tr : MvPolynomial (Fin d) R →+* Sec s W.1 := (e : Localization.Away g →+* Γ(X, X.basicOpen g)).comp g'
    refine ⟨d, { tr with commutes' := fun r => ?_ }, ?_⟩
    · show e (g' (MvPolynomial.C r)) = algebraMap R (Sec s W.1) r
      rw [← RingHom.comp_apply g' MvPolynomial.C, hg'C]
      exact hcompat r
    · exact RingHom.FormallyEtale.comp (fe_of_etale hg'e) he

theorem chart_inf (hs : IsSeparated s) (U V : Chart s) : ∃ W : Chart s, W.1.1 = U.1.1 ⊓ V.1.1 := by
  have ha : IsAffineOpen (U.1.1 ⊓ V.1.1) :=
    isAffineHom_diagonal_iff.1 (inferInstance : IsAffineHom (Limits.pullback.diagonal s)) ⊤ (isAffineOpen_top _)
      _ le_top _ le_top U.1.2 V.1.2
  let W : X.affineOpens := ⟨_, ha⟩
  have hW : W.1 ≤ U.1.1 := inf_le_left
  have he := res_etale (s := s) hW
  obtain ⟨hf, d, t, ht⟩ := U.2
  refine ⟨⟨W, ?_, d, (Sec.res s hW).comp t, ht.comp (fe_of_etale he)⟩, rfl⟩
  have k := (RingHom.flat_algebraMap_iff.2 hf).comp (RingHom.Etale.iff_flat_and_formallyUnramified.1 he).1
  rw [AlgHom.comp_algebraMap] at k
  exact RingHom.flat_algebraMap_iff.1 k

theorem bas_le (U : X.affineOpens) : ⊤ ≤ (bas s U).x ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge

theorem bas_inN (U : Chart s) : InN κ (bas s U.1) := by
  haveI : Module.Flat R (Sec s U.1.1) := U.2.1
  obtain ⟨δ, hδ⟩ := flatExt R (Sec s U.1.1) I κ
  refine ExtDP.of_eq (κ := κ) δ (bot_sup_eq _).symm ⟨by simp, fun {n} a ha => ?_⟩ hδ
  rw [Ideal.mem_bot] at ha
  subst ha
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [RingHom.id_apply, RingHom.id_apply, DividedPowers.dpow_zero _ (Ideal.zero_mem _),
      DividedPowers.dpow_zero _ (Ideal.zero_mem _)]
  · rw [RingHom.id_apply, RingHom.id_apply, DividedPowers.dpow_eval_zero _ hn.ne',
      DividedPowers.dpow_eval_zero _ hn.ne']

theorem eq_of_affPt (U : X.affineOpens) {B : Type} [CommRing B] {f g : Sec s U.1 →+* B}
    (h : spMap f ≫ affPt s U = spMap g ≫ affPt s U) : f = g := by
  have h1 : spMap f = spMap g := (cancel_mono (affPt s U)).1 h
  have h2 : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

theorem exists_hom_of_le (U : X.affineOpens) {B : Type} [CommRing B] (x : Sp B ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U.1) :
    ∃ f : Sec s U.1 →+* B, spMap f ≫ affPt s U = x := by
  have hr : Set.range x ⊆ Set.range (affPt s U) := by
    rintro _ ⟨p, rfl⟩
    have hp : p ∈ x ⁻¹ᵁ U.1 := h trivial
    show _ ∈ Set.range U.2.fromSpec
    rw [U.2.range_fromSpec]
    exact hp
  let y := IsOpenImmersion.lift (affPt s U) x hr
  refine ⟨(Spec.preimage y).hom, ?_⟩
  have e : spMap (Spec.preimage y).hom = y := Spec.map_preimage y
  rw [e]
  exact IsOpenImmersion.lift_fac _ _ _

theorem exists_lift_of_coord (U : X.affineOpens) {d : ℕ} (t : MvPolynomial (Fin d) R →ₐ[R] Sec s U.1)
    (ht : t.toRingHom.FormallyEtale) (T : Thick (dp0 R) s) (f : Sec s U.1 →+* T.B₀) (hf : spMap f ≫ affPt s U = T.x)
    (z : Fin d → T.B) (hz : ∀ k, T.π (z k) = f (t (MvPolynomial.X k))) :
    ∃ j : bas s U ⟶ T, ∀ k, j.φ (t (MvPolynomial.X k)) = z k := by
  have hw : affPt s U ≫ s = spMap (algebraMap R (Sec s U.1)) := (bas s U).w
  have hsp : spMap (f.comp (algebraMap R (Sec s U.1))) = spMap (T.π.comp (algebraMap R T.B)) := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← hw, ← Category.assoc, hf, T.w]
  have hR : f.comp (algebraMap R (Sec s U.1)) = T.π.comp (algebraMap R T.B) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective hsp)
  let u : MvPolynomial (Fin d) R →ₐ[R] T.B := MvPolynomial.aeval z
  have hfu : f.comp t.toRingHom = T.π.comp u.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h1 := RingHom.congr_fun hR r
      show f (t (MvPolynomial.C r)) = T.π (u (MvPolynomial.C r))
      rw [← MvPolynomial.algebraMap_eq, t.commutes, u.commutes]
      exact h1
    · intro k
      show f (t (MvPolynomial.X k)) = T.π (u (MvPolynomial.X k))
      rw [MvPolynomial.aeval_X]
      exact (hz k).symm
  obtain ⟨g, hg1, hg2⟩ := fe_lift t.toRingHom ht T.π T.surj (nil_ker T) u.toRingHom f hfu
  let φ : Sec s U.1 →ₐ[R] T.B :=
    { g with
      commutes' := fun r => by
        have h1 := RingHom.congr_fun hg1 (algebraMap R (MvPolynomial (Fin d) R) r)
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes] at h1
        exact h1 }
  have hφ : spMap (T.π.comp (φ : Sec s U.1 →+* T.B)) ≫ affPt s U = T.x := by
    have e : T.π.comp (φ : Sec s U.1 →+* T.B) = f := hg2
    rw [e, hf]
  refine ⟨Thick.trivHom φ hφ, fun k => ?_⟩
  have h1 := RingHom.congr_fun hg1 (MvPolynomial.X k)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [MvPolynomial.aeval_X] at h1
  exact h1

theorem exists_lift (U : Chart s) (T : Thick (dp0 R) s) (h : ⊤ ≤ T.x ⁻¹ᵁ U.1.1) : Nonempty (bas s U.1 ⟶ T) := by
  obtain ⟨-, d, t, ht⟩ := U.2
  obtain ⟨f, hf⟩ := exists_hom_of_le (s := s) U.1 T.x h
  choose z hz using fun k ↦ T.surj (f (t (MvPolynomial.X k)))
  exact ⟨(exists_lift_of_coord U.1 t ht T f hf z hz).choose⟩

theorem π_eq (U : X.affineOpens) {T : Thick (dp0 R) s} (a b : bas s U ⟶ T) (c : Sec s U.1) :
    T.π (a.φ c) = T.π (b.φ c) :=
  (a.comm c).symm.trans ((RingHom.congr_fun (eq_of_affPt U (a.pt.trans b.pt.symm)) c).trans (b.comm c))

theorem lift_ext (U : X.affineOpens) {d : ℕ} (t : MvPolynomial (Fin d) R →ₐ[R] Sec s U.1)
    (ht : t.toRingHom.FormallyEtale) {T : Thick (dp0 R) s} (a b : bas s U ⟶ T)
    (h : ∀ k, a.φ (t (MvPolynomial.X k)) = b.φ (t (MvPolynomial.X k))) : a = b := by
  have e1 : (a.φ.comp t : MvPolynomial (Fin d) R →ₐ[R] T.B) = b.φ.comp t :=
    MvPolynomial.algHom_ext (fun k => h k)
  have key := fe_uniq t.toRingHom ht T.π (nil_ker T) (a.φ : Sec s U.1 →+* T.B) (b.φ : Sec s U.1 →+* T.B)
    (RingHom.ext fun p => AlgHom.congr_fun e1 p) (RingHom.ext fun c => π_eq U a b c)
  exact Thick.Hom.ext' (AlgHom.ext fun c => RingHom.congr_fun key c)

theorem exists_coprod (U : Chart s) (S : Thick (dp0 R) s) (hS : InN κ S) (h : ⊤ ≤ S.x ⁻¹ᵁ U.1.1) (n : ℕ)
    (hn : 1 ≤ n) : ∃ (P : Thick (dp0 R) s) (i : S ⟶ P) (j : bas s U.1 ⟶ P), InN κ P ∧ IsLev P.δ n ∧
      ∀ (V : Thick (dp0 R) s), IsLev V.δ n → ∀ (φ : S ⟶ V) (b : bas s U.1 ⟶ V),
        ∃! ψ : P ⟶ V, i ≫ ψ = φ ∧ j ≫ ψ = b := by
  obtain ⟨-, d, t, ht⟩ := U.2
  obtain ⟨fS, hfS⟩ := @exists_hom_of_le R _ X s U.1 S.B₀ S.ring₀ S.x h
  choose zS hzS using fun k : Fin d => S.surj (fS (t (MvPolynomial.X k)))
  obtain ⟨jS, -⟩ := exists_lift_of_coord U.1 t ht S fS hfS zS hzS
  obtain ⟨P, i, y, hP, hlev, hy, huniv⟩ := exists_adj S hS d n hn
  have hbπ : ∀ {T : Thick (dp0 R) s} (a : bas s U.1 ⟶ T) (c : Sec s U.1.1), T.π (a.φ c) = a.φ₀ c :=
    fun a c => (a.comm c).symm
  have hyπ : ∀ k, P.π (y k) = 0 := fun k => (P.ker _).2 (hy k)
  obtain ⟨j, hj⟩ := exists_lift_of_coord U.1 t ht P (jS ≫ i).φ₀ (jS ≫ i).pt
    (fun k => (jS ≫ i).φ (t (MvPolynomial.X k)) + y k)
    (fun k => by
      simp only []
      rw [map_add (f := _), hyπ, add_zero, hbπ])
  refine ⟨P, i, j, hP, hlev, fun V hV φ b => ?_⟩
  have hiψ : ∀ (ψ : P ⟶ V), i ≫ ψ = φ → ∀ x, ψ.φ (i.φ x) = φ.φ x := by
    intro ψ e x
    rw [← Thick.comp_φ, e]
  let zV : Fin d → V.B := fun k => b.φ (t (MvPolynomial.X k)) - (jS ≫ φ).φ (t (MvPolynomial.X k))
  have hzV : ∀ k, zV k ∈ V.J := fun k => by
    refine (V.ker _).1 ?_
    simp only [zV, map_sub]
    exact sub_eq_zero.2 (π_eq U.1 b (jS ≫ φ) _)
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := huniv V hV φ zV hzV
  refine ⟨ψ, ⟨hψ1, ?_⟩, ?_⟩
  · apply lift_ext U.1 t ht
    intro k
    rw [Thick.comp_φ, hj k, map_add (f := _), hψ2]
    simp only [zV]
    rw [Thick.comp_φ jS i, Thick.comp_φ jS φ, hiψ ψ hψ1]
    ring
  · rintro ψ' ⟨h1, h2⟩
    apply hψu
    refine ⟨h1, fun k => ?_⟩
    have e1 : ψ'.φ (j.φ (t (MvPolynomial.X k))) = b.φ (t (MvPolynomial.X k)) := by
      rw [← Thick.comp_φ, h2]
    rw [hj k, map_add (f := _), Thick.comp_φ jS i, hiψ ψ' h1] at e1
    simp only [zV]
    rw [Thick.comp_φ jS φ, ← e1]
    ring

end FubiniStudyChowHeightFormula₂.Adr
