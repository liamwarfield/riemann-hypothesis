module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.FirstChernNaturality
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.FirstChernNaturality

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  simp [chains, chainsXIso, chainsN, HomologicalComplex.extendMap_f]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem freeGen_nat {P P' : PSh} (g : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R P' U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  unfold freeGen
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P')).app (op U)).hom
    ((((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) = _
  congr 1
  simp only [ModuleCat.freeMk, freeP]
  simp [ModuleCat.free]
  erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem ev_zpull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (γ : Cocycle ((chains R).obj E') I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1 p s h U x =
      ev γ.1 p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  have hc : (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1.v (-(p : ℤ)) s h =
      ((chains R).map f).f (-(p : ℤ)) ≫ γ.1.v (-(p : ℤ)) s h := by
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by simp) h]
  unfold ev
  rw [hc, ← Category.assoc, chainsXIso_inv_nat, Category.assoc]
  exact congrArg (((chainsXIso R E' p).inv ≫ γ.1.v (-(p : ℤ)) s h).hom.app (op U)).hom
    (freeGen_nat (f.app (op (SimplexCategory.mk p))) U x)

theorem sub_nat {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  unfold Sx.sub
  exact congrFun (congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)) x

theorem lineUnit_comp {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) :
    lineUnit (f ≫ L) x = lineUnit L ((f.app (op (SimplexCategory.mk 1))).app (op U) x) := rfl

theorem etale_first_chern_class_natural_of_spec (hC1 : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle) : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassNaturalUnderPullback := by
  intro q _ E E' f L hinv
  have hinvE : Inv q E := fun U ⟨x⟩ => hinv U ⟨(f.app _).app _ x⟩
  obtain ⟨⟨γ, hγ⟩, h2⟩ := hC1 q L hinv
  rw [h2 γ hγ]
  obtain ⟨_, h2'⟩ := hC1 q (f ≫ L) hinvE
  rw [h2' (zcomp (Cocycle.ofHom ((chains _).map f)) γ (zero_add 2)) ?_]
  · rfl
  obtain ⟨g0, g1, g2⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · intro U x
    rw [ev_zpull]; exact g0 U _
  · intro U x v hv
    rw [ev_zpull]; exact g1 U _ v (by rw [hv, lineUnit_comp])
  · intro U x v w hv hw
    rw [ev_zpull]
    exact g2 U _ v w (by rw [hv, lineUnit_comp, sub_nat]) (by rw [hw, lineUnit_comp, sub_nat])

end LateralTheory.E.FirstChernNaturality
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DomCoverPf
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonDenom
noncomputable def UpperTheory.Reformulated.B.Qn19.AIC :
    (A : Type) → [CommRing A] → Prop :=
    fun (A : Type) [CommRing A] ↦
      ∀ (p : Polynomial A), p.Monic → (0 : ℕ) < p.natDegree → ∃ (a : A), Polynomial.eval a p = (0 : A)

private theorem UpperTheory.Reformulated.B.Qn19.commonDenom {R L : Type} [CommRing R] [CommRing L] (φ : R →+* L)
    (h : ∀ z : L, ∃ a b : R, IsUnit (φ b) ∧ z * φ b = φ a) (s : Finset L) :
    ∃ b : R, IsUnit (φ b) ∧ ∀ z ∈ s, ∃ a : R, φ a = z * φ b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert x s _ ih =>
    obtain ⟨b, hb, hs⟩ := ih
    obtain ⟨a, c, hc, hx⟩ := h x
    refine ⟨b * c, by rw [map_mul]; exact hb.mul hc, ?_⟩
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨a * b, by rw [map_mul, map_mul, ← hx]; ring⟩
    · obtain ⟨d, hd⟩ := hs z hz
      exact ⟨d * c, by rw [map_mul, map_mul, hd]; ring⟩

theorem UpperTheory.Reformulated.B.Qn19.aicFrac :
    ∀ (R L : Type) [inst : CommRing R] [inst_1 : CommRing L] (φ : R →+* L),
      UpperTheory.Reformulated.B.Qn19.AIC R →
        (∀ (z : L), ∃ (a : R) (b : R), IsUnit ((φ : R → L) b) ∧ z * (φ : R → L) b = (φ : R → L) a) → UpperTheory.Reformulated.B.Qn19.AIC L := by
  intro R L _ _ φ hR h p hp hdeg
  obtain ⟨b, hb, hs⟩ := UpperTheory.Reformulated.B.Qn19.commonDenom φ h p.coeffs
  have hmon : (p.scaleRoots (φ b)).Monic := (Polynomial.monic_scaleRoots_iff _).2 hp
  have hlift : p.scaleRoots (φ b) ∈ Polynomial.lifts φ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · by_cases h0 : p.coeff i = 0
      · exact ⟨0, by simp [h0]⟩
      · obtain ⟨a, ha⟩ := hs _ (Polynomial.coeff_mem_coeffs h0)
        obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
        exact ⟨a * b ^ k, by rw [map_mul, map_pow, ha, hk]; ring⟩
    · subst hi
      exact ⟨1, by simp [hp.coeff_natDegree]⟩
    · exact ⟨0, by simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]⟩
  obtain ⟨q, hq, hqd, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  rw [Polynomial.natDegree_scaleRoots] at hqd
  obtain ⟨a, ha⟩ := hR q hqm (by rw [hqd]; exact hdeg)
  obtain ⟨u, hu⟩ := hb
  refine ⟨(↑u⁻¹ : L) * φ a, ?_⟩
  have h1 : Polynomial.eval (φ a) (p.scaleRoots (φ b)) = 0 := by
    rw [← hq, Polynomial.eval_map, Polynomial.eval₂_hom, ha, map_zero]
  have h2 := Polynomial.scaleRoots_eval_mul p ((↑u⁻¹ : L) * φ a) (φ b)
  have h3 : φ b * ((↑u⁻¹ : L) * φ a) = φ a := by
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  rw [h3, h1, ← hu] at h2
  exact ((u.isUnit.pow p.natDegree).mul_right_eq_zero).1 h2.symm
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC

namespace LateralTheory.E.DomCoverPf

theorem aicFrac (R L : Type) [CommRing R] [CommRing L] (φ : R →+* L) (hR : AIC R)
    (h : ∀ z : L, ∃ a b : R, IsUnit (φ b) ∧ z * φ b = φ a) : AIC L :=
  _root_.UpperTheory.Reformulated.B.Qn19.aicFrac R L φ hR h

def IdemCover : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ t_E3Cut.SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧
    ∀ z : Localization.AtPrime r, ∃ a b : C, IsUnit (algebraMap D (Localization.AtPrime r) (g.hom b)) ∧
      z * algebraMap D (Localization.AtPrime r) (g.hom b) = algebraMap D (Localization.AtPrime r) (g.hom a)

theorem DomCover_of (h2 : IdemCover) : t_E3Cut.DomCover := by
  intro C hC
  obtain ⟨D, g, hi, hs, hr⟩ := h2 C
  refine ⟨D, g, hi, hs, fun r _ => ⟨(hr r).1, ?_⟩⟩
  exact aicFrac C (Localization.AtPrime r) ((algebraMap D (Localization.AtPrime r)).comp g.hom) hC (hr r).2

end LateralTheory.E.DomCoverPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafNewtonPf
noncomputable section
open PowerSeries

namespace LateralTheory.E.LeafNewtonPf

def nser {A : Type 1} [CommRing A] (c : ℕ → A) : PowerSeries A :=
  -(X * PowerSeries.derivative (mk c)) * (mk c).invOfUnit 1

lemma uniq {A : Type 1} [CommRing A] {f g s : PowerSeries A} (hf : constantCoeff f = 1) (h : s * f = g) :
    g * f.invOfUnit 1 = s := by
  rw [← h, mul_assoc, mul_invOfUnit f 1 (by simp [hf]), mul_one]

lemma nser_eq {A : Type 1} [CommRing A] (c : ℕ → A) {s : PowerSeries A} (h0 : constantCoeff (mk c) = 1)
    (h : s * mk c = -(X * PowerSeries.derivative (mk c))) : nser c = s := uniq h0 h

lemma nser_spec {A : Type 1} [CommRing A] (c : ℕ → A) (h0 : c 0 = 1) :
    nser c * mk c = -(X * PowerSeries.derivative (mk c)) := by
  unfold nser
  rw [mul_assoc, invOfUnit_mul (mk c) 1 (by simp [h0]), mul_one]

lemma map_deriv {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (f : PowerSeries A) :
    map φ (PowerSeries.derivative f) = PowerSeries.derivative (map φ f) := by
  ext n
  simp [coeff_derivative, coeff_map, map_mul, map_natCast]

lemma part1 {A B : Type 1} [CommRing A] [CommRing B] (φ : A →+* B) (c : ℕ → A) (h0 : c 0 = 1) (k : ℕ) :
    φ (LateralTheory.E.D2.newton c k) = LateralTheory.E.D2.newton (fun j => φ (c j)) k := by
  have hm : map φ (mk c) = mk (fun j => φ (c j)) := by ext n; simp [coeff_map]
  have key : nser (fun j => φ (c j)) = map φ (nser c) := by
    apply nser_eq _ (by simp [h0])
    have := congrArg (map φ) (nser_spec c h0)
    rw [map_mul, hm, map_neg, map_mul, map_X, map_deriv, hm] at this
    exact this
  show φ (coeff k (nser c)) = coeff k (nser (fun j => φ (c j)))
  rw [key, coeff_map]

lemma part2 {A : Type 1} [CommRing A] (c d e : ℕ → A) (hc : c 0 = 1) (hd : d 0 = 1)
    (he : ∀ k, e k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 * d p.2) (k : ℕ) :
    LateralTheory.E.D2.newton e k = LateralTheory.E.D2.newton c k + LateralTheory.E.D2.newton d k := by
  have hm : mk e = mk c * mk d := by ext n; rw [coeff_mk, he, coeff_mul]; simp [coeff_mk]
  have he0 : e 0 = 1 := by rw [he]; simp [hc, hd]
  have key : nser e = nser c + nser d := by
    apply nser_eq _ (by simp [he0])
    rw [hm, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have h1 := nser_spec c hc
    have h2 := nser_spec d hd
    linear_combination (mk d) * h1 + (mk c) * h2
  show coeff k (nser e) = coeff k (nser c) + coeff k (nser d)
  rw [key, map_add (f := _)]

lemma geom {A : Type 1} [CommRing A] (x : A) : mk (fun k => x ^ k) * (1 - C x * X) = 1 := by
  ext n
  rcases n with _ | n
  · simp [mul_sub]
  · rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm _ (C x), coeff_succ_mul_X, coeff_C_mul]
    simp [pow_succ, mul_comm]

lemma part3 {A : Type 1} [CommRing A] (c : ℕ → A) (x : A) (h0 : c 0 = 1) (h1 : c 1 = -x)
    (h2 : ∀ j, 1 < j → c j = 0) (k : ℕ) (hk : 0 < k) : LateralTheory.E.D2.newton c k = x ^ k := by
  have hm : mk c = 1 - C x * X := by
    ext n
    rcases n with _ | _ | n
    · simp [h0]
    · simp [h1]
    · rw [coeff_mk, h2 _ (by omega)]
      simp [coeff_one]
  have key : nser c = C x * X * mk (fun k => x ^ k) := by
    apply nser_eq _ (by simp [h0])
    rw [mul_assoc, hm, geom, mul_one]
    simp [map_sub, mul_comm]
  show coeff k (nser c) = x ^ k
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [key, mul_comm (C x) X, mul_assoc, coeff_succ_X_mul, coeff_C_mul, coeff_mk, pow_succ, mul_comm]

theorem LeafNewton_of : LateralTheory.E.D2.LeafNewton :=
  ⟨fun _ _ _ _ φ c h0 k => part1 φ c h0 k,
   fun _ _ c d e hc hd he k => part2 c d e hc hd he k,
   fun _ _ c x h0 h1 h2 k hk => part3 c x h0 h1 h2 k hk⟩

end LateralTheory.E.LeafNewtonPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ZariskiLocalCech
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZariskiLocalCech

def CechSigma : Prop := t_E3Cut.Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens)
  {ι : Type} (V : ι → X.Opens), (∀ j, V j ≤ O) → O ≤ ⨆ j, V j →
  (∀ n : ℕ, Eqv R (sch.map (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k)))) F) →
  Eqv R (sch.map (g ∣_ O)) F

section
variable {R : Type} [CommRing R] {F : Shv R}

theorem eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := fun n => by
  have h : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [h]; exact (hf n).comp (hg n)

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := fun n => by
  have h1 : ∀ x, pull R (inv f) F n (pull R f F n x) = x := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R f F n (pull R (inv f) F n x) = x := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem sigmaEqv (hC : t_E3Cut.Coprod) {ι : Type} {Y X : ι → Scheme.{0}} (f : ∀ j, Y j ⟶ X j)
    (hf : ∀ j, Eqv R (sch.map (f j)) F) : Eqv R (sch.map (Limits.Sigma.map f)) F := fun n => by
  have key : (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι Y j)) F n
      (pull R (sch.map (Limits.Sigma.map f)) F n x)) =
      Pi.map (fun j => pull R (sch.map (f j)) F n) ∘
        (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x) := by
    funext x j
    simp only [Function.comp_apply, Pi.map_apply]
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, Sigma.ι_map]
  have hb := (Function.Bijective.piMap (fun j => hf j n)).comp (hC R F X n)
  rw [← key] at hb
  exact (Function.Bijective.of_comp_iff' (hC R F Y n) _).1 hb

theorem eqv_of_top {Y X : Scheme.{0}} (g : Y ⟶ X) (h : Eqv R (sch.map (g ∣_ ⊤)) F) : Eqv R (sch.map g) F := by
  have : IsIso (⊤ : X.Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have : IsIso (g ⁻¹ᵁ ⊤).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have e : g = inv (g ⁻¹ᵁ ⊤).ι ≫ (g ∣_ ⊤) ≫ (⊤ : X.Opens).ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [e, Functor.map_comp, Functor.map_comp]
  exact eqv_comp (eqv_iso _) (eqv_comp h (eqv_iso _))

end

theorem inf_basicOpen {X : Scheme.{0}} {A : X.Opens} {κ : Type} [DecidableEq κ] (f : κ → Γ(X, A)) (s : Finset κ) :
    (s.inf fun k => X.basicOpen (f k)) ⊓ A = X.basicOpen (∏ k ∈ s, f k) := by
  induction s using Finset.induction_on with
  | empty => simp [X.basicOpen_of_isUnit isUnit_one]
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.prod_insert ha, Scheme.basicOpen_mul, ← ih, inf_assoc]

theorem iInf_basicOpen {X : Scheme.{0}} {A : X.Opens} {n : ℕ} (f : Fin (n + 1) → Γ(X, A)) :
    (⨅ k, X.basicOpen (f k)) = X.basicOpen (∏ k, f k) := by
  rw [← inf_basicOpen f Finset.univ, Finset.inf_univ_eq_iInf]
  exact (inf_eq_left.2 ((iInf_le (fun k => X.basicOpen (f k)) 0).trans (X.basicOpen_le (f 0)))).symm

theorem ZarLocal_of (hCop : t_E3Cut.Coprod) (hCS : CechSigma) : t_E3Cut.ZarLocal := by
  intro hH R _ F Y X g hU
  choose U hxU hUe using hU
  have hA : ∀ x : X, ∃ A : X.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ U x := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (hxU x) (U x).2
    exact ⟨V, hV, hxV, hVU⟩
  choose A hAaff hxA hAU using hA
  have st1 : ∀ (x : X) (O : X.Opens), O ≤ A x → Eqv R (sch.map (g ∣_ O)) F := by
    intro x O hO
    refine hCS hH R F g O (ι := {f : Γ(X, A x) // X.basicOpen f ≤ O}) (fun f => X.basicOpen f.1) (fun f => f.2) ?_ ?_
    · intro y hy
      obtain ⟨f, hfO, hyf⟩ := (hAaff x).exists_basicOpen_le ⟨y, hy⟩ (hO hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfO⟩, hyf⟩
    · intro n
      apply sigmaEqv hCop
      intro j
      have e := iInf_basicOpen (X := X) (A := A x) (fun k => (j k).1)
      apply hUe x
      · rw [e]; exact (hAaff x).basicOpen _
      · exact (iInf_le _ 0).trans ((X.basicOpen_le _).trans (hAU x))
  refine eqv_of_top g (hCS hH R F g ⊤ A (fun _ => le_top) ?_ ?_)
  · intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxA y⟩
  · exact fun n => sigmaEqv hCop _ fun j => st1 (j 0) _ (iInf_le _ 0)

end LateralTheory.E.ZariskiLocalCech
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafLinePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafLinePf

theorem det_mulVec_one (A : Type) [CommRing A] (g : GL (Fin 1) A) :
    (g : Matrix (Fin 1) (Fin 1) A).mulVec (fun _ => 1) = ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) • (fun _ => (1 : A)) := by
  funext i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [Matrix.mulVec, dotProduct, Matrix.det_unique]

def e1 (A : Type) [CommRing A] : Um 1 A := ⟨fun _ => 1, by
  rw [Set.range_const]; exact Ideal.span_singleton_one⟩

def secF (A : Type) [CommRing A] : SingleObj (GL (Fin 1) A) ⥤ Um 1 A where
  obj _ := e1 A
  map g := ⟨(g, Matrix.GeneralLinearGroup.det g), det_mulVec_one A g⟩
  map_id _ := Subtype.ext (Prod.ext rfl (map_one _))
  map_comp f g := Subtype.ext (Prod.ext rfl (map_mul _ _ _))

theorem eqToHom_val {A : Type} [CommRing A] {v w : Um 1 A} (h : v = w) : (eqToHom h).1 = 1 := by
  cases h; rfl

theorem comp_val {A : Type} [CommRing A] {u v w : Um 1 A} (a : u ⟶ v) (b : v ⟶ w) : (a ≫ b).1 = b.1 * a.1 := rfl

theorem det_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 1) A) :
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f g) : Bˣ) : B) = f ((Matrix.GeneralLinearGroup.det g : Aˣ) : A) := by
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.map_det]
  rfl

def secNat : glCat 1 ⟶ pglCat 1 where
  app A := (secF A).toCatHom
  naturality A B f := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun _ => Subtype.ext (funext fun _ => (map_one f.hom).symm)) (fun _ _ g => ?_)
    apply Subtype.ext
    erw [comp_val, comp_val, eqToHom_val, eqToHom_val, one_mul, mul_one]
    refine Prod.ext rfl ?_
    ext
    change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.hom (show GL (Fin 1) A from g)) : (B : Type)ˣ) : (B : Type)) =
      f.hom ((Matrix.GeneralLinearGroup.det (show GL (Fin 1) A from g) : (A : Type)ˣ) : (A : Type))
    exact det_map f.hom _

theorem ofCatMap_comp {C D F : CommRingCat.{0} ⥤ Cat.{0,0}} (α : C ⟶ D) (β : D ⟶ F) :
    ofCatMap α ≫ ofCatMap β = ofCatMap (α ≫ β) := rfl

theorem ofCatMap_id (C : CommRingCat.{0} ⥤ Cat.{0,0}) : ofCatMap (𝟙 C) = 𝟙 _ := rfl

def sec : ofCat (glCat 1) ⟶ PGL 1 := ofCatMap secNat

theorem sec_pr : sec ≫ PGL.pr 1 = 𝟙 (ofCat (glCat 1)) := rfl

theorem single_eqToHom {M : Type} [Monoid M] {x y : SingleObj M} (h : x = y) : (eqToHom h : x ⟶ y) = (1 : M) := by
  cases h; rfl

theorem sec_line : sec ≫ PGL.line 1 = 𝟙 (ofCat (glCat 1)) := by
  rw [sec, PGL.line]
  erw [ofCatMap_comp]
  rw [← ofCatMap_id]
  congr 1
  apply NatTrans.ext
  funext A
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ g => ?_)
  erw [single_eqToHom]
  change _ = ((1 : GL (Fin 1) A) * (id g : GL (Fin 1) A)) * 1
  rw [one_mul, mul_one]
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (Matrix.GeneralLinearGroup.det (id g : GL (Fin 1) A)) = (id g : GL (Fin 1) A)
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

end LateralTheory.E.LeafLinePf

namespace LateralTheory.E.D2
open LateralTheory.E.LeafLinePf

theorem LeafLine_of (hA : LeafA6nat) : LeafLine := by
  intro q _ P E h L c hc
  obtain ⟨h0, -, heq⟩ := hc
  have hw : 𝟙 E ≫ L = (L ≫ sec) ≫ PGL.pr 1 := by
    rw [Category.assoc, sec_pr, Category.id_comp, Category.comp_id]
  let σ : E ⟶ PB L := pullback.lift (𝟙 E) (L ≫ sec) hw
  have hpr : σ ≫ PB.pr L = 𝟙 E := pullback.lift_fst _ _ _
  have hline : σ ≫ PB.line L = L := by
    rw [PB.line, ← Category.assoc]
    erw [pullback.lift_snd]
    rw [Category.assoc, sec_line, Category.comp_id]
  have h' : Inv q (PB L) := inv_of (PB.pr L) h
  have hm : ∀ j, P.map σ h h' (P.map (PB.pr L) h' h (P.ι h j (c j))) = P.ι h j (c j) := by
    intro j
    rw [P.map_ι, P.map_ι, ← pull_comp, hpr, pull_id]
  have hx : P.map σ h h' (P.deg1 h' (c1 q (PB.line L))) = P.deg1 h (c1 q L) := by
    rw [Collected.deg1, P.map_ι, pull_cast, (hA q).2.2.1 σ (PB.line L) h', hline]
  have := congrArg (P.map σ h h') heq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add (f := _), map_mul, map_pow, map_zero, zero_add, hm, hx,
    map_one, h0] at this
  simp only [one_mul, Nat.sub_zero, Nat.sub_self, pow_one, pow_zero, mul_one] at this
  linear_combination this

end LateralTheory.E.D2
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafChernPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.ChernPf

theorem cast_rfl {q : ℕ} {E : Spc} {n i : ℤ} (x : Ht q E n i) (h1 : n = n) (h2 : i = i) : x.cast h1 h2 = x := rfl

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (h1 : n = n') (h2 : i = i')
    (h3 : n' = n'') (h4 : i' = i'') : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem term {q : ℕ} (P : Collected q) {E F : Spc} (f : F ⟶ E) (h : Inv q E) (h' : Inv q F) (y : Ht q F 2 1)
    {n' i' : ℤ} (u : Ht q E n' i') (k m N : ℕ) (hN : k + m = N) (hn : n' = 2 * (k : ℤ)) (hi : i' = k)
    (h1 : n' + 2 * (m : ℤ) = 2 * (N : ℤ)) (h2 : i' + (m : ℤ) = N) :
    P.ι h' N ((cup q (pull _ f _ _ u) (cpow q y m)).cast h1 h2) =
      P.map f h' h (P.ι h k (u.cast hn hi)) * P.ι h' m (cpow q y m) := by
  subst hN hn hi
  rw [cast_rfl, P.map_ι]
  exact P.ι_mul h' k m _ _

variable {q : ℕ} {E : Spc} {N : ℕ}

def Phi (V : E ⟶ ofCat (glCat N)) (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    Ht q (PB V) (2 * (N : ℤ)) N :=
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ (2 * (N : ℤ)) N)

def ac (c : ∀ j : ℕ, Ht q E (2 * j) j) : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ)) :=
  fun j => (c (N - j)).cast (by have := j.isLt; omega) (by have := j.isLt; omega)

theorem phi_ι (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N))
    (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) :
    P.ι (inv_of (PB.pr V) h) N (Phi V a) = ∑ j : Fin N, P.map (PB.pr V) (inv_of (PB.pr V) h) h
      (P.ι h (N - j) ((a j).cast (by have := j.isLt; omega) (by have := j.isLt; omega))) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (j : ℕ) := by
  unfold Phi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [term P (PB.pr V) h (inv_of (PB.pr V) h) _ (a j) (N - j) j N (by have := j.isLt; omega)
    (by have := j.isLt; omega) (by have := j.isLt; omega), P.ι_cpow]

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2.ChernPf
variable {q : ℕ} {E : Spc} {N : ℕ}

theorem cast_inj {n i n' i' : ℤ} {x y : Ht q E n i} (h1 : n = n') (h2 : i = i') (e : x.cast h1 h2 = y.cast h1 h2) : x = y := by
  subst h1 h2; exact e

theorem cast_idx {n i : Fin N → ℤ} (a : ∀ j, Ht q E (n j) (i j)) (j j' : Fin N) (e : j = j')
    (h1 : n j = n j') (h2 : i j = i j') : (a j).cast h1 h2 = a j' := by
  subst e; rfl

theorem sum_eq (P : Collected q) (h : Inv q E) (V : E ⟶ ofCat (glCat N)) (c : ∀ j : ℕ, Ht q E (2 * j) j)
    (h0 : P.ι h 0 (c 0) = 1) :
    ∑ j ∈ Finset.range (N + 1), P.map (PB.pr V) (inv_of (PB.pr V) h) h (P.ι h j (c j)) *
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ (N - j) =
      P.deg1 (inv_of (PB.pr V) h) (c1 q (PB.line V)) ^ N + P.ι (inv_of (PB.pr V) h) N (Phi V (ac c)) := by
  have key : ∀ g : ℕ → P.R (PB V) (inv_of (PB.pr V) h),
      ∑ j ∈ Finset.range (N + 1), g j = ∑ j ∈ Finset.range N, g (N - j) + g 0 := by
    intro g
    rw [← Finset.sum_range_reflect, Finset.sum_range_succ]
    simp
  rw [key, phi_ι P h V, h0, map_one, one_mul, Nat.sub_zero, add_comm, Finset.sum_range]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.sub_sub_self j.isLt.le]
  dsimp only [ac]
  rw [ChernPf.cast_cast, cast_rfl]

def mkc (a : ∀ j : Fin N, Ht q E (2 * (N : ℤ) - 2 * ((j : ℕ) : ℤ)) ((N : ℤ) - ((j : ℕ) : ℤ))) : ∀ j : ℕ, Ht q E (2 * j) j :=
  fun j => if h0 : j = 0 then (one q E).cast (by simp [h0]) (by simp [h0])
    else if hj : j ≤ N then (a ⟨N - j, by omega⟩).cast (by simp; omega) (by simp; omega) else 0

end LateralTheory.E.D2.ChernPf

namespace LateralTheory.E.D2
open ChernPf

theorem LeafChern_of : LeafChern := by
  intro hD1 q _ P E h N V
  have hB : Function.Bijective (Phi (q := q) V) := hD1 q V h (2 * (N : ℤ)) N
  have hι : ∀ {F : Spc} (h : Inv q F) k, Function.Injective (P.ι h k) := fun h k a b e => by
    simpa [P.π_ι] using congrArg (P.π h k) e
  have char : ∀ c, P.ι h 0 (c 0) = 1 → (IsChern P h V c ↔
      (∀ j, N < j → c j = 0) ∧ Phi V (ac c) = -cpow q (c1 q (PB.line V)) N) := by
    intro c h0
    unfold IsChern
    rw [sum_eq P h V c h0, ← P.ι_cpow, ← map_add (f := _), map_eq_zero_iff _ (hι _ _), add_eq_zero_iff_neg_eq, eq_comm]
    simp only [h0, true_and]
    exact and_congr_right fun _ => eq_comm
  have uniq : ∀ c c', IsChern P h V c → IsChern P h V c' → c = c' := by
    intro c c' hc hc'
    have hA : ac c = ac c' := hB.1 (((char c hc.1).1 hc).2.trans ((char c' hc'.1).1 hc').2.symm)
    funext j
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hι h 0 (hc.1.trans hc'.1.symm)
    by_cases hjN : N < j
    · rw [hc.2.1 j hjN, hc'.2.1 j hjN]
    have := cast_inj _ _ (congrFun hA ⟨N - j, by omega⟩)
    have e : N - ((⟨N - j, by omega⟩ : Fin N) : ℕ) = j := by simp; omega
    rw [e] at this
    exact this
  obtain ⟨a, ha⟩ := hB.2 (-cpow q (c1 q (PB.line V)) N)
  have hc0 : P.ι h 0 (mkc a 0) = 1 := by
    dsimp only [mkc]
    rw [dite_eq_left rfl]
    exact P.ι_one h
  have hac : ac (mkc a) = a := by
    funext j
    dsimp only [ac, mkc]
    rw [dite_eq_right (by omega), dite_eq_left (by omega), ChernPf.cast_cast]
    exact cast_idx a _ _ (Fin.ext (by simp; omega)) _ _
  have hC : IsChern P h V (mkc a) := (char _ hc0).2 ⟨fun j hj => by
    dsimp only [mkc]
    rw [dite_eq_right (by omega), dite_eq_right (by omega)], by rw [hac]; exact ha⟩
  exact ⟨mkc a, hC, fun c' hc' => uniq _ _ hc' hC⟩

end LateralTheory.E.D2
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafWhitneyPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2.WhitneyPf

theorem alg {A : Type*} [CommRing A] (C D : ℕ → A) (x : A) (a b : ℕ) (hC : ∀ i, a < i → C i = 0)
    (hD : ∀ j, b < j → D j = 0) :
    ∑ k ∈ Finset.range (a + b + 1), (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      (∑ i ∈ Finset.range (a + 1), C i * x ^ (a - i)) * (∑ j ∈ Finset.range (b + 1), D j * x ^ (b - j)) := by
  set f : ℕ → ℕ → A := fun i j => C i * D j * x ^ (a + b - (i + j)) with hf
  have h1 : ∀ k, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, C p.1 * D p.2) * x ^ (a + b - k) =
      ∑ i ∈ Finset.range (k + 1), f i (k - i) := by
    intro k
    rw [Finset.sum_mul, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ f k]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [hf, hp]
  simp_rw [h1]
  rw [Finset.sum_range_diag_flip (a + b + 1) f, Finset.sum_mul_sum]
  have h2 : ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), C i * x ^ (a - i) * (D j * x ^ (b - j)) =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hi hj
    simp only [hf]
    rw [show a + b - (i + j) = (a - i) + (b - j) by omega, pow_add]; ring
  rw [h2]
  symm
  calc ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f i j
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_subset ?_ ?_
        · simp only [Finset.mem_range] at hi
          intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
        · intro j _ hnj
          simp only [Finset.mem_range] at hnj
          simp only [hf]; rw [hD j (by omega)]; ring
    _ = ∑ i ∈ Finset.range (a + b + 1), ∑ j ∈ Finset.range (a + b + 1 - i), f i j := by
        refine Finset.sum_subset ?_ ?_
        · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
        · intro i _ hni
          simp only [Finset.mem_range] at hni
          refine Finset.sum_eq_zero fun j _ => ?_
          simp only [hf]; rw [hC i (by omega)]; ring

variable {q : ℕ}

def ccup {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j) (hk : i + j = k) : Ht q E (2 * k) k :=
  (cup q a b).cast (by subst hk; push_cast; ring) (by subst hk; push_cast; ring)

theorem ι_ccup (P : Collected q) {E : Spc} (h : Inv q E) {i j k : ℕ} (a : Ht q E (2 * i) i) (b : Ht q E (2 * j) j)
    (hk : i + j = k) : P.ι h k (ccup a b hk) = P.ι h i a * P.ι h j b := by
  subst hk; exact P.ι_mul h i j a b

theorem cast_zero {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem pull_cast {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem ccup_zero_left {E : Spc} {i j k : ℕ} (b : Ht q E (2 * j) j) (hk : i + j = k) :
    ccup (0 : Ht q E (2 * i) i) b hk = 0 := by
  unfold ccup; rw [map_zero, AddMonoidHom.zero_apply, cast_zero]

theorem ccup_zero_right {E : Spc} {i j k : ℕ} (a : Ht q E (2 * i) i) (hk : i + j = k) :
    ccup a (0 : Ht q E (2 * j) j) hk = 0 := by
  unfold ccup; rw [map_zero, cast_zero]

section
variable [NeZero q]

theorem pull_ccup (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') {i j k : ℕ} (a : Ht q E' (2 * i) i)
    (b : Ht q E' (2 * j) j) (hk : i + j = k) : pull _ f _ _ (ccup a b hk) = ccup (pull _ f _ _ a) (pull _ f _ _ b) hk := by
  subst hk; unfold ccup; rw [pull_cast, (hA q).1]

theorem pull_cpow (hA : DivisorNaturality) {E E' : Spc} (f : E ⟶ E') (hE' : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (hA q).2.1 f hE']
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (hA q).1, ih]

def yExpr {E E' : Spc} (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    Ht q E' (2 * a) a :=
  ∑ j : Fin (a + 1), ccup (pull _ g _ _ (c j)) (cpow q (c1 q L) (a - j)) (by have := j.isLt; omega)

theorem ι_yExpr (P : Collected q) {E E' : Spc} (hE : Inv q E) (hE' : Inv q E') (g : E' ⟶ E) (L : E' ⟶ ofCat (glCat 1))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    P.ι hE' a (yExpr g L c a) = ∑ j ∈ Finset.range (a + 1), P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j) := by
  unfold yExpr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun j => P.map g hE' hE (P.ι hE j (c j)) * P.deg1 hE' (c1 q L) ^ (a - j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ι_ccup, P.map_ι, P.ι_cpow]

theorem pull_yExpr (hA : DivisorNaturality) {E E' E'' : Spc} (f : E'' ⟶ E') (hE' : Inv q E') (g : E' ⟶ E)
    (L : E' ⟶ ofCat (glCat 1)) (c : ∀ j : ℕ, Ht q E (2 * j) j) (a : ℕ) :
    pull _ f _ _ (yExpr g L c a) = yExpr (f ≫ g) (f ≫ L) c a := by
  unfold yExpr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_ccup hA, pull_cpow hA f hE', (hA q).2.2.1 f L hE', pull_comp]

theorem yExpr_eq_zero (P : Collected q) {E : Spc} (h : Inv q E) {a : ℕ} (V : E ⟶ ofCat (glCat a))
    (c : ∀ j : ℕ, Ht q E (2 * j) j) (hc : IsChern P h V c) : yExpr (PB.pr V) (PB.line V) c a = 0 := by
  have := ι_yExpr P h (inv_of (PB.pr V) h) (PB.pr V) (PB.line V) c a
  rw [hc.2.2] at this
  rw [← P.π_ι (inv_of (PB.pr V) h) a (yExpr (PB.pr V) (PB.line V) c a), this, map_zero]

end

def eExpr {E : Spc} (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) : Ht q E (2 * k) k :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).attach,
    ccup (c p.1.1) (d p.1.2) (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2)

theorem ι_eExpr (P : Collected q) {E : Spc} (h : Inv q E) (c d : ∀ j : ℕ, Ht q E (2 * j) j) (k : ℕ) :
    P.ι h k (eExpr c d k) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2) := by
  unfold eExpr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal k)
    (fun p => P.ι h p.1 (c p.1) * P.ι h p.2 (d p.2))]
  exact Finset.sum_congr rfl fun p _ => ι_ccup P h _ _ _

end LateralTheory.E.D2.WhitneyPf

namespace LateralTheory.E.D2
open WhitneyPf

theorem LeafWhitney_of (hG : LeafGeom) (hC2 : LeafCover2) (hS : LeafA6supp) (hA : LeafA6nat) : LeafWhitney := by
  intro q _ P E h a b V W c d hc hd
  classical
  have he := ι_eExpr P h c d
  refine ⟨eExpr c d, ⟨?_, ?_, ?_⟩, he⟩
  · rw [he]; simp [hc.1, hd.1]
  · intro j hj
    unfold eExpr
    refine Finset.sum_eq_zero fun p _ => ?_
    have hp := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
    by_cases ha : a < p.1.1
    · rw [hc.2.1 _ ha, ccup_zero_left]
    · rw [hd.2.1 _ (by omega), ccup_zero_right]
  · have hX := inv_of (PB.pr (bsumOf V W)) h
    obtain ⟨U₁, U₂, f₁, f₂, p₁, p₂, m₁, m₂, lc, e1, e2, e3, e4⟩ := hG V W
    have hcov := hC2 (ZMod q) f₁ f₂ m₁ m₂ lc
    have hy : pull _ f₁ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a) = 0 := by
      rw [pull_yExpr hA f₁ hX, ← e1, ← e2, ← pull_yExpr hA p₁ (inv_of (PB.pr V) h), yExpr_eq_zero P h V c hc,
        map_zero]
    have hz : pull _ f₂ _ _ (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) = 0 := by
      rw [pull_yExpr hA f₂ hX, ← e3, ← e4, ← pull_yExpr hA p₂ (inv_of (PB.pr W) h), yExpr_eq_zero P h W d hd,
        map_zero]
    have h0 := hS q f₁ f₂ hcov _ _ hy hz
    have key : P.ι hX (a + b) (ccup (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) c a)
        (yExpr (PB.pr (bsumOf V W)) (PB.line (bsumOf V W)) d b) rfl) = 0 := by
      unfold ccup; rw [h0, cast_zero, map_zero]
    rw [ι_ccup, ι_yExpr P h hX, ι_yExpr P h hX,
      ← alg (fun i => P.map (PB.pr (bsumOf V W)) hX h (P.ι h i (c i)))
        (fun j => P.map (PB.pr (bsumOf V W)) hX h (P.ι h j (d j))) _ a b
        (fun i hi => by simp only [hc.2.1 i hi, map_zero])
        (fun j hj => by simp only [hd.2.1 j hj, map_zero])] at key
    refine Eq.trans ?_ key
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
    simp only [map_mul]

end LateralTheory.E.D2
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSSCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSSCut

def incl0 {R : Type} [CommRing R] (K : Cx R) [K.IsStrictlyLE 0] :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (K.X 0) ⟶ K :=
  HomologicalComplex.mkHomFromSingle (𝟙 _) (fun k _ =>
    (CochainComplex.isZero_of_isStrictlyLE K 0 k (by
      have : (0 : ℤ) + 1 = k := by assumption
      omega)).eq_of_tgt _ _)

instance chains_isStrictlyLE {R : Type} [CommRing R] (E : Spc) : CochainComplex.IsStrictlyLE ((chains R).obj E) 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

def LeafFilt : Prop := E4.Hyps → ∀ (R : Type) [CommRing R] (K : Cx R) [K.IsStrictlyLE 0] (F : Shv R) (n : ℤ),
  (∀ r : ℕ, 0 < r → (r : ℤ) ≤ n →
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (K.X (-(r : ℤ)))) F (n - r))) →
  Finite (HK.pull R (incl0 K) F n).ker

def LeafCompare : Prop := E4.Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℤ),
  Eqv R (cechAug f) F → Finite (HK.pull R (incl0 ((chains R).obj (cech f))) F n).ker →
  Finite (pull R (sch.map f) F n).ker

def LeafTerms : Prop := E4.Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f]
  (r : ℕ) (m : ℤ), (∀ (Z : Scheme.{0}) (g : Z ⟶ X), IsProper g → Finite (H R (sch.obj Z) F m)) →
  Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (((chains R).obj (cech f)).X (-(r : ℤ)))) F m)

theorem goal_of (h1 : LeafFilt) (h2 : LeafCompare) (h3 : LeafTerms) : E4.LeafSS := by
  intro hy R _ F Y X f _ n hE hfin
  refine h2 hy R F f n hE ?_
  refine h1 hy R ((chains R).obj (cech f)) F n ?_
  intro r hr hrn
  exact h3 hy R F f r (n - r) (fun Z g hg => hfin Z g hg (n - r) (by omega))

end LateralTheory.E.LeafSSCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AICSHPf
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.AICSHPf

theorem root_near {T : Type} [CommRing T] [IsDomain T] (hA : ∀ p : Polynomial T, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0)
    (P : Ideal T) [P.IsPrime] (a₀ : T) :
    ∀ (n : ℕ) (f : T[X]), f.natDegree = n → f.Monic → f.eval a₀ ∈ P → ∃ a, f.IsRoot a ∧ a - a₀ ∈ P := by
  intro n
  induction n with
  | zero =>
    intro f hd hm hv
    have : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst this
    simp only [eval_one] at hv
    exact absurd ((Ideal.eq_top_iff_one P).2 hv) (Ideal.IsPrime.ne_top inferInstance)
  | succ n ih =>
    intro f hd hm hv
    obtain ⟨r, hr⟩ := hA f hm (by omega)
    have hroot : f.IsRoot r := hr
    set q := f /ₘ (X - C r) with hq
    have hfac : (X - C r) * q = f := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) (by rw [hfac]; exact hm)
    have hdeg : q.natDegree = n := by
      have := (monic_X_sub_C r).natDegree_mul hqm
      rw [hfac, natDegree_X_sub_C] at this; omega
    have hv' : (a₀ - r) * q.eval a₀ ∈ P := by
      rw [← hfac] at hv; simpa [eval_mul] using hv
    rcases (inferInstance : P.IsPrime).mem_or_mem hv' with h | h
    · refine ⟨r, hroot, ?_⟩
      have := P.neg_mem_iff.2 h; simpa using this
    · obtain ⟨a, ha, ha'⟩ := ih q hdeg hqm h
      refine ⟨a, ?_, ha'⟩
      rw [← hfac]; simp [IsRoot, eval_mul, ha.eq_zero]

theorem henselian {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) : HenselianLocalRing T where
  is_henselian f hf a₀ h₀ _ := root_near hA (IsLocalRing.maximalIdeal T) a₀ _ f rfl hf h₀

theorem algClosed {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) :
    IsAlgClosed (IsLocalRing.ResidueField T) := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hirr
  obtain ⟨P, hPl, hPd, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.2 fun n => IsLocalRing.residue_surjective _) hpm
  have hpos : 0 < P.natDegree := by
    rw [Polynomial.natDegree_eq_of_degree_eq hPd]; exact Irreducible.natDegree_pos hirr
  obtain ⟨a, ha⟩ := hA P hPm hpos
  refine ⟨IsLocalRing.residue T a, ?_⟩
  rw [← hPl, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]

end LateralTheory.E.AICSHPf

namespace LateralTheory.E.t_E3Cut

theorem AICSH_of : AICSH := by
  intro T _ _ _ hA
  let _ := LateralTheory.E.AICSHPf.henselian hA
  have := LateralTheory.E.AICSHPf.algClosed hA
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.E.t_E3Cut
end
end
