module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsSncDataW
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsB

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.WCharts
section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsD
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

def fracR {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i k : Fin m) : FinalTheorems.reesChart g i :=
  ⟨IsLocalization.mk' (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)), Algebra.subset_adjoin ⟨k, rfl⟩⟩

theorem fracR_self {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i : Fin m) : fracR g i i = 1 := by
  apply Subtype.ext
  exact IsLocalization.mk'_self' (Localization.Away (g i))

theorem algebraMap_reesChart_eq {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i k : Fin m) :
    algebraMap R (FinalTheorems.reesChart g i) (g k) = fracR g i k * algebraMap R (FinalTheorems.reesChart g i) (g i) := by
  apply Subtype.ext
  exact (IsLocalization.mk'_spec (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i))).symm

theorem algebraMap_reesChart_mem_nonZeroDivisors {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R)
    (i : Fin m) : algebraMap R (FinalTheorems.reesChart g i) (g i) ∈ nonZeroDivisors (FinalTheorems.reesChart g i) := by
  have hu : IsUnit (algebraMap R (Localization.Away (g i)) (g i)) :=
    IsLocalization.Away.algebraMap_isUnit (g i)
  have key : ∀ x : FinalTheorems.reesChart g i, x * algebraMap R _ (g i) = 0 → x = 0 := by
    intro x hx
    have h1 : (x : Localization.Away (g i)) * algebraMap R _ (g i) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (hu.mul_left_eq_zero.mp h1)
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => key x (by rwa [mul_comm] at hx), key⟩

theorem specMap_constSec {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) (U : S.affineOpens) :
    Spec.map (CommRingCat.ofHom (constSec s U.1)) = U.2.fromSpec ≫ s := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Spec (.of ℂ))) U.2 le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  rfl

theorem adjoin_reesChart_eq_top {R : Type} [CommRing R] (c : ℂ →+* R) {σ : Type} (z : σ → R)
    (hz : ∀ r : R, ∃ f : MvPolynomial σ ℂ, r = eval₂ c z f) {m : ℕ} (g : Fin m → R) (i : Fin m)
    {n : ℕ} (y : Fin n → FinalTheorems.reesChart g i)
    (hyz : ∀ q, ∃ l, y l = algebraMap R _ (z q)) (hyt : ∀ k, ∃ l, y l = fracR g i k) :
    @Algebra.adjoin ℂ (FinalTheorems.reesChart g i) _ _ ((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra
      (Set.range y) = ⊤ := by
  let _ : Algebra ℂ (FinalTheorems.reesChart g i) := ((algebraMap R (FinalTheorems.reesChart g i)).comp c).toAlgebra
  have hR : ∀ r : R, algebraMap R (FinalTheorems.reesChart g i) r ∈ Algebra.adjoin ℂ (Set.range y) := by
    intro r
    obtain ⟨f, rfl⟩ := hz r
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [eval₂_C]
      exact Subalgebra.algebraMap_mem _ a
    | add f h hf hh => rw [eval₂_add, map_add (f := _)]; exact add_mem hf hh
    | mul_X f q hf =>
      rw [eval₂_mul, eval₂_X, map_mul]
      obtain ⟨l, hl⟩ := hyz q
      refine mul_mem hf ?_
      rw [← hl]
      exact Algebra.subset_adjoin ⟨l, rfl⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨l, hl⟩ := hyt k
    have h2 : y l ∈ Algebra.adjoin ℂ (Set.range y) := Algebra.subset_adjoin ⟨l, rfl⟩
    rw [hl] at h2
    exact h2
  | algebraMap r => exact hR r
  | add x y hx hy ihx ihy => exact add_mem ihx ihy
  | mul x y hx hy ihx ihy => exact mul_mem ihx ihy

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_eval₂_chartCoord {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (r : Γ(projX P hP, (chartOpen hP p).1)) :
    ∃ f : MvPolynomial (Σ k, ι k) ℂ, r = eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f := by
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (gammaChart hP p r)
  refine ⟨f, ?_⟩
  rw [← gammaChart_symm_mk, hf, RingEquiv.symm_apply_apply]

def yC {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) {m : ℕ}
    (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) :
    Fin (Fintype.card (Σ k, ι k) + m) → FinalTheorems.reesChart g i :=
  fun l => Sum.elim (fun a => algebraMap _ (FinalTheorems.reesChart g i)
    (chartCoord hP p ((Fintype.equivFin _).symm a))) (fracR g i) (finSumFinEquiv.symm l)

theorem yC_yq {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) (q : Σ k, ι k) :
    yC hP p g i (finSumFinEquiv (Sum.inl (Fintype.equivFin _ q))) =
      algebraMap _ (FinalTheorems.reesChart g i) (chartCoord hP p q) := by
  simp [yC]

theorem yC_yt {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) (k : Fin m) :
    yC hP p g i (finSumFinEquiv (Sum.inr k)) = fracR g i k := by
  simp [yC]

theorem adjoin_yC {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) :
    @Algebra.adjoin ℂ (FinalTheorems.reesChart g i) _ _
      ((algebraMap _ (FinalTheorems.reesChart g i)).comp (constSec (toSpecC hP) (chartOpen hP p).1)).toAlgebra
      (Set.range (yC hP p g i)) = ⊤ :=
  adjoin_reesChart_eq_top _ (chartCoord hP p) (exists_eval₂_chartCoord hP p) g i (yC hP p g i)
    (fun q => ⟨_, yC_yq hP p g i q⟩) (fun k => ⟨_, yC_yt hP p g i k⟩)

end

end ReciprocityTheory.AnForm.R
end

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem affPres_of_iso {W : Scheme.{0}} (s : W ⟶ Spec (.of ℂ)) (V : W.Opens) (A : Type) [CommRing A]
    [Algebra ℂ A] (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = V.ι ≫ s) (n : ℕ) (y : Fin n → A)
    (hy : Algebra.adjoin ℂ (Set.range y) = ⊤) :
    ∃ (I : Ideal (MvPolynomial (Fin n) ℂ)) (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ I)))
      (hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I))) = V.ι ≫ s),
      ∀ l : Fin n, (AffPres.mk V n I iso hiso : AffPres s).secHom (X l) =
        V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (y l))) := by
  have hs : Function.Surjective (aeval y : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) := by
    rw [← AlgHom.range_eq_top, aeval_range, hy]
  let ψ := Ideal.quotientKerAlgEquivOfSurjective hs
  let iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker (aeval y : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A))) :=
    e ≪≫ asIso (Spec.map (RingEquiv.toCommRingCatIso ψ.toRingEquiv).hom)
  have hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸
      RingHom.ker (aeval y : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)))) = V.ι ≫ s := by
    rw [← he]
    simp only [iso, Iso.trans_hom, Category.assoc]
    congr 1
    simp only [asIso_hom]
    rw [← Spec.map_comp]
    congr 2
    ext c
    simp [ψ]
  refine ⟨_, iso, hiso, fun l => ?_⟩
  have key : (Spec.map (RingEquiv.toCommRingCatIso ψ.toRingEquiv).hom).appTop
      ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ (X l))) = (Scheme.ΓSpecIso (.of A)).inv (y l) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    congr 1
    show ψ (Ideal.Quotient.mk _ (X l)) = y l
    simp [ψ, Ideal.quotientKerAlgEquivOfSurjective_mk]
  simp only [AffPres.secHom, RingHom.comp_apply, iso, Iso.trans_hom, asIso_hom, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  exact congrArg _ (congrArg _ key)

theorem inter_reesCharts {X W : Scheme.{0}} (π : W ⟶ X) (J : X.IdealSheafData) (hB : FinalTheorems.Blowup π J)
    (U : X.affineOpens) {m : ℕ} (g : Fin m → Γ(X, U.1)) (hg : Ideal.span (Set.range g) = J.ideal U)
    (V : Fin m → W.Opens) (hV : ∀ i, V i ≤ π ⁻¹ᵁ U.1)
    (e : ∀ i, (V i).toScheme ≅ Spec (CommRingCat.of (FinalTheorems.reesChart g i)))
    (he : ∀ i, (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (FinalTheorems.reesChart g i))) ≫
      U.2.fromSpec = (V i).ι ≫ π)
    (i j : Fin m) (t : Γ(W, V i))
    (ht : t = (V i).topIso.hom ((e i).hom.appTop ((Scheme.ΓSpecIso _).inv
      ⟨IsLocalization.mk' (Localization.Away (g i)) (g j) (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)),
        Algebra.subset_adjoin ⟨j, rfl⟩⟩))) :
    V i ⊓ V j = W.basicOpen t :=
  inter_reesCharts' π J hB U g hg V hV e he i j t ht

theorem chart_aff {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {W : Scheme.{0}} (π : W ⟶ projX P hP) {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1))
    (i : Fin m) (V : W.Opens) (e : V.toScheme ≅ Spec (.of (FinalTheorems.reesChart g i)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(projX P hP, (chartOpen hP p).1)
      (FinalTheorems.reesChart g i))) ≫ (chartOpen hP p).2.fromSpec = V.ι ≫ π) :
    ∃ (I : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ))
      (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ ⧸ I)))
      (hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ ⧸ I))) = V.ι ≫ (π ≫ toSpecC hP)),
      ∀ l, (AffPres.mk V _ I iso hiso : AffPres (π ≫ toSpecC hP)).secHom (X l) =
        V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso _).inv (yC hP p g i l))) := by
  let _ : Algebra ℂ (FinalTheorems.reesChart g i) := ((algebraMap _ (FinalTheorems.reesChart g i)).comp
    (constSec (toSpecC hP) (chartOpen hP p).1)).toAlgebra
  have h1 : CommRingCat.ofHom (algebraMap ℂ (FinalTheorems.reesChart g i)) =
      CommRingCat.ofHom (constSec (toSpecC hP) (chartOpen hP p).1) ≫
        CommRingCat.ofHom (algebraMap _ (FinalTheorems.reesChart g i)) := rfl
  have heC : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (FinalTheorems.reesChart g i))) =
      V.ι ≫ (π ≫ toSpecC hP) := by
    calc e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (FinalTheorems.reesChart g i)))
        = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(projX P hP, (chartOpen hP p).1)
            (FinalTheorems.reesChart g i))) ≫ (chartOpen hP p).2.fromSpec ≫ toSpecC hP := by
          rw [h1, Spec.map_comp, specMap_constSec]
      _ = (V.ι ≫ π) ≫ toSpecC hP := by rw [← he]; simp only [Category.assoc]
      _ = V.ι ≫ (π ≫ toSpecC hP) := Category.assoc _ _ _
  exact affPres_of_iso (π ≫ toSpecC hP) V (FinalTheorems.reesChart g i) e heC _ (yC hP p g i) (adjoin_yC hP p g i)

theorem cocycle_of_nonZeroDivisor {Ri Rj O : Type*} [CommRing Ri] [CommRing Rj] [CommRing O]
    (ri : Ri →+* O) (rj : Rj →+* O) {Gi Gj Gk tij tik : Ri} {Gj' Gk' tjk : Rj} {Oj Ok : O}
    (h1 : Gj = tij * Gi) (h2 : Gk = tik * Gi) (h3 : Gk' = tjk * Gj')
    (e1 : ri Gj = Oj) (e2 : rj Gj' = Oj) (e3 : ri Gk = Ok) (e4 : rj Gk' = Ok)
    (hG : ri Gi ∈ nonZeroDivisors O) : rj tjk * ri tij = ri tik := by
  have h5 : rj tjk * (ri tij * ri Gi) = ri tik * ri Gi := by
    rw [← map_mul, ← h1, e1, ← e2, ← map_mul, ← h3, e4, ← e3, h2, map_mul]
  have key : (rj tjk * ri tij - ri tik) * ri Gi = 0 := by
    rw [sub_mul, mul_assoc, h5, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hG).2 _ key)

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_wData_of_logRes (hQ : FinalTheorems.FinTypeQE)
    {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D)
    (hrad : P.IsRadical)
    (hsing : ∀ (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval y h = 0) →
      ¬ IsRegularLocalRing (chartLocRing P p y) → ∀ f ∈ D, eval y f = 0)
    (hmin : ∀ q ∈ P.minimalPrimes, IsRelevant q → ¬ D ≤ q)
    (hL : FinalTheorems.LogResStC (projX P hP) (projB P D hP)) :
    Nonempty (WData P D hP) := by
  obtain ⟨J, W, π, h1, h2, h3, h4, -, ⟨U0, hU0, hiso0⟩, -, h8, h9⟩ := hL
  choose m g hg V hV e he using fun p => h9 (chartOpen hP p)
  choose I iso hiso hsec using fun p i => chart_aff hP p π (g p) i (V p i) (e p i) (he p i)
  have hle : ∀ p i, V p i ≤ π ⁻¹ᵁ (chartOpen hP p).1 := fun p i => (le_iSup (V p) i).trans (hV p).le
  let secH : ∀ p i, FinalTheorems.reesChart (g p) i →+* Γ(W, V p i) := fun p i =>
    ((V p i).topIso.hom.hom).comp (((e p i).hom.appTop).hom.comp
      (Scheme.ΓSpecIso (.of (FinalTheorems.reesChart (g p) i))).inv.hom)
  have hsa : ∀ p i r, secH p i (algebraMap _ (FinalTheorems.reesChart (g p) i) r) =
      π.appLE _ (V p i) (hle p i) r := fun p i r =>
    sec_algebraMap_of_iso π (chartOpen hP p) (V p i) (hle p i) _ (e p i) (he p i) r
  have hnz : ∀ p i, π.appLE _ (V p i) (hle p i) (g p i) ∈ nonZeroDivisors Γ(W, V p i) := fun p i =>
    (hsa p i (g p i)) ▸ sec_mem_nonZeroDivisors _ _ (algebraMap_reesChart_mem_nonZeroDivisors _ _)
  have hgeq : ∀ p i k, π.appLE _ (V p i) (hle p i) (g p k) =
      (V p i).topIso.hom ((e p i).hom.appTop ((Scheme.ΓSpecIso _).inv (fracR (g p) i k))) *
        π.appLE _ (V p i) (hle p i) (g p i) := by
    intro p i k
    calc π.appLE _ (V p i) (hle p i) (g p k)
        = secH p i (algebraMap _ (FinalTheorems.reesChart (g p) i) (g p k)) := (hsa p i (g p k)).symm
      _ = secH p i (fracR (g p) i k * algebraMap _ (FinalTheorems.reesChart (g p) i) (g p i)) :=
          congrArg (secH p i) (algebraMap_reesChart_eq (g p) i k)
      _ = secH p i (fracR (g p) i k) * secH p i (algebraMap _ (FinalTheorems.reesChart (g p) i) (g p i)) :=
          map_mul (secH p i) _ _
      _ = secH p i (fracR (g p) i k) * π.appLE _ (V p i) (hle p i) (g p i) :=
          congrArg (secH p i (fracR (g p) i k) * ·) (hsa p i (g p i))
  have hinter : ∀ p i j, V p i ⊓ V p j = W.basicOpen ((V p i).topIso.hom ((e p i).hom.appTop
      ((Scheme.ΓSpecIso _).inv (fracR (g p) i j)))) := fun p i j =>
    inter_reesCharts π J h2 (chartOpen hP p) (g p) (hg p) (V p) (hle p) (e p) (he p) i j _ rfl
  have eq1 : ∀ p {O Q : W.Opens} (hQ : Q ≤ π ⁻¹ᵁ (chartOpen hP p).1) (h : O ≤ Q) r,
      W.presheaf.map (homOfLE h).op (π.appLE _ Q hQ r) = π.appLE _ O (h.trans hQ) r := by
    intro p O Q hQ h r
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  refine ⟨{
    W := W, π := π, lft := ?_, J := J, blowup := h2, support_le := h1, regular := h3, snc := h4,
    isIso_off := ?_, m := m, g := g, span_g := hg,
    pres := fun p i => AffPres.mk (V p i) _ (I p i) (iso p i) (hiso p i),
    le_pres := hle, iSup_pres := hV,
    t := fun p i k => (V p i).topIso.hom ((e p i).hom.appTop ((Scheme.ΓSpecIso _).inv (fracR (g p) i k))),
    t_self := ?_, g_eq := hgeq, inter := hinter, t_cocycle := ?_,
    yq := fun p i q => finSumFinEquiv (Sum.inl (Fintype.equivFin _ q)),
    yt := fun p i k => finSumFinEquiv (Sum.inr k),
    sec_yq := ?_, sec_yt := ?_, gen := ?_ }⟩
  · have := h8
    infer_instance
  · have := hiso0
    refine isIso_morphismRestrict_of_le (U := U0) π ?_
    intro x hx
    have hx' : x ∉ (projB P D hP : Set (projX P hP)) := hx
    have hreg : IsRegularLocalRing ((projX P hP).presheaf.stalk x) := by
      by_contra hn
      exact hx' (sing_subset_projB hP hD hQ hsing hn)
    show x ∈ (U0 : Set (projX P hP))
    rw [hU0]
    exact sncAt_of_not_mem (projB P D hP) x hx' hreg
  · intro p i
    dsimp only
    simp only [fracR_self, map_one]
  · intro p i j k
    dsimp only
    have hG := res_mem_nonZeroDivisors (inf_le_left : V p i ⊓ V p j ≤ V p i)
      (isAffineOpen_of_iso _ (e p i)) (hnz p i)
    exact cocycle_of_nonZeroDivisor
      (W.presheaf.map (homOfLE (inf_le_left : V p i ⊓ V p j ≤ V p i)).op).hom
      (W.presheaf.map (homOfLE (inf_le_right : V p i ⊓ V p j ≤ V p j)).op).hom
      (hgeq p i j) (hgeq p i k) (hgeq p j k)
      (eq1 p (hle p i) (inf_le_left : V p i ⊓ V p j ≤ V p i) (g p j))
      (eq1 p (hle p j) (inf_le_right : V p i ⊓ V p j ≤ V p j) (g p j))
      (eq1 p (hle p i) (inf_le_left : V p i ⊓ V p j ≤ V p i) (g p k))
      (eq1 p (hle p j) (inf_le_right : V p i ⊓ V p j ≤ V p j) (g p k)) hG
  · intro p i q
    dsimp only
    exact (hsec p i _).trans ((congrArg (fun a => (V p i).topIso.hom ((e p i).hom.appTop
      ((Scheme.ΓSpecIso (.of (FinalTheorems.reesChart (g p) i))).inv a))) (yC_yq hP p (g p) i q)).trans
        (hsa p i _))
  · intro p i k
    dsimp only
    exact (hsec p i _).trans (congrArg (fun a => (V p i).topIso.hom ((e p i).hom.appTop
      ((Scheme.ΓSpecIso (.of (FinalTheorems.reesChart (g p) i))).inv a))) (yC_yt hP p (g p) i k))
  · intro p i l
    dsimp only
    refine ⟨X l, ?_, by rw [sub_self]; exact zero_mem _⟩
    rw [vars_X]
    intro a ha
    rw [Finset.mem_singleton] at ha
    rw [ha]
    rcases h : finSumFinEquiv.symm l with q | k
    · apply Finset.mem_union_left
      rw [Finset.mem_image]
      refine ⟨(Fintype.equivFin _).symm q, Finset.mem_univ _, ?_⟩
      simp only [Equiv.apply_symm_apply, ← h]
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨k, Finset.mem_univ _, ?_⟩
      simp only [← h, Equiv.apply_symm_apply]

end

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.WeightedSieveThreeParameter
section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.ContinuousOnOfCharts
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem sep_of_continuousOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {U : Set X} (hU : IsOpen U) {f : X → Y} (hf : ContinuousOn f U) {x y : X} (hx : x ∈ U)
    (hy : y ∈ U) (hne : f x ≠ f y) :
    ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v := by
  obtain ⟨a, b, ha, hb, hxa, hyb, hab⟩ := t2_separation hne
  refine ⟨U ∩ f ⁻¹' a, U ∩ f ⁻¹' b, hf.isOpen_inter_preimage hU ha, hf.isOpen_inter_preimage hU hb,
    ⟨hx, hxa⟩, ⟨hy, hyb⟩, ?_⟩
  exact Set.disjoint_left.mpr fun z hz hz' => Set.disjoint_left.mp hab hz.2 hz'.2

def blkNorm (z : (Σ k, ι k) → ℂ) (q : Σ k, ι k) : ℝ :=
  Complex.normSq (z q) / ∑ j : ι q.1, Complex.normSq (z ⟨q.1, j⟩)

theorem blkNorm_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (q : Σ k, ι k) :
    blkNorm z q = blkNorm z' q := by
  obtain ⟨a, ha, rfl⟩ := h
  have hq : Complex.normSq (a q.1) ≠ 0 := by simpa using ha q.1
  simp only [blkNorm, map_mul]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hq]

theorem blkNorm_ne_zero_iff (z : (Σ k, ι k) → ℂ) (q : Σ k, ι k) : blkNorm z q ≠ 0 ↔ z q ≠ 0 := by
  constructor
  · intro h hz
    apply h
    simp [blkNorm, hz]
  · intro hz
    have h1 : 0 < Complex.normSq (z q) := Complex.normSq_pos.mpr hz
    have h2 : Complex.normSq (z q) ≤ ∑ j : ι q.1, Complex.normSq (z ⟨q.1, j⟩) :=
      Finset.single_le_sum (f := fun j => Complex.normSq (z ⟨q.1, j⟩))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ q.2)
    exact (div_pos h1 (h1.trans_le h2)).ne'

def vecNorm {m : ℕ} (v : Fin m → ℂ) (l : Fin m) : ℝ :=
  Complex.normSq (v l) / ∑ k, Complex.normSq (v k)

theorem vecNorm_smul {m : ℕ} {v v' : Fin m → ℂ} (a : ℂ) (ha : a ≠ 0) (h : ∀ k, v k = a * v' k)
    (l : Fin m) : vecNorm v l = vecNorm v' l := by
  have hq : Complex.normSq a ≠ 0 := by simpa using ha
  simp only [vecNorm, h, map_mul]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hq]

theorem vecNorm_ne_zero_iff {m : ℕ} (v : Fin m → ℂ) (l : Fin m) : vecNorm v l ≠ 0 ↔ v l ≠ 0 := by
  constructor
  · intro h hz
    apply h
    simp [vecNorm, hz]
  · intro hz
    have h1 : 0 < Complex.normSq (v l) := Complex.normSq_pos.mpr hz
    have h2 : Complex.normSq (v l) ≤ ∑ k, Complex.normSq (v k) :=
      Finset.single_le_sum (f := fun k => Complex.normSq (v k))
        (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ l)
    exact (div_pos h1 (h1.trans_le h2)).ne'

namespace WData

attribute [local instance] WData.lft

variable (w : WData P D hP)

theorem coord_eq_of_mem (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    w.coord c x = (w.pres c.1 c.2).coord x.1 hx :=
  dif_pos hx

theorem continuousOn_coord (c : w.Idx) : ContinuousOn (w.coord c) (w.src c) := by
  rw [continuousOn_iff']
  intro O hO
  refine ⟨w.src c ∩ w.coord c ⁻¹' O, TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, O, hO, rfl⟩, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  tauto

theorem continuousOn_of_charts {Y : Type*} [TopologicalSpace Y] (U : Set w.M) (f : w.M → Y)
    (h : ∀ x ∈ U, ∃ c, x ∈ w.src c ∧ w.src c ⊆ U ∧ ∃ F : (Fin (w.pres c.1 c.2).n → ℂ) → Y,
      Continuous F ∧ ∀ y ∈ w.src c, f y = F (w.coord c y)) :
    ContinuousOn f U := by
  intro x hx
  obtain ⟨c, hxc, -, F, hF, hfF⟩ := h x hx
  have h1 : ContinuousOn (F ∘ w.coord c) (w.src c) := hF.comp_continuousOn (w.continuousOn_coord c)
  have h2 : ContinuousOn f (w.src c) := h1.congr fun y hy => hfF y hy
  exact (h2.continuousAt ((w.isOpen_alt_bis c).mem_nhds hxc)).continuousWithinAt

def lv (c : w.Idx) (x : w.M) : (Σ k, ι k) → ℂ := fun q => eval (w.coord c x) (w.lift c q)

theorem lv_self (c : w.Idx) (x : w.M) (k : K) : w.lv c x ⟨k, c.1 k⟩ = 1 := by
  simp [lv, lift]

theorem one_le_sum_lv (c : w.Idx) (x : w.M) (k : K) :
    1 ≤ ∑ j : ι k, Complex.normSq (w.lv c x ⟨k, j⟩) := by
  have h2 := Finset.single_le_sum (f := fun j => Complex.normSq (w.lv c x ⟨k, j⟩))
    (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ (c.1 k))
  simp only [lv_self, map_one] at h2
  exact h2

def ch (x : w.M) : w.Idx := (w.cover x).choose

theorem mem_ch (x : w.M) : x ∈ w.src (w.ch x) := (w.cover x).choose_spec

def blk (q : Σ k, ι k) (x : w.M) : ℝ := blkNorm (w.lv (w.ch x) x) q

theorem blk_eq (q : Σ k, ι k) (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    w.blk q x = blkNorm (w.lv c x) q :=
  blkNorm_of_sameOrbit (w.compat (w.ch x) c x ⟨w.mem_ch x, hx⟩) q

theorem continuous_blk (q : Σ k, ι k) : Continuous (w.blk q) := by
  rw [← continuousOn_univ]
  refine w.continuousOn_of_charts _ _ fun x _ => ⟨w.ch x, w.mem_ch x, Set.subset_univ _, ?_⟩
  set c := w.ch x
  refine ⟨fun v => Complex.normSq (eval v (w.lift c q)) /
    max 1 (∑ j : ι q.1, Complex.normSq (eval v (w.lift c ⟨q.1, j⟩))), ?_, ?_⟩
  · refine (Complex.continuous_normSq.comp (MvPolynomial.continuous_eval _)).div
      (continuous_const.max (continuous_finsetSum _ fun j _ =>
        Complex.continuous_normSq.comp (MvPolynomial.continuous_eval _))) fun v => ?_
    exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  · intro y hy
    show _ = Complex.normSq (w.lv c y q) / max 1 (∑ j : ι q.1, Complex.normSq (w.lv c y ⟨q.1, j⟩))
    rw [w.blk_eq q c y hy, blkNorm, max_eq_right (w.one_le_sum_lv c y q.1)]

def tv (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) : Fin (w.m p) → ℂ :=
  fun k => w.coord ⟨p, i⟩ x (w.yt p i k)

theorem tv_eq_val (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) (hx : x ∈ w.src ⟨p, i⟩)
    (k : Fin (w.m p)) : w.tv p i x k = val (w.π ≫ toSpecC hP) (w.t p i k) x.1 hx := by
  have h := (w.pres p i).eval_coord_eq_val x.1 hx x.2 (X (w.yt p i k))
  rw [eval_X, w.sec_yt] at h
  rw [tv, w.coord_eq_of_mem ⟨p, i⟩ x hx]
  exact h

theorem val_t_mul (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M) (hi : x ∈ w.src ⟨p, i⟩)
    (hj : x ∈ w.src ⟨p, j⟩) (k : Fin (w.m p)) :
    val (w.π ≫ toSpecC hP) (w.t p i k) x.1 hi =
      val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hj * val (w.π ≫ toSpecC hP) (w.t p i j) x.1 hi := by
  have hij : x.1 ∈ (w.pres p i).V ⊓ (w.pres p j).V := by
    rw [TopologicalSpace.Opens.mem_inf]
    exact ⟨hi, hj⟩
  obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) ((w.pres p i).V ⊓ (w.pres p j).V) x.1 hij x.2
  have h := congrArg φ (w.t_cocycle p i j k)
  rw [map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict] at h
  exact h.symm

theorem val_t_ne_zero_iff (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M)
    (hi : x ∈ w.src ⟨p, i⟩) :
    val (w.π ≫ toSpecC hP) (w.t p i j) x.1 hi ≠ 0 ↔ x ∈ w.src ⟨p, j⟩ := by
  have h1 := val_eq_zero_iff (w.π ≫ toSpecC hP) (w.t p i j) x.1 hi x.2
  have h2 := Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := w.W) x.1 hi (w.t p i j)
  have h3 : x.1 ∈ w.W.basicOpen (w.t p i j) ↔ x ∈ w.src ⟨p, j⟩ := by
    rw [← w.inter p i j, TopologicalSpace.Opens.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩
  exact (h1.not.trans h2).trans h3

theorem tv_self (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) (hx : x ∈ w.src ⟨p, i⟩) :
    w.tv p i x i = 1 := by
  obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) (w.pres p i).V x.1 hx x.2
  rw [w.tv_eq_val p i x hx, ← hφ, w.t_self, map_one]

theorem tv_ne_zero_iff (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M) (hi : x ∈ w.src ⟨p, i⟩) :
    w.tv p i x j ≠ 0 ↔ x ∈ w.src ⟨p, j⟩ := by
  rw [w.tv_eq_val p i x hi]
  exact w.val_t_ne_zero_iff p i j x hi

theorem tv_mul (p : (k : K) → ι k) (i j : Fin (w.m p)) (x : w.M) (hi : x ∈ w.src ⟨p, i⟩)
    (hj : x ∈ w.src ⟨p, j⟩) (k : Fin (w.m p)) : w.tv p i x k = w.tv p i x j * w.tv p j x k := by
  rw [w.tv_eq_val p i x hi, w.tv_eq_val p i x hi, w.tv_eq_val p j x hj, w.val_t_mul p i j x hi hj k,
    mul_comm]

theorem one_le_sum_tv (p : (k : K) → ι k) (i : Fin (w.m p)) (x : w.M) (hx : x ∈ w.src ⟨p, i⟩) :
    1 ≤ ∑ k, Complex.normSq (w.tv p i x k) := by
  have h2 := Finset.single_le_sum (f := fun k => Complex.normSq (w.tv p i x k))
    (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  simp only [w.tv_self p i x hx, map_one] at h2
  exact h2

def overP (p : (k : K) → ι k) : Set w.M := {x | ∃ i, x ∈ w.src ⟨p, i⟩}

theorem isOpen_overP (p : (k : K) → ι k) : IsOpen (w.overP p) := by
  have h : w.overP p = ⋃ i, w.src ⟨p, i⟩ := by
    ext x
    simp [overP]
  rw [h]
  exact isOpen_iUnion fun i => w.isOpen_alt_bis _


open Classical in
def fib (p : (k : K) → ι k) (l : Fin (w.m p)) (x : w.M) : ℝ :=
  if h : ∃ i, x ∈ w.src ⟨p, i⟩ then vecNorm (w.tv p h.choose x) l else 0

theorem fib_eq (p : (k : K) → ι k) (l : Fin (w.m p)) (i : Fin (w.m p)) (x : w.M)
    (hx : x ∈ w.src ⟨p, i⟩) : w.fib p l x = vecNorm (w.tv p i x) l := by
  have h : ∃ i, x ∈ w.src ⟨p, i⟩ := ⟨i, hx⟩
  rw [fib, dif_pos h]
  exact vecNorm_smul _ ((w.tv_ne_zero_iff p _ i x h.choose_spec).mpr hx)
    (fun k => w.tv_mul p _ i x h.choose_spec hx k) l

theorem continuousOn_fib (p : (k : K) → ι k) (l : Fin (w.m p)) :
    ContinuousOn (w.fib p l) (w.overP p) := by
  refine w.continuousOn_of_charts _ _ fun x hx => ?_
  obtain ⟨i, hi⟩ := hx
  refine ⟨⟨p, i⟩, hi, fun y hy => ⟨i, hy⟩, ?_⟩
  refine ⟨fun v => Complex.normSq (v (w.yt p i l)) /
    max 1 (∑ k, Complex.normSq (v (w.yt p i k))), ?_, ?_⟩
  · refine (Complex.continuous_normSq.comp (continuous_apply _)).div
      (continuous_const.max (continuous_finsetSum _ fun k _ =>
        Complex.continuous_normSq.comp (continuous_apply _))) fun v => ?_
    exact (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  · intro y hy
    show _ = Complex.normSq (w.tv p i y l) / max 1 (∑ k, Complex.normSq (w.tv p i y k))
    rw [w.fib_eq p l i y hy, vecNorm, max_eq_right (w.one_le_sum_tv p i y hy)]

end WData

end

end ReciprocityTheory.AnForm.R
end

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem WData.t2Space (w : WData P D hP) : T2Space w.M := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases hcom : ∃ d, x ∈ w.src d ∧ y ∈ w.src d
  · obtain ⟨d, hxd, hyd⟩ := hcom
    have hne : w.coord d x ≠ w.coord d y := by
      intro h
      have h' : (⟨x, hxd⟩ : w.src d) = ⟨y, hyd⟩ := (w.isEmbedding d).injective h
      exact hxy (congrArg Subtype.val h')
    exact sep_of_continuousOn (w.isOpen_alt_bis d) (w.continuousOn_coord d) hxd hyd hne
  push Not at hcom
  obtain ⟨c, hxc⟩ := w.cover x
  obtain ⟨c', hyc'⟩ := w.cover y
  by_cases hblk : ∃ q, w.blk q x ≠ w.blk q y
  · obtain ⟨q, hq⟩ := hblk
    exact sep_of_continuousOn isOpen_univ (w.continuous_blk q).continuousOn trivial trivial hq
  push Not at hblk
  have hy1 : ∀ k, eval (w.coord c' y) (w.lift c' ⟨k, c.1 k⟩) ≠ 0 := by
    intro k
    have h1 : w.blk ⟨k, c.1 k⟩ x ≠ 0 := by
      rw [w.blk_eq _ c x hxc, blkNorm_ne_zero_iff, w.lv_self]
      exact one_ne_zero
    rw [hblk, w.blk_eq _ c' y hyc', blkNorm_ne_zero_iff] at h1
    exact h1
  have hyp : w.π.base y.1 ∈ (chartOpen hP c.1).1 := (w.mem_chartOpen_iff c' y hyc' c.1).mpr hy1
  obtain ⟨j, hyj⟩ : ∃ j, y ∈ w.src ⟨c.1, j⟩ := by
    have h : y.1 ∈ w.π ⁻¹ᵁ (chartOpen hP c.1).1 := hyp
    rw [← w.iSup_pres] at h
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    exact ⟨j, hj⟩
  by_cases hfib : ∃ l, w.fib c.1 l x ≠ w.fib c.1 l y
  · obtain ⟨l, hl⟩ := hfib
    exact sep_of_continuousOn (w.isOpen_overP c.1) (w.continuousOn_fib c.1 l) ⟨c.2, hxc⟩
      ⟨j, hyj⟩ hl
  push Not at hfib
  have h1 : w.fib c.1 j y ≠ 0 := by
    rw [w.fib_eq c.1 j j y hyj, vecNorm_ne_zero_iff, w.tv_self c.1 j y hyj]
    exact one_ne_zero
  rw [← hfib j, w.fib_eq c.1 j c.2 x hxc, vecNorm_ne_zero_iff, w.tv_ne_zero_iff c.1 c.2 j x hxc] at h1
  exact (hcom _ h1 hyj).elim

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.NormEvalLeOfVarsSubset
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem norm_eval_le_of_vars_subset {n : ℕ} (F : MvPolynomial (Fin n) ℂ) (S : Finset (Fin n))
    (hS : F.vars ⊆ S) (y : Fin n → ℂ) (hy : ∀ i ∈ S, ‖y i‖ ≤ 1) :
    ‖eval y F‖ ≤ ∑ m ∈ F.support, ‖F.coeff m‖ := by
  rw [MvPolynomial.eval_eq']
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_mul]
  have h1 : ‖∏ i, y i ^ m i‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [norm_pow]
    by_cases h : m i = 0
    · simp [h]
    · refine pow_le_one₀ (norm_nonneg _) (hy i (hS ?_))
      rw [MvPolynomial.mem_vars_iff_mem_support]
      exact ⟨m, hm, Finsupp.mem_support_iff.mpr h⟩
  calc ‖F.coeff m‖ * ‖∏ i, y i ^ m i‖ ≤ ‖F.coeff m‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖F.coeff m‖ := mul_one _

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

def cptPiece (c : w.Idx) : Set w.M :=
  {x | x ∈ w.src c ∧ (∀ q, ‖w.coord c x (w.yq c.1 c.2 q)‖ ≤ 1) ∧
    ∀ k, ‖w.coord c x (w.yt c.1 c.2 k)‖ ≤ 1}

theorem isCompact_cptPiece (c : w.Idx) : IsCompact (w.cptPiece c) := by
  let S : Finset (Fin (w.pres c.1 c.2).n) :=
    Finset.univ.image (w.yq c.1 c.2) ∪ Finset.univ.image (w.yt c.1 c.2)
  choose F hFv hFK using w.gen c.1 c.2
  let B : Set (Fin (w.pres c.1 c.2).n → ℂ) :=
    (⋂ h ∈ ((w.pres c.1 c.2).K : Set (MvPolynomial (Fin (w.pres c.1 c.2).n) ℂ)), {y | eval y h = 0}) ∩
      ((⋂ q, {y | ‖y (w.yq c.1 c.2 q)‖ ≤ 1}) ∩ ⋂ k, {y | ‖y (w.yt c.1 c.2 k)‖ ≤ 1})
  have hBc : IsClosed B :=
    (isClosed_biInter fun h _ => isClosed_eq (MvPolynomial.continuous_eval h) continuous_const).inter
      ((isClosed_iInter fun q =>
        isClosed_le (continuous_norm.comp (continuous_apply _)) continuous_const).inter
      (isClosed_iInter fun k =>
        isClosed_le (continuous_norm.comp (continuous_apply _)) continuous_const))
  have hmemB : ∀ y, y ∈ B ↔ (∀ h ∈ (w.pres c.1 c.2).K, eval y h = 0) ∧
      (∀ q, ‖y (w.yq c.1 c.2 q)‖ ≤ 1) ∧ ∀ k, ‖y (w.yt c.1 c.2 k)‖ ≤ 1 := by
    intro y
    simp only [B, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
  have hS : ∀ y ∈ B, ∀ i ∈ S, ‖y i‖ ≤ 1 := by
    intro y hy i hi
    rw [hmemB] at hy
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hy.2.1 a
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact hy.2.2 a
  have hBsub : B ⊆ Set.univ.pi fun l =>
      Metric.closedBall (0 : ℂ) (∑ m ∈ (F l).support, ‖(F l).coeff m‖) := by
    intro y hy
    have hy' := (hmemB y).mp hy
    refine Set.mem_univ_pi.mpr fun l => ?_
    rw [mem_closedBall_zero_iff]
    have h1 : y l = eval y (F l) := by
      have h2 := hy'.1 _ (hFK l)
      rw [map_sub, eval_X, sub_eq_zero] at h2
      exact h2
    rw [h1]
    exact norm_eval_le_of_vars_subset (F l) S (hFv l) y (hS y hy)
  have hBk : IsCompact B :=
    (isCompact_univ_pi fun l => isCompact_closedBall _ _).of_isClosed_subset hBc hBsub
  have hrange : B ⊆ Set.range (fun y : w.src c => w.coord c y) := by
    intro y hy
    have h3 : y ∈ w.coord c '' w.src c := by
      rw [w.image c]
      exact ((hmemB y).mp hy).1
    obtain ⟨x, hx, rfl⟩ := h3
    exact ⟨⟨x, hx⟩, rfl⟩
  have hpre := (w.isEmbedding c).isInducing.isCompact_preimage' hBk hrange
  have heq : w.cptPiece c = Subtype.val '' ((fun y : w.src c => w.coord c y) ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨hx, hq, ht⟩
      refine ⟨⟨x, hx⟩, (hmemB _).mpr ⟨?_, hq, ht⟩, rfl⟩
      have h4 : w.coord c x ∈ w.coord c '' w.src c := ⟨x, hx, rfl⟩
      rw [w.image c] at h4
      exact h4
    · rintro ⟨y, hy, rfl⟩
      have hy' := (hmemB _).mp hy
      exact ⟨y.2, hy'.2.1, hy'.2.2⟩
  rw [heq]
  exact hpre.image continuous_subtype_val

theorem exists_cptPiece (x : w.M) : ∃ c, x ∈ w.cptPiece c := by
  obtain ⟨c0, h0⟩ := w.cover x
  have hz := w.lift_mem c0 x h0
  obtain ⟨p, hpnz, hpmax⟩ := exists_chart (fun q => eval (w.coord c0 x) (w.lift c0 q)) hz.1
  have hπ : w.π.base x.1 ∈ (chartOpen hP p).1 := (w.mem_chartOpen_iff c0 x h0 p).mpr hpnz
  have hxp : x.1 ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hπ
  rw [← w.iSup_pres p] at hxp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxp
  have hcl : IsClosed ({x.1} : Set w.W) := x.2
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin (w.m p) → ℂ, ∀ k, τ k = val (w.π ≫ toSpecC hP) (w.t p i k) x.1 hi :=
    ⟨_, fun _ => rfl⟩
  have hτi : τ i = 1 := by
    obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) _ x.1 hi hcl
    rw [hτ, w.t_self, ← hφ, map_one]
  have : Nonempty (Fin (w.m p)) := ⟨i⟩
  obtain ⟨j, hj⟩ := Finite.exists_max fun k => ‖τ k‖
  have hτj1 : 1 ≤ ‖τ j‖ := by
    have h5 := hj i
    rwa [hτi, norm_one] at h5
  have hpos : 0 < ‖τ j‖ := lt_of_lt_of_le one_pos hτj1
  have hij : x.1 ∈ (w.pres p i).V ⊓ (w.pres p j).V := by
    rw [w.inter p i j]
    refine (w.W.evaluation_ne_zero_iff_mem_basicOpen x.1 hi (w.t p i j)).mp ?_
    rw [Ne, ← val_eq_zero_iff (w.π ≫ toSpecC hP) _ x.1 hi hcl, ← hτ]
    exact norm_pos_iff.mp hpos
  have hjV : x.1 ∈ (w.pres p j).V := hij.2
  have hcoc : ∀ k, val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV * τ j = τ k := by
    intro k
    obtain ⟨φ, hφ⟩ := val_ringHom (w.π ≫ toSpecC hP) _ x.1 hij hcl
    have h6 := congrArg φ (w.t_cocycle p i j k)
    rw [map_mul, hφ, hφ, hφ, val_restrict, val_restrict, val_restrict] at h6
    rw [hτ, hτ]
    exact h6
  refine ⟨⟨p, j⟩, hjV, fun q => ?_, fun k => ?_⟩
  · have e1 : w.coord ⟨p, j⟩ x (w.yq p j q) =
        val (w.π ≫ toSpecC hP) ((w.pres p j).secHom (X (w.yq p j q))) x.1 hjV := by
      rw [(w.pres p j).val_secHom x.1 hjV hcl, eval_X, w.coord_of_mem ⟨p, j⟩ x hjV]
    rw [e1, w.sec_yq,
      (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (w.le_pres p j) (chartCoord hP p q)
        x.1 hjV hcl).2]
    refine (congrArg (fun v => ‖v‖) (w.val_chartCoord c0 x h0 p _ q)).trans_le ?_
    simp only [affCoord, norm_div]
    exact div_le_one_of_le₀ (hpmax q.1 q.2) (norm_nonneg _)
  · have e1 : w.coord ⟨p, j⟩ x (w.yt p j k) = val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV := by
      rw [← w.sec_yt p j k, (w.pres p j).val_secHom x.1 hjV hcl, eval_X,
        w.coord_of_mem ⟨p, j⟩ x hjV]
    rw [e1]
    have h7 : ‖val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV‖ * ‖τ j‖ = ‖τ k‖ := by
      rw [← norm_mul, hcoc k]
    calc ‖val (w.π ≫ toSpecC hP) (w.t p j k) x.1 hjV‖ = ‖τ k‖ / ‖τ j‖ := by
          rw [← h7, mul_div_cancel_right₀ _ hpos.ne']
      _ ≤ 1 := div_le_one_of_le₀ (hj k) hpos.le

end WData

theorem WData.compactSpace (w : WData P D hP) : CompactSpace w.M := by
  refine isCompact_univ_iff.mp ?_
  have h : (Set.univ : Set w.M) = ⋃ c, w.cptPiece c := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact w.exists_cptPiece x
  rw [h]
  exact isCompact_iUnion fun c => w.isCompact_cptPiece c

end

end ReciprocityTheory.AnForm.R
end

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}


open Classical in
def WData.idxEquiv (w : WData P D hP) : w.Idx ≃ Fin (Fintype.card w.Idx) :=
  Fintype.equivFin w.Idx


open Classical in
def WData.toAlgRes (w : WData P D hP) {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e)
    (hD : IsMultiHomogIdeal D) (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q) :
    AlgRes ι P D e where
  M := w.M
  top := w.topology
  compact := w.compactSpace
  t2 := w.t2Space
  n := Fintype.card w.Idx
  amb i := (w.pres (w.idxEquiv.symm i).1 (w.idxEquiv.symm i).2).n
  ideal i := (w.pres (w.idxEquiv.symm i).1 (w.idxEquiv.symm i).2).K
  src i := w.src (w.idxEquiv.symm i)
  isOpen_alt_bis i := w.isOpen_alt_bis _
  cover x := by
    obtain ⟨c, hc⟩ := w.cover x
    exact ⟨w.idxEquiv c, by simpa using hc⟩
  coord i := w.coord (w.idxEquiv.symm i)
  isEmbedding i := w.isEmbedding _
  image i := w.image _
  trans i j := w.trans _ _
  regular i := w.regular_coord _
  dim i x hx := w.dim_coord he _ x hx
  lift i := w.lift (w.idxEquiv.symm i)
  lift_one i := w.lift_one _
  lift_mem i := w.lift_mem _
  compat i j := w.compat _ _
  surj z hz hzD := by
    obtain ⟨c, x, hx, h⟩ := w.surj hD z hz hzD
    obtain ⟨i, rfl⟩ := w.idxEquiv.symm.surjective c
    exact ⟨i, x, hx, h⟩
  inj i j := w.inj hD _ _
  inv i := w.inv hD _
  bd i := w.bd (w.idxEquiv.symm i)
  le_bd i := w.le_bd _
  zero_bd i := w.zero_bd hD _
  rc := w.rc
  comp := w.comp
  sncAt i := w.sncAt he _
  comp_eq i := w.comp_eq he _
  mult f a hf hfP hzero := by
    obtain ⟨m, hm⟩ := w.mult he hD hcomp f a hf hfP hzero
    exact ⟨m, fun i x hx => hm _ x hx⟩

theorem algRes_of_logResStC (hQ : FinalTheorems.FinTypeQE)
    (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (hP : IsMultiHomogIdeal P) (hrad : P.IsRadical) (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (hsing : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ¬ IsRegularLocalRing (locAt (chartIdeal P p) z) → ∀ f ∈ D, eval z f = 0)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (locAt (chartIdeal P p) z) = e)
    (hL : FinalTheorems.LogResStC (projX P hP) (projB P D hP)) :
    Nonempty (AlgRes ι P D e) := by
  obtain ⟨w⟩ := exists_wData_of_logRes hQ hP hD hrad hsing hcomp hL
  exact ⟨w.toAlgRes (w.ringKrullDim_stalk e hD hcomp hdim) hD hcomp⟩

end

end ReciprocityTheory.AnForm.R
