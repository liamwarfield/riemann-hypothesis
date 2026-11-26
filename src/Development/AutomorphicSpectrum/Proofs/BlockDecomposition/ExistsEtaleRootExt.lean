module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UZeroApplySelf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleRootExt
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open TensorProduct

namespace GlobalTheory.CompanionTheory.RootPerf

theorem pf_rootExt (p : ℕ) (hp : p.Prime) {k : Type} [CommRing k] (hk : D.Pf p k) {d : ℕ}
    (Y : RootExt p (MvPolynomial (Fin d) k) (MvPolynomial.X : Fin d → MvPolynomial (Fin d) k)) :
    D.Pf p Y.E := by
  classical
  obtain ⟨hchar, hbij⟩ := hk
  rcases subsingleton_or_nontrivial k with hsub | hnt
  · have h10 : (1 : MvPolynomial (Fin d) k) = 0 := by
      rw [← map_one (MvPolynomial.C (σ := Fin d) (R := k)), Subsingleton.elim (1 : k) 0, map_zero]
    have hE : Subsingleton Y.E := subsingleton_of_zero_eq_one (by
      have h := congrArg (algebraMap (MvPolynomial (Fin d) k) Y.E) h10
      rw [map_one, map_zero] at h
      exact h.symm)
    exact ⟨Subsingleton.elim _ _, ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨y, Subsingleton.elim _ _⟩⟩⟩
  · haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 hchar
    haveI : ExpChar k p := ExpChar.prime hp
    haveI : Nontrivial Y.E := nontrivial_of_ne 1 0 (by rw [← Y.b_a₀]; exact Y.b.ne_zero _)
    have hcE : ((p : ℕ) : Y.E) = 0 := by
      rw [← map_natCast (algebraMap (MvPolynomial (Fin d) k) Y.E),
        ← map_natCast (MvPolynomial.C (σ := Fin d) (R := k)), hchar, map_zero, map_zero]
    haveI : CharP Y.E p := (CharP.charP_iff_prime_eq_zero hp).2 hcE
    haveI : ExpChar Y.E p := ExpChar.prime hp
    have hfk : ⇑(frobenius k p) = fun x => x ^ p := funext (frobenius_def p)
    let σ : k ≃+* k := RingEquiv.ofBijective (frobenius k p) (by rw [hfk]; exact hbij)
    have hσ : ∀ a : k, σ.symm a ^ p = a := fun a =>
      (frobenius_def p (σ.symm a)).symm.trans (σ.apply_symm_apply a)
    let f : MvPolynomial (Fin d) k →+* Y.E :=
      MvPolynomial.eval₂Hom ((algebraMap (MvPolynomial (Fin d) k) Y.E).comp
        (MvPolynomial.C.comp σ.symm.toRingHom)) (fun j => Y.r j 1)
    obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := Y.univ Y.E f (fun j m => Y.r j (m + 1))
      (fun j => by
        show Y.r j (0 + 1) = MvPolynomial.eval₂Hom _ _ (MvPolynomial.X j)
        rw [MvPolynomial.eval₂Hom_X'])
      (fun j m => Y.r_succ j (m + 1))
    let F := frobenius Y.E p
    have hF : ∀ x : Y.E, F x = x ^ p := frobenius_def p
    have hFf : F.comp f = algebraMap (MvPolynomial (Fin d) k) Y.E := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [RingHom.comp_apply, hF]
        show ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.C a)) ^ p = _
        rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, RingHom.comp_apply,
          ← map_pow (algebraMap (MvPolynomial (Fin d) k) Y.E), ← map_pow MvPolynomial.C]
        rw [show σ.symm.toRingHom a = σ.symm a from rfl, hσ]
      · intro j
        rw [RingHom.comp_apply, hF]
        show ((MvPolynomial.eval₂Hom _ _) (MvPolynomial.X j)) ^ p = _
        rw [MvPolynomial.eval₂Hom_X', Y.r_succ, Y.r_zero]
    obtain ⟨u, -, hu⟩ := Y.univ Y.E (algebraMap (MvPolynomial (Fin d) k) Y.E) Y.r Y.r_zero Y.r_succ
    have hid : RingHom.id Y.E = u := hu _ ⟨RingHom.id_comp _, fun _ _ => rfl⟩
    have h1 : F.comp g = u := hu _ ⟨by rw [RingHom.comp_assoc, hg1, hFf],
      fun j m => by rw [RingHom.comp_apply, hg2, hF]; exact Y.r_succ j m⟩
    have h2 : g.comp F = u := by
      refine hu _ ⟨RingHom.ext fun x => ?_, fun j m => ?_⟩
      · rw [RingHom.comp_apply, RingHom.comp_apply, hF, map_pow]
        have hx := congrArg (fun φ => φ x) hg1
        simp only [RingHom.comp_apply] at hx
        rw [hx, ← hF, ← RingHom.comp_apply, hFf]
      · rw [RingHom.comp_apply, hF, map_pow, hg2]
        exact Y.r_succ j m
    refine ⟨hcE, Function.bijective_iff_has_inverse.2 ⟨g, fun x => ?_, fun x => ?_⟩⟩
    · have hx := congrArg (fun φ => φ x) (h2.trans hid.symm)
      simpa [hF] using hx
    · have hx := congrArg (fun φ => φ x) (h1.trans hid.symm)
      simpa [hF] using hx

theorem exists_etale_rootExt (p : ℕ) {P E₀ : Type} [CommRing P] [CommRing E₀] (ψ : P →+* E₀)
    (hψ : ψ.Etale) {d : ℕ} (s : Fin d → P) (t : Fin d → E₀) (hst : ∀ j, ψ (s j) = t j)
    (Y : RootExt p P s) (X : RootExt p E₀ t) : ∃ ψ' : Y.E →+* X.E, ψ'.Etale := by
  classical
  letI : Algebra P E₀ := ψ.toAlgebra
  haveI : Algebra.Etale P E₀ := hψ
  letI : Algebra P X.E := ((algebraMap E₀ X.E).comp ψ).toAlgebra
  haveI hbc : Algebra.Etale Y.E (Y.E ⊗[P] E₀) := Algebra.Etale.baseChange P E₀ Y.E
  obtain ⟨gY, ⟨hgY1, hgY2⟩, -⟩ := Y.univ X.E ((algebraMap E₀ X.E).comp ψ) X.r
    (fun k => by rw [X.r_zero, RingHom.comp_apply, hst]) X.r_succ
  let gYa : Y.E →ₐ[P] X.E := AlgHom.mk gY (fun r => by
    change gY (algebraMap P Y.E r) = _
    rw [← RingHom.comp_apply, hgY1]
    rfl)
  let gE : E₀ →ₐ[P] X.E := AlgHom.mk (algebraMap E₀ X.E) (fun r => rfl)
  let χ : Y.E ⊗[P] E₀ →ₐ[P] X.E := Algebra.TensorProduct.lift gYa gE (fun _ _ => Commute.all _ _)
  have hχ : ∀ (y : Y.E) (e : E₀), χ (y ⊗ₜ[P] e) = gY y * algebraMap E₀ X.E e := fun y e =>
    Algebra.TensorProduct.lift_tmul _ _ _ y e
  have hpow : ∀ k m, (Y.r k (m + 1) ⊗ₜ[P] (1 : E₀)) ^ p = Y.r k m ⊗ₜ[P] (1 : E₀) := by
    intro k m
    rw [Algebra.TensorProduct.tmul_pow, one_pow, Y.r_succ]
  obtain ⟨φ, ⟨hφ1, hφ2⟩, -⟩ := X.univ (Y.E ⊗[P] E₀)
    (Algebra.TensorProduct.includeRight : E₀ →ₐ[P] Y.E ⊗[P] E₀).toRingHom
    (fun k m => Y.r k m ⊗ₜ[P] (1 : E₀))
    (fun k => by
      show Y.r k 0 ⊗ₜ[P] (1 : E₀) = (1 : Y.E) ⊗ₜ[P] t k
      rw [Y.r_zero, Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra, hst])
    hpow
  obtain ⟨u, -, hu⟩ := X.univ X.E (algebraMap E₀ X.E) X.r X.r_zero X.r_succ
  have hc1 : (χ.toRingHom.comp φ).comp (algebraMap E₀ X.E) = algebraMap E₀ X.E := by
    rw [RingHom.comp_assoc, hφ1]
    refine RingHom.ext fun e => ?_
    show χ ((1 : Y.E) ⊗ₜ[P] e) = algebraMap E₀ X.E e
    rw [hχ, map_one, one_mul]
  have hc2 : ∀ k m, (χ.toRingHom.comp φ) (X.r k m) = X.r k m := by
    intro k m
    show χ (φ (X.r k m)) = X.r k m
    rw [hφ2]
    show χ (Y.r k m ⊗ₜ[P] (1 : E₀)) = X.r k m
    rw [hχ, map_one, mul_one, hgY2]
  have h1 : χ.toRingHom.comp φ = RingHom.id X.E :=
    (hu _ ⟨hc1, hc2⟩).trans (hu _ ⟨RingHom.id_comp _, fun _ _ => rfl⟩).symm
  have hL : φ.comp gY = (Algebra.TensorProduct.includeLeft (S := P) : Y.E →ₐ[P] Y.E ⊗[P] E₀).toRingHom := by
    obtain ⟨v, -, hv⟩ := Y.univ (Y.E ⊗[P] E₀)
      ((Algebra.TensorProduct.includeLeft (S := P) : Y.E →ₐ[P] Y.E ⊗[P] E₀).toRingHom.comp
        (algebraMap P Y.E))
      (fun k m => Y.r k m ⊗ₜ[P] (1 : E₀))
      (fun k => by
        show Y.r k 0 ⊗ₜ[P] (1 : E₀) = _
        rw [Y.r_zero]
        rfl)
      hpow
    refine (hv _ ⟨?_, ?_⟩).trans (hv _ ⟨rfl, fun _ _ => rfl⟩).symm
    · rw [RingHom.comp_assoc, hgY1, ← RingHom.comp_assoc, hφ1]
      refine RingHom.ext fun x => ?_
      show (1 : Y.E) ⊗ₜ[P] ψ x = algebraMap P Y.E x ⊗ₜ[P] (1 : E₀)
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]
    · intro k m
      show φ (gY (Y.r k m)) = Y.r k m ⊗ₜ[P] (1 : E₀)
      rw [hgY2, hφ2]
  have h2 : φ.comp χ.toRingHom = RingHom.id (Y.E ⊗[P] E₀) := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul y e =>
      show φ (χ (y ⊗ₜ[P] e)) = y ⊗ₜ[P] e
      rw [hχ, map_mul, ← RingHom.comp_apply φ gY, hL, ← RingHom.comp_apply φ (algebraMap E₀ X.E), hφ1]
      show (y ⊗ₜ[P] (1 : E₀)) * ((1 : Y.E) ⊗ₜ[P] e) = y ⊗ₜ[P] e
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  let e : (Y.E ⊗[P] E₀) ≃+* X.E := RingEquiv.ofRingHom χ.toRingHom φ h1 h2
  refine ⟨e.toRingHom.comp (algebraMap Y.E (Y.E ⊗[P] E₀)), ?_⟩
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.2 hbc)
    (RingHom.Etale.of_bijective e.bijective)

theorem root_perf : ∀ (p : ℕ), p.Prime → ∀ {k E₀ : Type} [CommRing k] [CommRing E₀] (i : k →+* E₀) {d : ℕ} (t : Fin d → E₀), (MvPolynomial.eval₂Hom i t).Etale → D.Pf p k → ∀ X : RootExt p E₀ t, D.Pf p X.E ∧ ∀ π ∈ nonZeroDivisors k, algebraMap E₀ X.E (i π) ∈ nonZeroDivisors X.E := by
  intro p hp k E₀ instk instE i d t het hk X
  have hflat : i.Flat := GlobalTheory.CompanionTheory.LiftFlat.flat_of_eval₂Hom_etale i t het
  obtain ⟨Y⟩ := GlobalTheory.CompanionTheory.RootAdjoin.nonempty_rootExt p hp (MvPolynomial (Fin d) k)
    (MvPolynomial.X : Fin d → MvPolynomial (Fin d) k)
  have hY : D.Pf p Y.E := pf_rootExt p hp hk Y
  obtain ⟨ψ', hψ'⟩ := exists_etale_rootExt p (MvPolynomial.eval₂Hom i t) het MvPolynomial.X t
    (fun j => MvPolynomial.eval₂Hom_X' i t j) Y X
  refine ⟨GlobalTheory.CompanionTheory.EtalePerfect.pf_of_etale p hp ψ' hψ' hY, fun π hπ => ?_⟩
  letI : Algebra k E₀ := i.toAlgebra
  haveI : Module.Flat k E₀ := hflat
  have hreg : IsSMulRegular E₀ π := Module.Flat.isSMulRegular_of_nonZeroDivisors hπ
  haveI : Module.Free E₀ X.E := Module.Free.of_basis X.b
  haveI : Module.Flat E₀ X.E := Module.Flat.of_free
  have hreg' : IsSMulRegular E₀ (i π) := by
    rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg ⊢
    intro m hm
    apply hreg m
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simpa [smul_eq_mul] using hm
  have hreg'' := IsSMulRegular.of_flat (S := X.E) hreg'
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  apply hreg''.right_eq_zero_of_smul
  rw [Algebra.smul_def, mul_comm]
  exact hz

end GlobalTheory.CompanionTheory.RootPerf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVectorBundle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVectorBundle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrVB
open GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem rp_class {W : X.Opens} {P : ObjectProperty (Thick (LL q))} {d r : ℕ} {u : Fin d → ∀ T : Thick (LL q), T.B}
    {x : Idx r d → Γ(X, W)} {c c' : HU (GF q r) P r} (h : Rp (W := W) P u x c) (h' : Rp (W := W) P u x c') : c = c' := by
  obtain ⟨f, hf, rfl, hs⟩ := h
  obtain ⟨f', hf', rfl, hs'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hs s).trans (hs' s).symm)
  subst e
  rfl

theorem inU_mono {W W' : X.Opens} (h : W' ≤ W) {T : Thick (LL q)} (hT : InU W' T) : InU W T :=
  hT.trans (fun _ hx => h hx)

theorem isLift_res {V W : X.Opens} (h : W ≤ V) {d : ℕ} {t : Fin d → Γ(X, V)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift V t u) {t' : Fin d → Γ(X, W)} (ht : ∀ i, t' i = rs h (t i)) : IsLift W t' u := by
  intro i T hT
  rw [ht, hu i T (inU_mono h hT), ev_res h T (inU_mono h hT) hT]

theorem st_iff {Q : ObjectProperty (Thick (LL q))} {W : X.Opens} (T : Thick (LL q)) :
    St Q {W} T ↔ Q T ∧ InU W T := by
  constructor
  · rintro ⟨h, V, hV, hi⟩
    obtain rfl : V = W := hV
    exact ⟨h, hi⟩
  · rintro ⟨h, hi⟩
    exact ⟨h, W, rfl, hi⟩

theorem inU_capO {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (LL q)) :
    InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  have e : capO U i = ⨅ a ∈ (Finset.univ : Finset (Fin n)), U (i a) := by simp [capO]
  rw [e, GlobalTheory.T.inOpen_finite_inf_iff (fun a => U (i a)) Finset.univ T]
  simp

theorem capT_eq (l s : ℕ) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => SS q l s (U α)) i = SS q l s (capO U i) := by
  funext T
  refine propext ⟨fun h => ?_, fun h a => ?_⟩
  · exact (st_iff T).2 ⟨((st_iff T).1 (h 0)).1, (inU_capO U i T).2 fun a => ((st_iff T).1 (h a)).2⟩
  · obtain ⟨h1, h2⟩ := (st_iff T).1 h
    exact (st_iff T).2 ⟨h1, (inU_capO U i T).1 h2 a⟩

def Free (W : X.Opens) (P : ObjectProperty (Thick (LL q))) (r : ℕ) {d : ℕ} (u : Fin d → ∀ T : Thick (LL q), T.B) : Prop :=
  (∀ cl : HU (GF q r) P r, ∃ x, Rp (W := W) P u x cl) ∧ ∀ x : Idx r d → Γ(X, W), Rp (W := W) P u x 0 → x = 0

section Forms
variable {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
  {P : ObjectProperty (Thick (LL q))} {r : ℕ}

theorem rp_zero (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) :
    Rp (W := W) P u (0 : Idx r d → Γ(X, W)) (0 : HU (GF q r) P r) := by
  obtain ⟨c, hc⟩ := hE W t u hu P hP r 0
  have h2 := (hA W t u hu P hP r _ _ _ _ hc (hA W t u hu P hP r _ _ _ _ hc hc).2).1
  rw [add_neg_cancel, add_neg_cancel] at h2
  exact h2

theorem rp_sum (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) {κ' : Type} (S : Finset κ')
    (x : κ' → Idx r d → Γ(X, W)) (c : κ' → HU (GF q r) P r) (h : ∀ k ∈ S, Rp (W := W) P u (x k) (c k)) :
    Rp (W := W) P u (∑ k ∈ S, x k) (∑ k ∈ S, c k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact rp_zero hE hA hu hP
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hA W t u hu P hP r _ _ _ _ (h a (Finset.mem_insert_self a S))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).1

theorem rp_coef (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) (hF : Free W P r u)
    {x x' : Idx r d → Γ(X, W)} {c : HU (GF q r) P r} (h : Rp (W := W) P u x c) (h' : Rp (W := W) P u x' c) : x = x' := by
  have h2 := (hA W t u hu P hP r _ _ _ _ h (hA W t u hu P hP r _ _ _ _ h' h').2).1
  rw [add_neg_cancel c] at h2
  exact add_neg_eq_zero.1 (hF.2 _ h2)

theorem exists_equiv (hE : StExists) (hA : StAdd) (hu : IsLift W t u) (hP : ∀ T, P T → InU W T) (hF : Free W P r u) :
    ∃ e : HU (GF q r) P r ≃+ (Idx r d → Γ(X, W)), ∀ cl, Rp (W := W) P u (e cl) cl := by
  choose f hf using hF.1
  choose g hg using fun x => hE W t u hu P hP r x
  exact ⟨{ toFun := f, invFun := g, left_inv := fun c => rp_class (hg _) (hf c),
           right_inv := fun x => rp_coef hA hu hP hF (hf _) (hg x),
           map_add' := fun a b => rp_coef hA hu hP hF (hf _) (hA W t u hu P hP r _ _ _ _ (hf a) (hf b)).1 }, hf⟩

end Forms

theorem free_at (hL : StLoc) {l s : ℕ} (hb : TFBase (dividedPowersBot O) l s) {V W : X.Opens} (h : W ≤ V)
    (hW : IsAffineOpen W) {d : ℕ} (c : Coord q V d) {u : Fin d → ∀ T : Thick (LL q), T.B} (hu : IsLift V c.t u)
    {r : ℕ} (hr : r < s) {P : ObjectProperty (Thick (LL q))} (hP : P = SS q l s W) : Free W P r u := by
  subst hP
  obtain ⟨c', hc'⟩ := GlobalTheory.T.coordinates_restrict_affine_open c h hW
  exact hL l s hb q c' u (isLift_res h hu hc') r hr

theorem chg (hE : StExists) (hA : StAdd) (hR : StRes) (hAct : StAct) {W W₂ : X.Opens} (h : W ≤ W₂) {da db : ℕ}
    {ta : Fin da → Γ(X, W₂)} {tb : Fin db → Γ(X, W₂)} {ua : Fin da → ∀ T : Thick (LL q), T.B}
    {ub : Fin db → ∀ T : Thick (LL q), T.B} (hua : IsLift W₂ ta ua) (hub : IsLift W₂ tb ub)
    {P P₂ : ObjectProperty (Thick (LL q))} (hPP : P ≤ P₂) (hP : ∀ T, P T → InU W T) (hP₂ : ∀ T, P₂ T → InU W₂ T) {r : ℕ}
    (A : HU (GF q r) P₂ r ≃+ (Idx r da → Γ(X, W₂))) (hA' : ∀ cl, Rp (W := W₂) P₂ ua (A cl) cl)
    (B : HU (GF q r) P₂ r ≃+ (Idx r db → Γ(X, W₂))) (hB' : ∀ cl, Rp (W := W₂) P₂ ub (B cl) cl)
    [DecidableEq (Idx r db)] (x : HU (GF q r) P r) (y : Idx r db → Γ(X, W)) (hy : Rp (W := W) P ub y x) :
    Rp (W := W) P ua (fun k => ∑ k', rs h (A (B.symm (Pi.single k' 1)) k) * y k') x := by
  have hua' : IsLift W (fun i => rs h (ta i)) ua := isLift_res h hua fun _ => rfl
  have hub' : IsLift W (fun i => rs h (tb i)) ub := isLift_res h hub fun _ => rfl
  have hb1 : ∀ k', Rp (W := W₂) P₂ ub (Pi.single k' 1) (B.symm (Pi.single k' 1)) := fun k' => by
    have := hB' (B.symm (Pi.single k' 1))
    rwa [AddEquiv.apply_symm_apply] at this
  choose m hm using fun k' => hAct W P hP r (y k')
  have hd1 : ∀ k', Rp (W := W) P ub (fun I => y k' * rs h ((Pi.single k' 1 : Idx r db → Γ(X, W₂)) I))
      (m k' ((resU (GF q r) hPP).pull r (B.symm (Pi.single k' 1)))) := fun k' =>
    hm k' _ _ hub' _ _ (hR W₂ W h tb ub hub P₂ P hPP hP₂ hP r _ _ (hb1 k'))
  have hd2 : ∀ k', Rp (W := W) P ua (fun I => y k' * rs h (A (B.symm (Pi.single k' 1)) I))
      (m k' ((resU (GF q r) hPP).pull r (B.symm (Pi.single k' 1)))) := fun k' =>
    hm k' _ _ hua' _ _ (hR W₂ W h ta ua hua P₂ P hPP hP₂ hP r _ _ (hA' _))
  have s1 := rp_sum hE hA hub' hP Finset.univ _ _ fun k' _ => hd1 k'
  have s2 := rp_sum hE hA hua' hP Finset.univ _ _ fun k' _ => hd2 k'
  have e1 : (∑ k', fun I => y k' * rs h ((Pi.single k' 1 : Idx r db → Γ(X, W₂)) I)) = y := by
    funext I
    rw [Finset.sum_apply, Finset.sum_eq_single I]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne (Ne.symm hb)]
    · simp
  rw [e1] at s1
  rw [rp_class s1 hy] at s2
  convert s2 using 1
  funext k
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem capO_pair {ι : Type} (U : ι → X.Opens) (α β : ι) : capO U ![α, β] = U α ⊓ U β := by
  refine le_antisymm (le_inf (capO_le U _ 0) (capO_le U _ 1)) (le_iInf fun a => ?_)
  fin_cases a
  · exact inf_le_left
  · exact inf_le_right

theorem capT_inU (l s : ℕ) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (LL q))
    (h : capT (fun α => SS q l s (U α)) i T) : InU (capO U i) T :=
  (inU_capO U i T).2 fun a => ((st_iff T).1 (h a)).2

theorem ss_inU (l s : ℕ) (W : X.Opens) (T : Thick (LL q)) (h : SS q l s W T) : InU W T := ((st_iff T).1 h).2

section Main
variable {ι : Type} (U : ι → X.Opens) (d : ι → ℕ) (c : ∀ α, Coord q (U α) (d α))

def uu (α : ι) : Fin (d α) → ∀ T : Thick (LL q), T.B := fun k T => lft (U α) T ((c α).t k)

theorem uu_lift (α : ι) : IsLift (U α) (c α).t (uu U d c α) := fun k T h => lft_spec T h _

theorem uu_res (α : ι) {W : X.Opens} (h : W ≤ U α) : IsLift W (fun k => rs h ((c α).t k)) (uu U d c α) :=
  isLift_res h (uu_lift U d c α) fun _ => rfl

end Main

theorem main : StExists → StAdd → StSmul → StRes → StAct → StLoc → StVB := by
  classical
  intro hE hA hS hR hAct hL O _ l s hb X q ι _ U d c ha r hr
  have hPi : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (T : Thick (LL q)), capT (fun α => SS q l s (U α)) i T → InU (capO U i) T :=
    fun i T h => capT_inU l s U i T h
  have hFi : ∀ (n : ℕ) (a : Fin (n + 1)) (i : Fin (n + 1) → ι),
      Free (capO U i) (capT (fun α => SS q l s (U α)) i) r (uu U d c (i a)) := fun n a i =>
    free_at hL hb (capO_le U i a) (ha n i) (c (i a)) (uu_lift U d c (i a)) hr (capT_eq l s U i)
  choose E hEr using fun (n : ℕ) (a : Fin (n + 1)) (i : Fin (n + 1) → ι) =>
    exists_equiv hE hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i)
  have aff2 : ∀ α β, IsAffineOpen (U α ⊓ U β) := fun α β => by
    rw [← capO_pair]
    exact ha 1 _
  choose A hAr using fun α β => exists_equiv (P := SS q l s (U α ⊓ U β)) (r := r) hE hA (uu_res U d c α inf_le_left)
    (ss_inU l s (U α ⊓ U β)) (free_at hL hb inf_le_left (aff2 α β) (c α) (uu_lift U d c α) hr rfl)
  choose B hBr using fun α β => exists_equiv (P := SS q l s (U α ⊓ U β)) (r := r) hE hA (uu_res U d c β inf_le_right)
    (ss_inU l s (U α ⊓ U β)) (free_at hL hb inf_le_right (aff2 α β) (c β) (uu_lift U d c β) hr rfl)
  refine ⟨{ κ := fun α => Idx r (d α)
            fin := fun _ => inferInstance
            g := fun α β k k' => A α β ((B α β).symm (Pi.single k' 1)) k
            e := fun n a => AddEquiv.piCongrRight fun i => E n a i
            e_smul := ?_
            e_δ := ?_
            e_chg := ?_ }⟩
  · intro n a z x i k
    have := rp_coef hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i) (hEr n a i (z • x i))
      (hS _ _ _ (uu_res U d c (i a) (capO_le U i a)) _ (hPi i) r _ _ z (hEr n a i (x i)))
    exact congrFun this k
  · intro n a b x i k
    have := rp_coef hA (uu_res U d c (i (b.succAbove a)) (capO_le U i (b.succAbove a))) (hPi i) (hFi (n + 1) (b.succAbove a) i)
      (hEr (n + 1) (b.succAbove a) i _)
      (hR _ _ (capO_comp U i b.succAbove) _ _ (uu_res U d c (i (b.succAbove a)) (capO_le U (i ∘ b.succAbove) a))
        _ (capT (fun α => SS q l s (U α)) i) (fun _ h _ => h _) (hPi _) (hPi i) r _ _ (hEr n a (i ∘ b.succAbove) (x (i ∘ b.succAbove))))
    exact congrFun this k
  · intro n a b x i k
    have hle : capO U i ≤ U (i a) ⊓ U (i b) := le_inf (capO_le U i a) (capO_le U i b)
    have hPP : capT (fun α => SS q l s (U α)) i ≤ SS q l s (U (i a) ⊓ U (i b)) := fun T h =>
      (st_iff T).2 ⟨((st_iff T).1 (h a)).1, inU_mono hle (hPi i T h)⟩
    have := rp_coef hA (uu_res U d c (i a) (capO_le U i a)) (hPi i) (hFi n a i) (hEr n a i (x i))
      (chg hE hA hR hAct hle (uu_res U d c (i a) inf_le_left) (uu_res U d c (i b) inf_le_right) hPP (hPi i)
        (ss_inU l s _) (A (i a) (i b)) (hAr _ _) (B (i a) (i b)) (hBr _ _) (x i) _ (hEr n b i (x i)))
    exact congrFun this k

end GlobalTheory.CompanionTheory.GrVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVectorBundleStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_vector_bundle : GlobalTheory.CompanionTheory.GrForm.StExists → GlobalTheory.CompanionTheory.GrForm.StAdd → GlobalTheory.CompanionTheory.GrForm.StSmul → GlobalTheory.CompanionTheory.GrForm.StRes → GlobalTheory.CompanionTheory.GrForm.StAct → GlobalTheory.CompanionTheory.GrForm.StLoc → GlobalTheory.CompanionTheory.GrForm.StVB := by
  first | exact @GlobalTheory.CompanionTheory.GrVB.main | exact GlobalTheory.CompanionTheory.GrVB.main | (intros; apply GlobalTheory.CompanionTheory.GrVB.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentRefinementOfUnimodular
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentRefinementOfUnimodular
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TestCover

section Ring

variable {S : Type*} [CommRing S]

theorem mem_of_compare {f g d : S} (h : Ideal.span {f, g} = ⊤) (h1 : d * f ∈ Ideal.span {g})
    (h2 : (1 - d) * g ∈ Ideal.span {f}) : d ∈ Ideal.span {g} ∧ 1 - d ∈ Ideal.span {f} := by
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 (Ideal.eq_top_iff_one _ |>.1 h)
  constructor
  · have e : d = x * (d * f) + (d * y) * g := by
      linear_combination (-d) * hxy
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1)
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g))
  · have e : 1 - d = ((1 - d) * x) * f + y * ((1 - d) * g) := by
      linear_combination (-(1 - d)) * hxy
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
      (Ideal.mul_mem_left _ _ h2)

theorem idem_prod {ι : Type*} (t : Finset ι) (f : ι → S) (h : ∀ k, IsIdempotentElem (f k)) :
    IsIdempotentElem (∏ k ∈ t, f k) := by
  unfold IsIdempotentElem
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => h k

theorem span_top_of_prod {m : ℕ} (e : Fin m → S) (h : ∏ k, (1 - e k) = 0) :
    Ideal.span (Set.range e) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem]
  have hk : ∀ k, Ideal.Quotient.mk (Ideal.span (Set.range e)) (1 - e k) = 1 := fun k => by
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range e)) (e k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self k))
    rw [map_sub, map_one, h0, sub_zero]
  have := congrArg (Ideal.Quotient.mk (Ideal.span (Set.range e))) h
  rw [map_prod, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_const_one, map_zero] at this
  rw [map_one, this]

theorem idem_refine
    (hV : ∀ f g : S, Ideal.span {f, g} = ⊤ →
      ∃ e : S, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}) :
    ∀ (m : ℕ) (s : Fin m → S) (c : S), IsIdempotentElem c → c ∈ Ideal.span (Set.range s) →
      ∃ e : Fin m → S, (∀ k, IsIdempotentElem (e k)) ∧ (∀ k, e k ∈ Ideal.span {s k}) ∧
        c * ∏ k, (1 - e k) = 0 := by
  intro m
  induction m with
  | zero =>
    intro s c _ hc
    have h0 : c = 0 := by
      rw [Set.range_eq_empty, Ideal.span_empty] at hc
      exact (Submodule.mem_bot _).1 hc
    exact ⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0, by rw [h0, zero_mul]⟩
  | succ m ih =>
    intro s c hc hcs
    have hr : Set.range s = insert (s 0) (Set.range (Fin.tail s)) := by
      conv_lhs => rw [← Fin.cons_self_tail s]
      exact Fin.range_cons _ _
    rw [hr, Ideal.mem_span_insert] at hcs
    obtain ⟨a, r, hr', hcr⟩ := hcs
    have htop : Ideal.span {s 0, r + (1 - c)} = ⊤ := by
      rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
      exact ⟨a, 1, by linear_combination -hcr⟩
    obtain ⟨d, hd, h1, h2⟩ := hV _ _ htop
    obtain ⟨hdg, hds⟩ := mem_of_compare htop h1 h2
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hdg
    have hcc : c * c = c := hc
    have hcd : IsIdempotentElem (c * d) := hc.mul hd
    have hmem : c * d ∈ Ideal.span (Set.range (Fin.tail s)) := by
      have e : c * d = (t * c) * r := by
        rw [← ht]
        linear_combination (-t) * hcc
      rw [e]
      exact Ideal.mul_mem_left _ _ hr'
    obtain ⟨e', hi, hm, hp⟩ := ih (Fin.tail s) (c * d) hcd hmem
    refine ⟨Fin.cons (1 - d) e', ?_, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using hd.one_sub
      · simpa using hi i
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using hds
      · simpa [Fin.tail] using hm i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      linear_combination hp

end Ring

theorem test_cover : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∀ {m : ℕ} (s : Fin m → A.U),
    Ideal.span (Set.range s) = ⊤ → ∃ e : Fin m → A.A, (∀ k, IsIdempotentElem (e k)) ∧
      Ideal.span (Set.range e) = ⊤ ∧ ∀ k, A.sharp (e k) ∈ Ideal.span {s k} := by
  intro l _ A hA m s hs
  have hV : ∀ f g : A.U, Ideal.span {f, g} = ⊤ →
      ∃ e : A.U, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} :=
    fun f g h => hA.val_aic.1 f g ⟨0, by rw [pow_zero, h]; trivial⟩
  obtain ⟨u, hi, hm, hp⟩ := idem_refine hV m s 1 IsIdempotentElem.one (by rw [hs]; trivial)
  rw [one_mul] at hp
  have hex : ∀ k, ∃ e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = u k := fun k =>
    (RL.idem_au A (u k) (hi k)).exists
  choose e he hsh using hex
  have hc := (RL.sharp_cong A).2.2
  have hzero : A.sharp 0 = 0 := by
    have := hc 1 IsIdempotentElem.one
    rwa [sub_self, map_one, sub_self] at this
  have hsp : A.sharp (∏ k, (1 - e k)) = 0 := by
    rw [map_prod, ← hp]
    exact Finset.prod_congr rfl fun k _ => by rw [hc _ (he k), hsh]
  have hidem : IsIdempotentElem (∏ k, (1 - e k)) :=
    idem_prod _ _ fun k => (he k).one_sub
  have h0 : ∏ k, (1 - e k) = 0 :=
    (RL.idem_au A 0 IsIdempotentElem.zero).unique ⟨hidem, hsp⟩ ⟨IsIdempotentElem.zero, hzero⟩
  exact ⟨e, he, span_top_of_prod e h0, fun k => by rw [hsh]; exact hm k⟩

end GlobalTheory.CompanionTheory.TestCover
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentRefinementOfUnimodularStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_refinement_of_unimodular : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∀ {m : ℕ} (s : Fin m → A.U), Ideal.span (Set.range s) = ⊤ → ∃ e : Fin m → A.A, (∀ k, IsIdempotentElem (e k)) ∧ Ideal.span (Set.range e) = ⊤ ∧ ∀ k, A.sharp (e k) ∈ Ideal.span {s k} := by
  first | exact @GlobalTheory.CompanionTheory.TestCover.test_cover | exact GlobalTheory.CompanionTheory.TestCover.test_cover | (intros; apply GlobalTheory.CompanionTheory.TestCover.test_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ZetaAlongK

open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem firstCountable_gl : FirstCountableTopology (GL ι 𝔸[k]) := by
  have h1 : SecondCountableTopology (Matrix ι ι 𝔸[k]) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → 𝔸[k]))
  have h2 : SecondCountableTopology (Matrix ι ι 𝔸[k])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι 𝔸[k])).symm.isEmbedding.secondCountableTopology
  have h3 : SecondCountableTopology (GL ι 𝔸[k]) :=
    (Units.isEmbedding_embedProduct (M := Matrix ι ι 𝔸[k])).secondCountableTopology
  exact @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ h3

theorem differentiableAt_globalZeta_of_majorant {F : 𝔸[k] → ℂ} (hFc : Continuous F)
    (χ : HeckeCharacter k) {s₀ : ℂ} {δ : ℝ} (hδ : 0 < δ) {f₀ f₁ f₂ : IdeleGroup k → ℝ}
    (i₀ : Integrable f₀ (ideleMeasure k)) (i₁ : Integrable f₁ (ideleMeasure k))
    (i₂ : Integrable f₂ (ideleMeasure k))
    (b₀ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ s₀.re ≤ f₀ t)
    (b₁ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re - 2 * δ) ≤ f₁ t)
    (b₂ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re + 2 * δ) ≤ f₂ t) :
    DifferentiableAt ℂ (globalZeta F χ) s₀ := by
  have hT : ∀ x : IdeleGroup k, 0 < (IdeleGroup.ideleModule k x : ℝ) :=
    fun x ↦ (IdeleGroup.ideleModule k x).2
  set G : ℂ → IdeleGroup k → ℂ := fun s x ↦
    F x * (χ.toIdele x : ℂ) * ((IdeleGroup.ideleModule k x : ℝ) : ℂ) ^ s with hG
  set G' : ℂ → IdeleGroup k → ℂ :=
    fun s x ↦ G s x * Complex.log (IdeleGroup.ideleModule k x : ℝ) with hG'
  set bound : IdeleGroup k → ℝ := fun x ↦ (f₁ x + f₂ x) / δ with hbound
  have hbound_int : Integrable bound (ideleMeasure k) := (i₁.add i₂).div_const δ
  have hcont' : Continuous (G' s₀) :=
    (continuous_zetaIntegrand hFc χ s₀).mul
      ((Complex.continuous_ofReal.comp continuous_ideleModule_val).clog
        fun x ↦ Complex.ofReal_mem_slitPlane.2 (hT x))
  have hint₀ : Integrable (G s₀) (ideleMeasure k) := by
    refine i₀.mono' (continuous_zetaIntegrand hFc χ s₀).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    simp only [hG]
    rw [norm_zetaIntegrand]
    exact b₀ x
  have hle : ∀ x, ∀ s ∈ Metric.ball s₀ δ, ‖G' s x‖ ≤ bound x := by
    intro x s hs
    have hre : |s.re - s₀.re| < δ := by
      have := (Complex.abs_re_le_norm (s - s₀)).trans_lt (mem_ball_iff_norm.1 hs)
      rwa [Complex.sub_re] at this
    have hnorm : ‖G' s x‖ = ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re *
        |Real.log (IdeleGroup.ideleModule k x : ℝ)|) := by
      simp only [hG', hG]
      rw [norm_mul, norm_zetaIntegrand, ← Complex.ofReal_log (hT x).le, Complex.norm_real,
        Real.norm_eq_abs, mul_assoc]
    rw [hnorm]
    calc ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re * |Real.log (IdeleGroup.ideleModule k x : ℝ)|)
        ≤ ‖F x‖ * (((IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ) :=
          mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le (hT x) hδ hre) (norm_nonneg _)
      _ = (‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            ‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ := by ring
      _ ≤ bound x := div_le_div_of_nonneg_right (add_le_add (b₁ x) (b₂ x)) hδ.le
  have hdiff : ∀ x, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (fun s ↦ G s x) (G' s x) s := by
    intro x s _
    have h := ((Complex.hasStrictDerivAt_const_cpow (y := s)
      (Or.inl (Complex.ofReal_ne_zero.2 (hT x).ne'))).hasDerivAt).const_mul
        (F x * (χ.toIdele x : ℂ))
    refine h.congr_deriv ?_
    simp only [hG', hG]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ideleMeasure k) (F := G)
    (F' := G') (x₀ := s₀) (bound := bound) (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall fun s ↦ (continuous_zetaIntegrand hFc χ s).aestronglyMeasurable)
    hint₀ hcont'.aestronglyMeasurable
    (Eventually.of_forall fun x s hs ↦ hle x s hs) hbound_int
    (Eventually.of_forall fun x s hs ↦ hdiff x s hs)
  exact key.2.differentiableAt

def col (m : GL ι 𝔸[k]) (i : ι) : ι → 𝔸[k] := (m : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1

theorem continuous_col (i : ι) : Continuous fun m : GL ι 𝔸[k] => col m i :=
  (Units.continuous_val (M := Matrix ι ι 𝔸[k])).matrix_mulVec continuous_const

theorem continuous_line {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (x : ι → 𝔸[k]) :
    Continuous fun t : 𝔸[k] => Ψ (t • x) :=
  hΨ.comp (continuous_id.smul continuous_const)

def Maj (Ψ : (ι → 𝔸[k]) → ℂ) (i : ι) (C : Set (GL ι 𝔸[k])) : Prop :=
  ∀ a b : ℝ, 1 < a → ∃ f : IdeleGroup k → ℝ, Integrable f (ideleMeasure k) ∧
    ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t

theorem differentiableOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    DifferentiableOn ℂ (fun s => lineZeta Ψ ω s (col m i)) {s | 1 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 < s₀.re := hs₀
  set δ := (s₀.re - 1) / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨f₀, i₀, b₀⟩ := h s₀.re s₀.re hs₀'
  obtain ⟨f₁, i₁, b₁⟩ := h (s₀.re - 2 * δ) (s₀.re - 2 * δ) (by rw [hδdef]; linarith)
  obtain ⟨f₂, i₂, b₂⟩ := h (s₀.re + 2 * δ) (s₀.re + 2 * δ) (by linarith)
  exact (differentiableAt_globalZeta_of_majorant (F := fun t => Ψ (t • col m i))
    (continuous_line hΨ _) ω hδ i₀ i₁ i₂ (fun t => b₀ _ le_rfl le_rfl m hm t)
    (fun t => b₁ _ le_rfl le_rfl m hm t) (fun t => b₂ _ le_rfl le_rfl m hm t)).differentiableWithinAt

theorem norm_lineZeta_le {Ψ : (ι → 𝔸[k]) → ℂ} (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} {f : IdeleGroup k → ℝ} {a b : ℝ} (hf : Integrable f (ideleMeasure k))
    (h : ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    ‖lineZeta Ψ ω s (col m i)‖ ≤ ∫ t, f t ∂ideleMeasure k := by
  refine norm_integral_le_of_norm_le hf (Eventually.of_forall fun t => ?_)
  rw [norm_zetaIntegrand (fun a => Ψ (a • col m i)) ω s t]
  exact h _ h1 h2 m hm t

def ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) : ℂ :=
  Ψ ((t : 𝔸[k]) • col y.2 i) * (ω.toIdele t : ℂ) * ((IdeleGroup.ideleModule k t : ℝ) : ℂ) ^ y.1

theorem norm_ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) :
    ‖ig Ψ ω i y t‖ = ‖Ψ ((t : 𝔸[k]) • col y.2 i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ y.1.re :=
  norm_zetaIntegrand (fun a => Ψ (a • col y.2 i)) ω y.1 t

theorem continuous_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (y : ℂ × GL ι 𝔸[k]) : Continuous (ig Ψ ω i y) :=
  continuous_zetaIntegrand (continuous_line hΨ (col y.2 i)) ω y.1

theorem continuous_ig_param {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (t : IdeleGroup k) : Continuous fun y : ℂ × GL ι 𝔸[k] => ig Ψ ω i y t := by
  have c1 : Continuous fun y : ℂ × GL ι 𝔸[k] => Ψ ((t : 𝔸[k]) • col y.2 i) :=
    hΨ.comp ((continuous_const : Continuous fun _ : ℂ × GL ι 𝔸[k] => (t : 𝔸[k])).smul
      ((continuous_col i).comp continuous_snd))
  refine (c1.mul continuous_const).mul ?_
  exact continuous_fst.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule k t).2.ne'))

theorem eventually_near {C : Set (GL ι 𝔸[k])} {s₀ : ℂ} {m₀ : GL ι 𝔸[k]} {a b : ℝ} (ha : a < s₀.re)
    (hb : s₀.re < b) : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝[{s | 1 < s.re} ×ˢ C] (s₀, m₀),
      a ≤ y.1.re ∧ y.1.re ≤ b ∧ y.2 ∈ C := by
  have hc : Continuous fun y : ℂ × GL ι 𝔸[k] => y.1.re := Complex.continuous_re.comp continuous_fst
  have e1 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), a < y.1.re :=
    hc.continuousAt.eventually (lt_mem_nhds ha)
  have e2 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), y.1.re < b :=
    hc.continuousAt.eventually (gt_mem_nhds hb)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with y y1 y2 y3
  exact ⟨y1.le, y2.le, y3.2⟩

theorem continuousOn_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => ∫ t, ig Ψ ω i y t ∂ideleMeasure k)
      ({s | 1 < s.re} ×ˢ C) := by
  have := firstCountable_gl (k := k) (ι := ι)
  rintro ⟨s₀, m₀⟩ ⟨hs₀, hm₀⟩
  have hs₀' : 1 < s₀.re := hs₀
  obtain ⟨f, hf, hb⟩ := h ((1 + s₀.re) / 2) (s₀.re + 1) (by linarith)
  have hnear := eventually_near (C := C) (m₀ := m₀) (s₀ := s₀) (a := (1 + s₀.re) / 2) (b := s₀.re + 1)
    (by linarith) (by linarith)
  refine continuousWithinAt_of_dominated (bound := f) ?_ ?_ hf ?_
  · exact Eventually.of_forall fun y => (continuous_ig hΨ ω i y).aestronglyMeasurable
  · filter_upwards [hnear] with y hy
    refine Eventually.of_forall fun t => ?_
    rw [norm_ig]
    exact hb _ hy.1 hy.2.1 _ hy.2.2 t
  · exact Eventually.of_forall fun t => (continuous_ig_param hΨ ω i t).continuousWithinAt

theorem continuousOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => lineZeta Ψ ω y.1 (col y.2 i))
      ({s | 1 < s.re} ×ˢ C) :=
  continuousOn_ig hΨ ω h

theorem zt_eq {G : Type} [Group G] (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι)
    (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (g : G) :
    zt π d i Ψ ω s g = lineZeta Ψ ω s (col (kap π d g)⁻¹ i) := rfl

theorem zetaK : EpConv → ZetaK := by
  intro hE G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ
  have hΨc : Continuous Ψ := GJMatrix.continuous_of_mem_schwartzBruhatPi hΨ
  have hcont : Continuous fun g : G => (kap π d g)⁻¹ :=
    ((continuous_const.mul hS.cont).mul continuous_const).inv
  have hC : IsCompact ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) := hK.image hcont
  have hM : Maj Ψ i ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) :=
    fun a b ha => (hE k ι Ψ hΨ).1 i a b _ ha hC
  have hmem : ∀ κ : K, (kap π d κ)⁻¹ ∈ (fun g : G => (kap π d g)⁻¹) '' (K : Set G) :=
    fun κ => ⟨κ, κ.2, rfl⟩
  refine ⟨fun κ => differentiableOn_lineZeta hΨc ω hM (hmem κ), ?_, ?_⟩
  · have hmap : Continuous fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹) :=
      continuous_fst.prodMk (hcont.comp (continuous_subtype_val.comp continuous_snd))
    have hS' : Set.MapsTo (fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹))
        ({s : ℂ | 1 < s.re} ×ˢ Set.univ)
        ({s : ℂ | 1 < s.re} ×ˢ ((fun g : G => (kap π d g)⁻¹) '' (K : Set G))) :=
      fun y hy => ⟨hy.1, hmem y.2⟩
    have h2 := ContinuousOn.comp (continuousOn_lineZeta hΨc ω hM) hmap.continuousOn hS'
    exact h2.congr fun y _ => zt_eq π d i Ψ ω y.1 y.2
  · intro a b ha
    obtain ⟨f, hf, hb⟩ := (hE k ι Ψ hΨ).1 i a b _ ha hC
    exact ⟨∫ t, f t ∂ideleMeasure k, fun s h1 h2 κ => norm_lineZeta_le ω hf hb h1 h2 (hmem κ)⟩

end GlobalTheory.CompanionTheory.ZetaAlongK
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConvStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_integral_of_epstein_conv : EpConv → ZetaK := by
  first | exact @GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | exact GlobalTheory.CompanionTheory.ZetaAlongK.zetaK | (intros; apply GlobalTheory.CompanionTheory.ZetaAlongK.zetaK <;> assumption)
end
end
