module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreStH
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleRootExt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedCohomologyVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormSmul
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormSmul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrFormSmul
open GlobalTheory.CompanionTheory.GrForm

theorem rep_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j} (r : R)
    (h : Rep a b z c) (hz : ∀ s, z' s - r • z s ∈ b.S _) : Rep a b z' (r • c) := by
  obtain ⟨f, hf, rfl, hfz⟩ := h
  refine ⟨r • f, by rw [map_smul, hf, smul_zero], rfl, fun s => ?_⟩
  rw [Ideal.Quotient.eq.mpr (hz s), ← Ideal.Quotient.mkₐ_eq_mk R, map_smul, Ideal.Quotient.mkₐ_eq_mk, ← hfz s]
  rfl

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lft_str_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (a : O) (f : Γ(X, W)) :
    lft W T (strV q W a * f) - T.i a * lft W T f ∈ T.J := by
  rw [← Ideal.Quotient.eq, lft_spec T h, map_mul, map_mul, lft_spec T h, ev_str T h]

theorem lift_nat {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (i : Fin d) {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') :
    u i T' - φ.φ (u i T) ∈ T'.J := by
  rw [← Ideal.Quotient.eq, hu i T' h', ev_nat φ h h', ← hu i T h, Ideal.quotientMap_mk]

private theorem mul_mem_sFil_succ_of_mem_sFil_of_mem_J {P : ObjectProperty (Thick (LL q))} {r : ℕ} (T : P.FullSubcategory)
    {y z : T.obj.B} (hy : y ∈ (sFil P (r : ℤ)).S T) (hz : z ∈ T.obj.J) :
    y * z ∈ (sFil P ((r : ℤ) + 1)).S T := by
  have h1 : z ∈ pdP T.obj.δ 1 := by
    have := GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP T.obj.δ 1 hz
    rwa [T.obj.δ.dpow_one hz] at this
  exact GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.obj.δ r 1 (Ideal.mul_mem_mul (show y ∈ pdP T.obj.δ r from hy) h1)

theorem stSmul : StSmul := by
  intro O _ X q W d t u hu P hP r x c a hc
  unfold Rp at hc ⊢
  refine rep_smul _ _ a hc (fun s => ?_)
  have hw : ∀ I : Fin r → Fin d, wz (Φ := sP P) (fun i T => u i T.obj) I s ∈ (sFil P (r : ℤ)).S (s.obj (Fin.last r)) :=
    fun I => wz_mem (GlobalTheory.CompanionTheory.DPFil.isFil_sFil P) _
      (fun i T T' φ => lift_nat hu i (P.ι.map φ) (hP _ T.property) (hP _ T'.property)) I s
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ (fun I _ => ?_)
  rw [← mul_smul_comm, ← mul_sub]
  exact mul_mem_sFil_succ_of_mem_sFil_of_mem_J _ (hw _) (lft_str_sub _ (hP _ (s.obj (Fin.last r)).property) a (x I))

end GlobalTheory.CompanionTheory.GrFormSmul
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormSmulStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_smul : GlobalTheory.CompanionTheory.GrForm.StSmul := by
  first | exact @GlobalTheory.CompanionTheory.GrFormSmul.stSmul | exact GlobalTheory.CompanionTheory.GrFormSmul.stSmul | (intros; apply GlobalTheory.CompanionTheory.GrFormSmul.stSmul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCover
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCover
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrForm.AffCover

theorem iInf_basicOpen {X : Scheme.{0}} {V : X.Opens} : ∀ (n : ℕ) (g : Fin (n + 1) → Γ(X, V)),
    (⨅ a, X.basicOpen (g a)) = X.basicOpen (∏ k, g k) := by
  intro n
  induction n with
  | zero =>
    intro g
    simp
  | succ n ih =>
    intro g
    rw [Fin.prod_univ_succ, Scheme.basicOpen_mul, ← ih (fun k => g k.succ)]
    exact le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun a => iInf_le _ a.succ))
      (le_iInf fun a => Fin.cases inf_le_left (fun b => inf_le_right.trans (iInf_le _ b)) a)

theorem stCover : GlobalTheory.CompanionTheory.GrForm.StCover := by
  intro O _ X q _ V hV
  classical
  have loc : ∀ x : V, ∃ (f : Γ(X, V)) (d : ℕ), x.1 ∈ X.basicOpen f ∧ Nonempty (Coord q (X.basicOpen f) d) := by
    intro x
    have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V le_top).hom :=
      RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
    obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth
      RingHom.isStandardSmooth_respectsIso q hV h x.2
    obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨f, n, hf, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he⟩
  choose f d hx hc using loc
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).2) (fun x hxV => Set.mem_iUnion.2 ⟨⟨x, hxV⟩, hx _⟩)
  refine ⟨t, inferInstance, fun a => X.basicOpen (f a.1), fun a => d a.1, fun a => (hc a.1).some, ?_, ?_⟩
  · refine le_antisymm (iSup_le fun a => X.basicOpen_le _) fun x hxV => ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht hxV)
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  · intro n i
    have e : capO (fun a : t => X.basicOpen (f a.1)) i = X.basicOpen (∏ k, f (i k).1) :=
      iInf_basicOpen n (fun k => f (i k).1)
    rw [e]
    exact hV.basicOpen _

end GlobalTheory.CompanionTheory.GrForm.AffCover
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCoverStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_cover : GlobalTheory.CompanionTheory.GrForm.StCover := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.AffCover.stCover | exact GlobalTheory.CompanionTheory.GrForm.AffCover.stCover | (intros; apply GlobalTheory.CompanionTheory.GrForm.AffCover.stCover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedCohomologyVanishing
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem capT_eq {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι : Type}
    (Q : ObjectProperty (Thick (LL q))) (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => St Q {U α}) i = St Q {capO U i} := by
  funext T
  have h := GlobalTheory.T.inOpen_finite_inf_iff (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U ∘ i) Finset.univ T
  have e : (⨅ α ∈ (Finset.univ : Finset (Fin (n + 1))), (U ∘ i) α) = capO U i := by simp [capO]
  rw [e] at h
  refine propext ⟨fun hT => ?_, fun hT a => ?_⟩
  · refine ⟨(hT 0).1, capO U i, rfl, h.2 fun a _ => ?_⟩
    obtain ⟨-, V, hV, hI⟩ := hT a
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact hI
  · obtain ⟨h1, V, hV, hI⟩ := hT
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact ⟨h1, _, rfl, h.1 hI a (Finset.mem_univ _)⟩

theorem dividedPowerFiltration_bot {K : Type} [CommRing K] {s : ℕ} (hs : 0 < s) : pdP (dividedPowersBot K) s = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hr, rfl⟩
  have : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hc p hp)
    omega
  obtain ⟨p, hp, hp0⟩ := this
  have h0 : (dividedPowersBot K).dpow p.1 p.2 = 0 := by
    have : p.2 = 0 := hl p hp
    rw [this]
    exact (dividedPowersBot K).dpow_eval_zero hp0
  simp only [SetLike.mem_coe]
  rw [List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h0⟩)]
  exact Ideal.zero_mem _

theorem tfBase {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 0 < s) : TFBase (dividedPowersBot K) 1 s := by
  refine ⟨dividedPowerFiltration_bot hs, ?_, ?_⟩
  · intro r x h
    simpa using h
  · intro n hn
    exact ⟨0, (n : K)⁻¹, by simpa only [pow_zero] using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)⟩

def zeroSerre (K : Type) [CommRing K] : Serre.{1} K where
  P M _ _ := Subsingleton M
  zero _ _ _ h := h
  mid M₁ M₂ M₃ _ _ _ _ _ _ f g hfg h₁ h₃ := ⟨fun a b => by
    have key : ∀ x : M₂, x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := (hfg x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, map_zero]
    rw [key a, key b]⟩

theorem subsingleton_H {K : Type} [CommRing K] (C : Cx.{1} K) (n : ℕ) (h : Subsingleton (C.X n)) : Subsingleton (C.H n) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Subsingleton.elim a b]

theorem cech_van (hV : StVan) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} (U : ι → X.Opens) (d : ι → ℕ)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r b a : ℕ) (hr : r < s)
    (hbr : b ≠ r) : Subsingleton ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) b).cx.H a) := by
  refine subsingleton_H _ a ?_
  refine ⟨fun x y => funext fun i => ?_⟩
  have e := capT_eq (q := q) (TF l s) U i
  obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (c (i 0)) (capO_le U i 0) (ha _ i)
  have : Subsingleton (HU (GF q r) (capT (fun α => SS q l s (U α)) i) b) := by
    rw [e]
    exact hV l s hb q c' r b hr hbr
  exact Subsingleton.elim _ _

theorem cech_pos (hB : StVB) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} [Fintype ι] (U : ι → X.Opens) (d : ι → ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (hU : (⨆ α, U α) = V)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r p : ℕ) (hr : r < s) :
    Subsingleton ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r).cx.H (p + 1)) := by
  obtain ⟨vb⟩ := hB l s hb q U d c ha r hr
  exact GlobalTheory.T.affine_cover_higher_cohomology_vanishes (strV q) V hV U hU ha (CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r) vb p

set_option maxHeartbeats 2000000 in
theorem main (hV : StVan) (hB : StVB) (hC : StCover) : KH.GlobSerreSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := by
  intro hS K _ _ X q _ V hVa s r j hr hj
  have hs : 0 < s := by omega
  have hb : TFBase (dividedPowersBot K) 1 s := tfBase hs
  obtain ⟨ι, _, U, d, c, hU, ha⟩ := hC q V hVa
  have hle : ∀ α, U α ≤ V := fun α => hU ▸ le_iSup U α
  have hinc : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Set.range U) ≤
      St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) {V} := by
    rintro T ⟨h1, W, ⟨α, rfl⟩, hI⟩
    exact ⟨h1, V, rfl, fun x hx => hle α (hI hx)⟩
  have hz := GlobalTheory.T.cech_refinement_cohomology_bijective (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} hinc
    (by
      rintro W rfl
      rw [← hU, sSup_range]) j
  have hcech : ∀ a b, a + b = j → (zeroSerre K).P ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q 1 s (U α)) b).cx.H a) := by
    intro a b hab
    by_cases hbr : b = r
    · subst hbr
      cases a with
      | zero => exact absurd (by omega) hj
      | succ p => exact cech_pos hB 1 s hb q U d V hVa hU c ha b p hr
    · exact cech_van hV 1 s hb q U d c ha r b a hr hbr
  have hG := hS (O := K) (R := K) (I := ⊥) (γ := dividedPowersBot K) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥) (Λ := K)
    (GF q r) (TF 1 s) U (zeroSerre K) j hcech
  exact @Function.Injective.subsingleton _ _ _ (hz.1 r ((r : ℤ) + 1)).1 hG

end GlobalTheory.CompanionTheory.GrForm

namespace GlobalTheory.CompanionTheory.GrForm

theorem gr_aff : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := fun hL _ hP hS _ =>
  main (GlobalTheory.T.graded_form_vanish_of_frame GlobalTheory.T.graded_form_frame hL hP)
    (GlobalTheory.T.graded_form_vector_bundle (GlobalTheory.T.graded_form_exists_of_cocycle GlobalTheory.T.graded_form_cocycle) GlobalTheory.T.graded_form_add GlobalTheory.T.graded_form_smul GlobalTheory.T.graded_form_restrict GlobalTheory.T.graded_form_action (GlobalTheory.T.graded_form_local_of_frame GlobalTheory.T.graded_form_frame hL hP))
    GlobalTheory.T.graded_form_cover hS
end GlobalTheory.CompanionTheory.GrForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedCohomologyVanishingStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_graded_cohomology_vanishing : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.gr_aff | exact GlobalTheory.CompanionTheory.GrForm.gr_aff | (intros; apply GlobalTheory.CompanionTheory.GrForm.gr_aff <;> assumption)
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem gr_aff_pf : KH.GrAff :=
  GlobalTheory.T.affine_graded_cohomology_vanishing locGr_h locVan_h polyTf_h globSerreSt_h globVanSt_h

end CrystallineSemistableComparison.Pb
