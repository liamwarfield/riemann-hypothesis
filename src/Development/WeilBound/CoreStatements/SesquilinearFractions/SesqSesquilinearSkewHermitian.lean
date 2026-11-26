module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.SesqSesquilinearSkewHermitian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_zero_of_trace_pairing_zero {z : E} (h : ∀ c : 𝓞 E, Algebra.trace ℚ E ((c : E) * z) = 0) : z = 0 := by
  rw [HT.LatBasic.expand_dual z]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := h (RingOfIntegers.basis E k)
  rw [integralBasis_apply, mul_comm, ← RingOfIntegers.coe_eq_algebraMap, hk, zero_smul]

theorem eq_of_trace_pairing_eq {z w : E} (h : ∀ c : 𝓞 E, Algebra.trace ℚ E ((c : E) * z) = Algebra.trace ℚ E ((c : E) * w)) :
    z = w := by
  rw [← sub_eq_zero]
  exact eq_zero_of_trace_pairing_zero fun c => by rw [mul_sub, map_sub, h c, sub_self]

theorem trace_mul_sesq_eq_form (D : Datum H) (a : 𝓞 E) (x y : D.La) :
    Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ) := by
  classical
  have e : ∀ k, Algebra.trace ℚ E ((a : E) * ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k)) =
      (D.EF (RingOfIntegers.basis E k • x) y : ℚ) * ((RingOfIntegers.basis E).repr a k : ℚ) := by
    intro k
    rw [show (a : E) * ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k) =
        (D.EF (RingOfIntegers.basis E k • x) y : ℤ) • (HT.dualInt E k * (a : E)) by rw [zsmul_eq_mul]; ring,
      map_zsmul, zsmul_eq_mul, HT.LatBasic.repr_eq_trace]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sesq, Finset.mul_sum, map_sum, e]
  have ha : a • x = ∑ k, ((RingOfIntegers.basis E).repr a k : ℤ) • (RingOfIntegers.basis E k • x) := by
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr a]
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => smul_assoc _ _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ha, map_sum, LinearMap.sum_apply]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem Datum_EF_antisymm (D : Datum H) (x y : D.La) : D.EF y x = -D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt x, D.alt y, zero_add, add_zero] at h
  linarith

theorem Host_bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.coe_injective
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E (a : E)

theorem trace_complexConj (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := by
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσ : ∀ w, σ w = IsCMField.complexConj E w := fun _ => rfl
  rw [← hσ, Algebra.trace_apply, Algebra.trace_apply]
  have : Algebra.lmul ℚ E (σ z) = σ.toLinearEquiv.conj (Algebra.lmul ℚ E z) := by
    ext w
    show σ z * w = σ (z * σ.symm w)
    rw [map_mul, AlgEquiv.apply_symm_apply]
  rw [this, LinearMap.trace_conj']

theorem sesq_sesquilinear_properties (D : Datum H) :
    (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧
      (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧
      (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧
      (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧
      (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧
      (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧
      ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b := by
  refine ⟨trace_mul_sesq_eq_form D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    simp only [sesq, smul_add, map_add (f := _), LinearMap.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  · intro x y y'
    simp only [sesq, map_add (f := _), Int.cast_add, add_mul, Finset.sum_add_distrib]
  · intro a x y
    apply eq_of_trace_pairing_eq
    intro c
    rw [trace_mul_sesq_eq_form, ← _root_.mul_assoc, ← map_mul, trace_mul_sesq_eq_form, smul_smul]
  · intro a x y
    apply eq_of_trace_pairing_eq
    intro c
    have h1 : D.EF (c • x) (a • y) = D.EF ((H.bar a * c) • x) y := by
      conv_lhs => rw [← Host_bar_bar (H := H) a]
      rw [← D.adj, smul_smul]
    rw [trace_mul_sesq_eq_form, h1, ← _root_.mul_assoc, mul_comm (c : E), ← H.bar_eq, ← map_mul, trace_mul_sesq_eq_form]
  · intro x y
    apply eq_of_trace_pairing_eq
    intro c
    have h1 : D.EF (c • y) x = -D.EF ((H.bar c) • x) y := by
      rw [Datum_EF_antisymm, D.adj, Host_bar_bar]
    rw [trace_mul_sesq_eq_form, h1, mul_neg, map_neg, Int.cast_neg, neg_inj]
    have h2 : (c : E) * IsCMField.complexConj E (sesq D x y) =
        IsCMField.complexConj E (((H.bar c : 𝓞 E) : E) * sesq D x y) := by
      rw [map_mul, H.bar_eq, IsCMField.complexConj_apply_apply]
    rw [h2, trace_complexConj, trace_mul_sesq_eq_form]
  · intro δ hδ x y
    have hdual : sesq D x y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
      rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _)]
      intro c hc
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc
      refine ⟨D.EF (c • x) y, ?_⟩
      rw [Algebra.traceForm_apply, mul_comm, ← RingOfIntegers.coe_eq_algebraMap, trace_mul_sesq_eq_form]
      simp
    have hmul : (δ : E) * sesq D x y ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) *
        FractionalIdeal.dual ℤ ℚ 1) :=
      FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩) hdual
    rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _))] at hmul
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hmul
    exact ⟨b, hb.symm⟩

end GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

theorem sesq_sesquilinear_skew_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧ (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧ (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧ (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧ (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧ (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧ ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b :=
  fun _ _ _ _ _ D => GlobalTheory.CompanionTheory.Ar.Fl.sesq_sesquilinear_properties D

end PositivityTheory.Xgf
end

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.GBridge
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

private theorem pt_zero_lemma {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

private theorem LieModel_pt_sum_eq_prod {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) :
    ∀ (n : ℕ) (v : Fin n → U), M.pt (∑ k, v k) = (List.ofFn fun k => M.pt (v k)).prod := by
  intro n
  induction n with
  | zero => intro v; simp [pt_zero_lemma M]
  | succ n ih =>
    intro v
    rw [Fin.sum_univ_succ, M.add, ih, List.ofFn_succ, List.prod_cons]

private theorem isComb_pt_iff_eq_pt_sum {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) (n : ℕ) (c : Fin n → R) (u : Fin n → U)
    (w : epsAt x ⟶ G) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k) := by
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsComb
  rw [LieModel_pt_sum_eq_prod M]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : v = fun i => M.pt (c i • u i) := by
      funext i
      apply Over.OverMorphism.ext
      rw [hv i, M.smul]
    rw [hv']
  · intro h
    refine ⟨fun i => M.pt (c i • u i), fun i => ?_, h⟩
    rw [M.smul]

private theorem isEigVec_pt_iff_mem_eigSp {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) {O : Type} [CommRing O] (act : OAct O G)
    (ρ : O →+* Module.End R U) (τ : O →+* R) (hM : M.IsActOf act.act ρ) (u : U) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ := by
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec eigSp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  constructor
  · rintro ⟨-, h⟩ a
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hM a u, M.smul, h a]
  · intro h
    refine ⟨M.tan u, fun a => ?_⟩
    rw [← hM a u, h a, M.smul]

theorem lie_model_eigenvectors_action : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ := by
  intro S R _ G _ x U _ _ M
  refine ⟨fun n c u w => isComb_pt_iff_eq_pt_sum M n c u w, fun O _ act ρ τ hM => ⟨fun u => isEigVec_pt_iff_mem_eigSp M act ρ τ hM u, fun n u => ?_⟩⟩
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsEigFrame
  constructor
  · rintro ⟨hu, huniq⟩
    have hu' : ∀ i, u i ∈ eigSp ρ τ := fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mp (hu i)
    have hex : ∀ e ∈ eigSp ρ τ, ∃! c : Fin n → R, e = ∑ k, c k • u k := by
      intro e he
      obtain ⟨c, hc, huq⟩ := huniq (M.pt e) ((isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mpr he)
      exact ⟨c, M.inj ((isComb_pt_iff_eq_pt_sum M n c u _).mp hc),
        fun c' hc' => huq c' ((isComb_pt_iff_eq_pt_sum M n c' u _).mpr (congrArg M.pt hc'))⟩
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain ⟨c, -, huq⟩ := hex 0 (Submodule.zero_mem _)
      have hg0 : g = 0 := (huq g hg.symm).trans (huq 0 (by simp)).symm
      rw [hg0]
      rfl
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hu' i
      · intro e he
        obtain ⟨c, hc, -⟩ := hex e he
        rw [hc]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro ⟨hli, hsp⟩
    have hu' : ∀ i, u i ∈ eigSp ρ τ := fun i => hsp ▸ Submodule.subset_span ⟨i, rfl⟩
    refine ⟨fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mpr (hu' i), fun w hw => ?_⟩
    have ht : IsTanAt G x w := by
      obtain ⟨h, -⟩ := hw
      exact h
    obtain ⟨e, rfl⟩ := M.onto w ht
    have he : e ∈ eigSp ρ τ := (isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mp hw
    rw [← hsp] at he
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp he
    refine ⟨c, (isComb_pt_iff_eq_pt_sum M n c u _).mpr (congrArg M.pt hc.symm), fun c' hc' => ?_⟩
    have h1 : e = ∑ k, c' k • u k := M.inj ((isComb_pt_iff_eq_pt_sum M n c' u _).mp hc')
    have h2 : ∑ k, (c' k - c k) • u k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h1, hc, sub_self]
    funext k
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h2 k)

end PositivityTheory.Xgf
end

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.GGramPush
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder CategoryTheory.Obj

namespace PositivityTheory.Xgf.ChartPullbackComposition

variable {X X' X'' : Scheme.{0}}

def chartPullComp (L : LB X) (φ : X' ⟶ X) (ψ : X'' ⟶ X') : ChartPull (L.pull (ψ ≫ φ)) (L.pull φ) ψ where
  idx J := J
  le J y hy := (mem_pull (F := φ)).2 ((mem_pull (F := ψ ≫ φ)).1 hy)
  g y J J' hj hj' := by
    have h1 : ψ y ∈ (L.pull φ).U J := (mem_pull (F := φ)).2 ((mem_pull (F := ψ ≫ φ)).1 hj)
    have h2 : ψ y ∈ (L.pull φ).U J' := (mem_pull (F := φ)).2 ((mem_pull (F := ψ ≫ φ)).1 hj')
    refine (gm_pull_g L (ψ ≫ φ) (𝟙 _) y J J' hj hj').trans ?_
    refine Eq.trans ?_ (gm_pull_g L φ ψ y J J' h1 h2).symm
    rw [Category.id_comp]

end PositivityTheory.Xgf.ChartPullbackComposition

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.ChartPullbackComposition in
theorem hodge_gram_invariant_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (n : ℕ) (v' : Fin n → (epsAt x' ⟶ t'.G)) (v : Fin n → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x = x' ≫ f → (∀ k, (v k).left = (v' k).left ≫ m.φ) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  intro E _ _ _ H S S' t t' f m x' x n v' v Γ hx hv
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := ⟨w₀, hw₀⟩

  have hpull : ∀ {Z : Scheme.{0}} (ψ' : Z ⟶ t'.G.left), LBIso (t'.PP.L.pull ψ') (t.PP.L.pull (ψ' ≫ m.φ)) :=
    fun ψ' => LBIso.chartPull (chartPullPull t'.PP.L ψ' ψ' rfl) (chartPullComp t.PP.L m.φ ψ') hL
  constructor
  · rintro ⟨Q, ψ', v₁, u, Hm, χ, W, hPB, hLB, hAH, hv₁, hΓ⟩
    refine ⟨Q, ψ' ≫ m.φ, v₁, u, Hm, χ, W, (hPB.comp m.cart).congr hx.symm rfl, ?_, hAH, fun i => ⟨?_, (hv₁ i).2⟩, hΓ⟩
    · exact LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB t'.PP.isLB _) Q.isLB (LBIso.symm (hpull ψ')) hLB
    · rw [← Category.assoc, (hv₁ i).1, hv i]
  · rintro ⟨Q, ψ, v₁, u, Hm, χ, W, hPB, hLB, hAH, hv₁, hΓ⟩
    have hP := ((isGrpPullback_pullback t'.G x').comp m.cart).congr hx.symm rfl
    obtain ⟨e, he, heψ⟩ := grpPullback_iso hPB hP
    have hψ' : IsGrpPullback Q.A t'.G x' (e.hom.left ≫ pullback.fst t'.G.hom x') :=
      ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback t'.G x')).congr (Category.id_comp x') rfl
    have hcomp : (e.hom.left ≫ pullback.fst t'.G.hom x') ≫ m.φ = ψ := by
      rw [Category.assoc]; exact heψ
    refine ⟨Q, e.hom.left ≫ pullback.fst t'.G.hom x', v₁, u, Hm, χ, W, hψ', ?_, hAH, fun i => ⟨?_, (hv₁ i).2⟩, hΓ⟩
    · refine LBIso.trans (pull_isLB t'.PP.isLB _) (pull_isLB t.PP.isLB _) Q.isLB (hpull _) ?_
      rw [hcomp]
      exact hLB
    · apply m.cart.1.hom_ext
      · rw [Category.assoc, hcomp, (hv₁ i).1, hv i]
      · rw [Category.assoc, hψ'.1.w, ← Category.assoc, Over.w, Over.w]
        rfl

end PositivityTheory.Xgf
end
