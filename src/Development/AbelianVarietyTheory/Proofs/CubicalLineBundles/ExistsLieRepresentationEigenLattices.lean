module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCMPairingFamilyOfPolarisationDiagonalComplex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLattices
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.GenFib

theorem _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat (K : Type) [Field K]
    [NumberField K] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (𝓞 K))) (F : _root_.GlobalTheory.CM.GenFib P) (O : Type)
    [CommRing O] (act : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O P.A) :
    ∃ r : O →+* Module.End K (Fin F.P₀.g → K),
      (∀ a, F.IsDiffOf F (act.act a) (r a)) ∧
      ∀ (τ : O →+* 𝓞 K) c, (c ∈ F.eigLat act τ ↔
          c ∈ F.lieLat ∧ ∀ a, r a c = τ a • c) ∧
        (c ∈ Submodule.span K (F.eigLat act τ :
            Set (Fin F.P₀.g → K)) ↔ ∀ a, r a c = τ a • c) := by
  obtain ⟨hex, hinj, -, -, hlie, heig⟩ := _root_.GlobalTheory.CM.integral_tangent_coordinates K P F
  have hcoord : ∀ {u c c'}, F.IsCoord u c → F.IsCoord u c' → c = c' := fun h h' =>
    (hex _ h.1).unique h h'
  have hdiff : ∀ a, ∃! M, F.IsDiffOf F (act.act a) M := fun a =>
    (_root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P F (act.act a) (act.hom a)).1
  choose R hR using fun a => (hdiff a).exists
  have huniq : ∀ a M, F.IsDiffOf F (act.act a) M → R a = M :=
    fun a M h => (hdiff a).unique (hR a) h
  have hone : R 1 = 1 := huniq 1 1 (by
    intro u c h
    simpa [act.one] using h)
  have hmul : ∀ a b, R (a * b) = R a * R b := fun a b => by
    rw [mul_comm a b]
    refine huniq _ _ ?_
    intro u c h
    rw [act.mul, ← Category.assoc]
    exact hR a _ _ (hR b u c h)
  have hadd : ∀ a b, R (a + b) = R a + R b := fun a b => by
    refine huniq _ _ ?_
    intro u c h
    rw [act.add, comp_mul]
    exact _root_.GlobalTheory.CM.IntCoord.isCoord_mul F (hR a u c h) (hR b u c h)

  have hspan : Submodule.span K (F.lieLat :
      Set (Fin F.P₀.g → K)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hφ0 (LinearMap.ext h)
    have hM : F.IsDiffOf F (act.act 1) (1 + φ.smulRight x) := by
      intro u c h
      have hφc : φ c = 0 := LinearMap.mem_ker.1 (hle (Submodule.subset_span ((hlie c).2 ⟨u, h⟩)))
      simpa [act.one, hφc] using h
    have h1 := LinearMap.congr_fun (hone.symm.trans (huniq 1 _ hM)) x
    simp at h1
    rcases h1 with h1 | h1
    · exact hx h1
    · exact hx (by simp [h1])
  have hlat : ∀ τ : O →+* 𝓞 K, ∀ c, c ∈ F.eigLat act τ ↔
      c ∈ F.lieLat ∧ ∀ a, R a c = τ a • c := by
    intro τ c
    rw [heig O act τ c, hlie c]
    constructor
    · rintro ⟨u, hu, hcomb⟩
      exact ⟨⟨u, hu⟩, fun a =>
        hcoord (hR a u c hu) (_root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu (hcomb a))⟩
    · rintro ⟨⟨u, hu⟩, hc⟩
      refine ⟨u, hu, fun a => ?_⟩
      have hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb ![τ a] ![u] (_root_.GlobalTheory.CM.IntCoord.sc (τ a) ≫ u) :=
        (_root_.GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl
      have he := hinj _ _ _ (hR a u c hu)
        (by rw [hc a]; exact _root_.GlobalTheory.CM.IntCoord.isCoord_smul F hu hs)
      rw [he]
      exact hs
  refine ⟨RingHom.mk' ⟨⟨R, hone⟩, hmul⟩ hadd, fun a => hR a, fun τ c => ⟨hlat τ c, ?_⟩⟩
  show _ ↔ ∀ a, R a c = τ a • c
  constructor
  · intro hc
    refine Submodule.span_induction (p := fun c _ => ∀ a, R a c = τ a • c) ?_ ?_ ?_ ?_ hc
    · exact fun x hx a => ((hlat τ x).1 hx).2 a
    · intro a
      simp
    · intro x y _ _ hx hy a
      rw [map_add (f := _), hx, hy, smul_add]
    · intro k x _ hx a
      rw [map_smul, hx, smul_comm]
  · intro hc
    have hcspan : c ∈ Submodule.span K (F.lieLat :
        Set (Fin F.P₀.g → K)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 K))).1 hcspan
    rw [Submodule.span_eq] at hy
    have hzy : (z : 𝓞 K) • (IsLocalization.mk' K (1 : 𝓞 K) z • y) = y := by
      rw [← smul_assoc, Algebra.smul_def (z : 𝓞 K) (IsLocalization.mk' K (1 : 𝓞 K) z),
        IsLocalization.mk'_spec', map_one, one_smul]
    have hyeig : ∀ a, R a y = τ a • y := fun a => by
      rw [← hzy, LinearMap.map_smul_of_tower, hc a, smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ((hlat τ y).2 ⟨hy, hyeig⟩))

end GlobalTheory.CM.GenFib
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieRepresentation_eigenLattices : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (O : Type) [CommRing O] (act : OAct O P.A), ∃ r : O →+* Module.End K (Fin F.P₀.g → K), (∀ a, F.IsDiffOf F (act.act a) (r a)) ∧ ∀ (τ : O →+* 𝓞 K) c, (c ∈ F.eigLat act τ ↔ c ∈ F.lieLat ∧ ∀ a, r a c = τ a • c) ∧ (c ∈ Submodule.span K (F.eigLat act τ : Set (Fin F.P₀.g → K)) ↔ ∀ a, r a c = τ a • c) := by
  first | exact @GlobalTheory.CM.GenFib.exists_lieRep_eigLat | exact GlobalTheory.CM.GenFib.exists_lieRep_eigLat | (intros; apply GlobalTheory.CM.GenFib.exists_lieRep_eigLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.HermHom

theorem isTangent_of_isLieComb {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g n : ℕ} (u : HolUnif A L g)
    {W : Fin n → (Fin g → ℂ)} {v : Fin n → (epsR ℂ ⟶ A)} {c : Fin n → ℂ} {w : epsR ℂ ⟶ A}
    (hv : ∀ i, IsTangent (v i)) (h : ∀ i, u.IsDiff (W i) (v i)) (hw : IsLieComb c v w) : IsTangent w := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff] at hw
  subst hw
  rw [← ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff]
  exact (GlobalTheory.UnifDifferential.isDiff_prod u (fun i => c i • W i) _
    (fun i => ReciprocityTheory.ChartRestriction.G.Chart.isTan_scale _ ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 (hv i)))
    (fun i => GlobalTheory.UnifDifferential.isDiff_scale u (h i) _)).1

theorem map_comb {K : Type} [Field K] (s : K →+* ℂ) {A A' : Over (Sp K)} [GrpObj A] [GrpObj A']
    {B B' : Over (Sp ℂ)} [GrpObj B] [GrpObj B'] {ψ : B.left ⟶ A.left} {ψ' : B'.left ⟶ A'.left}
    (hψ : IsGrpPullback B A (spMap s) ψ) (hψ' : IsGrpPullback B' A' (spMap s) ψ')
    {L : LB B.left} {L' : LB B'.left} {g g' n n' : ℕ} (u : HolUnif B L g) (u' : HolUnif B' L' g')
    {v : Fin n → (epsR K ⟶ A)} {v' : Fin n' → (epsR K ⟶ A')}
    (hv : ∀ i, IsTangent (v i)) (hv' : ∀ i, IsTangent (v' i))
    {t : Fin n → (epsR ℂ ⟶ B)} {t' : Fin n' → (epsR ℂ ⟶ B')}
    {W : Fin n → Fin g → ℂ} {W' : Fin n' → Fin g' → ℂ}
    (hW : ∀ i, IsVecOver s ψ (v i) (t i) ∧ u.IsDiff (W i) (t i))
    (hW' : ∀ i, IsVecOver s ψ' (v' i) (t' i) ∧ u'.IsDiff (W' i) (t' i))
    (hu : ∀ x, IsTangent x → ∃! w, u'.IsDiff w x)
    {f : A ⟶ A'} {f₁ : B ⟶ B'} (e : f₁.left ≫ ψ' = ψ ≫ f.left) {Φ : (Fin g → ℂ) → (Fin g' → ℂ)}
    (hΦ : ∀ w x, IsTangent x → u.IsDiff w x → IsTangent (x ≫ f₁) ∧ u'.IsDiff (Φ w) (x ≫ f₁))
    {c : Fin n → K} {c' : Fin n' → K} (hc : ∀ w, IsLieComb c v w → IsLieComb c' v' (w ≫ f)) :
    Φ (∑ i, s (c i) • W i) = ∑ i, s (c' i) • W' i := by
  have ht : ∀ i, IsTangent (t i) := fun i => (hW i).1.isTangent hψ (hv i)
  have ht' : ∀ i, IsTangent (t' i) := fun i => (hW' i).1.isTangent hψ' (hv' i)
  have hw : IsLieComb c v (ReciprocityTheory.ChartRestriction.G.Chart.prodPts c v) :=
    (ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff c v _).2 rfl
  have hx : IsLieComb (fun i => s (c i)) t (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (fun i => s (c i)) t) :=
    (ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff _ t _).2 rfl
  have hxo : IsVecOver s ψ (ReciprocityTheory.ChartRestriction.G.Chart.prodPts c v)
      (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (fun i => s (c i)) t) :=
    (GlobalTheory.lieComb_baseChange _ _ s _ _ ψ hψ _ v _ c t _ (fun j => (hW j).1) hw).2 hx
  have hxT := isTangent_of_isLieComb u ht (fun i => (hW i).2) hx
  have hxD := GlobalTheory.UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W t _ _ ht (fun i => (hW i).2) hx
  obtain ⟨hfT, hfD⟩ := hΦ _ _ hxT hxD
  have hyo := GlobalTheory.NormHom.isVecOver_comp hxo e
  have hy : IsLieComb (fun i => s (c' i)) t' (ReciprocityTheory.ChartRestriction.G.Chart.prodPts (fun i => s (c i)) t ≫ f₁) :=
    (GlobalTheory.lieComb_baseChange _ _ s _ _ ψ' hψ' _ v' _ c' t' _ (fun j => (hW' j).1) (hc _ hw)).1 hyo
  have hyD := GlobalTheory.UnifDifferential.isDiff_of_isLieComb _ _ _ _ u' W' t' _ _ ht' (fun i => (hW' i).2) hy
  exact (hu _ hfT).unique hfD hyD

private lemma hermForm_sum_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) {J : Type*} (S : Finset J)
    (a : J → ℂ) (z : J → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i ∈ S, a i • z i) w = ∑ i ∈ S, a i * hermForm Hm (z i) w := by
  simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]

private lemma hermForm_sum_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) {J : Type*}
    (S : Finset J) (a : J → ℂ) (w : J → Fin g → ℂ) :
    hermForm Hm z (∑ i ∈ S, a i • w i) = ∑ i ∈ S, starRingEnd ℂ (a i) * hermForm Hm z (w i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [hermForm]
  · intro i S hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp only [hermForm, star_add, star_smul, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
    simp [Complex.star_def]

private lemma hermFam_form_apply_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (x : V) : h.form σ x 0 = 0 := by
  have hx := h.add_right σ x 0 0
  rw [add_zero] at hx
  linear_combination -hx

private lemma form_sum_smul_right {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (x : V) {J : Type*} (S : Finset J) (a : J → K) (y : J → V) :
    h.form σ x (∑ i ∈ S, a i • y i) = ∑ i ∈ S, σ (a i) * h.form σ x (y i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [hermFam_form_apply_zero]
  · intro i S hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, h.add_right, h.smul_right, ih]

private lemma form_sum_smul_left {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V)
    (σ : K →+* ℂ) (y : V) {J : Type*} (S : Finset J) (a : J → K) (x : J → V) :
    h.form σ (∑ i ∈ S, a i • x i) y = ∑ i ∈ S, starRingEnd ℂ (σ (a i)) * h.form σ (x i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h.conj_symm σ y, form_sum_smul_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, h.conj_symm]

theorem form_eq {K : Type} [Field K] {n g : ℕ} (h : HermFam K (Fin n → K)) (s : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (r : ℂ)
    (hh : ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = r * hermForm Hm (W j) (W i)) (c c' : Fin n → K) :
    h.form s c c' = r * hermForm Hm (∑ i, s (c' i) • W i) (∑ i, s (c i) • W i) := by
  classical
  have hb : ∀ d : Fin n → K, d = ∑ i, d i • (Pi.single i 1 : Fin n → K) := fun d => by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hb c, hb c']
  rw [form_sum_smul_left]
  simp_rw [form_sum_smul_right, hh, hermForm_sum_smul_left, hermForm_sum_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_diff_eq : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)) (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → F.IsDiffOf F' f M → F.IsDiffOf F g N → ∀ s c c', h'.form s (M c) (M c') = h.form s c (N c') := by
  intro hT hL K _ _ P F P' F' h h' f g M N hh hh' hf hg hl hM hN s c c'
  obtain ⟨Q, ψ, v, u, Hm, χ, W, hQ, hAH, hW, hF⟩ := hh s
  obtain ⟨Q', ψ', v', u', Hm', χ', W', hQ', hAH', hW', hF'⟩ := hh' s
  obtain ⟨-, f₀, hf₀, ef₀, hc₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f hf
  obtain ⟨-, g₀, hg₀, eg₀, hcg₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F g hg
  haveI := hf₀
  haveI := hg₀
  obtain ⟨f₁, hf₁, ef₁⟩ := GlobalTheory.NormHom.exists_monHom_lift hQ.2.1 hQ'.2.1 f₀
  obtain ⟨g₁, hg₁, eg₁⟩ := GlobalTheory.NormHom.exists_monHom_lift hQ.2.1 hQ.2.1 g₀
  obtain ⟨-, -, -, -, tu1, tu2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT Q Q.g u Hm χ hAH
  obtain ⟨-, -, -, -, tu1', tu2', -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT Q' Q'.g u' Hm' χ' hAH'
  obtain ⟨Φ, hΦex, -, hΦ, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g
    u u' tu1' tu2' f₁ hf₁
  obtain ⟨Γ, hΓex, -, hΓ, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g
    u u tu1 tu2 g₁ hg₁
  have e1 : ∀ d : Fin F.P₀.g → K, Φ (∑ i, s (d i) • W i) = ∑ i, s (M d i) • W' i := fun d =>
    map_comb s hQ.2.1 hQ'.2.1 u u' (fun i => F.basis.1 i) (fun i => F'.basis.1 i) hW hW' tu1' ef₁ hΦ
      (fun w hw => hc₀ M hM d w hw)
  have e2 : ∀ d : Fin F.P₀.g → K, Γ (∑ i, s (d i) • W i) = ∑ i, s (N d i) • W i := fun d =>
    map_comb s hQ.2.1 hQ.2.1 u u (fun i => F.basis.1 i) (fun i => F.basis.1 i) hW hW tu1 eg₁ hΓ
      (fun w hw => hcg₀ N hN d w hw)
  have lam1 : LamEq F'.P₀.L f₀ f₀ F.P₀.L g₀ (𝟙 F.P₀.A) :=
    GlobalTheory.CM.lamEq_baseChange _ _ _ P.A P.A P'.A P.A F.P₀.A F.P₀.A F'.P₀.A F.P₀.A F.φ F.φ F'.φ F.φ
      F.fib.2.1.1.w F.fib.2.1.1.w F'.fib.2.1 F.fib.2.1 P'.L P.L F'.P₀.L F.P₀.L P'.isLB P.isLB F'.P₀.isLB
      F.P₀.isLB F'.fib.2.2 F.fib.2.2 f f g (𝟙 _) f₀ f₀ g₀ (𝟙 _) ef₀ ef₀ eg₀ (by simp) hl
  have lam2 : LamEq Q'.L f₁ f₁ Q.L g₁ (𝟙 Q.A) :=
    GlobalTheory.CM.lamEq_baseChange _ _ _ F.P₀.A F.P₀.A F'.P₀.A F.P₀.A Q.A Q.A Q'.A Q.A ψ ψ ψ' ψ
      hQ.2.1.1.w hQ.2.1.1.w hQ'.2.1 hQ.2.1 F'.P₀.L F.P₀.L Q'.L Q.L F'.P₀.isLB F.P₀.isLB Q'.isLB Q.isLB
      hQ'.2.2 hQ.2.2 f₀ f₀ g₀ (𝟙 _) f₁ f₁ g₁ (𝟙 _) ef₁ ef₁ eg₁ (by simp) lam1
  have hweil := GlobalTheory.CM.weilEq_of_lamEq hL ℂ Q Q Q' Q f₁ f₁ g₁ (𝟙 _) hf₁ hf₁ hg₁ inferInstance lam2
  have hherm := (GlobalTheory.T.weilEq_iff_hermForm_eq_complex hT hL Q Q Q' Q u u u' u Hm' Hm χ' χ hAH' hAH f₁ f₁ g₁ (𝟙 _) Φ Φ Γ LinearMap.id
    hΦex hΦex hΓex (fun z => by simp)).1 hweil
  rw [form_eq h' s Hm' W' _ hF' (M c) (M c'), form_eq h s Hm W _ hF c (N c'), ← e1 c, ← e1 c', ← e2 c', hherm]
  rfl

end GlobalTheory.HermHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)) (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → F.IsDiffOf F' f M → F.IsDiffOf F g N → ∀ s c c', h'.form s (M c) (M c') = h.form s c (N c') := by
  first | exact @GlobalTheory.HermHom.form_diff_eq | exact GlobalTheory.HermHom.form_diff_eq | (intros; apply GlobalTheory.HermHom.form_diff_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.PairingScheme

theorem exists_unitOn {K : Type} [CommRing K] (c : Γ(Sp K, ⊤)ˣ) : ∃ z : Kˣ, unitOn z = c := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom c, ?_⟩
  ext
  simp [unitOn]

theorem comp_pow_eq_one {S : Scheme.{0}} {T X A : Over S} [GrpObj X] [GrpObj A] (f : X ⟶ A) [IsMonHom f]
    {x : T ⟶ X} {k : ℕ} (hx : x ^ k = 1) : (x ≫ f) ^ k = 1 := by
  rw [← MonObj.pow_comp, hx, MonObj.one_comp]

theorem pull_pow_eq_one {S : Scheme.{0}} {T T' X : Over S} [GrpObj X] (t : T' ⟶ T)
    {x : T ⟶ X} {k : ℕ} (hx : x ^ k = 1) : (t ≫ x) ^ k = 1 := by
  rw [← MonObj.comp_pow, hx, MonObj.comp_one]

theorem weilIs_iff_of_lamEq : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → ∀ (T : Over (Sp R)) (k : ℕ) (x : T ⟶ X.A) (y : T ⟶ Y.A) (c : Γ(T.left, ⊤)ˣ), 0 < k → x ^ k = 1 → y ^ k = 1 → (Out.WeilIs A.A A.L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs B.A B.L k (x ≫ g₁) (y ≫ g₂) c) := by
  intro hL R _ _ _ X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ hlam T k x y c hk hx hy
  have hN : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  obtain ⟨T₀, x₀, y₀, hx₀, hy₀, huniv, hsep⟩ := GlobalTheory.T.exists_universal_torsion_pair_polAV hL R X Y k hk
  obtain ⟨a, ha, -⟩ := (hL.weil (Sp R) A k T₀).1 _ _ (comp_pow_eq_one f₁ hx₀) (comp_pow_eq_one f₂ hy₀)
  obtain ⟨b, hb, -⟩ := (hL.weil (Sp R) B k T₀).1 _ _ (comp_pow_eq_one g₁ hx₀) (comp_pow_eq_one g₂ hy₀)
  have hab : a = b := by
    apply Units.ext
    refine hsep _ _ fun k' _ _ _ β t => ?_
    have hw := (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL R X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ k' β).1 hlam
    have ha' := CommPairing.weilIs_pull hL.globalFns A.isAb A.isLB t ha
    have hb' := CommPairing.weilIs_pull hL.globalFns B.isAb B.isLB t hb
    obtain ⟨z, hz⟩ := exists_unitOn (K := k') (Units.map t.left.appTop.hom.toMonoidHom a)
    have hx' := pull_pow_eq_one t hx₀
    have hy' := pull_pow_eq_one t hy₀
    rw [← Category.assoc, ← Category.assoc] at ha' hb'
    have h₁ := (hw k (t ≫ x₀) (t ≫ y₀) z hk hx' hy').1 (by rw [hz]; exact ha')
    rw [hz] at h₁
    have h₂ := ((hL.weil (Sp R) B k _).1 _ _ (comp_pow_eq_one g₁ hx') (comp_pow_eq_one g₂ hy')).unique h₁ hb'
    exact congrArg Units.val h₂
  subst hab
  obtain ⟨t, rfl, rfl⟩ := huniv T x y hx hy
  have ha' := CommPairing.weilIs_pull hL.globalFns A.isAb A.isLB t ha
  have hb' := CommPairing.weilIs_pull hL.globalFns B.isAb B.isLB t hb
  rw [← Category.assoc, ← Category.assoc] at ha' hb'
  constructor
  · intro H
    rw [((hL.weil (Sp R) A k _).1 _ _ (comp_pow_eq_one f₁ hx) (comp_pow_eq_one f₂ hy)).unique H ha']
    exact hb'
  · intro H
    rw [((hL.weil (Sp R) B k _).1 _ _ (comp_pow_eq_one g₁ hx) (comp_pow_eq_one g₂ hy)).unique H hb']
    exact ha'

end GlobalTheory.PairingScheme
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairings_eq_of_cubeLBPairingIso : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → ∀ (T : Over (Sp R)) (k : ℕ) (x : T ⟶ X.A) (y : T ⟶ Y.A) (c : Γ(T.left, ⊤)ˣ), 0 < k → x ^ k = 1 → y ^ k = 1 → (Out.WeilIs A.A A.L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs B.A B.L k (x ≫ g₁) (y ≫ g₂) c) := by
  first | exact @GlobalTheory.PairingScheme.weilIs_iff_of_lamEq | exact GlobalTheory.PairingScheme.weilIs_iff_of_lamEq | (intros; apply GlobalTheory.PairingScheme.weilIs_iff_of_lamEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConj
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CurveAdjoint

theorem linear_eq_of_ex {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (G z)) : F = G := by
  have hD : ∀ z, (F - G) z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h1 := u.ex_add (G z) ((F - G) z)
    have e : G z + (F - G) z = F z := by simp
    rw [e, h z] at h1
    exact mul_left_cancel (a := u.ex (G z)) (by rw [_root_.mul_one]; exact h1.symm)
  refine LinearMap.ext fun z => ?_
  have hc : Continuous (fun t : ℝ => (⟨(F - G) ((t : ℂ) • z), hD _⟩ : u.Λ)) :=
    Continuous.subtype_mk ((F - G).continuous_of_finiteDimensional.comp
      (Complex.continuous_ofReal.smul continuous_const)) _
  haveI := u.discrete
  have h2 := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0))
  simp only [Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul, map_zero] at h2
  exact sub_eq_zero.mp h2

theorem exists_scalar {g : ℕ} (hg : g = 1) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : ∃ c : ℂ, ∀ z, F z = c • z := by
  subst hg
  refine ⟨F (fun _ => 1) 0, fun z => ?_⟩
  have hz : z = z 0 • (fun _ : Fin 1 => (1 : ℂ)) := by
    funext i
    rw [Subsingleton.elim i 0]
    simp
  rw [hz, map_smul]
  funext i
  rw [Subsingleton.elim i 0]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem map_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (j : OK H →+* ℂ) (x y : OK H)
    (h : (y : 𝓞 E) = H.bar x) : j y = starRingEnd ℂ (j x) := by
  obtain ⟨-, huniq, ⟨br, hbr, hw, -⟩, hquad, -⟩ := OK_isDedekindDomain_and_projective E H
  have hy : y = br x := Subtype.ext (h.trans (hbr x).symm)
  have hbw : br (wK H) = 1 - wK H := eq_sub_of_add_eq' hw
  obtain ⟨⟨m₁, m₂⟩, hx, -⟩ := huniq x
  have hN : (1 : ℝ) ≤ (((1 + H.d) / 4 : ℕ) : ℝ) := by
    have := H.d_mod
    exact_mod_cast (by omega : 1 ≤ (1 + H.d) / 4)
  have hq := congrArg j hquad
  simp only [j.map_add, j.map_pow, map_natCast j] at hq
  have hz : starRingEnd ℂ (j (wK H)) = 1 - j (wK H) := by
    have e := congrArg Complex.re hq
    have f := congrArg Complex.im hq
    simp [pow_two] at e f
    have ha : (j (wK H)).re = 1 / 2 := by
      rcases eq_or_ne (j (wK H)).im 0 with h0 | h0
      · exfalso
        rw [h0] at e
        nlinarith [sq_nonneg ((j (wK H)).re - 1 / 2)]
      · have h2 : 2 * (j (wK H)).re = 1 := by
          apply mul_left_cancel₀ h0
          linear_combination f
        linarith
    apply Complex.ext <;> simp <;> linarith
  rw [hy, hx]
  simp only [br.map_add, br.map_mul, map_intCast br, hbw, j.map_add, j.map_mul,
    map_intCast j, j.map_sub, j.map_one, map_add (starRingEnd ℂ),
    map_mul (starRingEnd ℂ), map_intCast (starRingEnd ℂ), hz]

theorem lamEq_act_bar : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (a : OAct (OK H) P.A), Function.Injective σ → P.g = 1 → ∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) := by
  intro hT hL E _ _ _ H R _ _ σ P a hσ hg x y hxy
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨Q, φ, hQg, hφ, hLφ⟩ := GlobalTheory.exists_isPolFibre hL.polBaseChange σ P
  haveI : IsCommMonObj Q.A := Q.isAb.comm
  have hQ1 : Q.g = 1 := hQg.trans hg
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, hend, -⟩ := hT Q rig hrig
  have hex : ∀ r : OK H, ∃ c : ℂ, ∃ w' : Q.A ⟶ Q.A, IsMonHom w' ∧ w'.left ≫ φ = φ ≫ (a.act r).left ∧
      ∀ z, u.ex (c • z) = u.ex z ≫ w' := by
    intro r
    haveI := a.hom r
    obtain ⟨w', hw'm, hw'⟩ := GlobalTheory.PairingFibre.exists_hom hφ hφ (a.act r)
    obtain ⟨F, hF⟩ := hend w' hw'm
    obtain ⟨c', hc'⟩ := exists_scalar hQ1 F
    exact ⟨c', w', hw'm, hw', fun z => by rw [← hc' z, hF z]⟩
  choose c w hmon hcomm hlift using hex
  have hcomm' : ∀ r {Z : Scheme.{0}} (h : P.A.left ⟶ Z), (w r).left ≫ φ ≫ h = φ ≫ (a.act r).left ≫ h := by
    intro r Z h
    rw [← Category.assoc, hcomm r, Category.assoc]
  have huniq : ∀ r (c' : ℂ) (w' : Q.A ⟶ Q.A), w'.left ≫ φ = φ ≫ (a.act r).left →
      (∀ z, u.ex (c' • z) = u.ex z ≫ w') → c' = c r := by
    intro r c' w' hw' hl
    have hww : w' = w r := by
      apply Over.OverMorphism.ext
      apply hφ.1.hom_ext
      · rw [hw', hcomm r]
      · rw [Over.w w', Over.w (w r)]
    subst hww
    have he := linear_eq_of_ex u (c' • LinearMap.id) (c r • LinearMap.id) (fun z => by
      simp only [LinearMap.smul_apply, LinearMap.id_apply]
      rw [hl, hlift r])
    have he' := congrFun (LinearMap.congr_fun he (fun _ => 1)) ⟨0, by omega⟩
    simpa using he'
  have hone : c 1 = 1 :=
    (huniq 1 1 (𝟙 Q.A) (by rw [a.one]; simp) (fun z => by simp)).symm
  have hmul : ∀ r s, c (r * s) = c r * c s := by
    intro r s
    refine (huniq (r * s) (c r * c s) (w r ≫ w s) ?_ ?_).symm
    · simp only [a.mul, Over.comp_left, Category.assoc, hcomm, hcomm']
    · intro z
      rw [← Category.assoc, ← hlift r z, ← hlift s (c r • z), smul_smul, _root_.mul_comm]
  have hadd : ∀ r s, c (r + s) = c r + c s := by
    intro r s
    refine (huniq (r + s) (c r + c s) (w r * w s) ?_ ?_).symm
    · let jm : Over.mk (Q.A.hom ≫ spMap σ) ⟶ P.A := Over.homMk φ hφ.1.w
      have h := hφ.2 Q.A (w r) (w s) (jm ≫ a.act r) (jm ≫ a.act s) (by simp [jm, hcomm r]) (by simp [jm, hcomm s])
      rw [← h, ← MonObj.comp_mul, ← a.add, Over.comp_left]
      simp [jm]
    · intro z
      rw [add_smul, u.ex_add, hlift r, hlift s, MonObj.comp_mul]
  let j : OK H →+* ℂ := RingHom.mk' ⟨⟨c, hone⟩, hmul⟩ hadd
  have hj : c y = starRingEnd ℂ (c x) := map_bar H j x y hxy
  have hQ : WeilEq Q.L (w x) (𝟙 Q.A) Q.L (𝟙 Q.A) (w y) (𝟙 (Sp ℂ)) := by
    rw [GlobalTheory.T.weilEq_iff_hermForm_eq_complex hT hL Q Q Q Q u u u u Hm Hm χ χ hAH hAH (w x) (𝟙 Q.A) (𝟙 Q.A) (w y)
      (c x • LinearMap.id) LinearMap.id LinearMap.id (c y • LinearMap.id)
      (fun z => by simpa using hlift x z) (fun z => by simp) (fun z => by simp) (fun z => by simpa using hlift y z)]
    intro z v
    simp [hermForm, hj, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, star_smul]
  have hP : WeilEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) (spMap σ) := by
    have hb := (GlobalTheory.PairingFibre.weilEq_iff hφ hφ hφ hφ P.isLB P.isLB Q.isLB Q.isLB (LBIso.symm hLφ) (LBIso.symm hLφ)
      (f₁ := a.act x) (f₂ := 𝟙 P.A) (g₁ := 𝟙 P.A) (g₂ := a.act y)
      (f₁' := w x) (f₂' := 𝟙 Q.A) (g₁' := 𝟙 Q.A) (g₂' := w y)
      (hcomm x) (by simp) (by simp) (hcomm y) (𝟙 (Sp ℂ))).mp hQ
    rwa [Category.id_comp] at hb
  exact (GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hL R P P P P (a.act x) (𝟙 P.A) (𝟙 P.A) (a.act y)
    (a.hom x) inferInstance inferInstance (a.hom y) ℂ σ).2 inferInstance hσ hP

end GlobalTheory.CurveAdjoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmActionPolarisedCurveAdjointConjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDedekindDomain R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (a : OAct (OK H) P.A), Function.Injective σ → P.g = 1 → ∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq P.L (a.act x) (𝟙 P.A) P.L (𝟙 P.A) (a.act y) := by
  first | exact @GlobalTheory.CurveAdjoint.lamEq_act_bar | exact GlobalTheory.CurveAdjoint.lamEq_act_bar | (intros; apply GlobalTheory.CurveAdjoint.lamEq_act_bar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MemLieVectorLineIdealIffMemLieLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MemLieVectorLineIdealIffMemLieLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isVecLine_mem_iff_mem_lieLat : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ∀ c : K, c ∈ ℓ.I ↔ (Pi.single i c : Fin x.P.g → K) ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  intro K _ _ A x φ hf i ℓ h c
  obtain ⟨hgood, hp, -⟩ := h
  choose M cl hM hcl hc using hp
  obtain ⟨h1, -, h3⟩ := local_global_ideal_lattice K
  refine (h1 ℓ.I cl hgood.1 hcl c).trans (Iff.trans ?_ (h3 _ _ _).symm)
  refine forall_congr' fun p => ?_
  refine (hc p c).symm.trans (Iff.trans ?_ (isModelAt_integral_iff_mem_lieLat K A x φ hf p (M p) (hM p) _))
  have e : (Pi.single i c : Fin x.P.g → K) = c • (Pi.single i 1 : Fin x.P.g → K) := by
    rw [← Pi.single_smul', smul_eq_mul, _root_.mul_one]
  rw [e, Matrix.smul_vecMul]

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MemLieVectorLineIdealIffMemLieLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lieVector_line_ideal_iff_mem_lie_lattice : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ∀ c : K, c ∈ ℓ.I ↔ (Pi.single i c : Fin x.P.g → K) ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  first | exact @GlobalTheory.LamF.isVecLine_mem_iff_mem_lieLat | exact GlobalTheory.LamF.isVecLine_mem_iff_mem_lieLat | (intros; apply GlobalTheory.LamF.isVecLine_mem_iff_mem_lieLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurveHomFamilyToFibreAtPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurveHomFamilyToFibreAtPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem two_mul_sub_one_sq_of_ringHom (τ : OK H →+* ℂ) : (2 * τ (wK H) - 1) ^ 2 = -(H.d : ℂ) := by
  have h : (2 * wK H - 1) ^ 2 = -(H.d : OK H) := by
    apply Subtype.ext
    have e : 2 * H.w0 - 1 = H.rt := by rw [H.two_weight_eq_one_add_root]; ring
    have := H.rt_sq
    rw [← e] at this
    have e2 : ((2 : OK H) : 𝓞 E) = 2 := rfl
    simpa [wK, e2] using this
  have := congrArg (fun x : OK H => τ x) h
  set_option synthInstance.maxHeartbeats 200000 in
    simpa only [map_pow, map_sub, map_mul, map_ofNat, map_neg, map_natCast, map_intCast, map_one] using this

theorem exists_hermitianPairing_eq_im_mul_pureType {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty Pe) {ω : ℂ} {x : D.La} (hx : x ∈ PureType.lat hP (2 * ω - 1)) (h0 : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ((D.EF (H.w0 • x) x : ℤ) : ℝ) = ω.im * r := by
  obtain ⟨Hm, hH, hpos, hEF⟩ := hP.2.2.2.2
  have hw0 : Pe (H.w0 • x) = ω • Pe x := by
    have e : (2 : ℂ) • Pe (H.w0 • x) = (2 : ℂ) • ω • Pe x := by
      rw [two_smul, ← map_add (f := _), ← add_smul, ← two_mul, H.two_weight_eq_one_add_root, add_smul, one_smul, map_add (f := _),
        PureType.period_rt_smul hP hx]
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact smul_right_injective _ two_ne_zero e
  have hne : Pe x ≠ 0 := fun h => h0 (hP.2.1 (by rw [h, map_zero]))
  refine ⟨_, hpos _ hne, ?_⟩
  have := PureTypeVector.hermForm_smul_smul Hm ω 1 (Pe x) (Pe x)
  rw [one_smul] at this
  rw [← hEF, hw0, this]
  simp [PureTypeVector.hermForm_self_im hH]

theorem exists_isFam_complex : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (ω : ℂ) (C : Ell H ℂ ω) (u₀ : HolUnif C.P.A C.P.L C.P.g) (c : ℂ) (T : PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t (FU.u i Pe)) (ε : ℤˣ) (h : (FU.Di i).La → (FU.Di i).La → OK H), PureType.IsThetaUnif u₀ → c ≠ 0 → PureType.IsQuadLattice u₀.Λ H.d c → 0 < ((ε : ℤ) : ℝ) * ω.im → IsKForm (FU.Di i) ε h →
  ∃ ψ : PureType.lat hP (2 * ω - 1) → (C.P.A ⟶ T.t.G), IsFam C T h _ ψ ∧ ∀ a (z : ℂ), (u₀.ex (fun _ => c * z) ≫ ψ a).left ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  intro hT hL E _ _ _ H D l Xo g ty FU i Pe hP ω C u₀ c T m ε h hu hc hΛ hε hh
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.cmCurve_lie_character_of_adjoinGenerator E H ℂ ω C
  have hρ : (2 * ω - 1) ^ 2 = -(H.d : ℂ) := hτ ▸ two_mul_sub_one_sq_of_ringHom τ
  obtain ⟨φ, hφ, hφe⟩ := PureType.exists_isHomFamily_complex hT hL.weil FU i hP m u₀ C.dim hu hc hΛ hρ
  refine ⟨φ, GlobalTheory.T.isCMPairingFamily_of_polarisationDiagonal_complex hT hL E H ω C _ ε h T _ φ hh (fun x hx h0 => ?_) (hφ _ (C.basis.1 0)), fun a z => ?_⟩
  · obtain ⟨r, hr, e⟩ := exists_hermitianPairing_eq_im_mul_pureType hP hx h0
    have : (0 : ℝ) < ((ε : ℤ) : ℝ) * ((FU.Di i).EF (H.w0 • x) x : ℤ) := by
      rw [e, ← _root_.mul_assoc]
      exact mul_pos hε hr
    exact_mod_cast this
  · rw [Over.comp_left, Category.assoc]
    exact hφe a z

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurveHomFamilyToFibreAtPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmCurve_homFamily_to_fibre_at_period : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (ω : ℂ) (C : Ell H ℂ ω) (u₀ : HolUnif C.P.A C.P.L C.P.g) (c : ℂ) (T : PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t (FU.u i Pe)) (ε : ℤˣ) (h : (FU.Di i).La → (FU.Di i).La → OK H), PureType.IsThetaUnif u₀ → c ≠ 0 → PureType.IsQuadLattice u₀.Λ H.d c → 0 < ((ε : ℤ) : ℝ) * ω.im → IsKForm (FU.Di i) ε h →
  ∃ ψ : PureType.lat hP (2 * ω - 1) → (C.P.A ⟶ T.t.G), IsFam C T h _ ψ ∧ ∀ a (z : ℂ), (u₀.ex (fun _ => c * z) ≫ ψ a).left ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  first | exact @GlobalTheory.CM.exists_isFam_complex | exact GlobalTheory.CM.exists_isFam_complex | (intros; apply GlobalTheory.CM.exists_isFam_complex <;> assumption)
end
end
