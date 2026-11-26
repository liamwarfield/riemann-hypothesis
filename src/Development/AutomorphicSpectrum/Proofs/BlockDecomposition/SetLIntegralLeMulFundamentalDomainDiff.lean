module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsAdicComplete
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLAdicClosed
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.lift_levelP_alt₂
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFundamentalDomainDiff
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Unfolding

theorem setLIntegral_le_mul_fundamentalDomain_diff {G : Type} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
    (F S T : Set G) (hF : IsFundamentalDomain Γ F μ) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h : G → ℝ≥0∞) (hh : Measurable h)
    (hinv : ∀ γ ∈ Γ, ∀ x, h (γ * x) = h x) (N : ℕ)
    (hN : ∀ x, {γ : Γ | (γ : G) * x ∈ S}.encard ≤ N)
    (hST : ∀ γ ∈ Γ, ∀ x, γ * x ∈ S → x ∉ T) :
    ∫⁻ x in S, h x ∂μ ≤ N * ∫⁻ x in F \ T, h x ∂μ := by
  have hmeas : ∀ γ : Γ, Measurable (fun x : G => S.indicator h (γ • x)) := fun γ =>
    (hh.indicator hS).comp (measurable_const_smul γ)
  have h1 : ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := by
    rw [← lintegral_indicator hS]
    exact hF.lintegral_eq_tsum'' _
  have hpt : ∀ x, ∑' γ : Γ, S.indicator h (γ • x) ≤ N * Tᶜ.indicator h x := by
    intro x
    by_cases hx : x ∈ T
    · have hz : ∀ γ : Γ, S.indicator h (γ • x) = 0 := fun γ => by
        apply Set.indicator_of_notMem
        intro hmem
        exact hST γ γ.2 x (by simpa [Subgroup.smul_def] using hmem) hx
      simp [hz]
    · have hrew : ∀ γ : Γ, S.indicator h (γ • x) =
          ({γ : Γ | (γ : G) * x ∈ S}).indicator (fun _ => h x) γ := fun γ => by
        by_cases hg : (γ : G) * x ∈ S
        · rw [Set.indicator_of_mem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_mem hg, hinv γ γ.2 x]
        · rw [Set.indicator_of_notMem (s := {γ : Γ | (γ : G) * x ∈ S}) (by exact hg),
            Subgroup.smul_def, smul_eq_mul, Set.indicator_of_notMem hg]
      simp_rw [hrew]
      rw [← tsum_subtype, ENNReal.tsum_set_const,
        Set.indicator_of_mem (show x ∈ Tᶜ from hx)]
      gcongr
      have hc := ENat.toENNReal_le.mpr (hN x)
      simpa using hc
  calc ∫⁻ x in S, h x ∂μ = ∑' γ : Γ, ∫⁻ x in F, S.indicator h (γ • x) ∂μ := h1
    _ = ∫⁻ x in F, ∑' γ : Γ, S.indicator h (γ • x) ∂μ :=
        (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
    _ ≤ ∫⁻ x in F, (N : ℝ≥0∞) * Tᶜ.indicator h x ∂μ := lintegral_mono hpt
    _ = N * ∫⁻ x in F, Tᶜ.indicator h x ∂μ :=
        lintegral_const_mul _ (hh.indicator hT.compl)
    _ = N * ∫⁻ x in F \ T, h x ∂μ := by
        rw [setLIntegral_indicator hT.compl, Set.inter_comm, Set.diff_eq]

end GlobalTheory.CompanionTheory.Unfolding
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassReductionCompatible
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.FirstChernClassFactorial

theorem pow_dvd_factorial_mul (l : ℕ) (hl : 0 < l) (n : ℕ) : l ^ n ∣ (l * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (l * n).factorial * l.factorial ∣ (l * n + l).factorial :=
      Nat.factorial_mul_factorial_dvd_factorial_add _ _
    have h2 : l ∣ l.factorial := Nat.dvd_factorial hl le_rfl
    rw [pow_succ, Nat.mul_succ]
    exact (mul_dvd_mul ih h2).trans h1

theorem factorial_acr {l : ℕ} [Fact l.Prime] (n k : ℕ) (hk : l * n ≤ k) : (k.factorial : (PAlg.base l).Acr n) = 0 := by
  obtain ⟨a, ha⟩ := (pow_dvd_factorial_mul l (Fact.out : l.Prime).pos n).trans (Nat.factorial_dvd_factorial hk)
  rw [ha, Nat.cast_mul, Nat.cast_pow, (PAlg.base l).pow_l_acr n, zero_mul]

theorem dlog_eq_of_factorial {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) {N N' : ℕ} (h : N ≤ N')
    (hf : ∀ k, N ≤ k → (k.factorial : A) = 0) (v : A) : B.dlog δ N' v = B.dlog δ N v := by
  unfold B.dlog
  refine (Finset.sum_subset (Finset.range_mono h) fun k _ hk => ?_).symm
  rw [hf k (by simpa using hk)]
  simp


open B in
theorem isFirstChern_base_change {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b b' : Base}
    {ht : b.t = 1} {ht' : b'.t = 1} {κ : O →+* b.R ⧸ b.I} {κ' : O →+* b'.R ⧸ b'.I}
    (σ : b.R →+* b'.R) (hp : b.p = b'.p) (hI : IsDPMorphism b.γ b'.γ σ) (τ : b.R ⧸ b.I →+* b'.R ⧸ b'.I)
    (hτ : τ.comp κ = κ') (hτσ : ∀ r, τ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (σ r))
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (c' : Λ →+* b'.R) (hc : ∀ a, σ (c a) = c' (RingHom.id Λ a))
    (D : E.LineData X) {N N' : ℕ} (hN : N ≤ N') (hf : ∀ k, N ≤ k → (k.factorial : b'.R) = 0)
    (y : CH.H (OM ((schFn q).cr b ht κ) c) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := b) (ht := ht) (κ := κ) D c N' y) :
    IsFirstChernClassOfLineBundle (q := q) (b := b') (ht := ht') (κ := κ') D c' N
      ((omMor (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc).pull 2 y) := by
  intro C _ G Lf
  let mm := omMor (c := c) (c' := c') (crMor (F := schFn q) (F' := schFn q) (b := b) (b' := b') (ht := ht) (ht' := ht') σ hp hI
        (basePt (schFn q) τ hτ) fun _ y r => congrArg y.1.1 (hτσ r)) (RingHom.id Λ) hc
  let G' : C ⥤ Thick ((schFn q).cr b ht κ) := G ⋙ mm.G
  let Lf' : CLift G' D := { p := Lf.p, hp := Lf.hp, w := Lf.w, hw := Lf.hw }
  obtain ⟨hz', hcl⟩ := hy C G' Lf'
  let m4 : CH.Mor (G' ⋙ OM _ c) (G ⋙ OM _ c') (RingHom.id _) :=
    { G := 𝟭 C, τ := fun T => mm.τ (G.obj T), nat := fun φ x => mm.nat (G.map φ) x }
  have hE : m4.pullC 2 (Lf'.coc c N') = Lf.coc c' N := by
    funext s
    refine dlog_eq_of_factorial (G.obj (s.obj (Fin.last 2))).δ hN (fun j hj => ?_) _
    have := congrArg (G.obj (s.obj (Fin.last 2))).i (hf j hj)
    rw [map_natCast, map_zero] at this
    exact this
  have hz : CH.d _ 2 (Lf.coc c' N) = 0 := by
    rw [← hE, m4.d_pullC, hz', map_zero]
  refine ⟨hz, ?_⟩
  have h1 : (CH.Mor.restrict (OM _ c') G).pull 2 (mm.pull 2 y) =
      m4.pull 2 ((CH.Mor.restrict (OM _ c) G').pull 2 y) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rfl
  refine Eq.trans ?_ h1.symm
  rw [← hcl]
  have key : ∀ (z : CH.Cn (G ⋙ OM _ c') 2) (h : CH.d _ 2 z = 0), z = Lf.coc c' N →
      (CH.cx _).cls z h = (CH.cx _).cls (Lf.coc c' N) hz := by
    rintro _ _ rfl
    rfl
  exact (key (m4.pullC 2 (Lf'.coc c N')) (by rw [m4.d_pullC, hz', map_zero]) hE).symm


open B in
theorem chern_class_reduction_compatible {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l) (k : Bool)
    (D : E.LineData X) (n : ℕ) (y : B.Hc (schFn q) κ k (n + 1) 2)
    (hy : IsFirstChernClassOfLineBundle (q := q) (b := bs l k (n + 1)) (ht := rfl) (κ := κb κ k (n + 1)) D ((PAlg.base l).cris (n + 1)) (l * (n + 1)) y) :
    IsFirstChernClassOfLineBundle (q := q) (b := bs l k n) (ht := rfl) (κ := κb κ k n) D ((PAlg.base l).cris n) (l * n)
      (redHc (schFn q) κ k n.le_succ 2 y) :=
  isFirstChern_base_change (b := bs l k (n + 1)) (b' := bs l k n) ((PAlg.base l).red n.le_succ) rfl (dd_red k _ n.le_succ)
    (Ideal.quotientMap _ _ (red_le k n.le_succ)) (red_κb κ k n.le_succ) (fun _ => rfl) _ _ (red_cris _ n.le_succ) D
    (Nat.mul_le_mul_left l n.le_succ) (fun j hj => factorial_acr n j hj) y hy

theorem exists_C1H {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (D : E.LineData M.X)
    (hD : sSup (𝒱D D) = ⊤) : ∃ x : (M.HS false 2).lim, B.IsFirstChernFamily M.p D (okToOC l K) false x.1 := by
  have ex : ∀ n, ∃! x, B.IsFirstChernClassOfLineBundle (q := M.p) (b := B.bs l false n) (ht := rfl) (κ := B.κb (okToOC l K) false n) D
      ((PAlg.base l).cris n) (l * n) x := fun n =>
    GlobalTheory.T.existsUnique_chern_class_nilpotent_base (B.DD false (PAlg.base l) n) l (Fact.out : l.Prime).ne_zero M.p (B.κb (okToOC l K) false n) D hD
      ((PAlg.base l).cris n) (l * n) (factorial_acr n _ le_rfl)
  choose x hx hu using ex
  refine ⟨⟨x, fun n => ?_⟩, hx⟩
  exact hu n _ (chern_class_reduction_compatible M.p (okToOC l K) false D n (x (n + 1)) (hx (n + 1)))

end GlobalTheory.CompanionTheory.FirstChernClassFactorial
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechCoverCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechCoverCompatible
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

private theorem rs_rs' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (z : ↑(X.presheaf.obj (Opposite.op U))) : rs X h₂ (rs X h₁ z) = rs X (h₂.trans h₁) z := by
  simp only [rs]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem congr_secMulOn {X X' : Scheme.{0}} {π : X ⟶ X'} {N : LB X} {N' : LB X'}
    (v : LB.Iso N (N'.pull π)) (hN : N.IsLB) (hN' : N'.IsLB) (hv : v.IsGen) {a b c : ℤ}
    (h : a + b = c) {V : X.Opens} {V' : X'.Opens} (e : V ≤ π ⁻¹ᵁ V')
    (x : SecOn (pw N' a) V') (y : SecOn (pw N' b) V') (s : SecOn (pw N a) V)
    (t : SecOn (pw N b) V)
    (hs : SecOn.congr (isLB_pw hN a) (LB.isLB_pull (isLB_pw hN' a) π) (pullPow v a)
      (pullPow_isGen v a hv) V s = SecOn.pullLE (pw N' a) π V' V e x)
    (ht : SecOn.congr (isLB_pw hN b) (LB.isLB_pull (isLB_pw hN' b) π) (pullPow v b)
      (pullPow_isGen v b hv) V t = SecOn.pullLE (pw N' b) π V' V e y) :
    SecOn.congr (isLB_pw hN c) (LB.isLB_pull (isLB_pw hN' c) π) (pullPow v c)
      (pullPow_isGen v c hv) V (secMulOn h s t) =
      SecOn.pullLE (pw N' c) π V' V e (secMulOn h x y) := by
  subst h
  classical
  have hMc : ((pw N' (a + b)).pull π).IsLB := LB.isLB_pull (isLB_pw hN' (a + b)) π
  have key : ∀ (p : ((pw N' (a + b)).pull π).ι) (q : N.ι) {O : X.Opens}
      (hp : O ≤ V ⊓ ((pw N' (a + b)).pull π).U p)
      (hq : O ≤ V ⊓ (pw N (a + b)).U q) (hpq : O ≤ ((pw N' (a + b)).pull π).U p ⊓ (pw N (a + b)).U q),
      rs X hp (GlobalTheory.LB.coord (SecOn.congr (isLB_pw hN (a + b)) (LB.isLB_pull (isLB_pw hN' (a + b)) π)
        (pullPow v (a + b)) (pullPow_isGen v (a + b) hv) V (secMulOn rfl s t)) p) =
      rs X hp (GlobalTheory.LB.coord (SecOn.pullLE (pw N' (a + b)) π V' V e (secMulOn rfl x y)) p) := by
    intro p q O hp hq hpq
    have ha := SecOn.coord_congr (isLB_pw hN a) (LB.isLB_pull (isLB_pw hN' a) π) (pullPow v a)
      (pullPow_isGen v a hv) s p q hp hq hpq
    have hb := SecOn.coord_congr (isLB_pw hN b) (LB.isLB_pull (isLB_pw hN' b) π) (pullPow v b)
      (pullPow_isGen v b hv) t p q hp hq hpq
    rw [hs, SecOn.coord_pullLE π e x p] at ha
    rw [ht, SecOn.coord_pullLE π e y p] at hb
    rw [SecOn.coord_congr (isLB_pw hN (a + b)) (LB.isLB_pull (isLB_pw hN' (a + b)) π) (pullPow v (a + b))
      (pullPow_isGen v (a + b) hv) _ p q hp hq hpq, SecOn.coord_pullLE π e (secMulOn rfl x y) p,
      coord_secMulOn, coord_secMulOn rfl x y (p PUnit.unit)]
    erw [map_mul, map_mul, map_mul, ha, hb]
    dsimp only [pullPow]
    erw [zpow_add, Units.val_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _
  have hcov : V ≤ ⨆ a' : ((pw N' (a + b)).pull π).ι × N.ι, V ⊓ ((pw N' (a + b)).pull π).U a'.1 ⊓ N.U a'.2 := by
    intro z hz
    have h1 : z ∈ (⨆ i, ((pw N' (a + b)).pull π).U i) := by rw [hMc.cover]; trivial
    have h2 : z ∈ (⨆ i, N.U i) := by rw [hN.cover]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at h1 h2 ⊢
    obtain ⟨p, hp⟩ := h1
    obtain ⟨q, hq⟩ := h2
    exact ⟨(p, q), ⟨⟨hz, hp⟩, hq⟩⟩
  refine SecOn.ext_of_cover
    (fun a' : ((pw N' (a + b)).pull π).ι × N.ι => V ⊓ ((pw N' (a + b)).pull π).U a'.1 ⊓ N.U a'.2)
    (fun a' => inf_le_left.trans inf_le_left) hcov ?_
  intro a'
  apply (SecOn.chart hMc a'.1 (inf_le_left.trans inf_le_right)).injective
  rw [SecOn.chart_apply, SecOn.chart_apply, SecOn.coord_restrict, SecOn.coord_restrict, rs_rs', rs_rs']
  exact key a'.1 a'.2 _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)

private theorem secOnR_linEquiv_symm_of {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {L M : LB X} {V : X.Opens} (φ : SecOn L V ≃ₗ[↑(X.presheaf.obj (Opposite.op V))] SecOn M V) (m : SecOn M V) :
    (SecOnR.linEquiv f φ).symm (SecOnR.of f M V m) = SecOnR.of f L V (φ.symm m) := by
  rw [LinearEquiv.symm_apply_eq, SecOnR.linEquiv_of, LinearEquiv.apply_symm_apply]

theorem red_secMulOn : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a b c : ℤ) (h : a + b = c) (e : ℕ) (S : Finset ι) (x : SecOn (pw (N (e + 1)) a) (D (e + 1) S)) (y : SecOn (pw (N (e + 1)) b) (D (e + 1) S)), red I Y N D β hβ v hN hDβ c e S (SecOnR.of _ _ _ (secMulOn h x y)) = SecOnR.of _ _ _ (secMulOn h ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ x))) ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ b e S (SecOnR.of _ _ _ y)))) := by
  intro R _ I Y β hβ N v hN ι D hDβ a b c h e S x y
  simp only [red, redL, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, SecOnR.pull_of,
    secOnR_linEquiv_symm_of, LinearEquiv.symm_apply_apply]
  refine congrArg (SecOnR.of _ _ _) ?_
  rw [LinearEquiv.symm_apply_eq]
  exact (congr_secMulOn (v e) (hN e).1 (hN (e + 1)).1 (hN e).2 h (hDβ e S) x y _ _
    (LinearEquiv.apply_symm_apply _ _) (LinearEquiv.apply_symm_apply _ _)).symm

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechCoverCompatibleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_cech_cover_compatible : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a b c : ℤ) (h : a + b = c) (e : ℕ) (S : Finset ι) (x : SecOn (pw (N (e + 1)) a) (D (e + 1) S)) (y : SecOn (pw (N (e + 1)) b) (D (e + 1) S)), red I Y N D β hβ v hN hDβ c e S (SecOnR.of _ _ _ (secMulOn h x y)) = SecOnR.of _ _ _ (secMulOn h ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ x))) ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ b e S (SecOnR.of _ _ _ y)))) := by
  exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.red_secMulOn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundOfNatDegree
open Polynomial

namespace GlobalTheory.CompanionTheory.LinRec

noncomputable def shift : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun u := fun i => u (i + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma shift_apply (u : ℕ → ℂ) (i : ℕ) : shift u i = u (i + 1) := rfl

lemma shift_pow (j : ℕ) (u : ℕ → ℂ) (i : ℕ) : (shift ^ j) u i = u (i + j) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, shift_apply]
    rfl

lemma aeval_shift (p : ℂ[X]) (u : ℕ → ℂ) (i : ℕ) :
    aeval shift p u i = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, shift_pow, smul_eq_mul]

lemma aeval_diff (q : ℂ[X]) (z : ℂ) (u : ℕ → ℂ) (hu : aeval shift ((X - C z) * q) u = 0) :
    aeval shift q (fun i => u (i + 1) - z * u i) = 0 := by
  have h : aeval shift (X - C z : ℂ[X]) u = fun i => u (i + 1) - z * u i := by
    funext i
    simp [aeval_X, aeval_C, shift_apply, Module.algebraMap_end_apply]
  rw [← h, ← Module.End.mul_apply, ← map_mul, mul_comm]
  exact hu

lemma geom_step (z : ℂ) (κ c M : ℝ) (hz : ‖z‖ < Real.exp κ) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (u : ℕ → ℂ) (h0 : ‖u 0‖ ≤ M)
    (hv : ∀ i : ℕ, ‖u (i + 1) - z * u i‖ ≤ c * Real.exp (κ * i) * M) (i : ℕ) :
    ‖u i‖ ≤ (1 + c / (Real.exp κ - ‖z‖)) * Real.exp (κ * i) * M := by
  have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hz
  set D : ℝ := 1 + c / (Real.exp κ - ‖z‖) with hDdef
  have hD1 : 1 ≤ D := by
    have : 0 ≤ c / (Real.exp κ - ‖z‖) := div_nonneg hc hpos.le
    linarith
  have hD : ‖z‖ * D + c ≤ D * Real.exp κ := by
    have : D * (Real.exp κ - ‖z‖) = (Real.exp κ - ‖z‖) + c := by
      rw [hDdef]; field_simp
    nlinarith
  induction i with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    nlinarith
  | succ i ih =>
    have hE : 0 < Real.exp (κ * i) := Real.exp_pos _
    have h1 : ‖u (i + 1)‖ ≤ ‖z‖ * ‖u i‖ + ‖u (i + 1) - z * u i‖ := by
      have : u (i + 1) = z * u i + (u (i + 1) - z * u i) := by ring
      calc ‖u (i + 1)‖ = ‖z * u i + (u (i + 1) - z * u i)‖ := by rw [← this]
        _ ≤ ‖z * u i‖ + ‖u (i + 1) - z * u i‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul]
    have hexp : Real.exp (κ * ((i + 1 : ℕ) : ℝ)) = Real.exp (κ * i) * Real.exp κ := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    have hEM : 0 ≤ Real.exp (κ * i) * M := by positivity
    calc ‖u (i + 1)‖ ≤ ‖z‖ * (D * Real.exp (κ * i) * M) + c * Real.exp (κ * i) * M :=
          h1.trans (add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg _)) (hv i))
      _ = (‖z‖ * D + c) * (Real.exp (κ * i) * M) := by ring
      _ ≤ (D * Real.exp κ) * (Real.exp (κ * i) * M) := mul_le_mul_of_nonneg_right hD hEM
      _ = _ := by ring

theorem bound_of_natDegree (n : ℕ) : ∀ (p : ℂ[X]) (κ : ℝ), p.Monic → p.natDegree = n →
    (∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℕ → ℂ) (M : ℝ), aeval shift p u = 0 →
      (∀ j < n, ‖u j‖ ≤ M) → 0 ≤ M → ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  induction n with
  | zero =>
    intro p κ hp hd _
    refine ⟨0, le_rfl, fun u M hu _ _ i => ?_⟩
    have hp1 : p = 1 := by
      have h1 : p.coeff 0 = 1 := by
        have h2 := hp.coeff_natDegree
        rwa [hd] at h2
      rw [eq_C_of_natDegree_eq_zero hd, h1, C_1]
    subst hp1
    have hu0 : u = 0 := by simpa using hu
    simp [hu0]
  | succ n ih =>
    intro p κ hp hd hr
    obtain ⟨z, hz⟩ : ∃ z, p.IsRoot z := IsAlgClosed.exists_root p (by
      intro h0
      have : p.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h0.le
      omega)
    have hzlt := hr z hz
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hz
    have hq : q.Monic := (monic_X_sub_C z).of_mul_monic_left hp
    have hqd : q.natDegree = n := by
      rw [(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C] at hd
      omega
    obtain ⟨C', hC', hB⟩ := ih q κ hq hqd fun w hw => hr w (by
      have hw' : eval w q = 0 := hw
      simp [IsRoot, hw'])
    have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hzlt
    have hc : 0 ≤ C' * (1 + ‖z‖) := by positivity
    refine ⟨1 + C' * (1 + ‖z‖) / (Real.exp κ - ‖z‖), by positivity, fun u M hu hM hM0 i => ?_⟩
    refine geom_step z κ _ M hzlt hc hM0 u (hM 0 (Nat.succ_pos n)) (fun i => ?_) i
    have hb := hB (fun i => u (i + 1) - z * u i) ((1 + ‖z‖) * M) (aeval_diff q z u hu)
      (fun j hj => ?_) (by positivity) i
    · calc ‖u (i + 1) - z * u i‖ ≤ C' * Real.exp (κ * i) * ((1 + ‖z‖) * M) := hb
        _ = _ := by ring
    · calc ‖u (j + 1) - z * u j‖ ≤ ‖u (j + 1)‖ + ‖z * u j‖ := norm_sub_le _ _
        _ = ‖u (j + 1)‖ + ‖z‖ * ‖u j‖ := by rw [norm_mul]
        _ ≤ M + ‖z‖ * M := add_le_add (hM _ (by omega))
            (mul_le_mul_of_nonneg_left (hM _ (by omega)) (norm_nonneg _))
        _ = _ := by ring

theorem recBound : PositivityTheory.Rg.Rs.An.RecBound := by
  intro p κ hp hr
  obtain ⟨C, hC, h⟩ := bound_of_natDegree _ p κ hp rfl hr
  refine ⟨C, hC, fun u M hu hM hM0 i => h u M ?_ hM hM0 i⟩
  funext i
  rw [aeval_shift]
  exact hu i

end GlobalTheory.CompanionTheory.LinRec
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UpdateLeUpdate
noncomputable section

open Polynomial
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.Rs.An

namespace GlobalTheory.CompanionTheory.AnBoot

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem sr_eq_zero (x : Fin n → ℝ) {r : ℕ} (h : ¬ (0 < r ∧ r < n)) : sr x r = 0 := by
  unfold sr
  rw [dite_eq_right h]

theorem bnd_mono {φ : AdelicGLn.AdelicGL K n → ℂ} {m m' : ℕ → ℝ}
    (hm : ∀ r, 0 < r → r < n → m r ≤ m' r) (h : Bnd φ m) : Bnd φ m' := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := h ω hω hB t₀ Q hQ
  refine ⟨max C 0 * Real.exp (∑ r ∈ Finset.range n,
    (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)), ?_⟩
  intro b hb x hx q hq
  have h1 := hC b hb x hx q hq
  have hs : ∑ r ∈ Finset.range n, m r * sr x r ≤
      (∑ r ∈ Finset.range n, (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
        ∑ r ∈ Finset.range n, m' r * sr x r := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    by_cases hr : 0 < r ∧ r < n
    · rw [if_pos hr]
      have := mul_le_mul_of_nonneg_left (hx r) (sub_nonneg.2 (hm r hr.1 hr.2))
      nlinarith
    · rw [if_neg hr, sr_eq_zero x hr]
      simp
  calc ‖φ (b * tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) := h1
    _ ≤ max C 0 * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp ((∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) +
            ∑ r ∈ Finset.range n, m' r * sr x r) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hs) (le_max_right _ _)
    _ = max C 0 * Real.exp (∑ r ∈ Finset.range n,
          (m' r - m r) * (if 0 < r ∧ r < n then t₀ else 0)) *
            Real.exp (∑ r ∈ Finset.range n, m' r * sr x r) := by
        rw [Real.exp_add, mul_assoc]

theorem bnd_add {f g : AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ} (hf : Bnd f m) (hg : Bnd g m) :
    Bnd (fun y => f y + g y) m := by
  intro ω hω hB t₀ Q hQ
  obtain ⟨C, hC⟩ := hf ω hω hB t₀ Q hQ
  obtain ⟨D, hD⟩ := hg ω hω hB t₀ Q hQ
  refine ⟨C + D, fun b hb x hx q hq => ?_⟩
  have h1 := hC b hb x hx q hq
  have h2 := hD b hb x hx q hq
  calc ‖f (b * tor K x * q) + g (b * tor K x * q)‖
      ≤ ‖f (b * tor K x * q)‖ + ‖g (b * tor K x * q)‖ := norm_add_le _ _
    _ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) +
          D * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) := add_le_add h1 h2
    _ = (C + D) * Real.exp (∑ r ∈ Finset.range n, m r * sr x r) := by ring

theorem update_le_update (m : ℕ → ℝ) (r : ℕ) {a b : ℝ} (h : a ≤ b) (s : ℕ) :
    Function.update m r a s ≤ Function.update m r b s := by
  by_cases hs : s = r
  · subst hs
    simpa using h
  · simp [Function.update_of_ne hs]

theorem bnd_step (hD : DiffStep) (hC : CtStep) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Nice φ)
    {r : ℕ} (h0 : 0 < r) (h1 : r < n) {p : ℂ[X]} {κ : ℝ} (hp : p.Monic) (hk : Kill r φ p)
    (hz : ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) {m : ℕ → ℝ} (h : Bnd φ m) :
    Bnd φ (Function.update m r (max (m r - 1) κ)) := by
  have a : Bnd (fun g => φ g - ctn r φ g) (Function.update m r (max (m r - 1) κ)) :=
    bnd_mono (fun s _ _ => update_le_update m r (le_max_left _ _) s) (hD K n φ m r h0 h1 hφ h)
  have b : Bnd (ctn r φ) (Function.update m r (max (m r - 1) κ)) :=
    bnd_mono (fun s _ _ => update_le_update m r (le_max_right _ _) s)
      (hC K n φ m r p κ h0 h1 hφ h hp hk hz)
  have c := bnd_add a b
  simpa using c

theorem bnd_iter (hD : DiffStep) (hC : CtStep) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Nice φ)
    {r : ℕ} (h0 : 0 < r) (h1 : r < n) {p : ℂ[X]} {κ : ℝ} (hp : p.Monic) (hk : Kill r φ p)
    (hz : ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) {m : ℕ → ℝ} (h : Bnd φ m) (k : ℕ) :
    Bnd φ (Function.update m r (max (m r - k) κ)) := by
  induction k with
  | zero =>
    refine bnd_mono (fun s _ _ => ?_) h
    by_cases hs : s = r
    · subst hs
      simp
    · simp [Function.update_of_ne hs]
  | succ k ih =>
    have := bnd_step hD hC hφ h0 h1 hp hk hz ih
    rw [Function.update_self, Function.update_idem] at this
    refine bnd_mono (fun s _ _ => update_le_update m r ?_ s) this
    push_cast
    refine max_le ?_ (le_max_right _ _)
    rcases le_total (m r - k) κ with h' | h'
    · rw [max_eq_right h']
      exact le_trans (by linarith) (le_max_right _ _)
    · rw [max_eq_left h']
      exact le_trans (by linarith) (le_max_left _ _)

theorem bnd_one (hD : DiffStep) (hC : CtStep) {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Nice φ)
    {r : ℕ} (h0 : 0 < r) (h1 : r < n) {p : ℂ[X]} {κ : ℝ} (hp : p.Monic) (hk : Kill r φ p)
    (hz : ∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) {m : ℕ → ℝ} (h : Bnd φ m) :
    Bnd φ (Function.update m r κ) := by
  obtain ⟨k, hk'⟩ := exists_nat_ge (m r - κ)
  have := bnd_iter hD hC hφ h0 h1 hp hk hz h k
  rwa [max_eq_right (by linarith)] at this

theorem bootGlue : BootGlue := by
  intro hD hC K _ _ n φ M κ hφ hM hp
  have key : ∀ s : Finset ℕ, (∀ r ∈ s, 0 < r ∧ r < n) →
      Bnd φ (fun r => if r ∈ s then κ r else M) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using hM
    | insert a s ha ih =>
      intro hs
      have h' := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      obtain ⟨h0, h1⟩ := hs a (Finset.mem_insert_self a s)
      obtain ⟨p, hpm, hpk, hpz⟩ := hp a h0 h1
      have := bnd_one hD hC hφ h0 h1 hpm hpk hpz h'
      refine bnd_mono (fun r _ _ => le_of_eq ?_) this
      by_cases hr : r = a
      · subst hr
        simp
      · simp [Function.update_of_ne hr, Finset.mem_insert, hr]
  refine bnd_mono (fun r h0 h1 => le_of_eq ?_) (key (Finset.Ioo 0 n) (fun r hr => Finset.mem_Ioo.1 hr))
  simp [h0, h1]

end GlobalTheory.CompanionTheory.AnBoot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBase
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBase
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCBase

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {k s : ℕ} (h : k ≤ s) :
    pdP δ s ≤ pdP δ k := by
  unfold CrystallineSemistableComparison.Pb.pdP
  refine Ideal.span_mono ?_
  rintro z ⟨L, hL, hs, rfl⟩
  exact ⟨L, hL, h.trans hs, rfl⟩

theorem latBase_lev : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  intro l hl K M h k hk s hks
  have H := GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk
  show CrystallineSemistableComparison.Pb.LatBase (CrystallineSemistableComparison.Pb.Lat.γ (CrystallineSemistableComparison.Pb.Lat.fk l k) (CrystallineSemistableComparison.xi0 l) l M (h.hc k)) l s
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_bot_iff.mp ((dividedPowerFiltration_anti _ hks).trans
      (GlobalTheory.CompanionTheory.LatNil.dividedPowerFiltration_eq_bot _ _ l M k H (h.hc k)).le)
  · exact GlobalTheory.CompanionTheory.Lat.quot_pdP_no_torsion _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatticeUnit.natCast_dvd_pow _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatFG.dividedPowerFiltration_fg _ _ l M k H (h.hc k)
  · exact GlobalTheory.CompanionTheory.LatPrime.I_isPrime _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatVal.val _ _ l M k H
  · exact GlobalTheory.CompanionTheory.Lat.pow_mem_span_sup_I _ _ l M k H
  · exact GlobalTheory.CompanionTheory.LatCpl.isAdicComplete_A M H
  · exact GlobalTheory.CompanionTheory.LatClosed.closed _ _ l M k H (h.hc k)

end GlobalTheory.CompanionTheory.LatCBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBaseStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_lattice_base : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), 1 ≤ k → ∀ s, k ≤ s → LatBase (lev h k).γ l s := by
  first | exact @GlobalTheory.CompanionTheory.LatCBase.latBase_lev | exact GlobalTheory.CompanionTheory.LatCBase.latBase_lev | (intros; apply GlobalTheory.CompanionTheory.LatCBase.latBase_lev <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfParts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfParts
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.Mass

theorem anisotropic_binary_one_vector_formula : Prop1 → Simil → Hasse → Cnt → E1 := by
  intro hP hS hH hC F E _ _ _ _ _ σ hcm J hJ hA T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨β, rfl, hβ, he⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hβ0 : β ≠ 0 := hβ hd
  simp only [he]
  have hsph : {X : Fin 1 → Fin 2 → E | gramE σ J X = fun _ _ => algebraMap F E β} = sph σ J β := rfl
  rw [hsph]
  obtain ⟨c, hc⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0
  by_cases h0 : mi (hermScal (Ainf F) σ (algebraMap F _ β)) = 0 ∨
      ∃ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) = 0
  · rw [(GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 _ c _ _).2.1 hc h0]
    exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 0 1 _ _).2.2 hc.1 hc.2.1 h0
  push Not at h0
  have hne : (sph σ J β).Nonempty :=
    hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ0 h0.1
  have hall : ∀ β' : F, β' ≠ 0 → EP b μ 𝓕 mi m β' c := by
    intro β' hβ'
    by_cases hn : (sph σ J β').Nonempty
    · exact hS F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β β' hβ0 hβ' hne hn c hc
    · obtain ⟨c', hc'⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ'
      have hz : mi (hermScal (Ainf F) σ (algebraMap F _ β')) = 0 := by
        by_contra hz
        exact hn (hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β' hβ' hz)
      have ht : thetaMeas σ J μ 𝓕 (sph σ J β') = 0 := by
        have he' : IsEmpty (sph σ J β') := Set.not_nonempty_iff_eq_empty.1 hn ▸ inferInstance
        simp [thetaMeas]
      unfold EP
      rw [ht]
      exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 2 0 c _ _).2.2 hc'.1 hc'.2.1 (Or.inl hz)
  have h1 : c = 1 := hC F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm c hall
  exact h1 ▸ hc

end GlobalTheory.CompanionTheory.Mass
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfPartsStatement
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_vector_formula_of_parts : Prop1 → Simil → Hasse → Cnt → E1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | exact GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | (intros; apply GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetShalikaBoundOfSteps
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.LFun PositivityTheory.JacquetShalikaLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatakeBound

theorem jacquetShalikaBound_of_steps : ParameterUpperBound → liftZP_unit → ParameterAbsoluteValues → lift_levelP_alt₂ → G1 → G2 → G3 → G4 → GlobalTheory.Published.JacquetShalikaBound := by
  intro h10 h11 h11b h12 g1 g2 g3 g4 E _ _ _ a π hU w B hB α hα
  obtain ⟨L, rfl⟩ : ∃ L : List ℂˣ, (L : Multiset ℂˣ) = B := ⟨B.toList, Multiset.coe_toList B⟩
  have hcard : L.length = a := by simpa using hB.card
  subst hcard
  have hBz : (L : Multiset ℂˣ) = Finset.univ.val.map L.get := by rw [Fin.univ_val_map, List.ofFn_get]
  obtain ⟨i, rfl⟩ : ∃ i, L.get i = α := List.mem_iff_get.1 (Multiset.mem_coe.1 hα)
  have ha : 1 ≤ L.length := Fin.pos i
  induction π using Quotient.inductionOn with | _ π => ?_
  set z := L.get with hz
  let F := w.adicCompletion E
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  have hB' : HasSatGL w (π.locRep w) (Finset.univ.val.map z) := by rw [← hBz]; exact hB
  obtain ⟨ψ, hψ, l, hl0, hW⟩ := g4 E L.length ha π w
  obtain ⟨v, g, hv, hlv⟩ := g2 E L.length π w _ hB' l hl0
  obtain ⟨Bf, hBf⟩ := g1 E L.length π hU w
  have hs := g3 E L.length π w
  obtain ⟨hq, h12'⟩ := h12 E w
  have hH : Heig (π.locRep w) v z := h12' L.length π.V (π.locRep w) v z hv
  have hq1 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hpair := h11b L.length z (h11 F L.length π.V (π.locRep w) Bf hBf v z hv.1 hH)
  have hup : ∀ j, ‖(z j : ℂ)‖ < Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) := by
    intro j
    rcases Nat.lt_or_ge 1 L.length with h2 | h1
    · have := h10 F Measure.addHaar ψ hψ L.length π.V (π.locRep w) hs h2 l Bf hW hBf v z hH ⟨g, hlv⟩ j
      rwa [hq] at this
    · obtain ⟨k, hk⟩ := hpair j
      have hkj : k = j := Fin.ext (by have := k.2; have := j.2; omega)
      subst hkj
      have h0 : ‖(z k : ℂ)‖ = 1 := by
        have h00 : 0 ≤ ‖(z k : ℂ)‖ := norm_nonneg _
        nlinarith
      rw [h0, Real.lt_sqrt zero_le_one]
      simpa using hq1
  obtain ⟨k, hk⟩ := hpair i
  have hkpos : 0 < ‖(z k : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have hi : ‖(z i : ℂ)‖ = ‖(z k : ℂ)‖⁻¹ := eq_inv_of_mul_eq_one_right hk
  have hsq : (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (Ideal.absNorm w.asIdeal : ℝ) :=
    (Real.sqrt_eq_rpow _).symm
  refine ⟨?_, ?_⟩
  · rw [Real.rpow_neg (by positivity), hsq, hi]
    exact inv_strictAnti₀ hkpos (hup k)
  · rw [hsq]; exact hup i

end GlobalTheory.CompanionTheory.SatakeBound

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompareQuotientBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompareQuotientBijective
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.LsCmp

theorem cmpq_bijective (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (A : C ⥤ CommAlgCat.{0} R) (l n i : ℕ) : Function.Bijective ((cmpq A l n).f i) := by
  have hmk := cmpq_mk A l n i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hmk] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    have hy : ∀ s : ComposableArrows C i, ∃ a : ↑(A.obj (s.obj (Fin.last i))),
        a * algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n) = y s := by
      intro s
      have h1 : ((qM A l n).pullC i y) s = 0 := by
        rw [hq]
        rfl
      have h2 : Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) (y s) = 0 :=
        congrArg Subtype.val h1
      exact Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2)
    choose a ha using hy
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    refine ⟨a, ?_⟩
    funext s
    show ((l : R) ^ n) • a s = y s
    rw [Algebra.smul_def, mul_comm]
    exact ha s
  · intro g
    have hx : ∀ s : ComposableArrows C i, ∃ x : ↑(A.obj (s.obj (Fin.last i))),
        Ideal.Quotient.mk (Ideal.span {algebraMap R ↑(A.obj (s.obj (Fin.last i))) ((l : R) ^ n)}) x =
          Subtype.val (g s) := fun s => Ideal.Quotient.mk_surjective _
    choose x hx using hx
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [hmk]
    funext s
    apply Subtype.ext
    exact hx s

end GlobalTheory.CompanionTheory.LsCmp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompareQuotientBijectiveStatement
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compare_quotient_bijective : ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (l n i : ℕ), Function.Bijective ((cmpq A l n).f i) := by
  first | exact @GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective | exact GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective | (intros; apply GlobalTheory.CompanionTheory.LsCmp.cmpq_bijective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemCongruenceSubgroupOfDiv
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
  PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel Topology MatrixGroups

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JSSmooth

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem mem_congruenceSubgroup_of_div {c : ℕ} {g : GL (Fin n) F}
    (hg : Div (c + 1) ((g : Matrix (Fin n) (Fin n) F) - 1)) :
    g ∈ congruenceSubgroup F n (c + 1) := by
  choose y hy hgy using hg
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hent : ∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (c + 1) * y i j := fun i j => by
    rw [← hgy i j, Matrix.sub_apply]
  have hint : ∀ i j, g i j ∈ 𝒪[F] := fun i j => by
    have h1 : g i j = (uniformizer F : F) ^ (c + 1) * y i j +
        (1 : Matrix (Fin n) (Fin n) F) i j := by rw [← hent i j, sub_add_cancel]
    rw [h1]
    exact add_mem (mul_mem (pow_mem (uniformizer F).2 _) (hy i j)) (hone i j)
  let A : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨g i j, hint i j⟩
  have hres : (IsLocalRing.residue 𝒪[F]).mapMatrix A = 1 := by
    ext i j
    have hmem : A i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
      have h1 : A i j - (1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j =
          uniformizer F * (uniformizer F ^ c * ⟨y i j, hy i j⟩) := by
        apply Subtype.ext
        have h2 : (((1 : Matrix (Fin n) (Fin n) 𝒪[F]) i j : 𝒪[F]) : F) =
            (1 : Matrix (Fin n) (Fin n) F) i j := by
          rw [Matrix.one_apply, Matrix.one_apply]
          split_ifs <;> simp
        simp only [AddSubgroupClass.coe_sub, h2, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
        change g i j - _ = _
        rw [hent i j]
        ring
      rw [h1]
      exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (irreducible_uniformizer F).not_isUnit)
    have h3 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    rw [map_sub, sub_eq_zero] at h3
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : IsUnit A.det := by
    have h1 : IsLocalRing.residue 𝒪[F] A.det = 1 := by
      rw [RingHom.map_det, hres, Matrix.det_one]
    by_contra h
    have h2 := (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [h2] at h1
    exact zero_ne_one h1
  rw [mem_congruenceSubgroup_iff]
  refine ⟨⟨Matrix.GeneralLinearGroup.mk'' A hdet, Units.ext rfl⟩, fun i j => ?_⟩
  rw [hent i j, map_mul, map_pow]
  exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hy i j))

theorem smooth_of_isSmooth {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (h : GlobalTheory.PRep.IsSmooth ρ) : Smooth ρ := fun u => by
  have h1 : {g : GL (Fin n) F | ρ g u = u} ∈ 𝓝 (1 : GL (Fin n) F) :=
    (h u).mem_nhds (by simp)
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one F n).mem_iff.1 h1
  exact ⟨m, fun g hg => hm (congruenceSubgroup_antitone F n (Nat.le_succ m)
    (mem_congruenceSubgroup_of_div hg))⟩

theorem g3 : G3 := fun _ _ _ _ _ π w => smooth_of_isSmooth _ (π.isSmooth_locRep w)

end GlobalTheory.CompanionTheory.JSSmooth

end
end
