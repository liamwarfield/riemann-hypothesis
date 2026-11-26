module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem exists_equivariant_fun_on_spanning_families {R M G F : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Group G] [Field F] {r n : ℕ} (hrn : r ≤ n)
    (h0 : ∃ x₀ : Fin r → M, Submodule.span R (Set.range x₀) = ⊤)
    (h1 : ∀ x x' : Fin r → M, Submodule.span R (Set.range x) = ⊤ → Submodule.span R (Set.range x') = ⊤ →
      ∃! g : M ≃ₗ[R] M, ∀ b, g (x b) = x' b)
    (adj : (M ≃ₗ[R] M) → G) (hadj : ∀ g g', adj (g * g') = adj g' * adj g) (ψ : G →* Fˣ) :
    ∃ (ph : (Fin n → M) → F) (x₀ : Fin n → M),
      (∀ x x' : Fin n → M, (∀ b : Fin n, b.val < r → x b = x' b) → ph x = ph x') ∧
      (∀ x, ph x ≠ 0 → Submodule.span R (x '' {b | b.val < r}) = ⊤) ∧
      (∀ (kst : M ≃ₗ[R] M) x, ph (fun b => kst (x b)) = (((ψ (adj kst))⁻¹ : Fˣ) : F) * ph x) ∧
      ph x₀ = 1 ∧ Submodule.span R (x₀ '' {b | b.val < r}) = ⊤ := by
  classical
  obtain ⟨y, hy⟩ := h0
  have himg : ∀ x : Fin n → M, x '' {b | b.val < r} = Set.range (fun b : Fin r => x (Fin.castLE hrn b)) := by
    intro x
    ext m
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hrn b, b.2, rfl⟩
  have hadj1 : adj 1 = 1 := by
    have := hadj 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  let f : (Fin r → M) → F := fun z =>
    if h : Submodule.span R (Set.range z) = ⊤ then (((ψ (adj (h1 y z hy h).exists.choose))⁻¹ : Fˣ) : F) else 0
  have hf : ∀ (z : Fin r → M) (g : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ → (∀ b, g (y b) = z b) →
      f z = (((ψ (adj g))⁻¹ : Fˣ) : F) := by
    intro z g hz hg
    have : (h1 y z hy hz).exists.choose = g :=
      (h1 y z hy hz).unique (h1 y z hy hz).exists.choose_spec hg
    simp only [f, dif_pos hz, this]
  have hspan : ∀ (z : Fin r → M) (k : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ →
      Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
    intro z k hz
    have e : (Set.range fun b => k (z b)) = (k : M →ₗ[R] M) '' Set.range z := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, hz, Submodule.map_top, LinearEquiv.range]
  let x₀ : Fin n → M := fun b => if h : b.val < r then y ⟨b.val, h⟩ else 0
  have hx₀ : (fun b : Fin r => x₀ (Fin.castLE hrn b)) = y := by
    funext b
    simp [x₀]
  refine ⟨fun x => f (fun b => x (Fin.castLE hrn b)), x₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' h
    have : (fun b : Fin r => x (Fin.castLE hrn b)) = fun b => x' (Fin.castLE hrn b) :=
      funext fun b => h _ b.2
    simp only [this]
  · intro x hx
    rw [himg]
    by_contra hz
    exact hx (by simp only [f, dif_neg hz])
  · intro k x
    set z : Fin r → M := fun b => x (Fin.castLE hrn b) with hzdef
    change f (fun b => k (z b)) = _ * f z
    by_cases hz : Submodule.span R (Set.range z) = ⊤
    · obtain ⟨g, hg, -⟩ := h1 y z hy hz
      rw [hf z g hz hg, hf _ (k * g) (hspan z k hz) (fun b => by simp [hg b]), hadj, map_mul, mul_inv,
        Units.val_mul, mul_comm]
    · have hz' : ¬ Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
        intro h
        have := hspan _ k.symm h
        simp only [LinearEquiv.symm_apply_apply] at this
        exact hz this
      simp only [f, dif_neg hz, dif_neg hz', mul_zero]
  · change f (fun b : Fin r => x₀ (Fin.castLE hrn b)) = 1
    rw [hx₀, hf y 1 hy (fun b => rfl), hadj1]
    simp
  · rw [himg, hx₀, hy]

theorem exists_phiPin_of_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → Dw.p + Dw.q ≤ n → ∀ ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ, ∃ (φ : (Fin n → LevQ Dw d.l₂) → c.F) (ph : (Fin n → LaJ Xo c d) → c.F) (x₀ : Fin n → LaJ Xo c d), DeltaDat.PhiPin { d with φδ := φ } ph ψ x₀ := by
  intro E _ _ _ H Dw l Xo c n d hd hn ψ
  obtain ⟨h0, h1, adj, hadj, hiff⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨ph, x₀, ha, hb, hc, hd1, hd2⟩ :=
    exists_equivariant_fun_on_spanning_families hn h0 h1 adj hadj ψ
  refine ⟨fun q => d.eF.symm (∑ᶠ x : Fin n → LaJ Xo c d, d.eF (ph x) *
      ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^
        (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b)))), ph, x₀, ha, hb, ?_, hd1, hd2, ?_⟩
  · intro k kst h x
    have := (hiff k kst).mp h
    subst this
    exact hc kst x
  · intro q
    exact d.eF.apply_symm_apply _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPullCubicalId
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ObjRebase

def pullIdIso {X : Scheme.{0}} (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s := fun p => res (X := X) (U := L.U (p.1 PUnit.unit) ⊓ L.U p.2)
    (V := (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2) (fun _ hx => ⟨mem_pull.1 hx.1, hx.2⟩) (L.g (p.1 PUnit.unit) p.2)

theorem gw_pullIdIso {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (pullIdIso L) f y j k = gm f y (L.U j ⊓ L.U k) (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  exact gm_res f y _ hm _

theorem pgen_pullIdIso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : PGen (pullIdIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₁ : f y ∈ L.U j := hj
  have hj₂ : f y ∈ L.U j' := hj'
  rw [gw_pullIdIso L f y j k hj₁ hk, gw_pullIdIso L f y j' k' hj₂ hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₁ hk hk'
  have b := gm_cocycle hL f y hj₁ hj₂ hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]

theorem pmaps_pullIdIso {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (pullIdIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp', Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  refine (gm_res r z _ hm _).trans ((gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp' k, hq k⟩ _).trans ?_)
  exact (gw_pullIdIso L (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)).symm

def cubeMapId {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

theorem isPullCubical_id {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ _ _).2 ⟨pullIdIso L.L, pgen_pullIdIso L.isLB,
    pmaps_pullIdIso (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig L.rigGen,
    pmaps_pullIdIso (thφ G (x3 G)) thε c.t c.isGen⟩

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (G := G) (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sabMapId {S : Scheme.{0}} (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub

variable {D : Datum H} {l : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}

end GlobalTheory.ObjRebase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LinearIndependentSingleAdd
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped Matrix ComplexConjugate

namespace GlobalTheory.CuspExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_congr_diagonal (H : GlobalTheory.Published.Landherr) (X : Data E r) (k : Fin r) :
    ∃ (d : E) (P : Matrix (Fin r) (Fin r) E), P.det ≠ 0 ∧
      Matrix.diagonal (fun a : Fin r => (if (a : ℕ) < X.p0 then (1 : E) else -1) *
        (if a = k then d else 1)) = Pᵀ * X.Gm * P.map cc := by
  classical
  set s : Fin r → E := fun a => if (a : ℕ) < X.p0 then (1 : E) else -1 with hs
  have hs0 : ∀ a, s a ≠ 0 := fun a => by
    simp only [hs]; split_ifs <;> simp
  have hscc : ∀ a, cc (s a) = s a := fun a => by
    simp only [hs]; split_ifs <;> simp [cc]
  have hsτ : ∀ (τ : E →+* ℂ) a, τ (s a) = ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := fun τ a => by
    simp only [hs, sgn]; split_ifs <;> simp
  have hS0 : (Matrix.diagonal s).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hs0 a
  have hSh : ∀ a b, cc (Matrix.diagonal s a b) = Matrix.diagonal s b a := by
    intro a b
    by_cases h : a = b
    · subst h; simpa using hscc a
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  set d : E := X.Gm.det / (Matrix.diagonal s).det with hd
  have hd0 : d ≠ 0 := div_ne_zero X.Gm_det hS0
  have hdcc : cc d = d := by
    have h1 := GlobalTheory.Published.cc_det_of_herm X.Gm_herm
    have h2 := GlobalTheory.Published.cc_det_of_herm hSh
    unfold cc at h1 h2 ⊢
    rw [hd, map_div₀, h1, h2]
  have hdet : (Matrix.diagonal fun a : Fin r => s a * (if a = k then d else 1)).det = X.Gm.det := by
    rw [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _),
      ← Matrix.det_diagonal, hd]
    field_simp
  refine ⟨d, GlobalTheory.Published.Landherr.of_signature H X.Gm_herm ?_ X.Gm_det (hdet ▸ X.Gm_det)
    (X.Ψ : Set (E →+* ℂ)) (fun τ => ?_) (fun τ hτ => ⟨X.p0, X.signature ⟨τ, hτ⟩, ?_⟩) ⟨1, ?_⟩⟩
  · intro a b
    by_cases h : a = b
    · subst h
      have h1 := hscc a
      unfold cc at h1 hdcc ⊢
      rw [Matrix.diagonal_apply_eq, map_mul, h1]
      congr 1
      split_ifs
      · exact hdcc
      · exact map_one _
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]; simp [cc]
  · by_cases h : ComplexEmbedding.conjugate τ ∈ X.Ψ
    · exact Or.inr h
    · exact Or.inl ((X.cmType τ).mpr h)
  · obtain ⟨Q, hQ, hg⟩ := X.signature ⟨τ, hτ⟩
    have hpos : 0 < (τ d).re := by
      refine GlobalTheory.Published.Landherr.re_det_div_pos X.Gm_det τ ⟨Q, hQ, ?_⟩
      rw [← GlobalTheory.Published.gram_eq, hg, Matrix.diagonal_map (map_zero τ)]
      simp only [hsτ]
    have hre : ((τ d).re : ℂ) = τ d := by
      rw [← Complex.conj_eq_iff_re, ← GlobalTheory.Published.embedding_cc, hdcc]
    set t : ℝ := (Real.sqrt (τ d).re)⁻¹ with ht
    have ht0 : t ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hpos).ne'
    have htt : (t : ℂ) * τ d * t = 1 := by
      rw [← hre, mul_right_comm, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ht, ← mul_inv,
        Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
    refine ⟨Matrix.diagonal fun a => if a = k then (t : ℂ) else 1, ?_, ?_⟩
    · rw [Matrix.det_diagonal, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
      exact_mod_cast ht0
    · rw [GlobalTheory.Published.gram_eq, Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero τ),
        Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      rw [map_mul, hsτ]
      split_ifs
      · rw [Complex.conj_ofReal]
        linear_combination ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * htt
      · simp
  · rw [hdet, div_self X.Gm_det]; simp [cc]


omit [NumberField E] [IsCMField E] in
theorem linearIndependent_single_add {ρ : ℕ} {i j : Fin ρ → Fin r} (hi : Function.Injective i)
    (hij : ∀ a b, i a ≠ j b) :
    LinearIndependent E fun a => (Pi.single (i a) 1 + Pi.single (j a) 1 : Fin r → E) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have := congrFun hg (i a)
  simpa [Finset.sum_apply, Pi.single_apply, hij, hi.eq_iff] using this

theorem herm_diagonal_single_add {ρ : ℕ} {i j : Fin ρ → Fin r} (hi : Function.Injective i)
    (hj : Function.Injective j) (hij : ∀ a b, i a ≠ j b) (g : Fin r → E)
    (hg : ∀ a, g (i a) + g (j a) = 0) (a b : Fin ρ) :
    herm (Matrix.diagonal g) (Pi.single (i a) 1 + Pi.single (j a) 1)
      (Pi.single (i b) 1 + Pi.single (j b) 1) = 0 := by
  classical
  have hji : ∀ a b, j a ≠ i b := fun a b => (hij b a).symm
  rw [GlobalTheory.Published.LandherrSt.herm_eq, add_dotProduct, single_dotProduct, single_dotProduct,
    Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
  by_cases h : a = b
  · subst h
    simpa [cc, Pi.single_apply, hij, hji] using hg a
  · simp [cc, hij, hji, hi.eq_iff, hj.eq_iff, h]

theorem nonempty_cuspFD : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), ρ ≤ X.p0 → ρ + X.p0 ≤ r → 2 * ρ < r → Nonempty (FJ.CuspFD X ρ) := by
  intro HN E _ _ _ r ρ X h1 h2 h3
  classical
  have H := GlobalTheory.Published.landherr_of_landherrSt (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt HN)
  obtain ⟨k, hk⟩ : ∃ k : Fin r, (k : ℕ) + ρ < X.p0 ∨ X.p0 + ρ ≤ k := by
    by_cases h : ρ < X.p0
    · exact ⟨⟨0, by omega⟩, Or.inl (by simpa using h)⟩
    · exact ⟨⟨r - 1, by omega⟩, Or.inr (by simp only; omega)⟩
  obtain ⟨d, P, hP, hG⟩ := exists_congr_diagonal H X k
  let i : Fin ρ → Fin r := fun a => ⟨X.p0 - 1 - a, by have := a.2; omega⟩
  let j : Fin ρ → Fin r := fun a => ⟨X.p0 + a, by have := a.2; omega⟩
  have hi : Function.Injective i := fun a b h => by
    have := a.2; have := b.2
    simp only [i, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hj : Function.Injective j := fun a b h => by
    simp only [j, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hij : ∀ a b, i a ≠ j b := fun a b h => by
    have := a.2
    simp only [i, j, Fin.mk.injEq] at h
    omega
  refine ⟨⟨fun a => P *ᵥ (Pi.single (i a) 1 + Pi.single (j a) 1), ?_, fun a b => ?_⟩⟩
  · refine (linearIndependent_single_add (E := E) hi hij).map' (Matrix.toLin' P) ?_
    rw [LinearMap.ker_eq_bot]
    exact Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hP))
  · rw [GlobalTheory.Published.LandherrSt.herm_mulVec, ← hG]
    refine herm_diagonal_single_add hi hj hij _ (fun c => ?_) a b
    have := c.2
    have e1 : i c ≠ k := fun h => by
      have := congrArg Fin.val h
      simp only [i] at this
      omega
    have e2 : j c ≠ k := fun h => by
      have := congrArg Fin.val h
      simp only [j] at this
      omega
    have e3 : (i c : ℕ) < X.p0 := by simp only [i]; omega
    have e4 : ¬ (j c : ℕ) < X.p0 := by simp only [j]; omega
    simp only [if_pos e3, if_neg e4, if_neg e1, if_neg e2]
    ring

end GlobalTheory.CuspExist
end
