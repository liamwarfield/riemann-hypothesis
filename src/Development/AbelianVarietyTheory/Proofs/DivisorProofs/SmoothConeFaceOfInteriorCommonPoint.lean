module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

section IntCone

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem intCone_evalZ_sum {n : ℕ} {β : Fin n → LinearMap.BilinForm ℤ X} (h : φ.LinearOn β) (a : Fin n → ℕ) :
    φ.evalZ (∑ i, a i • β i) = ∑ i, (a i : ℝ) * φ.evalZ (β i) := by
  have := h (fun i => (a i : ℝ)) (fun i => Nat.cast_nonneg _)
  refine Eq.trans ?_ this
  unfold InvFun.evalZ
  congr 1
  funext x y
  simp [LinearMap.sum_apply]

theorem intCone_absorb {n s : ℕ} {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X)
    (hβp : ∀ i y, 0 ≤ β i y y) (hβl : φ.LinearOn β) {δ : Fin s → LinearMap.BilinForm ℤ X} (hδ : IsCone bar φ δ)
    (a : Fin n → ℕ) (b : Fin s → ℕ) (h : ∑ i, a i • β i = ∑ l, b l • δ l) (i : Fin n) (hi : 0 < a i) :
    ∃ (k : ℕ) (e : Fin s → ℕ), 0 < k ∧ k • β i = ∑ l, e l • δ l := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hδ.strict
  refine h3 (β i) (hβ i) (hβp i) ?_
  have hx1 : (ℓ (∑ i, a i • β i) : ℝ) = N * ∑ i, (a i : ℝ) * φ.evalZ (β i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← intCone_evalZ_sum hβl, h, intCone_evalZ_sum hδ.linear, map_sum, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, h1]
    ring
  have hx2 : (ℓ (∑ i, a i • β i) : ℝ) = ∑ i, (a i : ℝ) * ℓ (β i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_nsmul]
  have hle : ∀ j, (a j : ℝ) * (N * φ.evalZ (β j)) ≤ (a j : ℝ) * ℓ (β j) := fun j =>
    mul_le_mul_of_nonneg_left (h2 _ (hβ j) (hβp j)) (Nat.cast_nonneg _)
  have hsum : ∑ j, ((a j : ℝ) * ℓ (β j) - (a j : ℝ) * (N * φ.evalZ (β j))) = 0 := by
    rw [Finset.sum_sub_distrib, ← hx2, hx1, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by ring
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hle j))).1 hsum i (Finset.mem_univ _)
  have hai : (a i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  have h4 : (a i : ℝ) * (ℓ (β i) - N * φ.evalZ (β i)) = 0 := by rw [mul_sub]; exact ht
  have h5 := (mul_eq_zero.1 h4).resolve_left hai
  linarith

theorem intCone_face : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X], IsPolFanOn bar φ X → ∀ (r r' : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X)
    (γ' : Fin r' → LinearMap.BilinForm ℤ X), IsCone bar φ γ → IsCone bar φ γ' → ∀ (c : Fin r → ℕ) (c' : Fin r' → ℕ),
    (∀ j, 0 < c j) → ∑ j, c j • γ j = ∑ j, c' j • γ' j → ∀ j, ∃ j', γ j = γ' j' := by
  intro O _ bar φ X _ _ _ _ r r' γ γ' hγ hγ' c c' hc he j
  obtain ⟨k, d, hk, hd⟩ := intCone_absorb hγ.mem hγ.nonneg hγ.linear hγ' c c' he j (hc j)
  have hd' : ∑ i, d i • γ' i = ∑ l, (Pi.single j k : Fin r → ℕ) l • γ l := by
    rw [← hd, Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_apply, hl]) (by simp)]
    simp
  have habs : ∀ i, 0 < d i → ∃ (k' : ℕ) (e : Fin r → ℕ), 0 < k' ∧ k' • γ' i = ∑ l, e l • γ l :=
    fun i hi => intCone_absorb hγ'.mem hγ'.nonneg hγ'.linear hγ d _ hd' i hi
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  obtain ⟨g, hg⟩ := hγ'.basis.exists_dual
  let G : Fin r → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let G' : Fin r' → balForms bar X := fun i => ⟨γ' i, hγ'.mem i⟩
  have hfG : ∀ l m, f l (G m) = if l = m then 1 else 0 := hf
  have hgG : ∀ i m, g i (G' m) = if i = m then 1 else 0 := hg
  have hdG : k • G j = ∑ i, d i • G' i := Subtype.ext (by simp [G, G', hd])
  have hpos : ∀ i, 0 < d i → ∀ l, 0 ≤ f l (G' i) := by
    intro i hi l
    obtain ⟨k', e, hk', he'⟩ := habs i hi
    have h0 : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
    have h1 := congrArg (f l) h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      mul_one] at h1
    have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
    by_contra hneg
    push_neg at hneg
    have : (k' : ℤ) * f l (G' i) < 0 := mul_neg_of_pos_of_neg hk'' hneg
    linarith [Int.natCast_nonneg (e l)]
  have hex : ∃ i, 0 < d i := by
    by_contra hno
    push_neg at hno
    have h0 : k • γ j = 0 := by
      rw [hd]
      exact Finset.sum_eq_zero fun i _ => by rw [Nat.le_zero.1 (hno i), zero_smul]
    refine hγ.linearIndependent.ne_zero j (LinearMap.ext₂ fun x y => ?_)
    have h1 := LinearMap.congr_fun₂ h0 x y
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hk.ne')
    · simpa using h2
  obtain ⟨i, hi⟩ := hex
  have hzero : ∀ l, l ≠ j → f l (G' i) = 0 := by
    intro l hl
    have h1 := congrArg (f l) hdG
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum, hfG, if_neg hl, smul_zero] at h1
    simp only [map_nsmul, nsmul_eq_mul] at h1
    have hnn : ∀ i' ∈ Finset.univ, 0 ≤ (d i' : ℤ) * f l (G' i') := fun i' _ => by
      rcases Nat.eq_zero_or_pos (d i') with h | h
      · simp [h]
      · exact mul_nonneg (Int.natCast_nonneg _) (hpos i' h l)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1.symm i (Finset.mem_univ _)
    exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hi.ne')
  obtain ⟨k', e, hk', he'⟩ := habs i hi
  have hE : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
  have hem : ∀ m, (e m : ℤ) = k' * f m (G' i) := by
    intro m
    have h1 := congrArg (f m) hE
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      mul_one] at h1
    exact h1.symm
  have hEj : k' • G' i = e j • G j := by
    rw [hE]
    refine Finset.sum_eq_single j (fun m _ hm => ?_) (by simp)
    have h1 := hem m
    rw [hzero m hm, mul_zero] at h1
    rw [show e m = 0 by exact_mod_cast h1, zero_smul]
  have h1 := congrArg (g i) hEj
  simp only [map_nsmul, hgG, if_true, nsmul_eq_mul, mul_one] at h1
  have h2 := hem j
  have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
  have hu : f j (G' i) * g i (G j) = 1 := by
    have h3 : (k' : ℤ) * (f j (G' i) * g i (G j) - 1) = 0 := by
      rw [mul_sub, ← mul_assoc, ← h2, mul_one]
      linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hk''.ne')
  have hf1 : f j (G' i) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
    · exact h
    · have := Int.natCast_nonneg (e j)
      rw [h2, h] at this
      linarith
  have hej : e j = k' := by
    have := h2
    rw [hf1, mul_one] at this
    exact_mod_cast this
  rw [hej] at hEj
  refine ⟨i, LinearMap.ext₂ fun x y => ?_⟩
  have h3 := LinearMap.congr_fun₂ (congrArg Subtype.val hEj) x y
  simp only [G, G', Submodule.coe_smul, LinearMap.smul_apply, nsmul_eq_mul] at h3
  exact (mul_left_cancel₀ (by exact_mod_cast hk'.ne' : (k' : ℤ) ≠ 0) h3).symm

end IntCone

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPointStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothCone_face_of_interior_common_point : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolFanOn bar φ X → ∀ (r r' : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (γ' : Fin r' → LinearMap.BilinForm ℤ X), IsCone bar φ γ → IsCone bar φ γ' → ∀ (c : Fin r → ℕ) (c' : Fin r' → ℕ), (∀ j, 0 < c j) → ∑ j, c j • γ j = ∑ j, c' j • γ' j → ∀ j, ∃ j', γ j = γ' j' := by
  first | exact @GlobalTheory.Poinc.intCone_face | exact GlobalTheory.Poinc.intCone_face | (intros; apply GlobalTheory.Poinc.intCone_face <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompLevelStab

theorem mem_iff_of_inv {X : Scheme.{0}} (Z : Set X) (hZ : IsClopen Z) (hI : IsIrreducible Z) (f g : X ⟶ X)
    (hfg : f ≫ g = 𝟙 X) (x : X) (hx : x ∈ Z) (hfx : f.base x ∈ Z) (y : X) : f.base y ∈ Z ↔ y ∈ Z := by
  have hgf : ∀ z, g.base (f.base z) = z := fun z => by
    have := congrArg (fun h : X ⟶ X => h.base z) hfg
    simpa using this
  have A : f.base '' Z ⊆ Z :=
    (hI.image _ f.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ ⟨_, ⟨x, hx, rfl⟩, hfx⟩
  have B : g.base '' Z ⊆ Z :=
    (hI.image _ g.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ
      ⟨_, ⟨f.base x, hfx, rfl⟩, by rw [hgf]; exact hx⟩
  exact ⟨fun h => hgf y ▸ B ⟨_, h, rfl⟩, fun h => A ⟨y, h, rfl⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def mv (γ : LevelAut Dw l) : Xo.X ⟶ Xo.X := (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose

theorem mv_spec (γ : LevelAut Dw l) : ∃ ν : SABMap Xo.univ.t Xo.univ.t (mv hpq hA Xo γ),
    IsIso (mv hpq hA Xo γ) ∧ IsLevMove (mv hpq hA Xo γ) ν (liftLa γ) LinearMap.id :=
  (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose_spec

theorem x_move (c : Coeff l) (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    (move Xo c γ y).x = y.x ≫ mv hpq hA Xo γ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact (GlobalTheory.LevelActionLaws.frMove_transfer hpq hA Xo c γ i h (GlobalTheory.LevDesc.levR_move hpq hA γ y)).1

theorem mv_over (γ : LevelAut Dw l) : mv hpq hA Xo γ ≫ Xo.s = Xo.s := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact h.1

theorem mv_mul (c : Coeff l) (γ δ : LevelAut Dw l) : mv hpq hA Xo (γ * δ) = mv hpq hA Xo γ ≫ mv hpq hA Xo δ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  obtain ⟨ν', i', h'⟩ := mv_spec hpq hA Xo δ
  obtain ⟨ν₂, i₂, h₂⟩ := mv_spec hpq hA Xo (γ * δ)
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ ν ν'
  have hc : IsLevMove (mv hpq hA Xo γ ≫ mv hpq hA Xo δ) μ (liftLa (γ * δ)) LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, h'.1, h.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub γ δ a), hμ, ← Category.assoc, h.2.1,
        Category.assoc, h'.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a = (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, h.2.2, Category.assoc, h'.2.2, Category.assoc]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (γ * δ) i₂ inferInstance h₂ hc).1

theorem mv_one (c : Coeff l) : mv hpq hA Xo 1 = 𝟙 Xo.X := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo 1
  obtain ⟨ι, hι, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).1
  have hc : IsLevMove (𝟙 Xo.X) ι (liftLa (1 : LevelAut Dw l)) LinearMap.id := by
    refine ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c 1 i inferInstance h hc).1

end Moves

section Base

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l) (c : Coeff l)

def mvF (γ : LevelAut Dw l) : Xo.XF c ⟶ Xo.XF c :=
  pullback.lift (pullback.fst _ _ ≫ mv hpq hA Xo γ) (pullback.snd _ _) (by
    rw [Category.assoc, mv_over, pullback.condition])

theorem mvF_fst (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ mv hpq hA Xo γ :=
  pullback.lift_fst _ _ _

theorem mvF_snd (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

theorem mvF_mul (γ δ : LevelAut Dw l) : mvF hpq hA Xo c (γ * δ) = mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c δ := by
  apply pullback.hom_ext
  · rw [mvF_fst, Category.assoc, mvF_fst, ← Category.assoc, mvF_fst, Category.assoc, mv_mul hpq hA Xo c]
  · rw [mvF_snd, Category.assoc, mvF_snd, mvF_snd]

theorem mvF_one : mvF hpq hA Xo c 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mvF_fst, mv_one hpq hA Xo c, Category.comp_id, Category.id_comp]
  · rw [mvF_snd, Category.id_comp]

theorem mvF_inv_comp (γ : LevelAut Dw l) : mvF hpq hA Xo c γ⁻¹ ≫ mvF hpq hA Xo c γ = 𝟙 _ := by
  rw [← mvF_mul, inv_mul_cancel, mvF_one]

theorem mvF_comp_inv (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c γ⁻¹ = 𝟙 _ := by
  rw [← mvF_mul, mul_inv_cancel, mvF_one]

theorem ptF_move (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ptF (move Xo c γ y) = ptF y ≫ mvF hpq hA Xo c γ := by
  apply pullback.hom_ext
  · rw [Category.assoc, mvF_fst, ← Category.assoc]
    simp only [ptF, pullback.lift_fst]
    exact x_move hpq hA Xo c γ y
  · rw [Category.assoc, mvF_snd]
    simp only [ptF, pullback.lift_snd]

variable (Z : Comp Xo c)

def stab : Subgroup (LevelAut Dw l) where
  carrier := {h | ∀ x, (mvF hpq hA Xo c h⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))}
  one_mem' := fun x => by rw [inv_one, mvF_one]; rfl
  mul_mem' := by
    intro a b ha hb x
    rw [Set.mem_setOf_eq] at ha hb
    rw [mul_inv_rev, mvF_mul, Scheme.Hom.comp_apply, ha, hb]
  inv_mem' := by
    intro a ha x
    rw [Set.mem_setOf_eq] at ha
    have e : (mvF hpq hA Xo c a⁻¹).base ((mvF hpq hA Xo c a).base x) = x := by
      have := congrArg (fun f : Xo.XF c ⟶ Xo.XF c => f.base x) (mvF_comp_inv hpq hA Xo c a)
      simpa using this
    rw [inv_inv, ← ha, e]

end Base

section Restrict

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

theorem mem_V₀ (x : Xo.XF c) : x ∈ Y.j ⁻¹ᵁ barComp Y Z ↔ x ∈ (Z : Set (Xo.XF c)) := j_mem_barComp Z x

theorem le_V₀ (g : LevelAut Dw l) (hg : ∀ x, (mvF hpq hA Xo c g).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))) :
    Y.j ⁻¹ᵁ barComp Y Z ≤ mvF hpq hA Xo c g ⁻¹ᵁ (Y.j ⁻¹ᵁ barComp Y Z) := fun x hx =>
  (mem_V₀ Y Z _).2 ((hg x).2 ((mem_V₀ Y Z x).1 hx))

theorem inv_mem_stab {h : LevelAut Dw l} (hh : h ∈ stab hpq hA Xo c Z) :
    ∀ x, (mvF hpq hA Xo c h).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) := by
  have h2 := (stab hpq hA Xo c Z).inv_mem hh
  change ∀ x, (mvF hpq hA Xo c h⁻¹⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) at h2
  simpa only [inv_inv] using h2

def resAut (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) : Aut (V₀ Y Z) where
  asIso :=
    { hom := (mvF hpq hA Xo c h⁻¹).resLE _ _ (le_V₀ Y Z h⁻¹ hh)
      inv := (mvF hpq hA Xo c h).resLE _ _ (le_V₀ Y Z h (inv_mem_stab Z hh))
      hom_inv_id := by
        rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
          Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_inv_comp, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
          Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_comp_inv, Category.comp_id, Category.id_comp] }

theorem resAut_ι (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) :
    (resAut Y Z h hh).asIso.hom ≫ i₀ Y Z = i₀ Y Z ≫ mvF hpq hA Xo c h⁻¹ :=
  Scheme.Hom.resLE_comp_ι _ _

def resHom (S : Subgroup (LevelAut Dw l)) : ↥(S ⊓ stab hpq hA Xo c Z) →* Aut (V₀ Y Z) :=
  MonoidHom.mk' (fun g => resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2) fun a b => by
    apply Aut.ext
    apply Iso.ext
    change (resAut Y Z (a * b).1 (Subgroup.mem_inf.1 (a * b).2).2).asIso.hom =
      (resAut Y Z b.1 (Subgroup.mem_inf.1 b.2).2).asIso.hom ≫
        (resAut Y Z a.1 (Subgroup.mem_inf.1 a.2).2).asIso.hom
    rw [← cancel_mono (i₀ Y Z), Category.assoc, resAut_ι, resAut_ι,
      ← Category.assoc, resAut_ι, Category.assoc, ← mvF_mul, Subgroup.coe_mul, mul_inv_rev]

theorem j₀_s₀ : j₀ Y Z ≫ s₀ Y Z = i₀ Y Z ≫ pullback.snd _ _ ≫ spMap (RingHom.id c.F) := by
  show j₀ Y Z ≫ (barComp Y Z).ι ≫ Y.s = _
  rw [← Category.assoc, j₀_ι, Category.assoc, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ,
    Y.jQ_over]

end Restrict

theorem stab_acts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ S : Subgroup (LevelAut Dw l), ∃ (Γ : Subgroup (LevelAut Dw l)) (ρ : Γ →* Aut (V₀ Y Z)), Γ ≤ S ∧ ActsBy Γ.subtype ρ ∧ ∀ h ∈ S, ∀ y : FrPt Xo c ℂ, LiesOn Z y → LiesOn Z (move Xo c h⁻¹ y) → h ∈ Γ := by
  intro E _ _ _ H Dw l Xo c Y Z hpq hl S
  have hA : l.A.Coprime l.M := by rw [hl]; exact Nat.coprime_one_left _
  refine ⟨S ⊓ stab hpq hA Xo c Z, resHom (hpq := hpq) (hA := hA) Y Z S, inf_le_left, ⟨fun g => ?_, ?_⟩, ?_⟩
  · show (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).asIso.hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z
    rw [j₀_s₀, ← Category.assoc, resAut_ι, Category.assoc, ← Category.assoc (mvF _ _ _ _ _), mvF_snd]
  · intro g R _ _ y v hv
    show v ≫ (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).asIso.hom ≫ i₀ Y Z = _
    rw [resAut_ι, ← Category.assoc, hv, ← ptF_move]
    rfl
  · intro h hS y hy hy'
    refine Subgroup.mem_inf.2 ⟨hS, ?_⟩
    let pt : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have h1 := hy' pt
    rw [ptF_move hpq hA Xo c, Scheme.Hom.comp_apply] at h1
    exact mem_iff_of_inv _ (TrivOrderTieCompare.isClopen_comp Z) Z.2.1 (mvF hpq hA Xo c h⁻¹) (mvF hpq hA Xo c h)
      (mvF_inv_comp hpq hA Xo c h) _ (hy pt) h1

end GlobalTheory.CompLevelStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChangeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentStabilizer_acts_by_levelChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ S : Subgroup (LevelAut Dw l), ∃ (Γ : Subgroup (LevelAut Dw l)) (ρ : Γ →* Aut (V₀ Y Z)), Γ ≤ S ∧ ActsBy Γ.subtype ρ ∧ ∀ h ∈ S, ∀ y : FrPt Xo c ℂ, LiesOn Z y → LiesOn Z (move Xo c h⁻¹ y) → h ∈ Γ := by
  first | exact @GlobalTheory.CompLevelStab.stab_acts | exact GlobalTheory.CompLevelStab.stab_acts | (intros; apply GlobalTheory.CompLevelStab.stab_acts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullback
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DilScalar

variable {D : D7}

theorem int_mul {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem incA_int (x : 𝓞 D.host.E) : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, rfl⟩

theorem idemAt_mul_int {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e P)
    {y : D.host.E} (hv : P.valuation D.host.E y ≤ 1) : finPart D (e * incA D y) ∈ intAE D := by
  obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
  have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
  have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
  have hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hc
    exact hb ((he.2 _ hb0).2 hc)
  have hq : y = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hb1]
    exact hab
  have h := int_mul (incA_int (D := D) a) hi
  rw [← RingHom.map_mul, mul_left_comm, ← map_mul (incA D), ← hq] at h
  exact h

theorem val_uniformiser (P : HeightOneSpectrum (𝓞 D.host.E)) {ϖ : 𝓞 D.host.E}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) := by
  rw [P.valuation_of_algebraMap]
  have a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have a0 : P.intValuation ϖ ≠ 0 := fun h => a2 (h ▸ zero_le')
  rw [← WithZero.exp_log a0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  omega

theorem idemSum_dil_int {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q) {N : ℕ}
    (hN : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) {ϖ : 𝓞 D.host.E}
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) :
    finPart D (e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) ∈ intAE D := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => idemAt_mul_int (hes PP hPP) ?_
  have v1 := val_uniformiser (D := D) PP (hϖ PP hPP).1 (hϖ PP hPP).2
  have v2 : PP.valuation D.host.E (N : D.host.E) ≤ WithZero.exp (-1 : ℤ) := by
    rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) N, PP.valuation_of_algebraMap]
    have := (PP.intValuation_le_pow_iff_mem (N : 𝓞 D.host.E) 1).2 (by rw [pow_one]; exact hN PP hPP)
    simpa using this
  rw [map_mul, map_inv₀, v1]
  calc PP.valuation D.host.E (N : D.host.E) * (WithZero.exp (-1 : ℤ))⁻¹
      ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.DilScalar


set_option maxHeartbeats 1000000 in
open GlobalTheory.DilScalar in
theorem GlobalTheory.DilScalar.scalar_dil_facts : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D S, mt S z = Matrix.diagonal (fun _ => e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) → SuppAt e S z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D e) S z x) ∧ (∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) → actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) ∧ (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull (z, (1 : GA D T)) Φ)) ∧ ∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT := by
  intro D S T ΛS ΛT Q e he N hN0 hN ϖ hϖ0 hϖ z hz
  have hee : e * e = e := idemSum_sq he
  have hec : e * cA D e = 0 := he.2
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hXP : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hϖ0, map_one]
  have hYZ : cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hϖ0, map_one, map_one]
  have hea : e * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) =
      e * incA D ((ϖ : D.host.E)⁻¹) := by
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hec
  have hab : (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) *
      (e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) = 1 := by
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) - incA D ((ϖ : D.host.E)⁻¹)
        - incA D (ϖ : D.host.E) + 1) * hee
      + (cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) - cA D (incA D (ϖ : D.host.E))
        - cA D (incA D ((ϖ : D.host.E)⁻¹)) + 1) * hcc
      + (incA D ((ϖ : D.host.E)⁻¹) * cA D (incA D ((ϖ : D.host.E)⁻¹)) + cA D (incA D (ϖ : D.host.E)) * incA D (ϖ : D.host.E)
        - incA D ((ϖ : D.host.E)⁻¹) - incA D (ϖ : D.host.E) - cA D (incA D (ϖ : D.host.E))
        - cA D (incA D ((ϖ : D.host.E)⁻¹)) + 2) * hec
      + e * hXP + cA D e * hYZ

  have hPint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D := incA_int ϖ
  have hPmem : ∀ u ∈ latAll S T ΛS ΛT, incA D (ϖ : D.host.E) • u ∈ latAll S T ΛS ΛT :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hPint

  have hact : ∀ t : WO S T, actO S T z⁻¹ 1 t =
      t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) := by
    intro t
    have h0 : actO S T z⁻¹ 1 t = HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z) := by
      rw [actO_eq, inv_inv, mt_one']; exact congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) => HMul.hMul M (mt S z))
        (Matrix.one_mul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)))
    rw [h0, hz]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.map_apply]
  have hmapA : ∀ t : WO S T, IsHalf e t →
      (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) =
        t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w := by
    intro t ht
    ext i j
    simp only [Matrix.map_apply]
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) -
      (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) * ht i j + t i j * hea
  have halfA : ∀ t : WO S T, IsHalf e (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) +
      cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) → IsHalf e t := by
    intro t h i j
    have h1 := h i j
    simp only [Matrix.map_apply] at h1
    linear_combination (e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) * h1
      - (e * t i j - t i j) * hab
  have halfX : ∀ t : WO S T, IsHalf e (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) → IsHalf e t := by
    intro t h i j
    have h1 := h i j
    simp only [Matrix.map_apply] at h1
    linear_combination incA D (ϖ : D.host.E) * h1 - (e * t i j - t i j) * hXP
  have hpull : ∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) →
      actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) := by
    intro Ψ hΨ
    funext t
    show Ψ (actO S T z⁻¹ (1 : GA D T)⁻¹ t) = _
    rw [inv_one, hact]
    by_cases hh : IsHalf e t
    · rw [hmapA t hh]
    · have h1 : Ψ (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) +
          (1 - e - cA D e))) = 0 := by
        by_contra h0
        exact hh (halfA t (hΨ _ h0))
      have h2 : Ψ (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = 0 := by
        by_contra h0
        exact hh (halfX t (hΨ _ h0))
      rw [h1, h2]
  refine ⟨?_, ?_, hpull, ?_, ?_⟩
  ·
    intro i j
    rw [hz]
    by_cases h : i = j
    · subst h
      rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      linear_combination (incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hcc +
        (incA D ((ϖ : D.host.E)⁻¹) + cA D (incA D (ϖ : D.host.E)) - 2) * hec
    · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]
  ·
    have hdet : (mt S z).det * (mt S z⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← mt_mul', mul_inv_cancel, mt_one', Matrix.det_one]
    refine ⟨⟨cA D e * (mt S z).det + (1 - cA D e), cA D e * (mt S z⁻¹).det + (1 - cA D e), ?_, ?_⟩, rfl⟩
    · linear_combination (cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc
    · linear_combination (cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc
  ·
    intro Φ hΦ
    have hsupp := hΦ.1
    obtain ⟨_, k, hk, hinv, hcpt⟩ := hΦ
    rw [hpull Φ hsupp]
    have hint := idemSum_dil_int he hN hϖ
    refine ⟨fun t ht => halfX t (hsupp _ ht), N * k, Nat.mul_pos (Nat.pos_of_ne_zero hN0) hk,
      fun u hu hue t => ?_, fun t ht => ?_⟩
    · have key : (t + (N * k) • u).map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) =
          t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) +
            k • ((e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) • u) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul,
          map_natCast, Nat.cast_mul]
        linear_combination (-((k : AE D) * (N : AE D) * incA D ((ϖ : D.host.E)⁻¹))) * hue i j
      dsimp only
      rw [key]
      refine hinv _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint u hu) (fun i j => ?_) _
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹) * u i j) * hee
    · have h1 := hPmem _ (hcpt _ ht)
      have h2 : incA D (ϖ : D.host.E) • k • t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = k • t := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul]
        linear_combination ((k : AE D) * t i j) * hXP
      rw [h2] at h1
      rw [mul_smul]
      exact nsmul_mem h1 N
  ·
    intro t ht hmem
    rw [hact, hmapA t ht] at hmem
    have h1 := hPmem _ hmem
    convert h1 using 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (-t i j) * hXP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullbackStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarDilationElement_support_det_pullback : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D S, mt S z = Matrix.diagonal (fun _ => e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) → SuppAt e S z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D e) S z x) ∧ (∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) → actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) ∧ (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull (z, (1 : GA D T)) Φ)) ∧ ∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT := by
  first | exact @GlobalTheory.DilScalar.scalar_dil_facts | exact GlobalTheory.DilScalar.scalar_dil_facts | (intros; apply GlobalTheory.DilScalar.scalar_dil_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfSecCoord
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM.ProjExt

theorem eq_pt_of_secCoord {o : Type} [CommRing o] {m : ℕ} {A : Type} [CommRing A] (c : o →+* A)
    (y : Sp A ⟶ PSpace o m) (hy : y ≫ PSpace.str o m = spMap c) (v : Fin (m + 1) → A)
    (h : SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v) :
    ∃ hv : Ideal.span (Set.range v) = ⊤, y = GlobalTheory.ProjSpace.pt c v hv := by
  have h1 := (RepBC.secCoord_pull (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) (𝟙 _) y v).2
    (by rwa [Category.comp_id])
  obtain ⟨hv, e⟩ := (ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c y (by rwa [Category.comp_id]) v).1 h1
  exact ⟨hv, (Category.comp_id _).symm.trans e⟩

end GlobalTheory.ZM.ProjExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartitionSelectionEvaluation
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.RowsParts

variable {Bd : BdT} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {eps : ℝ} {Fm : FamP eps} {hc : 𝒜 Fm}

theorem ev_prem {p : Prop} {q : ℝ → BdP Bd} (h : p → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc (q C)) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc fun D O c b => p → q C D O c b := by
  by_cases hp : p
  · obtain ⟨C0, h0, h⟩ := h hp
    refine ⟨C0, h0, fun C hC => ?_⟩
    obtain ⟨x0, h⟩ := h C hC
    exact ⟨x0, fun x hx hle i _ => h x hx hle i⟩
  · exact ⟨0, le_rfl, fun _ _ => ⟨0, fun _ _ _ _ h => absurd h hp⟩⟩

end GlobalTheory.Fc.RowsParts

namespace GlobalTheory.Fc

open RowsParts

end GlobalTheory.Fc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltLocusFibre
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

set_option autoImplicit false
noncomputable section
open GlobalTheory.Adelic.LinSys
namespace GlobalTheory.BoundaryFibre

theorem eff_nsmul {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

end GlobalTheory.BoundaryFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianTripleMapIsOpenImmersionOpensRange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianTripleMapIsOpenImmersionOpensRange
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sabMap_isOpenImmersion_opensRange (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j) : ∃ _ : IsOpenImmersion m.φ, m.φ.opensRange = t.G.hom ⁻¹ᵁ j.opensRange := by
  have h : IsPullback m.φ t'.G.hom t.G.hom j := m.cart.1
  have hφ : m.φ = h.isoPullback.hom ≫ pullback.fst t.G.hom j := by simp
  have hi : IsOpenImmersion m.φ := by rw [hφ]; infer_instance
  refine ⟨hi, ?_⟩
  ext1
  have h1 : Set.range m.φ = Set.range (pullback.fst t.G.hom j) := by
    rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ]
  simpa [h1] using Scheme.Pullback.range_fst t.G.hom j
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianTripleMapIsOpenImmersionOpensRangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianTripleMap_isOpenImmersion_opensRange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j), ∃ _ : IsOpenImmersion m.φ, m.φ.opensRange = t.G.hom ⁻¹ᵁ j.opensRange := by
  first | exact @GlobalTheory.sabMap_isOpenImmersion_opensRange | exact GlobalTheory.sabMap_isOpenImmersion_opensRange | (intros; apply GlobalTheory.sabMap_isOpenImmersion_opensRange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCoordOfSubsingletonPic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

noncomputable section
namespace GlobalTheory.ZM.FieldPoint

theorem exists_secCoord_of_subsingleton_pic {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} (σ : I → M.Sec)
    {A : Type} [CommRing A] [Subsingleton (CommRing.Pic A)] (x : Sp A ⟶ X) : ∃ v : I → A, SecCoord M σ x v := by
  have hL := LB.isLB_pull hM x
  obtain ⟨t, ht⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic hL
  let a := ReciprocityTheory.ChartRestriction.G.DVR.genSec t ht
  have ha : ⊤ ≤ nonzeroLocus a := (nonzeroLocus_genSec hL t ht).ge
  choose v hv using fun j => fnOn_top_bijective.2 (resG _ ha (secRatio a (secPull (σ j) x)))
  refine ⟨v, t, ht, fun i j h => ?_⟩
  have h1 := secRatio_on a (secPull (σ i) x) j (le_top.trans ha) le_rfl
  rw [resG_self, resG_self] at h1
  change _ = fnOn _ (v i) * a.f j
  rw [← resG_fnOn (le_top : _ ≤ ⊤), hv, resG_resG]
  exact h1

theorem exists_secCoord : ∀ (o : Type) [CommRing o] (m : ℕ) (K : Type) [Field K] (y : Sp K ⟶ PSpace o m),
    ∃ v : Fin (m + 1) → K, SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v :=
  fun o _ m _ _ y => exists_secCoord_of_subsingleton_pic (O1_isLB o m) _ y

end GlobalTheory.ZM.FieldPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLE
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLE
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem chartPull_g_appLE : ∀ (Y Y' : Scheme.{0}) (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) (cp : ChartPull A' A h) (i j : A'.ι), ((A'.g i j : Γ(Y', A'.U i ⊓ A'.U j)ˣ) : Γ(Y', A'.U i ⊓ A'.U j)) = (h.appLE (A.U (cp.idx i) ⊓ A.U (cp.idx j)) (A'.U i ⊓ A'.U j) (le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j)))).hom ((A.g (cp.idx i) (cp.idx j) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))ˣ) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))) := by
  intro Y Y' A' A h cp i j
  have e : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (cp.idx i) ⊓ A.U (cp.idx j)) :=
    le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j))
  apply TopCat.Presheaf.section_ext Y'.sheaf (A'.U i ⊓ A'.U j)
  intro y hy
  have h1 := congrArg Units.val (cp.g y i j hy.1 hy.2)
  rw [gm_val _ y _ hy, gm_val h y _ (e hy)] at h1
  refine h1.trans ?_
  show _ = (Y'.presheaf.germ _ y hy).hom ((Y'.presheaf.map (homOfLE e).op).hom ((h.app _).hom _))
  exact (TopCat.Presheaf.germ_res_apply Y'.presheaf _ y hy _).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLEStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPullback_lineBundle_transition_eq_appLE : ∀ (Y Y' : Scheme.{0}) (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) (cp : ChartPull A' A h) (i j : A'.ι), ((A'.g i j : Γ(Y', A'.U i ⊓ A'.U j)ˣ) : Γ(Y', A'.U i ⊓ A'.U j)) = (h.appLE (A.U (cp.idx i) ⊓ A.U (cp.idx j)) (A'.U i ⊓ A'.U j) (le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j)))).hom ((A.g (cp.idx i) (cp.idx j) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))ˣ) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))) := by
  first | exact @GlobalTheory.chartPull_g_appLE | exact GlobalTheory.chartPull_g_appLE | (intros; apply GlobalTheory.chartPull_g_appLE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.SWLit.LinAct

section Alg

variable {R : Type} [CommRing R]

variable {A : Type} [CommRing A] [Algebra R A] {α β ν X : Type} [Fintype β] [DecidableEq β]
  [AddCommGroup X] [Module R X] (e : ν ⊕ ν ≃ α)

def Del (w : Matrix α β A) : Prop := ∀ i, w (e (.inl i)) = w (e (.inr i))

def Nab (w : Matrix α β A) : Prop := ∀ i, w (e (.inl i)) = -w (e (.inr i))



variable [Invertible (2 : R)] {e} {D : Matrix α β A ≃ₗ[R] X × X} (hΔ : ∀ w, Del e w → (D w).1 = 0) (hN : ∀ w, Nab e w → (D w).2 = 0)
include hΔ hN

end Alg

end GlobalTheory.SWLit.LinAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrSplitExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitExtDVR

theorem exists_complete_dvr_split_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G →
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (g : V →+* W),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ g.IsIntegral ∧ Function.Injective g ∧ IsLocalHom g ∧
      ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)),
        E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj ((Over.pullback (spMap g)).obj G)) := by
  intro V _ _ _ _ hcV G _ hG
  haveI := hcV
  let F := AlgebraicClosure (FractionRing V)
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  have hi : Function.Injective (algebraMap V F) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective _ _)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  obtain ⟨W, hd, hc, hfin, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G hG
  have hW : Function.Injective (algebraMap V W) := fun _ _ h => hi (congrArg (fun z : W => (z : F)) h)
  have : CharZero W := charZero_of_injective_algebraMap hW
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hW
  have hl : IsLocalHom (algebraMap V W) := inferInstance
  have hint : (algebraMap V W).IsIntegral := by
    have : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
    exact Algebra.IsIntegral.isIntegral
  exact ⟨W, inferInstance, inferInstance, hd, inferInstance, algebraMap V W, hc, hint, hW, hl, hs⟩

end GlobalTheory.SplitExtDVR
end
