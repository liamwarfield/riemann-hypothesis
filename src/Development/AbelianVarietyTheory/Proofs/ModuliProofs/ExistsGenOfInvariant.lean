module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfQuotientOfRigid
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IsoDescent

variable {X X' Y Y' : Scheme.{0}}

theorem exists_gen_of_invariant (M : LB Y) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (a : ∀ j, Γ(Y', m ⁻¹ᵁ M.U j)ˣ)
    (hc : ∀ (y : Y') i j, m y ∈ M.U i → m y ∈ M.U j →
      gm (𝟙 Y') y _ (a i) = gm m y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y') y _ (a j))
    (hinv : ∀ i (y : Y') j, m y ∈ M.U j → m (t i y) ∈ M.U j → gm (t i) y _ (a j) = gm (𝟙 Y') y _ (a j)) :
    ∃ v : LB.Gen M, v.IsGen := by
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have hunit : ∀ (U : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ U)ˣ),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), res e (pullU (t i) _ a) = a) →
      ∃ b : Γ(Y, U)ˣ, pullU m U b = a := by
    intro U a ha
    obtain ⟨g, hg, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨g', hg', -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (t i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have h1 : g * g' = 1 := hinj U (by rw [map_mul, map_one, hg, hg']; exact a.mul_inv)
    exact ⟨⟨g, g', h1, (mul_comm _ _).trans h1⟩, Units.ext hg⟩
  have hex : ∀ j, ∃ b : Γ(Y, M.U j)ˣ, pullU m _ b = a j := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ M.U j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    exact hinv i y j hy (e hy)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j, y ∈ m ⁻¹ᵁ M.U j → gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (a j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans (congrArg _ (hb j))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans ((hc y i j hy.1 hy.2).trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (by rw [Category.id_comp])
    ((gm_res _ y _ hy _).trans (val j hy.2)))

variable {L : LB X} {L' : LB X'} {K K' : Type} [Fintype K] [Fintype K']

theorem lbIso_of_invariant (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (u : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε)) (hu : u.IsGen)
    (u' : LB.Gen (LB.LinComb L' (fun k => m ≫ φ' k) ε')) (hu' : u'.IsGen)
    (hinv : ∀ i y J J', Good L y J → Good L' y J' →
      val u' (t i) y J' * (val u (t i) y J)⁻¹ = val u' (𝟙 Y') y J' * (val u (𝟙 Y') y J)⁻¹) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') := by
  have l₁ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L' (fun k => m ≫ φ' k) p.1 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k
  have l₂ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L (fun k => m ≫ φ k) p.2 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have v : ∀ (r : Y' ⟶ Y') (y : Y') (p : (K' → L'.ι) × (K → L.ι)),
      r y ∈ m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) →
      gm r y _ (res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) =
        gm r y (LB.wchart L' (fun k => m ≫ φ' k) p.1) (u'.s p.1) *
          (gm r y (LB.wchart L (fun k => m ≫ φ k) p.2) (u.s p.2))⁻¹ := fun r y p h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r y _ h _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r y _ h _))))
  refine exists_gen_of_invariant (LB.div (LB.LinComb L' φ' ε') (LB.LinComb L φ ε)) m t ht hd
    (fun p => res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) (fun y p q hp hq => ?_) (fun i y p hp hp' => ?_)
  · refine (v (𝟙 Y') y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) ((gm_div _ _ m y p q ⟨hp, hq⟩).trans
      (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L' φ' ε' m y p.1 q.1 hp.1 hq.1)
        (gm_linComb L φ ε m y p.2 q.2 hp.2 hq.2))) (v (𝟙 Y') y q hq)).symm)
    rw [gen_trans hu' (𝟙 Y') y (l₁ p hp) (l₁ q hq), gen_trans hu (𝟙 Y') y (l₂ p hp) (l₂ q hq), mul_inv,
      mul_mul_mul_comm]
    simp only [trF, Category.id_comp]
  · choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    choose J' hJ' using fun χ : Y' ⟶ X' => exists_chart hL' (χ y)
    have gJ : Good L y J := hJ
    have gJ' : Good L' y J' := hJ'
    refine (v (t i) y p hp').trans (Eq.trans ?_ (v (𝟙 Y') y p hp).symm)
    rw [gen_trans hu' (t i) y (l₁ p hp') (gJ'.mem _ _), gen_trans hu (t i) y (l₂ p hp') (gJ.mem _ _),
      gen_trans hu' (𝟙 Y') y (l₁ p hp) (gJ'.mem _ _), gen_trans hu (𝟙 Y') y (l₂ p hp) (gJ.mem _ _),
      mul_inv, mul_inv, mul_mul_mul_comm, mul_mul_mul_comm (trF _ _ (𝟙 Y') _ _ _)]
    refine congrArg₂ (· * ·) ?_ (hinv i y J J' gJ gJ')
    have e : ∀ {W : Scheme.{0}} (χ : Y ⟶ W), t i ≫ m ≫ χ = 𝟙 Y' ≫ m ≫ χ := fun χ => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact congrArg₂ (fun a b => a * b⁻¹) (Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X' => gm ψ y (L'.U (p.1 k) ⊓ L'.U (J' ψ)) (L'.g (p.1 k) (J' ψ)) ^ ε' k) (e (φ' k)))
      (Finset.prod_congr rfl fun k _ => congrArg
        (fun ψ : Y' ⟶ X => gm ψ y (L.U (p.2 k) ⊓ L.U (J ψ)) (L.g (p.2 k) (J ψ)) ^ ε k) (e (φ k)))

theorem lbIso_of_gens (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (u : LB.Gen (LB.LinComb L φ ε)) (hu : u.IsGen) (u' : LB.Gen (LB.LinComb L' φ' ε'))
    (hu' : u'.IsGen) : LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') :=
  lbIso_of_invariant hL hL' φ ε φ' ε' (𝟙 Y) (I := PEmpty) PEmpty.elim (fun i => i.elim)
    (fun _ f _ => ⟨f, rfl, fun _ h => h⟩) _ (DVR.pullGen_isGen _ _ _ u hu (𝟙 Y)) _
    (DVR.pullGen_isGen _ _ _ u' hu' (𝟙 Y)) (fun i => i.elim)

def chartPullDiv (M N : LB Y) (f : Y' ⟶ Y) :
    ChartPull ((LB.div M N).pull f) (LB.div (M.pull f) (N.pull f)) (𝟙 Y') :=
  have le : ∀ J : PUnit → M.ι × N.ι, ((LB.div M N).pull f).U J ≤
      (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (N.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    ⟨mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).1, mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g (LB.div M N) f (𝟙 Y') y J J' hJ hJ').trans ((gm_div N M (𝟙 Y' ≫ f) y _ _
        ⟨(mem_pull (L := LB.div M N)).1 hJ, (mem_pull (L := LB.div M N)).1 hJ'⟩).trans (Eq.symm ((gm_div (N.pull f) (M.pull f) (𝟙 Y') y
          (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
          (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) ⟨le J hJ, le J' hJ'⟩).trans ?_)))
      exact congrArg₂ (fun a b => a * b⁻¹) (gm_pull_g M f (𝟙 Y') y _ _ (le J hJ).1 (le J' hJ').1)
        (gm_pull_g N f (𝟙 Y') y _ _ (le J hJ).2 (le J' hJ').2) }

def chartPullFlat (L : LB X) (F : X' ⟶ X) (e : ℤ) (ψ : K → (Y ⟶ X')) (ε : K → ℤ) (f : Y' ⟶ Y) :
    ChartPull ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f)
      (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e)) (𝟙 Y') :=
  have mem : ∀ (J : PUnit → K → PUnit → L.ι) (y : Y'),
      y ∈ ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J →
      ∀ k, ψ k (f y) ∈ LB.wchart L (fun _ : PUnit => F) (J PUnit.unit k) := fun J y hy k =>
    Set.mem_iInter.1 ((mem_pull (L := LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).1 hy) k
  have le : ∀ J : PUnit → K → PUnit → L.ι,
      ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J ≤
        LB.wchart L (fun k => f ≫ ψ k ≫ F) (fun k => J PUnit.unit k PUnit.unit) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem J y hy k) PUnit.unit
  { idx := fun J k => J PUnit.unit k PUnit.unit
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g _ f (𝟙 Y') y J J' hJ hJ').trans ((gm_linComb
        (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε (𝟙 Y' ≫ f) y (J PUnit.unit) (J' PUnit.unit)
        (Set.mem_iInter.2 (mem J y hJ)) (Set.mem_iInter.2 (mem J' y hJ'))).trans (Eq.trans
          (Finset.prod_congr rfl fun k _ => ?_) (gm_linComb L _ _ (𝟙 Y') y _ _ (le J hJ) (le J' hJ')).symm))
      refine (congrArg (· ^ ε k) (gm_linComb L (fun _ : PUnit => F) (fun _ => e) ((𝟙 Y' ≫ f) ≫ ψ k) y _ _
        (mem J y hJ k) (mem J' y hJ' k))).trans ?_
      rw [Fintype.prod_unique, ← zpow_mul, mul_comm e]
      simp only [Category.assoc] }

theorem exists_gen_div_pull {W : Scheme.{0}} (L : LB X) (L' : LB X') (F : W ⟶ X) (F' : W ⟶ X') (e e' : ℤ)
    (ψ : K → (Y ⟶ W)) (ε : K → ℤ) (f : Y' ⟶ Y)
    (H : LBIso (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e))
      (LB.LinComb L' (fun k => f ≫ ψ k ≫ F') (fun k => ε k * e'))) :
    ∃ t : LB.Gen ((LB.div (LB.LinComb (LB.LinComb L' (K := PUnit) (fun _ => F') (fun _ => e')) ψ ε)
      (LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).pull f), t.IsGen := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullFlat L F e ψ ε f) (chartPullFlat L' F' e' ψ ε f)
  exact gen_chartPull (chartPullDiv _ _ f) w hw

end GlobalTheory.IsoDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfProper
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

section Pts

variable {k : Type} [Field k] [IsAlgClosed k]

theorem hom_ext_pts {X Y : Over (Sp k)} (hX : Smooth X.hom) [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ X.hom hX).1
  exact Over.OverMorphism.ext (ComplexPoints.hom_ext_of_points X.hom Y.hom (by rw [Over.w, Over.w]) fun x hx =>
    congrArg (fun q => q.left) (h (Over.homMk x hx)))

theorem exists_lift_pt {S : Scheme.{0}} {A B : Over S} (ψ : A ⟶ B) [LocallyOfFiniteType ψ.left] [Surjective ψ.left]
    (t : Sp k ⟶ S) (y : Over.mk t ⟶ B) : ∃ x : Over.mk t ⟶ A, x ≫ ψ = y := by
  let y' : Sp k ⟶ B.left := y.left
  obtain ⟨z, -⟩ := (pullback.snd ψ.left y').surjective (default : PrimeSpectrum k)
  obtain ⟨x, hx, -⟩ := ComplexPoints.exists_point_mem (pullback.snd ψ.left y') (Z := Set.univ)
    isClosed_univ.isLocallyClosed ⟨z, trivial⟩
  have e : (x ≫ pullback.fst ψ.left y') ≫ ψ.left = y' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  exact ⟨Over.homMk (x ≫ pullback.fst ψ.left y') (by rw [← Over.w ψ, ← Category.assoc, e]; exact Over.w y),
    Over.OverMorphism.ext e⟩

theorem exists_fac {A B Y : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj Y] (hA : Smooth A.hom) [IsSeparated Y.hom]
    (ψ₀ : A ⟶ B) [IsMonHom ψ₀] [Etale ψ₀.left] [Surjective ψ₀.left] [QuasiCompact ψ₀.left] (ψ : A ⟶ Y) [IsMonHom ψ]
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ ψ₀ = 1 → x ≫ ψ = 1) : ∃ α : B ⟶ Y, ψ₀ ≫ α = ψ := by
  let R : Over (Sp k) := Over.mk (pullback.fst ψ₀.left ψ₀.left ≫ A.hom)
  let p₁ : R ⟶ A := Over.homMk (pullback.fst _ _) rfl
  let p₂ : R ⟶ A := Over.homMk (pullback.snd _ _) (by
    show _ = pullback.fst ψ₀.left ψ₀.left ≫ A.hom
    rw [← Over.w ψ₀, ← pullback.condition_assoc])
  have e₀ : p₁ ≫ ψ₀ = p₂ ≫ ψ₀ := Over.OverMorphism.ext pullback.condition
  have e : p₁ ≫ ψ = p₂ ≫ ψ := hom_ext_pts (inferInstanceAs (Smooth (pullback.fst ψ₀.left ψ₀.left ≫ A.hom))) fun x => by
    have := h ((x ≫ p₁) * (x ≫ p₂)⁻¹) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, e₀, Category.assoc, mul_inv_cancel])
    rw [MonObj.mul_comp, GrpObj.inv_comp, mul_inv_eq_one, Category.assoc, Category.assoc] at this
    exact this
  have e' : pullback.fst ψ₀.left ψ₀.left ≫ ψ.left = pullback.snd ψ₀.left ψ₀.left ≫ ψ.left :=
    congrArg (fun q => q.left) e
  have hd : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left), g₁ ≫ ψ₀.left = g₂ ≫ ψ₀.left → g₁ ≫ ψ.left = g₂ ≫ ψ.left :=
    fun g₁ g₂ hg => by
      rw [← pullback.lift_fst g₁ g₂ hg, Category.assoc, e', pullback.lift_snd_assoc]
  have f := EffectiveEpi.fac ψ₀.left ψ.left hd
  refine ⟨Over.homMk (EffectiveEpi.desc ψ₀.left ψ.left hd) ?_, Over.OverMorphism.ext f⟩
  rw [← cancel_epi ψ₀.left, reassoc_of% f, Over.w, Over.w]

theorem isIso_of_mono {A B : Over (Sp k)} (α : A ⟶ B) [IsProper A.hom] [IsSeparated B.hom] (hB : Smooth B.hom)
    [Mono α.left] (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ B, ∃ x, x ≫ α = y) : IsIso α := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ B.hom hB).1
  have : IsProper (α.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper α.left := IsProper.of_comp α.left B.hom
  have : IsClosedImmersion α.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have : Surjective α.left := ComplexPoints.surjective_of_geomPoints_lift B.hom (𝟙 (Sp k)) α.left
    α.left.isClosedEmbedding.isClosed_range fun y hy => by
      obtain ⟨x, hx⟩ := h (Over.homMk y hy)
      exact ⟨x.left, congrArg (fun q => q.left) hx⟩
  have : IsIso α.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map α) := ‹_›
  exact isIso_of_reflects_iso α (Over.forget _)


omit [IsAlgClosed k] in
theorem toUnit_comp_injective {K : Type} [Field K] (x : Sp K ⟶ Sp k) (A : Over (Sp k)) :
    Function.Injective (fun z : 𝟙_ (Over (Sp k)) ⟶ A => toUnit (Over.mk x) ≫ z) := by
  have : Surjective x := ⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have : Epi x := Flat.epi_of_flat_of_surjective x
  intro a b h
  have e : (toUnit (Over.mk x)).left = x := by simp
  have h' : (toUnit (Over.mk x)).left ≫ a.left = (toUnit (Over.mk x)).left ≫ b.left := congrArg (fun q => q.left) h
  rw [e] at h'
  exact Over.OverMorphism.ext ((cancel_epi x).1 h')

theorem exists_of_torsion (hM : Out.MulNSt) (P : Out.PolAV (Sp k)) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ Sp k) {n : ℕ} (hk : (n : k) ≠ 0) (hK : (n : K) ≠ 0) (z : Over.mk x ⟶ P.A) (hz : z ^ n = 1) :
    ∃ z₀ : 𝟙_ (Over (Sp k)) ⟶ P.A, toUnit (Over.mk x) ≫ z₀ = z := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have c₁ : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} = n ^ (2 * P.g) := (hM _ P n hn).2.2.2.2 k (𝟙 _) hk
  have c₂ := (hM _ P n hn).2.2.2.2 K x hK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} → {y : Over.mk x ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨toUnit _ ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (toUnit_comp_injective x _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, congrArg Subtype.val ha⟩

end Pts

theorem exists_ptsEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (y : T.left ⟶ S) (e : T.hom ≫ f = y) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  subst e
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem unitOn_bijective (R : Type) [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem unitOn_pow {R : Type} [CommRing R] (c : Rˣ) (n : ℕ) : unitOn (c ^ n) = unitOn c ^ n := map_pow _ _ _

theorem unitOn_one {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := map_one _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isAbelianScheme_of_proper {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩

theorem exists_dim {k : Type} [Field k] (t : SAB H (Sp k)) : ∃ g, SmoothOfRelativeDimension g t.G.hom := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  exact exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum k))

abbrev polOf {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L)
    (hk : Out.KTriv t.G t.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g t.G.hom) : Out.PolAV S where
  A := t.G
  isAb := isAbelianScheme_of_proper t hp
  g := g
  smoothDim := hg
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => ⟨⊤, trivial, by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := ha
  ktriv := hk

end GlobalTheory.HeckePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.CoordMove
open GlobalTheory.ZM.RepBC

theorem isUnit_cst_id {R : Type} [CommRing R] (p : Sp R) (a : R) : IsUnit (cst (𝟙 (Sp R)) p a) ↔ a ∉ p.asIdeal := by
  rw [cst, gs_eq _ _ ⊤ trivial]
  refine ((Sp R).mem_basicOpen (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) p trivial).symm.trans ?_
  have := basicOpen_eq_of_affine (R := CommRingCat.of R) a
  exact (congrArg (fun U : (Sp R).Opens => p ∈ U) this).to_iff

theorem secCoord_iff {X : Scheme.{0}} (M : LB X) {I : Type} (th : I → M.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X)
    (v : I → R) : SecCoord M th x v ↔ ∃ τ : (M.pull x).Gen, τ.IsGen ∧ ∀ (i : I) (j : PUnit → M.ι) (p : Sp R),
      p ∈ (M.pull x).U j → gs x p _ ((th i).f (j PUnit.unit)) =
        cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := by
  refine exists_congr fun τ => and_congr_right fun _ => forall₂_congr fun i j => ?_
  have l : ∀ (h : (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit)) (p : Sp R), p ∈ (M.pull x).U j →
      gs (𝟙 (Sp R)) p ((M.pull x).U j) ((x.appLE _ _ h).hom ((th i).f (j PUnit.unit))) =
        gs x p _ ((th i).f (j PUnit.unit)) := fun h p hp =>
    (gs_appLE x _ _ h (𝟙 _) p hp _).trans (by rw [Category.id_comp])
  have r : ∀ (p : Sp R), p ∈ (M.pull x).U j → gs (𝟙 (Sp R)) p ((M.pull x).U j)
      (resG (Sp R) le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) *
        (show Γ(Sp R, (M.pull x).U j) from (τ.s j).val)) =
      cst (𝟙 (Sp R)) p (v i) * (gm (𝟙 (Sp R)) p ((M.pull x).U j) (τ.s j)).val := fun p hp =>
    (gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_res _ p le_top hp _) (gs_unit _ p _ hp _))
  exact ⟨fun h p hp => (l (pull_le M x j) p hp).symm.trans ((congrArg _ (h _)).trans (r p hp)),
    fun h e => fn_ext fun p hp => (l e p hp).trans ((h p hp).trans (r p hp).symm)⟩

theorem secCoord_down {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (H : LBIso L' (L.pull F)) {I : Type} (th : I → L.Sec) :
    ∃ th' : I → L'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R),
      SecCoord L' th' x v ↔ SecCoord L th (x ≫ F) v := by
  obtain ⟨w, hw⟩ := H
  have hw' := (isGen_iff w).1 hw
  choose th' h' using fun i => sec_pull_down hw' hL hL' (th i)
  refine ⟨th', fun R _ x v => ?_⟩
  have e : ∀ (p : Sp R) (j : PUnit → L.ι) (k : PUnit → L'.ι),
      pw w (fun _ : PUnit => x) (fun _ => 1) (𝟙 _) p j k = gw w x p (j PUnit.unit) (k PUnit.unit) := fun p j k => by
    rw [pw, Fintype.prod_unique, zpow_one, Category.id_comp]
  rw [secCoord_iff, secCoord_iff]
  constructor
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := exists_up hw' hL hL' τ hτ
    refine ⟨t, ht, fun i j p hp => ?_⟩
    obtain ⟨k, hk⟩ := exists_chart hL' (x p)
    have hk' : p ∈ (L'.pull x).U (fun _ => k) := mem_pull.2 hk
    have h₁ := h' i _ x p (j PUnit.unit) k (mem_pull₂.1 hp) hk
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p j (fun _ => k) hp hk')
    rw [e, Units.val_mul] at h₂
    refine h₁.trans ((congrArg (_ * ·) (h i (fun _ => k) p hk')).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) h₂.symm)
  · rintro ⟨τ, hτ, h⟩
    obtain ⟨t, ht, hv⟩ := CubTransport.exists_down_units hw' hL hL' (φ' := fun _ : PUnit => x) τ hτ
    refine ⟨t, ht, fun i k p hp => ?_⟩
    obtain ⟨j, hj⟩ := exists_chart hL (F (x p))
    have hj' : p ∈ (L.pull (x ≫ F)).U (fun _ => j) := mem_pull₂.2 hj
    have h₁ := h' i _ x p j (k PUnit.unit) hj (mem_pull.1 hp)
    have h₂ := congrArg Units.val (hv _ (𝟙 _) p (fun _ => j) k hj' hp)
    rw [e, Units.val_mul] at h₂
    refine (Units.mul_right_inj (gw w x p j (k PUnit.unit))).1 (h₁.symm.trans ((h i (fun _ => j) p hj').trans ?_))
    exact (congrArg (_ * ·) h₂).trans (mul_left_comm _ _ _)

theorem mem_nonzeroLocus_iff {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {R : Type} [CommRing R]
    {x : Sp R ⟶ X} {v : I → R} (i : I) (p : Sp R) (h : SecCoord M th x v) :
    x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal := by
  obtain ⟨τ, -, h⟩ := (secCoord_iff M th x v).1 h
  have key : ∀ k, x p ∈ M.U k → (IsUnit (gs (𝟙 X) (x p) _ ((th i).f k)) ↔ v i ∉ p.asIdeal) := fun k hk => by
    have e := h i (fun _ => k) p (mem_pull.2 hk)
    rw [gs_stalkMap x p _ hk] at e
    rw [← isUnit_cst_id, ← isUnit_map_iff (x.stalkMap p).hom]
    exact (congrArg IsUnit e).to_iff.trans (Units.isUnit_mul_units _ _)
  rw [mem_nonzeroLocus]
  refine ⟨fun ⟨k, hk, u⟩ => (key k hk).1 u, fun u => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart hM (x p)
  exact ⟨k, hk, (key k hk).2 u⟩

theorem secCoord_pull_iso_locus : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (X' : Scheme.{0}) (π : X' ⟶ X), ∃ th' : I → (M.pull π).Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v) ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → ∃ th' : I → M'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), SecCoord M' th' x v ↔ SecCoord M th x v) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R) (i : I) (p : Sp R), SecCoord M th x v → (x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal) := by
  intro X M I th hM
  refine ⟨fun X' π => ⟨fun i => secPull M π (th i), fun R _ x v => secCoord_pull M th π x v⟩, fun M' hM' H => ?_,
    fun R _ x v i p h => mem_nonzeroLocus_iff hM i p h⟩
  obtain ⟨th', h⟩ := secCoord_down hM hM'
    (LBIso.chartPull (chartPullId M') (chartPullPull M (𝟙 X) (𝟙 X) rfl) (LBIso.symm H)) th
  refine ⟨th', fun R _ x v => ?_⟩
  have := h R x v
  rwa [Category.comp_id] at this

end GlobalTheory.ZM.CoordMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionCoordinates_pull_iso_nonzeroLocus : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (X' : Scheme.{0}) (π : X' ⟶ X), ∃ th' : I → (M.pull π).Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X') (v : I → R), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v) ∧ (∀ M' : LB X, M'.IsLB → LBIso M M' → ∃ th' : I → M'.Sec, ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), SecCoord M' th' x v ↔ SecCoord M th x v) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R) (i : I) (p : Sp R), SecCoord M th x v → (x p ∈ Out.nonzeroLocus (th i) ↔ v i ∉ p.asIdeal) := by
  first | exact @GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus | exact GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus | (intros; apply GlobalTheory.ZM.CoordMove.secCoord_pull_iso_locus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIff
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIff
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.WeilFieldExt

open GlobalTheory.CommPairing ReciprocityTheory.ChartRestriction.G.Out

theorem corr_of_val_epi {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (q : Y' ⟶ Y) [Epi q]
    (hq : ∀ U : Y.Opens, Function.Injective (q.app U).hom)
    (h : ∀ y J, Good L y J → val t q y J = val t' q y J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  have inj : Function.Injective (pullU q (LB.wchart L φ j ⊓ LB.wchart L φ' j')) := fun a b e =>
    Units.ext (hq _ (congrArg Units.val e))
  apply inj
  refine unit_ext fun y hy => ?_
  have hy' : q y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hy
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun k => q ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    intro a b e
    have e := (cancel_epi q).1 e
    rcases a with a | a <;> rcases b with b | b
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy'.1 a, Set.mem_iInter.1 hy'.2 a])
  have := h y J hJ
  rw [val_of t _ y J j (fun k => e (.inl k)), val_of t' _ y J j' (fun k => e (.inr k))] at this
  exact (gm_id_pull q y _ hy' _).trans ((gm_res _ y _ hy' _).trans (this.trans
    ((gm_res _ y _ hy' _).symm.trans (gm_id_pull q y _ hy' _).symm)))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  refine (IsPullback.of_right (h₁₁ := (h ▷ A).left) (v₁₁ := pullback.fst T'.hom A.hom)
    (h₁₂ := pullback.snd T.hom A.hom) (v₁₂ := pullback.fst T.hom A.hom) (h₂₁ := h.left) (h₂₂ := T.hom)
    (v₁₃ := A.hom) ?_ ?_ (IsPullback.of_hasPullback T.hom A.hom).flip)
  · have e : (h ▷ A).left ≫ pullback.snd T.hom A.hom = pullback.snd T'.hom A.hom :=
      congrArg (fun q => q.left) (whiskerRight_snd h A)
    rw [e, Over.w h]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  · exact congrArg (fun q => q.left) (whiskerRight_fst h A)

theorem commIsOf_descend (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    [Epi (h ▷ A).left] (hq : ∀ U, Function.Injective ((h ▷ A).left.app U).hom)
    {θx θy : ThetaGrp A L k T} {a b : ThetaGrp A L k T'} (ha : a.pt = h ≫ θx.pt) (hb : b.pt = h ≫ θy.pt)
    {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k a b (Units.map h.left.appTop.hom.toMonoidHom c)) :
    CommIsOf A L k θx θy c := by
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1
    (commIsOf_change globalFns_holds hA hL (hx.trans ha.symm) (hy.trans hb.symm) H)
  refine corr_of_val_epi hL (h ▷ A).left hq fun z J hJ => ?_
  have key : ∀ θ θ' : ThetaGrp A L k T,
      val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) (h ▷ A).left z J =
        tval θ (h ▷ A).left z J * tval θ' ((h ▷ A).left ≫ (translT A θ.pt).left) z J := fun θ θ' =>
    (val_mul hJ _ _ _).trans (congrArg (tval θ (h ▷ A).left z J * ·) (val_pull hJ _ _ _))
  have e := H' _ (𝟙 _) z J hJ
  have t : ∀ x : T ⟶ A, (𝟙 _ ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (h ▷ A).left ≫ (translT A x).left := fun x => by
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (𝟙 _ ≫ (fst T' A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom c) =
      gm ((h ▷ A).left ≫ (fst T A).left) z ⊤ c := by
    refine (gm_pull (𝟙 _ ≫ (fst T' A).left) h.left z ⊤ trivial c).trans ?_
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t, g, Category.id_comp] at e
  exact (key θx θy).trans (e.trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key θy θx) (H1.val_constGen L c _ z J))).symm)

theorem weilIs_iff (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} [Unique T.left] (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k x y c ↔
      ∃ θx θy : ThetaGrp A L k T, θx.pt = x ∧ θy.pt = y ∧ CommIsOf A L k θx θy c := by
  constructor
  · intro H
    obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H default
    obtain rfl : V = ⊤ := eq_top_iff.2 fun p _ => by rwa [Unique.eq_default p]
    let s : T ⟶ overRes (⊤ : T.left.Opens) := Over.homMk T.left.topIso.inv (by
      show T.left.topIso.inv ≫ T.left.topIso.hom ≫ T.hom = T.hom
      rw [Iso.inv_hom_id_assoc])
    have w : s.left ≫ (⊤ : T.left.Opens).ι = 𝟙 _ := T.left.topIso.inv_hom_id
    have w' : s ≫ overResι ⊤ = 𝟙 T := Over.OverMorphism.ext w
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL s (hc θx θy hx hy)
    rw [hx, ← Category.assoc, w', Category.id_comp] at ha
    rw [hy, ← Category.assoc, w', Category.id_comp] at hb
    have e : Units.map s.left.appTop.hom.toMonoidHom (unitRes ⊤ c) = c := by
      apply Units.ext
      have := congrArg (fun q => q.appTop.hom c.val) w
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
      exact this
    rw [e] at H'
    exact ⟨a, b, ha, hb, H'⟩
  · rintro ⟨θx, θy, rfl, rfl, H⟩ p
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H
    exact ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' =>
      commIsOf_change globalFns_holds hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩

theorem exists_lift_descend (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    (hd : ∀ M : LB (T ⊗ A).left, M.IsLB → (∃ t : (M.pull (h ▷ A).left).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (x : T ⟶ A) (a : ThetaGrp A L k T') (ha : a.pt = h ≫ x) : ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  obtain ⟨t, ht⟩ := hd (thetaLB A L k x) (DVR.linComb_isLB L hL _ _)
    (gen_chartPull (chartPullOut L ![(snd T A).left, (translPt A x).left] ![k, -k] (h ▷ A).left
      ![(snd T' A).left, (translPt A a.pt).left] (fun i => by
        fin_cases i
        · exact (congrArg (fun q => q.left) (whiskerRight_snd h A)).symm
        · show (translPt A a.pt).left = (h ▷ A).left ≫ (translPt A x).left
          rw [← Over.comp_left, whisker_translPt, ha])) a.φ a.isGen)
  exact ⟨⟨x, t, ht⟩, rfl⟩

theorem unitOn_map {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    unitOn (Units.map i.toMonoidHom c) = Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) := by
  apply Units.ext
  exact congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))

end GlobalTheory.WeilFieldExt

namespace GlobalTheory


open WeilFieldExt CommPairing in
theorem weilIs_fieldExt_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) (L : LB G.left) (k : ℤ) (y y' : Over.mk x ⟶ G) (c : Kˣ), IsAbelianScheme G → L.IsLB → (Out.WeilIs G L k ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y') (unitOn (Units.map i.toMonoidHom c)) ↔ Out.WeilIs G L k y y' (unitOn c)) := by
  intro S G _ K Ω _ _ i x L k y y' c hG hL
  rw [unitOn_map]
  let h : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  refine ⟨fun H => ?_, fun H => weilIs_pull globalFns_holds hG hL h H⟩
  letI : Unique (Over.mk x).left := inferInstanceAs (Unique (PrimeSpectrum K))
  letI : Unique (Over.mk (spMap i ≫ x)).left := inferInstanceAs (Unique (PrimeSpectrum Ω))
  obtain ⟨a, b, ha, hb, Hc⟩ := (weilIs_iff hG hL _ _ _).1 H
  have pb : IsPullback (h ▷ G).left (fst _ G).left (fst _ G).left (spMap i) := isPullback_whisker h
  obtain ⟨e, -, -, -, inj⟩ := (FieldBaseChange.epi_and_isMonHom_iff K Ω i).1 _ _ _ _ _ pb
  have hd := (GlobalTheory.T.lineBundle_trivial_iso_descend_field K Ω i _ _ _ _ _
    (by have := hG.smooth; exact inferInstanceAs (Smooth (pullback.fst x G.hom)))
    (by have := hG.proper; exact inferInstanceAs (IsProper (pullback.fst x G.hom)))
    (by have := hG.geomConnected; exact inferInstanceAs (GeometricallyConnected (pullback.fst x G.hom))) pb).1
  obtain ⟨θ, rfl⟩ := exists_lift_descend hL h hd y a ha
  obtain ⟨θ', rfl⟩ := exists_lift_descend hL h hd y' b hb
  exact (weilIs_iff hG hL _ _ _).2 ⟨θ, θ', rfl, rfl, commIsOf_descend hG hL h inj ha hb Hc⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_fieldExtension_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) (L : LB G.left) (k : ℤ) (y y' : Over.mk x ⟶ G) (c : Kˣ), IsAbelianScheme G → L.IsLB → (Out.WeilIs G L k ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y') (unitOn (Units.map i.toMonoidHom c)) ↔ Out.WeilIs G L k y y' (unitOn c)) := by
  first | exact @GlobalTheory.weilIs_fieldExt_iff | exact GlobalTheory.weilIs_fieldExt_iff | (intros; apply GlobalTheory.weilIs_fieldExt_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

namespace SabMapDescent

section Bundles

variable {X Y : Scheme.{0}}

def chartPullDivPull (A B : LB X) (h : Y ⟶ X) :
    ChartPull ((LB.div B A).pull h) (LB.div (B.pull h) (A.pull h)) (𝟙 Y) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have b := mem_pull.1 hj'
    refine (gm_pull_g _ h (𝟙 Y) y J J' hj hj').trans ((gm_div A B (𝟙 Y ≫ h) y _ _ ⟨a, b⟩).trans (Eq.symm ?_))
    refine (gm_div (A.pull h) (B.pull h) (𝟙 Y) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, ⟨mem_pull.2 b.1, mem_pull.2 b.2⟩⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹) (gm_pull_g B h (𝟙 Y) y _ _ (mem_pull.2 a.1) (mem_pull.2 b.1))
      (gm_pull_g A h (𝟙 Y) y _ _ (mem_pull.2 a.2) (mem_pull.2 b.2))

theorem lbIso_of_gen_of_gen {A B : LB X} (s : A.Gen) (hs : s.IsGen) (t : B.Gen) (ht : t.IsGen) : LBIso A B := by
  refine ⟨⟨fun p => res (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ _) (t.s p.1) *
    (res (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ _) (s.s p.2))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have v : ∀ p : B.ι × A.ι, y ∈ B.U p.1 ⊓ A.U p.2 → gm (𝟙 X) y (B.U p.1 ⊓ A.U p.2)
      (res (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ _) (t.s p.1) *
        (res (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ _) (s.s p.2))⁻¹) =
      gm (𝟙 X) y _ (t.s p.1) * (gm (𝟙 X) y _ (s.s p.2))⁻¹ := fun p hp => by
    rw [map_mul, map_inv, gm_res _ y _ hp, gm_res _ y _ hp]
  have w : ∀ {C : LB X} (c : C.Gen), c.IsGen → ∀ i j, y ∈ C.U i → y ∈ C.U j →
      gm (𝟙 X) y _ (c.s i) = gm (𝟙 X) y _ (C.g i j) * gm (𝟙 X) y _ (c.s j) := fun {C} c hc i j hi hj => by
    have hm : (𝟙 X : X ⟶ X) y ∈ C.U i ⊓ C.U j := ⟨hi, hj⟩
    have := congrArg (gm (𝟙 X) y _) (hc i j)
    rwa [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at this
  refine ((gm_res _ y _ hy _).trans (v p hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [w t ht p.1 q.1 hy.1.1 hy.2.1, w s hs p.2 q.2 hy.1.2 hy.2.2, mul_inv, _root_.mul_mul_mul_comm]

end Bundles

def IsQuot {Γ : Type} [Group Γ] {X X' : Scheme.{0}} (ρ : Γ →* Aut X) (π : X ⟶ X') : Prop :=
  IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧
    ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) →
      f ∈ Set.range (π.app V).hom

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem IsQuot.epi {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π) : Epi π :=
  ⟨fun {T} a b e => (quotient_existsUnique_comp_eq Γ X X' ρ π h T (π ≫ a)
    fun g => by rw [← Category.assoc, h.2.1 g]).unique rfl e.symm⟩

theorem IsQuot.epi_of_isPullback {X X' Y Y' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π)
    {φ : Y ⟶ Y'} {p : Y ⟶ X} {p' : Y' ⟶ X'} (H : IsPullback φ p p' π) (hp : Flat p') : Epi φ := by
  have hbase := quotient_flat_baseChange Γ X X' Y Y' ρ π φ p p' h H hp
  obtain ⟨hex, hall⟩ := hbase
  obtain ⟨τ, hτ⟩ := hex
  exact IsQuot.epi (hall τ hτ)

omit [Finite Γ] in
theorem IsQuot.isReduced {X X' : Scheme.{0}} {ρ : Γ →* Aut X} {π : X ⟶ X'} (h : IsQuot ρ π) [IsReduced X] :
    IsReduced X' :=
  ⟨fun V => isReduced_of_injective (π.app V).hom (h.2.2 V).1⟩

theorem exists_isPullback {U U' X' P P' P₁ : Scheme.{0}} {ρ : Γ →* Aut U} {r : U ⟶ U'} (hq : IsQuot ρ r)
    {j : U' ⟶ X'} {p : P ⟶ U} {p' : P' ⟶ U'} {p₁ : P₁ ⟶ X'} [Flat p'] [Flat p₁] {φ : P ⟶ P'} {n : P ⟶ P₁}
    (hφ : IsPullback φ p p' r) (hn : IsPullback n p p₁ (r ≫ j)) (τ : Γ →* Aut P)
    (hτ : ∀ g, (τ g).asIso.hom ≫ p = p ≫ (ρ g).asIso.hom ∧ (τ g).asIso.hom ≫ φ = φ ∧ (τ g).asIso.hom ≫ n = n) :
    ∃ ψ : P' ⟶ P₁, φ ≫ ψ = n ∧ IsPullback ψ p' p₁ j := by
  have hφq : IsQuot τ φ := (quotient_flat_baseChange Γ U U' P P' ρ r φ p p' hq hφ inferInstance).2 τ
    fun g => ⟨(hτ g).2.1, (hτ g).1⟩
  have := hφq.epi
  obtain ⟨ψ, hψ, -⟩ := quotient_existsUnique_comp_eq Γ _ _ τ φ hφq _ n fun g => (hτ g).2.2
  have w : ψ ≫ p₁ = p' ≫ j := by
    rw [← cancel_epi φ, ← Category.assoc, hψ, hn.w, ← Category.assoc, ← hφ.w, Category.assoc]
  have H := IsPullback.of_hasPullback p₁ j
  let θ : P' ⟶ pullback p₁ j := pullback.lift ψ p' w
  have h₁ : θ ≫ pullback.fst p₁ j = ψ := pullback.lift_fst _ _ _
  have h₂ : θ ≫ pullback.snd p₁ j = p' := pullback.lift_snd _ _ _
  have hκ : IsPullback (φ ≫ θ) p (pullback.snd p₁ j) r :=
    IsPullback.of_right (by rw [Category.assoc, h₁, hψ]; exact hn) (by rw [Category.assoc, h₂, hφ.w]) H
  have hκq : IsQuot τ (φ ≫ θ) := (quotient_flat_baseChange Γ U U' P _ ρ r _ p _ hq hκ inferInstance).2 τ
    fun g => ⟨by rw [← Category.assoc, (hτ g).2.1], (hτ g).1⟩
  have := hκq.epi
  obtain ⟨σ, hσ, -⟩ := quotient_existsUnique_comp_eq Γ _ _ τ _ hκq _ φ fun g => (hτ g).2.1
  have : IsIso θ := ⟨σ, by rw [← cancel_epi φ, ← Category.assoc, hσ, Category.comp_id],
    by rw [← cancel_epi (φ ≫ θ), ← Category.assoc, hσ, Category.comp_id]⟩
  refine ⟨ψ, hψ, ?_⟩
  have := (IsPullback.of_horiz_isIso (fst := θ) (snd := p') (f := pullback.snd p₁ j) (g := 𝟙 U')
    ⟨by rw [h₂, Category.comp_id]⟩).paste_horiz H
  rwa [h₁, Category.id_comp] at this

theorem isGrpPullback_of_quot {U U' X' : Scheme.{0}} {ρ : Γ →* Aut U} {r : U ⟶ U'} (hq : IsQuot ρ r)
    {j : U' ⟶ X'} {G : Over U} {G' : Over U'} {G₁ : Over X'} [GrpObj G] [GrpObj G'] [GrpObj G₁] [Flat G'.hom]
    {φ : G.left ⟶ G'.left} {ψ : G'.left ⟶ G₁.left} (hφ : IsGrpPullback G G' r φ)
    (hn : IsGrpPullback G G₁ (r ≫ j) (φ ≫ ψ)) (hψ : IsPullback ψ G'.hom G₁.hom j) :
    IsGrpPullback G' G₁ j ψ := by
  have key : ∀ (T : Over U') (x y : T ⟶ G'), Flat T.hom →
      (pushPt hψ.w x * pushPt hψ.w y).left = (x * y).left ≫ ψ := by
    intro T x y hT
    have H := IsPullback.of_hasPullback T.hom r
    have := hq.epi_of_isPullback H hT
    let q := pullback.fst T.hom r
    let W : Over U := Over.mk (pullback.snd T.hom r)
    let l : (T ⟶ G') → (W ⟶ G) := fun z => Over.homMk
      (hφ.1.lift (q ≫ z.left) (pullback.snd T.hom r) (by rw [Category.assoc, Over.w z]; exact H.w))
      (hφ.1.lift_snd _ _ _)
    have hl : ∀ z, (l z).left ≫ φ = q ≫ z.left := fun z => hφ.1.lift_fst _ _ _
    let q' : Over.mk (W.hom ≫ r) ⟶ T := Over.homMk q H.w
    let q₁ : Over.mk (W.hom ≫ r ≫ j) ⟶ Over.mk (T.hom ≫ j) := Over.homMk q (by
      show q ≫ T.hom ≫ j = pullback.snd T.hom r ≫ r ≫ j
      rw [← Category.assoc, H.w, Category.assoc])
    have e₁ := hφ.2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
    have e₂ := hn.2 W (l x) (l y) (q₁ ≫ pushPt hψ.w x) (q₁ ≫ pushPt hψ.w y)
      (by rw [← Category.assoc (l x).left, hl, Category.assoc]; rfl)
      (by rw [← Category.assoc (l y).left, hl, Category.assoc]; rfl)
    rw [← MonObj.comp_mul] at e₁ e₂
    rw [← Category.assoc (l x * l y).left, ← e₁] at e₂
    rw [← cancel_epi q, ← Category.assoc q]
    exact e₂
  refine ⟨hψ, fun T x y x₀ y₀ hx hy => ?_⟩
  have hf : Flat (G' ⊗ G').hom := inferInstanceAs (Flat (pullback.fst G'.hom G'.hom ≫ G'.hom))
  have e := key (G' ⊗ G') (fst _ _) (snd _ _) hf
  let z : Over.mk (T.hom ≫ j) ⟶ Over.mk ((G' ⊗ G').hom ≫ j) := Over.homMk (lift x y).left (by
    show (lift x y).left ≫ (G' ⊗ G').hom ≫ j = T.hom ≫ j
    rw [← Category.assoc, Over.w])
  have hx' : x₀ = z ≫ pushPt hψ.w (fst _ _) := Over.OverMorphism.ext (by
    show _ = (lift x y).left ≫ (fst G' G').left ≫ ψ
    rw [← Category.assoc, ← Over.comp_left, lift_fst, hx])
  have hy' : y₀ = z ≫ pushPt hψ.w (snd _ _) := Over.OverMorphism.ext (by
    show _ = (lift x y).left ≫ (snd G' G').left ≫ ψ
    rw [← Category.assoc, ← Over.comp_left, lift_snd, hy])
  have hxy : x * y = lift x y ≫ (fst G' G' * snd G' G') := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [hx', hy', ← MonObj.comp_mul, hxy, Over.comp_left, e, Over.comp_left, Category.assoc]
  rfl

theorem subset_abLocus {S : Scheme.{0}} (G : Over S) [IsProper G.hom] (A : Set S) : A ⊆ abLocus G :=
  fun _ _ _ _ _ _ _ => inferInstance

end SabMapDescent


open SabMapDescent in
theorem exists_sabMap_of_quotient :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (U U' X' : Scheme.{0}) (ρ : Γ →* Aut U) (r : U ⟶ U') (t : SAB H U) (t' : SAB H U') (t₁ : SAB H X') (τ : Γ →* Aut t.G.left) (ν : SABMap t t' r) (j : U' ⟶ X') (n : SABMap t t₁ (r ≫ j)), (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsReduced U → IsProper t.G.hom → (∀ g, (τ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ g).asIso.hom ∧ (τ g).asIso.hom ≫ ν.φ = ν.φ ∧ (τ g).asIso.hom ≫ n.φ = n.φ) → ∃ n' : SABMap t' t₁ j, ν.φ ≫ n'.φ = n.φ := by
  intro E _ _ _ H Γ _ _ U U' X' ρ r t t' t₁ τ ν j n hq hred hprop hτ
  have hq : IsQuot ρ r := hq
  have := t.semi.smooth
  have := t.semi.geomConnected
  have := t'.semi.smooth
  have := t'.semi.separated
  have := t₁.semi.smooth
  obtain ⟨ψ, hψ, hpb⟩ := exists_isPullback hq ν.cart.1 n.cart.1 τ hτ
  have hgp : IsGrpPullback t'.G t₁.G j ψ := isGrpPullback_of_quot hq ν.cart (hψ ▸ n.cart) hpb
  have := hq.epi_of_isPullback ν.cart.1 inferInstance
  obtain ⟨hint, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ U U' ρ r hq
  have : Surjective ν.cm.F := MorphismProperty.of_isPullback (P := @Surjective) ν.cart.1.flip hsurj
  have : UniversallyClosed (ν.cm.F ≫ t'.G.hom) := by rw [ν.cart.1.w]; infer_instance
  have : UniversallyClosed t'.G.hom := .of_comp_surjective ν.cm.F _
  have : IsProper t'.G.hom := {}
  have he : eSec t.G ≫ t.G.hom = 𝟙 U := Over.w η[t.G]
  have he' : eSec t'.G ≫ t'.G.hom = 𝟙 U' := Over.w η[t'.G]
  have hiso : LBIso t'.PP.L (t₁.PP.L.pull ψ) := by
    refine exists_gen_of_quotient_of_rigid Γ U U' ρ r t.G t'.G ν.cm.F (eSec t.G) (eSec t'.G)
      (LB.div (t₁.PP.L.pull ψ) t'.PP.L) hq ν.cart.1 inferInstance he he' (by rw [ν.cm.e_comm, ν.base])
      (eq_one_of_appLE_section_eq_one U t.G _ he inferInstance
        (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) ⟨hred, subset_abLocus _ _⟩)
      (LB.isLB_div (pull_isLB t₁.PP.isLB ψ) t'.PP.isLB) ?_ ?_
    · obtain ⟨c, hc⟩ := gen_chartPull (chartPullLinComb t₁.PP.L ψ (K := PUnit) (fun _ => eSec t'.G)
        (fun _ => eSec t₁.G) (fun _ => 1) j fun _ => (cubeMapOf hgp).e_comm) t₁.PP.rig t₁.PP.rigGen
      obtain ⟨w, hw⟩ := lbIso_of_gen_of_gen t'.PP.rig t'.PP.rigGen c hc
      exact gen_chartPull (chartPullDivPull _ _ _) w hw
    · obtain ⟨a, ha, -⟩ := ν.lin
      obtain ⟨b, hb, -⟩ := n.lin
      have hb' : LBIso t.PP.L ((t₁.PP.L.pull ψ).pull ν.cm.F) :=
        LBIso.chartPull (chartPullId _) (chartPullLinComb t₁.PP.L ψ (K := PUnit) (fun _ => ν.cm.F)
          (fun _ => n.cm.F) (fun _ => 1) (𝟙 _) fun _ => hψ.trans (Category.id_comp _).symm) ⟨b, hb⟩
      obtain ⟨w, hw⟩ := LBIso.trans (pull_isLB t'.PP.isLB _) t.PP.isLB
        (pull_isLB (pull_isLB t₁.PP.isLB ψ) _) (LBIso.symm ⟨a, ha⟩) hb'
      exact gen_chartPull (chartPullDivPull _ _ _) w hw
  obtain ⟨n', hn'⟩ := GlobalTheory.exists_sabMap_of_lbIso E H X' U' t₁ t' j ψ ⟨hq.isReduced, subset_abLocus _ _⟩ hgp (fun a => by
    rw [← cancel_epi ν.cm.F, ← Category.assoc, ← ν.act, Category.assoc, hψ, n.act, ← Category.assoc, hψ]) hiso
  exact ⟨n', hn' ▸ hψ⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotientStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmTripleMap_descend_groupQuotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (U U' X' : Scheme.{0}) (ρ : Γ →* Aut U) (r : U ⟶ U') (t : SAB H U) (t' : SAB H U') (t₁ : SAB H X') (τ : Γ →* Aut t.G.left) (ν : SABMap t t' r) (j : U' ⟶ X') (n : SABMap t t₁ (r ≫ j)), (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsReduced U → IsProper t.G.hom → (∀ g, (τ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ g).asIso.hom ∧ (τ g).asIso.hom ≫ ν.φ = ν.φ ∧ (τ g).asIso.hom ≫ n.φ = n.φ) → ∃ n' : SABMap t' t₁ j, ν.φ ≫ n'.φ = n.φ := by
  first | exact @GlobalTheory.exists_sabMap_of_quotient | exact GlobalTheory.exists_sabMap_of_quotient | (intros; apply GlobalTheory.exists_sabMap_of_quotient <;> assumption)
end
end
