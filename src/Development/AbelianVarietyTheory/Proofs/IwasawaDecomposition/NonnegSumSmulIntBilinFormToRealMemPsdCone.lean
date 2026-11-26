module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SubsingletonOfLeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusPointsSubsetHolPeriodicOneParamSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan.ConeSub

theorem eq_zero_of_self_eq_zero {X : Type} [AddCommGroup X] (γ : LinearMap.BilinForm ℤ X)
    (hs : ∀ y z, γ y z = γ z y) (hp : ∀ y, 0 ≤ γ y y) {u : X} (hu : γ u u = 0) (w : X) : γ u w = 0 := by
  have key : ∀ t : ℤ, 0 ≤ γ w w + 2 * t * γ u w := by
    intro t
    have h := hp (w + t • u)
    simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu, hs w u] at h
    linarith
  by_contra h
  have h1 := key (-(γ w w + 1) * γ u w)
  have h2 : 0 < γ u w * γ u w := mul_self_pos.2 h
  have h3 := hp w
  nlinarith

theorem sum_expand {X₁ ι : Type} [AddCommGroup X₁] [Fintype ι] (B : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ) (b : ι → X₁) (z : ι → ℤ) :
    ∑ k, ∑ l, (z k : ℝ) * z l * B (b k) (b l) = B (∑ k, z k • b k) (∑ l, z l • b l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem sum_smul_toReal_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
    (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, 0 ≤ c i) →
    ∑ i, c i • toReal (γ i) ∈ psdCone (bar := bar) (X := X) := by
  intro O _ _ _ _ bar X _ _ _ m γ c hbal hpsd hc
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun i => 0 < c i) with hSdef
  have hcS : ∀ i, i ∉ S → c i = 0 := fun i hi =>
    le_antisymm (not_lt.1 fun h => hi (by simp [hSdef, h])) (hc i)
  by_cases hS : S.Nonempty
  swap
  · have h0 : ∑ i, c i • toReal (γ i) = 0 := Finset.sum_eq_zero fun i _ => by
      rw [hcS i fun h => hS ⟨i, h⟩, zero_smul]
    rw [h0]
    exact zero_mem_psdCone
  set B := ∑ i, c i • toReal (γ i) with hBdef
  have hBapp : ∀ a b, B a b = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    simp [hBdef, LinearMap.sum_apply]
  have hBreal : B ∈ realForms bar X :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (toReal_mem (hbal i))

  let R : Submodule O X :=
    { carrier := {y | ∀ i ∈ S, ∀ z, γ i y z = 0}
      add_mem' := fun {y y'} hy hy' i hi z => by rw [map_add (f := _), LinearMap.add_apply, hy i hi, hy' i hi, add_zero]
      zero_mem' := fun i _ z => by simp
      smul_mem' := fun a y hy i hi z => by
        change γ i (a • y) z = 0
        rw [(hbal i).2 a y z]; exact hy i hi _ }
  have hmemR : ∀ y, y ∈ R ↔ ∀ i ∈ S, ∀ z, γ i y z = 0 := fun y => Iff.rfl
  have hBR1 : ∀ y ∈ R, ∀ z, B y z = 0 := fun y hy z => by
    rw [hBapp]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S
    · rw [(hmemR y).1 hy i hi z]; simp
    · rw [hcS i hi, zero_mul]
  have hBsymm : ∀ y z, B y z = B z y := hBreal.1
  have hBR2 : ∀ y ∈ R, ∀ z, B z y = 0 := fun y hy z => by rw [hBsymm]; exact hBR1 y hy z

  have hZ : ∀ n : ℤ, n ≠ 0 → ∀ y, n • y ∈ R → y ∈ R := fun n hn y hy i hi z => by
    have h := (hmemR _).1 hy i hi z
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hn
  have hO : ∀ a : O, a ≠ 0 → ∀ y, a • y ∈ R → y ∈ R := by
    intro a ha y hy
    have hne : (Ideal.span {a}).comap (algebraMap ℤ O) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
    refine hZ n hn0 y fun i hi z => ?_
    have h := (hmemR _).1 hy i hi (bar a' • z)
    rw [← (hbal i).2 a' (a • y) z, smul_smul, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul] at h
    exact h
  have htor : Submodule.torsion O (X ⧸ R) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective R u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact hO a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat O (X ⧸ R) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation O (X ⧸ R) := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective O (X ⧸ R) := Module.Flat.projective_of_finitePresentation
  have : Module.Finite ℤ (X ⧸ R) := Module.Finite.trans O (X ⧸ R)
  have : Module.IsTorsionFree ℤ (X ⧸ R) := by
    refine ⟨fun {n} hn a b hab => ?_⟩
    induction a using Submodule.Quotient.induction_on with | H x => ?_
    induction b using Submodule.Quotient.induction_on with | H y => ?_
    simp only at hab
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq]
    refine hZ n (isRegular_iff_ne_zero.mp hn) (x - y) ?_
    rw [smul_sub]; exact hab
  have : Module.Free ℤ (X ⧸ R) := Module.free_of_finite_type_torsion_free'

  have hBq : ∀ x x' y y', Submodule.Quotient.mk (p := R) x = Submodule.Quotient.mk x' →
      Submodule.Quotient.mk (p := R) y = Submodule.Quotient.mk y' → B x y = B x' y' := by
    intro x x' y y' hx hy
    rw [Submodule.Quotient.eq] at hx hy
    have e1 : B x y = B (x - x') y + B x' (y - y') + B x' y' := by
      simp only [map_sub, LinearMap.sub_apply]; ring
    rw [e1, hBR1 _ hx, hBR2 _ hy, zero_add, zero_add]
  let s := Function.surjInv (Submodule.Quotient.mk_surjective R)
  have hs : ∀ u, Submodule.Quotient.mk (p := R) (s u) = u := Function.surjInv_eq _
  let B₁ := (AddMonoidHom.mk' (fun u => (AddMonoidHom.mk' (fun v => B (s u) (s v)) (fun v v' => by
      rw [← map_add (f := _)]; exact hBq _ _ _ _ rfl (by rw [hs, Submodule.Quotient.mk_add, hs, hs]))).toIntLinearMap)
    (fun u u' => by
      ext v
      change B (s (u + u')) (s v) = B (s u) (s v) + B (s u') (s v)
      rw [← LinearMap.add_apply, ← map_add (f := _)]
      exact hBq _ _ _ _ (by rw [hs, Submodule.Quotient.mk_add, hs, hs]) rfl)).toIntLinearMap
  have hB₁ : ∀ u v, B₁ u v = B (s u) (s v) := fun u v => rfl
  have hBB₁ : ∀ a b, B a b = B₁ (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) := fun a b =>
    hBq _ _ _ _ (hs _).symm (hs _).symm
  have hreal₁ : B₁ ∈ realForms bar (X ⧸ R) := by
    refine ⟨fun u v => by rw [hB₁, hB₁, hBsymm], fun a u v => ?_⟩
    rw [hB₁, hB₁]
    calc B (s (a • u)) (s v) = B (a • s u) (s v) := hBq _ _ _ _ (by rw [hs, Submodule.Quotient.mk_smul, hs]) rfl
      _ = B (s u) (bar a • s v) := hBreal.2 a _ _
      _ = B (s u) (s (bar a • v)) := hBq _ _ _ _ rfl (by rw [hs, Submodule.Quotient.mk_smul, hs])
  set cmin := S.inf' hS c with hcmin
  have hcmin0 : 0 < cmin := (Finset.lt_inf'_iff hS).2 fun i hi => (Finset.mem_filter.1 hi).2
  have hint : ∀ u : X ⧸ R, u ≠ 0 → cmin ≤ B₁ u u := by
    intro u hu
    obtain ⟨i, hi, hpos⟩ : ∃ i ∈ S, 0 < γ i (s u) (s u) := by
      by_contra hne
      push_neg at hne
      apply hu
      rw [← hs u, Submodule.Quotient.mk_eq_zero]
      exact fun i hi z => eq_zero_of_self_eq_zero (γ i) (hbal i).1 (hpsd i)
        (le_antisymm (hne i hi) (hpsd i _)) z
    rw [hB₁, hBapp]
    have h1 : (1 : ℝ) ≤ γ i (s u) (s u) := by exact_mod_cast hpos
    calc cmin ≤ c i := Finset.inf'_le _ hi
      _ ≤ c i * (γ i (s u) (s u) : ℝ) := le_mul_of_one_le_right (hc i) h1
      _ ≤ ∑ j, c j * (γ j (s u) (s u) : ℝ) :=
        Finset.single_le_sum (f := fun j => c j * (γ j (s u) (s u) : ℝ))
          (fun j _ => mul_nonneg (hc j) (by exact_mod_cast hpsd j _)) (Finset.mem_univ i)
  have hdef : IsPosDef B₁ := by
    let b := Module.Free.chooseBasis ℤ (X ⧸ R)
    rw [isPosDef_iff_basis b]
    intro x hx
    refine GlobalTheory.PointLawsEdge.real_pos_of_int_ge (fun k l => B₁ (b k) (b l)) (fun k l => hreal₁.1 _ _) hcmin0
      (fun z hz => ?_) x hx
    show cmin ≤ ∑ k, ∑ l, (z k : ℝ) * z l * B₁ (b k) (b l)
    rw [sum_expand]
    refine hint _ fun h0 => hz ?_
    exact funext (Fintype.linearIndependent_iff.1 b.linearIndependent z h0)
  exact ⟨X ⧸ R, inferInstance, inferInstance, hproj, R.mkQ, B₁, Submodule.mkQ_surjective R, hreal₁, hdef,
    fun a b => hBB₁ a b⟩
end GlobalTheory.PolFan.ConeSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), (∀ i, γ i ∈ balForms bar X) → (∀ i y, 0 ≤ γ i y y) → (∀ i, 0 ≤ c i) → ∑ i, c i • toReal (γ i) ∈ psdCone (bar := bar) (X := X) := by
  first | exact @GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone | exact GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone | (intros; apply GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactRepresentativesModTorusPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactRepresentativesModTorusPoints
noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.BdArc
  Filter Topology
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan GlobalTheory.Points GlobalTheory.IntegralPower

namespace GlobalTheory.TorusCocompact

theorem exists_isCompact_surjOn {V H : Type} [NormedAddCommGroup V] [ProperSpace V] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] (φ : V → H) (hφ : ∀ z w, φ (z + w) = φ z * φ w)
    (hs : Function.Surjective φ) (hc : Continuous φ) : ∃ C : Set V, IsCompact C ∧ ∀ z, ∃ c ∈ C, φ (z - c) = 1 := by
  let ψ : V →+ Additive H := AddMonoidHom.mk' (fun z => Additive.ofMul (φ z)) hφ
  have : BaireSpace (Additive H) := inferInstanceAs (BaireSpace H)
  have : T2Space (Additive H) := inferInstanceAs (T2Space H)
  have ho : IsOpenMap φ := AddMonoidHom.isOpenMap_of_sigmaCompact ψ hs hc
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover (fun n : ℕ => φ '' Metric.ball 0 n)
    (fun n => ho _ Metric.isOpen_ball) (fun h _ => by
      obtain ⟨z, rfl⟩ := hs h
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      exact Set.mem_iUnion.2 ⟨n, z, by simpa using hn, rfl⟩)
    (Monotone.directed_le fun m n h => Set.image_mono (Metric.ball_subset_ball (Nat.cast_le.2 h)))
  refine ⟨Metric.closedBall 0 n, isCompact_closedBall _ _, fun z => ?_⟩
  obtain ⟨c, hc, hcz⟩ := hn (Set.mem_univ (φ z))
  refine ⟨c, Metric.ball_subset_closedBall hc, ?_⟩
  have h := hφ (z - c) c
  rw [sub_add_cancel, hcz] at h
  exact (mul_eq_right.1 h.symm)

theorem exists_lift_point {A B : Over (Sp ℂ)} (q : A ⟶ B) [Surjective q.left] [LocallyOfFiniteType q.left]
    (w : Over.mk (𝟙 (Sp ℂ)) ⟶ B) : ∃ u : Over.mk (𝟙 (Sp ℂ)) ⟶ A, u ≫ q = w := by
  let w' : Sp ℂ ⟶ B.left := w.left
  obtain ⟨z, -⟩ := (pullback.snd q.left w').surjective (IsLocalRing.closedPoint ℂ)
  obtain ⟨x, hx, -⟩ := GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd q.left w') isClosed_univ.isLocallyClosed
    ⟨z, trivial⟩
  have h : (x ≫ pullback.fst q.left w') ≫ q.left = w' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  refine ⟨Over.homMk (x ≫ pullback.fst q.left w') ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w q, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h).trans (Over.w w)

section Fibre

variable {X : Scheme.{0}} {G : Over X} {y : Sp ℂ ⟶ X}

def fibrePt (x : Over.mk y ⟶ G) : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G :=
  Over.homMk (pullback.lift x.left (𝟙 (Sp ℂ)) ((Over.w x).trans (Category.id_comp y).symm))
    (pullback.lift_snd _ _ _)

theorem fibrePt_fst (x : Over.mk y ⟶ G) : (fibrePt x).left ≫ pullback.fst G.hom y = x.left :=
  pullback.lift_fst _ _ _

theorem fibre_ext {u v : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G}
    (h : u.left ≫ pullback.fst G.hom y = v.left ≫ pullback.fst G.hom y) : u = v :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w u).trans (Over.w v).symm))

theorem fibrePt_surjective : Function.Surjective (fibrePt (G := G) (y := y)) := fun u =>
  ⟨Over.homMk (u.left ≫ pullback.fst G.hom y) (by
    have h : u.left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w u
    rw [Category.assoc, pullback.condition, reassoc_of% h]
    rfl), fibre_ext (fibrePt_fst _)⟩

theorem fibrePt_mul [GrpObj G] (a b : Over.mk y ⟶ G) : fibrePt (a * b) = fibrePt a * fibrePt b := by
  let U : Over.mk ((Over.mk (𝟙 (Sp ℂ))).hom ≫ y) ⟶ Over.mk y := Over.homMk (𝟙 (Sp ℂ)) rfl
  have hU : ∀ x : Over.mk y ⟶ G, (U ≫ x).left = x.left := fun x => Category.id_comp _
  refine fibre_ext ?_
  rw [fibrePt_fst, ← (isGrpPullback_pullback G y).2 _ (fibrePt a) (fibrePt b) (U ≫ a) (U ≫ b)
    ((hU a).trans (fibrePt_fst a).symm) ((hU b).trans (fibrePt_fst b).symm), ← comp_mul, hU]

theorem continuous_fibrePt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (e : V → (Over.mk y ⟶ G))
    (he : IsHolTo Set.univ (fun z => (e z).left)) :
    Continuous fun z => leftPt (𝟙 (Sp ℂ)) (fibrePt (e z)) := by
  have h1 : Continuous fun z => leftPt y (e z) := by
    refine GlobalTheory.Points.continuous_iff.2 fun U => ⟨?_, fun f => ?_⟩
    · simpa using (he U 0).1
    · exact (he U f).2.continuousOn.mono fun _ hb => ⟨trivial, hb⟩
  refine (isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback G.hom y)).continuous_iff.2 ?_
  refine (h1.prodMk (continuous_const (y := 𝟙 (Sp ℂ)))).congr fun z => ?_
  exact Prod.ext (fibrePt_fst (e z)).symm (Over.w (fibrePt (e z))).symm

end Fibre


attribute [local instance] ptTopology in
theorem exists_isCompact_mod_torusPts : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G →
    (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) →
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) →
    ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  intro X G _ y g e E hG hadd hsurj hhol _
  let := E.addCommGroup
  let := E.grpB
  have := E.q_hom
  have := E.q_surjective
  have := E.isAbelian.proper
  have := hG.smooth
  have : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by
    rw [Over.w E.q]
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom y))
  have : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  have : CompactSpace (PtsOver E.B.hom (𝟙 (Sp ℂ))) := GlobalTheory.ProperPoints.compactSpace_pts E.B.hom
  have := compactSpace_of_ptsOver (𝟙 (Sp ℂ)) E.B
  have : IsTopologicalGroup (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) := by
    exact { continuous_mul := (continuous_comp_over _ (μ[E.B])).comp (continuous_lift _ E.B E.B)
            continuous_inv := continuous_comp_over _ (GrpObj.inv (X := E.B)) }
  have : T2Space (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) :=
    have := PtsOver.t2Space E.B.hom (𝟙 (Sp ℂ))
    T2Space.of_injective_continuous (f := fun x => (⟨x.left, Over.w x⟩ : PtsOver E.B.hom (𝟙 (Sp ℂ))))
      (fun _ _ h => Over.OverMorphism.ext (congrArg Subtype.val h))
      ((isEmbedding_leftPt (𝟙 (Sp ℂ)) E.B).continuous.subtype_mk _)
  obtain ⟨C, hC, H⟩ := exists_isCompact_surjOn (fun z => fibrePt (e z) ≫ E.q)
    (fun z w => by rw [hadd, fibrePt_mul, mul_comp])
    (fun w => by
      obtain ⟨u, rfl⟩ := exists_lift_point E.q w
      obtain ⟨x, rfl⟩ := fibrePt_surjective u
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z, rfl⟩)
    ((continuous_comp_over _ E.q).comp ((isEmbedding_leftPt _ _).continuous_iff.2 (continuous_fibrePt e hhol)))
  refine ⟨C, hC, fun z => ?_⟩
  obtain ⟨c, hc, hz⟩ := H z
  refine ⟨c, hc, E.isKernel.lift (fibrePt (e (z - c))) (toUnit _) hz, ?_⟩
  rw [IsPullback.lift_fst]
  exact fibrePt_fst _

end GlobalTheory.TorusCocompact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactRepresentativesModTorusPointsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_representatives_mod_torusPoints : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) → (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) → ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  first | exact @GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts | exact GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts | (intros; apply GlobalTheory.TorusCocompact.exists_isCompact_mod_torusPts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTop
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan

namespace GlobalTheory.PeriodSpan

theorem span_ker_eq_top : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsSemiAbelian G → ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective (e) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) ∧ (∀ w, ∃! v : epsPt (y) ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt (y) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) → Submodule.span ℂ {z | e z = 1} = ⊤ := by
  intro X G _ y g e hG ⟨hadd, hsurj, hhol, _, hd2⟩
  have hhol' : IsHolTo Set.univ (fun z => (e z).left) := hhol
  have h0 : e 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hsub : ∀ z w, e (z - w) = e z * (e w)⁻¹ := fun z w =>
    eq_mul_inv_of_mul_eq (by rw [← hadd, sub_add_cancel])
  by_contra hne
  obtain ⟨ℓ, hℓ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have hℓK : ∀ z, e z = 1 → ℓ z = 0 := fun z hz => hle (Submodule.subset_span hz)
  have hℓeq : ∀ z w, e z = e w → ℓ z = ℓ w := fun z w h => by
    have := hℓK (z - w) (by rw [hsub, h, mul_inv_cancel])
    rwa [map_sub, sub_eq_zero] at this
  let lam : (Over.mk y ⟶ G) → ℂ := fun x => ℓ (hsurj x).choose
  have hlam : ∀ z, lam (e z) = ℓ z := fun z => hℓeq _ _ (hsurj (e z)).choose_spec
  let S : Subgroup (Over.mk y ⟶ G) :=
    { carrier := {x | lam x = 0}
      one_mem' := by
        show lam 1 = 0
        rw [← h0, hlam, map_zero]
      mul_mem' := by
        intro x x' hx hx'
        obtain ⟨a, rfl⟩ := hsurj x
        obtain ⟨b, rfl⟩ := hsurj x'
        show lam (e a * e b) = 0
        have hx : lam (e a) = 0 := hx
        have hx' : lam (e b) = 0 := hx'
        rw [← hadd, hlam, map_add (f := _), ← hlam, ← hlam, hx, hx', add_zero]
      inv_mem' := by
        intro x hx
        obtain ⟨a, rfl⟩ := hsurj x
        have hx : lam (e a) = 0 := hx
        show lam (e a)⁻¹ = 0
        have hinv : (e a)⁻¹ = e (-a) :=
          inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
        rw [hinv, hlam, map_neg, ← hlam, hx, neg_zero] }
  have hper : perHolSub G y ≤ S := by
    refine Subgroup.closure_le _ |>.2 (Set.iUnion₂_subset fun ψ hψ => Set.range_subset_iff.2 fun s => ?_)
    obtain ⟨hψadd, hψhol, hψper⟩ := hψ
    obtain ⟨h, hh, -⟩ := (GlobalTheory.holomorphic_hom_determined X G).2.2.1 y ℂ g ψ e hψadd hadd hψhol hhol' hd2
    have hlin : ∀ s : ℂ, h s = s • h 1 := fun s => by rw [← h.map_smul, smul_eq_mul, _root_.mul_one]
    have h1 : ℓ (h 1) = 0 := by
      have h2 : ℓ (h (2 * Real.pi * Complex.I)) = 0 := hℓK _ (by rw [← hh, hψper])
      rw [hlin, map_smul, smul_eq_mul] at h2
      refine (mul_eq_zero.1 h2).resolve_left ?_
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    show lam (ψ s) = 0
    rw [hh, hlam, hlin, map_smul, h1, smul_zero]
  obtain ⟨E⟩ := hG.fibres ℂ y
  have htor : ∀ x ∈ torusPts G y E, lam x = 0 := fun x hx => hper (GlobalTheory.T.torusPoints_subset_holPeriodicOneParamSpan X G y E hx)
  obtain ⟨C, hC, hCz⟩ := GlobalTheory.T.exists_compact_representatives_mod_torusPoints X G y g e E hG hadd hsurj hhol' hd2
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (LinearMap.continuous_of_finiteDimensional ℓ).continuousOn
  have hbd : ∀ z, ‖ℓ z‖ ≤ M := fun z => by
    obtain ⟨c, hc, hzc⟩ := hCz z
    have := htor _ hzc
    rw [hlam, map_sub, sub_eq_zero] at this
    rw [this]
    exact hM c hc
  apply hℓ0
  refine LinearMap.ext fun z => ?_
  by_contra hz0
  have hz : ℓ z ≠ 0 := by simpa using hz0
  have hpos : 0 < ‖ℓ z‖ := norm_pos_iff.2 hz
  have := hbd ((((|M| + 1) / ‖ℓ z‖ : ℝ) : ℂ) • z)
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_mul_cancel₀ _ hpos.ne'] at this
  linarith [le_abs_self M]

end GlobalTheory.PeriodSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_periodLattice_complexSemiAbelian_eq_top : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsSemiAbelian G → ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective (e) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) ∧ (∀ w, ∃! v : epsPt (y) ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt (y) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) → Submodule.span ℂ {z | e z = 1} = ⊤ := by
  first | exact @GlobalTheory.PeriodSpan.span_ker_eq_top | exact GlobalTheory.PeriodSpan.span_ker_eq_top | (intros; apply GlobalTheory.PeriodSpan.span_ker_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Form

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_periodForm {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    [IsAdicComplete (maximalIdeal W) W] {t : SAB H (Sp W)}
    (P : PELUnif (maximalIdeal W) t) {ϖ : W} (hϖ : Irreducible ϖ) :
    ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ ∀ y, y ≠ 0 → 0 < be y y := by
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W P.D inferInstance χ).1).imp fun _ h => h.1
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D hQ' a b)
      (fun a a' b => by simp only [map_add (f := _), AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
      (fun a b b' => by simp only [map_add (f := _)])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul, zsmul_eq_mul, Int.cast_id])
  have hbe : ∀ a b, be a b = QForm.bOf P.D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, ⟨fun a b => ?_, fun x a b => ?_, fun a b => ?_⟩, fun y => ?_, fun y hy => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · rw [hbe, hbe]
    exact QForm.bOf_balance hϖ P.D GlobalTheory.allSixLaws.1 P.oD hQ' x a b
  · simp
  · obtain ⟨r, hr⟩ := hex y
    obtain ⟨u, hu⟩ := GlobalTheory.ValForm.hasVal_coord (hQ y) hr
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h0 y)
    rw [hn, zpow_natCast, ← map_pow, ← map_mul] at hu
    have e : r = u * ϖ ^ n := (IsFractionRing.injective W (FractionRing W) hu).trans (_root_.mul_comm _ _)
    refine ⟨u, fun _ => n, fun i => ?_, ?_⟩
    · have : i = 0 := Subsingleton.elim _ _
      subst this
      show be y y = _
      rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ', hn]
    · simpa [e] using hr
  · rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ']
    have := QForm.Q_pos hϖ P.D hQ' hy
    omega

end Form

section Trait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_unif_ext (T : CDVR) (t : SAB H (Sp T.V)) (hp : PolAt t (jK T.V)) :
    ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ IsLocalHom φ ∧
      Nonempty (SABMap t' t (spMap φ)) ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  let F := AlgebraicClosure (FractionRing T.V)
  have hF : Function.Injective (algebraMap T.V F) := by
    rw [IsScalarTower.algebraMap_eq T.V (FractionRing T.V) F]
    exact (algebraMap (FractionRing T.V) F).injective.comp (IsFractionRing.injective T.V _)
  have : FaithfulSMul T.V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hF
  have : Algebra.IsAlgebraic T.V F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing T.V)).2 inferInstance
  obtain ⟨W, hd, hc, hf, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split T.V F t.G t.semi
  have hi : Function.Injective (algebraMap T.V W) := fun _ _ h => hF (congrArg (fun z : W => (z : F)) h)
  have hz : CharZero W := charZero_of_injective_ringHom hi
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap T.V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  let g : FractionRing T.V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W ⟨hd, hc, hz⟩ _ hp' hs
  exact ⟨{ V := W }, algebraMap T.V W, _, hi, hl, ⟨m⟩, ⟨P⟩⟩

theorem closed_mem_abLocus_iff (T : CDVR) {t : SAB H (Sp T.V)} (P : PELUnif (maximalIdeal T.V) t) :
    (closedPoint T.V : Sp T.V) ∈ abLocus t.G ↔ Subsingleton P.D.toPre.X := by
  constructor
  · intro hc
    have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
      rw [zero_add, pow_one]; infer_instance
    have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
    have hle : maximalIdeal T.V ^ (0 + 1) ≤ (closedPoint T.V).asIdeal := by
      rw [zero_add, pow_one]; exact le_rfl
    obtain ⟨q, hq⟩ : closedPoint T.V ∈ Set.range (PrimeSpectrum.comap
        (Ideal.Quotient.mk (maximalIdeal T.V ^ (0 + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact hle
    let g := P.U.gt 0
    have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
    have hq' : thick T.V (maximalIdeal T.V) 0 q ∈ abLocus t.G := by
      rw [← hq] at hc; exact hc
    exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom
  · intro hs K _ _ s _
    have := (isAbelianScheme_of_unif_of_subsingleton GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 T.V T.cpl P.D P.A t.G t.semi
      P.U hs).proper
    infer_instance

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem charZero_of_point {K : CommRingCat.{0}} [Nontrivial K] (y : Spec K ⟶ Xo.XF c) : CharZero K := by
  let f := Spec.preimage (y ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  exact charZero_of_injective_ringHom f.hom.injective


open GlobalTheory.HomExt in
theorem exists_base_trait (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) :
    ∃ (T : CDVR) (χ : Sp T.V ⟶ Z.X) (y : Sp (FractionRing T.V) ⟶ Xo.XF c),
      χ (closedPoint T.V : Sp T.V) = x ∧ y ≫ Z.j = jK T.V ≫ χ := by
  by_cases hx : x ∈ Set.range Z.j
  · obtain ⟨u, rfl⟩ := hx
    let K := (Xo.XF c).residueField u
    have : CharZero K := charZero_of_point ((Xo.XF c).fromSpecResidueField u)
    obtain ⟨h₁, h₂, h₃⟩ := (GlobalTheory.FrameCmp.cDvr_powerSeries K : CDvr (PowerSeries K))
    let a : Sp (PowerSeries K) ⟶ Xo.XF c := spMap (PowerSeries.C (R := K)) ≫ (Xo.XF c).fromSpecResidueField u
    refine ⟨{ V := PowerSeries K }, a ≫ Z.j, jK _ ≫ a, ?_, Category.assoc _ _ _⟩
    exact (Scheme.Hom.comp_apply a Z.j _).trans (congrArg Z.j ((Scheme.Hom.comp_apply _ _ _).trans
      (Scheme.fromSpecResidueField_apply u _)))
  · obtain ⟨h₁, -, -, _, _, _, _⟩ := GlobalTheory.ModelRelCompare.densePart Z hβ
    obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes x
    have hξ' := genericPoints_subset_range_of_isDominant Z.j hξ
    have hne : ξ ≠ x := fun e => hx (e ▸ hξ')
    obtain ⟨W, _, _, _, a, h₀, h₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
    obtain ⟨y, hy⟩ := exists_lift_of_range_subset Z.j
      (spMap (algebraMap W (FractionRing W)) ≫ a) (by
        rintro _ ⟨t, rfl⟩
        have : spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W) := by
          apply PrimeSpectrum.ext
          change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
          rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
          exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
        rw [Scheme.Hom.comp_apply, this]
        exact h₀ ▸ hξ')
    have hc : CharZero (FractionRing W) := charZero_of_point (K := .of (FractionRing W)) y
    have hc' : CharZero W := ⟨fun p q e => Nat.cast_injective (R := FractionRing W) (by
      simpa using congrArg (algebraMap W (FractionRing W)) e)⟩
    exact ⟨{ V := W }, a, y, h₁, hy⟩

theorem exists_trait (Z : Model Xo c β) (hβ : IsDedFrac β) (x : Z.X) :
    ∃ (T : CDVR) (χ : Sp T.V ⟶ Z.X) (t : SAB H (Sp T.V)) (_ : SABMap t Z.t χ) (_ : PELUnif (maximalIdeal T.V) t),
      χ (closedPoint T.V : Sp T.V) = x ∧ Set.range (jK T.V ≫ χ) ⊆ Set.range Z.j := by
  obtain ⟨T, χ, y, hx, hy⟩ := exists_base_trait Z hβ x
  obtain ⟨_, ⟨m⟩⟩ := exists_sab χ Z.t
  have hp := GlobalTheory.GoodTrait.polAt_of_point Z m (jK T.V) y hy
  obtain ⟨T', φ, t', hi, hl, ⟨m'⟩, ⟨P⟩⟩ := exists_unif_ext T _ hp
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m'
  have j : Function.Injective ((algebraMap T'.V (FractionRing T'.V)).comp φ) :=
    (IsFractionRing.injective T'.V _).comp hi
  let g : FractionRing T.V →+* FractionRing T'.V := IsFractionRing.lift j
  have e : jK T'.V ≫ spMap φ = spMap g ≫ jK T.V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  refine ⟨T', spMap φ ≫ χ, t', n, P, ?_, ?_⟩
  · exact (Scheme.Hom.comp_apply (spMap φ) χ _).trans ((congrArg χ (comap_closedPoint φ)).trans hx)
  · rintro _ ⟨p, rfl⟩
    refine ⟨(spMap g ≫ y) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, hy, ← Category.assoc, ← e, Category.assoc]

end Trait

end GlobalTheory.TorRef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.FrameBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem lieBasis_iff {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x : Sp S ⟶ X) (G' : Over (Sp S)) [GrpObj G']
    (φ : G'.left ⟶ t.G.left) (hp : IsGrpPullback G' t.G x φ) :
    (∀ w : (Sp (DualNumber S) ⟶ t.G.left), IsTanAtG t x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧
    ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ ((∀ i, IsTanAtG t x ((v i).left ≫ φ)) ∧
      ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x (fun i => (v i).left ≫ φ) a w) := by
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left,
      w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAtG t x (w.left ≫ φ) := fun w => by
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
    · refine (Category.assoc _ _ _).trans ?_
      rw [Over.w w, Over.w η[G']]
      exact zs
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w,
      IsLieComb c v w ↔ IsCombAtG t x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_,
        inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (GlobalTheory.Frames.spMap_epsScaleR_comp (c i)).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x ⟶ t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩,
    fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩
  · have h := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
    simp only [comb, hup] at h
    exact h
  · have h := hB.2 _ ((tan _).1 hw)
    simp only [comb]
    exact h

theorem tanBasis_baseChange {X : Scheme.{0}} (t : SAB H X) {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (x : Sp S ⟶ X) (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hv' : ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x v a w) :
    (∀ i, IsTanAtG t (spMap φ ≫ x) (spMap (dualMap φ) ≫ v i)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ x) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) a w := by
  have := t.semi.comm
  have := t.semi.smooth
  have h₁ := isGrpPullback_pullback t.G x
  have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
  have h₃ := h₂.comp h₁
  have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
    Functor.isCommMonObj_obj
  obtain ⟨a₁, b₁⟩ := lieBasis_iff t x _ _ h₁
  obtain ⟨-, b₃⟩ := lieBasis_iff t _ _ _ h₃
  choose u hu using fun i => a₁ (v i) (hv i)
  have hb : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hv'⟩
  have hs : Smooth ((Over.pullback x).obj t.G).hom :=
    inferInstanceAs (Smooth (pullback.snd t.G.hom x))
  obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange S T φ _ _ _ h₂ hs n u hb
  have e : Chart.dualMapR φ = dualMap φ := by
    ext a <;> rfl
  have key := (b₃ n u').1 hb'
  have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
      spMap (dualMap φ) ≫ v i := fun i => by
    rw [← Category.assoc, hu', e, Category.assoc, hu]
  refine ⟨fun i => e' i ▸ key.1 i, ?_⟩
  rw [← funext e']
  exact key.2

end GlobalTheory.LocM.FrameBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Principalise

theorem memIdealOfLocally {W : Scheme.{0}} (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, GlobalTheory.Cartier.app_resG] at this
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

theorem comapIdealTopLe {X W : Scheme.{0}} [IsAffine W] (J : X.IdealSheafData) (g : W ⟶ X)
    (U : X.affineOpens) (h : ⊤ ≤ g ⁻¹ᵁ U.1) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤ Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U) := by
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop (Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U)) := by
    refine (GlobalTheory.Cartier.comap_le_iff _ _ _).2 fun U' a ha B hB => memIdealOfLocally _ _ _ fun y hy => ?_
    obtain ⟨t, htle, hyt⟩ := U.2.exists_basicOpen_le (V := U'.1 ⊓ U.1) ⟨g y, hB hy, h trivial⟩ (h trivial)
    obtain ⟨_, ⟨B', hB'a, rfl⟩, hyB', hB'le⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ B.1 ⊓ g ⁻¹ᵁ X.basicOpen t from ⟨hy, hyt⟩) (B.1 ⊓ g ⁻¹ᵁ X.basicOpen t).isOpen
    refine ⟨⟨B', hB'a⟩, fun x hx => (hB'le hx).1, hyB', ?_⟩
    have hDU' : X.basicOpen t ≤ U'.1 := htle.trans inf_le_left
    have h1 : resG X hDU' a ∈ J.ideal (X.affineBasicOpen t) :=
      J.ideal_le_comap_ideal (U := X.affineBasicOpen t) (V := U') hDU' ha
    rw [← J.map_ideal_basicOpen U t] at h1
    have hB'D : B' ≤ g ⁻¹ᵁ X.basicOpen t := fun x hx => (hB'le hx).2
    have e : resG W (fun x hx => (hB'le hx).1 : B' ≤ B.1) (resG W hB ((g.app U'.1).hom a)) =
        (g.appLE (X.basicOpen t) B' hB'D).hom (resG X hDU' a) := by
      show _ = resG W hB'D ((g.app (X.basicOpen t)).hom (resG X hDU' a))
      rw [GlobalTheory.Cartier.app_resG, GlobalTheory.Cartier.resG_resG, GlobalTheory.Cartier.resG_resG]
    rw [e, Scheme.IdealSheafData.ofIdealTop_ideal]
    have h2 := Ideal.mem_map_of_mem (g.appLE (X.basicOpen t) B' hB'D).hom h1
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at h2
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    exact h2
  have := key ⟨⊤, isAffineOpen_top W⟩
  rw [Scheme.IdealSheafData.ofIdealTop_ideal] at this
  refine this.trans (le_of_eq ?_)
  convert Ideal.map_id _
  rw [show homOfLE (le_top : (⊤ : W.Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem comapIdealAffine : ∀ {X W : Scheme.{0}} (J : X.IdealSheafData) (g : W ⟶ X) (U : X.affineOpens) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ U.1), (J.comap g).ideal A = Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U) := by
  intro X W J g U A h
  apply le_antisymm
  · intro x hx
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := (GlobalTheory.Cartier.comap_le_iff (J.comap g) A.1.ι _).1 le_rfl A x hx ⟨⊤, isAffineOpen_top _⟩ hA
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := comapIdealTopLe J (A.1.ι ≫ g) U (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U)),
      Ideal.mem_comap, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    exact h2
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (GlobalTheory.Cartier.comap_le_iff J g _).1 le_rfl U a ha A h

theorem kerIdealAffine : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U)), ∃ J : X.IdealSheafData, J.ideal ⟨U, hU⟩ = I ∧ ∀ N : ℕ, (N : Γ(X, U)) ∈ I → ∀ V : X.affineOpens, (N : Γ(X, V.1)) ∈ J.ideal V := by
  intro X _ U hU I
  have hR : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let q : Γ(X, U) →+* Γ(X, U) ⧸ I := Ideal.Quotient.mk I
  let f : Spec (CommRingCat.of (Γ(X, U) ⧸ I)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  haveI : QuasiCompact f := quasiCompact_of_noetherianSpace_source f
  have hz : ⊤ ≤ f ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hzapp : f.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : f.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [hzapp]
    congr 1
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have k1 : ∀ b, (f.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom (q b) := by
    intro b
    rw [m2, m3]
    rfl
  refine ⟨f.ker, ?_, ?_⟩
  · ext a
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    constructor
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        show resG _ hz ((f.app U).hom a) = 0
        rw [ha, map_zero]
      rw [k1] at h1
      have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).hom.hom h1
      rw [Iso.inv_hom_id_apply, map_zero] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        rw [k1, show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
      refine GlobalTheory.Cartier.ext_germ fun x hx => ?_
      rw [map_zero, ← GlobalTheory.Cartier.germ_resG hz x trivial]
      exact (congrArg _ h1).trans (map_zero _)
  · intro N hN V
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker, map_natCast]
    have h0 : (N : Γ(X, U) ⧸ I) = 0 := by
      rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]; exact hN
    have h1 : (N : Γ(Spec (CommRingCat.of (Γ(X, U) ⧸ I)), ⊤)) = 0 := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom, h0, map_zero]
    rw [← map_natCast (resG _ (le_top : f ⁻¹ᵁ V.1 ≤ ⊤)), h1, map_zero]

theorem exists_dvd_of_span_mul_eq {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {m : ℕ}
    (A : Fin m → R) (I' : Ideal R) {f : R} (h : Ideal.span (Set.range A) * I' = Ideal.span {f})
    (hf : f ∈ nonZeroDivisors R) : ∃ k, ∃ s ∉ P, ∀ k', A k ∣ s * A k' := by
  have hfm : f ∈ Ideal.span (Set.range A) * I' := h ▸ Ideal.mem_span_singleton_self f
  have key : ∀ x ∈ Ideal.span (Set.range A) * I', ∃ c : Fin m → R, (∀ k, c k ∈ I') ∧ x = ∑ k, A k * c k := by
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩ => ?_)
    · obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
      refine ⟨fun k => d k * b, fun k => I'.mul_mem_left _ hb, ?_⟩
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [smul_eq_mul]; ring
    · refine ⟨c + d, fun k => I'.add_mem (hc k) (hd k), ?_⟩
      simp only [hx, hy, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  obtain ⟨c, hc, hfc⟩ := key f hfm
  have hAc : ∀ k k', ∃ t, A k' * c k = f * t := fun k k' => by
    have : A k' * c k ∈ Ideal.span {f} :=
      h ▸ Ideal.mul_mem_mul (Ideal.subset_span ⟨k', rfl⟩) (hc k)
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨t, by rw [← ht, mul_comm]⟩
  choose t ht using hAc
  have hsum : ∑ k, t k k = 1 := by
    refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
    rw [Finset.mul_sum, _root_.mul_one]
    conv_rhs => rw [hfc]
    exact Finset.sum_congr rfl fun k _ => (ht k k).symm
  obtain ⟨k, hk⟩ : ∃ k, t k k ∉ P := by
    by_contra hcon
    push_neg at hcon
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2
      (hsum ▸ Ideal.sum_mem _ fun k _ => hcon k))
  refine ⟨k, t k k, hk, fun k' => ⟨t k k', ?_⟩⟩
  refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
  calc f * (t k k * A k') = (f * t k k) * A k' := by ring
    _ = A k * c k * A k' := by rw [ht]
    _ = A k * (A k' * c k) := by ring
    _ = f * (A k * t k k') := by rw [ht]; ring

end GlobalTheory.Principalise
end
end
