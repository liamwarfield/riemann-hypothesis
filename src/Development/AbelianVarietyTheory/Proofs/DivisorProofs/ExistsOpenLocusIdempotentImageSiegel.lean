module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSymplecticLevelLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenNearOfFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalRestrictionRelAmpleLocusOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalRestrictionRelAmpleLocusOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FibreAmple

noncomputable section

namespace GlobalTheory.DiagAmpleLocus

theorem diag_relAmple_locus : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → Set.range g.base ⊆ (U : Set S') := by
  intro S' _ G _ _ P hG hP
  have := hG.proper
  have : Flat G.hom := by have := hG.smooth; infer_instance
  have hD : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  let good : Set S' := {s | ∃ (Y X : Scheme.{0}) (j : Y ⟶ S') (_ : IsOpenImmersion j) (π : X ⟶ G.left)
      (f : X ⟶ Y), IsPullback π f G.hom j ∧ s ∈ Set.range j.base ∧
        RelAmple (Over.mk f) ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull π)}
  have hopen : IsOpen good := by
    rw [isOpen_iff_forall_mem_open]
    rintro s ⟨Y, X, j, hj, π, f, h, hs, hA⟩
    exact ⟨Set.range j.base, fun x hx => ⟨Y, X, j, hj, π, f, h, hx, hA⟩,
      j.isOpenEmbedding.isOpen_range, hs⟩
  refine ⟨⟨good, hopen⟩, fun V hV => ?_, ?_⟩
  · let AV := (Over.pullback V.ι).obj G
    have : IsProper AV.hom := inferInstanceAs (IsProper (pullback.snd G.hom V.ι))
    have key : RelAmple AV ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (pullback.fst G.hom V.ι)) := by
      refine GlobalTheory.AmpleLocal.relAmple_of_locally V AV _ (pull_isLB hD _) inferInstance inferInstance
        fun v => ?_
      obtain ⟨Y, X, j, hj, π, f, h, ⟨y, hy⟩, hA⟩ := hV v.2
      let V' : V.toScheme.Opens := V.ι ⁻¹ᵁ j.opensRange
      have hv : v ∈ V' := ⟨y, hy⟩
      have hrange : Set.range (V'.ι ≫ V.ι).base ⊆ Set.range j.base := by
        rintro _ ⟨w, rfl⟩
        exact w.2
      have sq : IsPullback ((AV.hom ⁻¹ᵁ V').ι ≫ pullback.fst G.hom V.ι) (AV.hom ∣_ V') G.hom (V'.ι ≫ V.ι) :=
        (isPullback_morphismRestrict AV.hom V').flip.paste_horiz (IsPullback.of_hasPullback G.hom V.ι)
      have h₁ := relAmple_of_factor hD h sq (IsOpenImmersion.lift j _ hrange)
        (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hD π) (GlobalTheory.lbIso_refl (pull_isLB hD π)) hA
      have : IsProper (Over.mk (AV.hom ∣_ V')).hom := inferInstanceAs (IsProper (AV.hom ∣_ V'))
      exact ⟨V', hv, GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _)
        (pull_isLB (pull_isLB hD _) _) (lbIso_pull_pull hD _ _) h₁⟩
    have e₁ : LBIso ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 AV) (𝟙 AV)).left)
        (P.pull ((lift (𝟙 AV) (𝟙 AV)).left ≫ Pdiv.PullbackComparison.pφ₂ V.ι G)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G AV _ _ (Pdiv.PullbackComparison.isSquare V.ι G)] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (Pdiv.PullbackComparison.pφ V.ι G))
        (P.pull (Pdiv.PullbackComparison.pφ V.ι G ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    exact GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _) (pull_isLB (pull_isLB hP _) _)
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hD _) e₁ e₂.symm) key
  · rintro T g A' _ φ φ₂ P' hpb hsq hP' e hA _ ⟨t, rfl⟩
    have h₀ : IsPullback φ A'.hom G.hom g := hpb.1
    have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) h₀ ‹_›
    have e₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp e _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G A' φ φ₂ hsq] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    have hA' : RelAmple A' ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) :=
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hP' _) (pull_isLB hD _)
        (LBIso.trans (pull_isLB hD _) (pull_isLB hP _) (pull_isLB hP' _) e₂ e₁.symm) hA
    obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := g.base t) trivial
    have : IsNoetherianRing Γ(S', V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    obtain ⟨VT, hVT, ht, hle⟩ := exists_isAffineOpen_mem_and_subset (X := T) (U := g ⁻¹ᵁ V) (x := t) hs
    obtain ⟨q, hq⟩ : t ∈ Set.range hVT.fromSpec.base := by rw [hVT.range_fromSpec]; exact ht
    let tV : Sp Γ(S', V) ⟶ S' := hV.fromSpec
    let φR := g.appLE V VT hle
    have sqR : Spec.map φR ≫ hV.fromSpec = hVT.fromSpec ≫ g := IsAffineOpen.SpecMap_appLE_fromSpec g hV hVT hle
    let p : PrimeSpectrum Γ(S', V) := (Spec.map φR).base q
    have hp : tV.base p = g.base t := by
      have := congrArg (fun f : Spec Γ(T, VT) ⟶ S' => f.base q) sqR
      simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
      rw [← hq]
      exact this
    have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime (q : PrimeSpectrum Γ(T, VT))
    have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    let k := p.asIdeal.ResidueField
    let kq := q.asIdeal.ResidueField
    let gR := algebraMap Γ(S', V) k
    let i : k →+* kq := Ideal.ResidueField.map p.asIdeal q.asIdeal φR.hom rfl
    have hi : spMap (algebraMap Γ(T, VT) kq) ≫ Spec.map φR = spMap i ≫ spMap gR := by
      show Spec.map (CommRingCat.ofHom _) ≫ Spec.map φR = Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom gR)
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (Ideal.ResidueField.map_algebraMap _ _ _ _ x).symm
    let y : Sp kq ⟶ S' := spMap i ≫ spMap gR ≫ tV
    have hu : (spMap (algebraMap Γ(T, VT) kq) ≫ hVT.fromSpec) ≫ g = y := by
      rw [Category.assoc, ← sqR, ← Category.assoc, hi, Category.assoc]
    have hfib := relAmple_of_factor hD h₀ (IsPullback.of_hasPullback G.hom y) _ hu (pull_isLB hD φ)
      (GlobalTheory.lbIso_refl (pull_isLB hD φ)) hA'
    let B : Over (Sp Γ(S', V)) := Over.mk (pullback.snd G.hom tV)
    have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd G.hom tV))
    have : Flat B.hom := inferInstanceAs (Flat (pullback.snd G.hom tV))
    have hB := IsPullback.of_hasPullback G.hom tV
    have hL := pull_isLB hD (pullback.fst G.hom tV)
    obtain ⟨r, hr, hAr⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hL gR (residueField_fraction p.asIdeal)
      (relAmple_of_fieldExtension hD i ((IsPullback.of_hasPullback B.hom (spMap gR)).paste_horiz hB)
        (IsPullback.of_hasPullback G.hom _) (pull_isLB hL _) (lbIso_pull_pull hD _ _) hfib)
    let Dr : (Sp Γ(S', V)).Opens := PrimeSpectrum.basicOpen r
    have hpD : p ∈ Dr := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
    have : IsProper (Over.mk (pullback.snd B.hom Dr.ι)).hom := inferInstanceAs (IsProper (pullback.snd B.hom Dr.ι))
    exact ⟨Dr.toScheme, _, Dr.ι ≫ tV, inferInstance, pullback.fst B.hom Dr.ι ≫ pullback.fst G.hom tV,
      pullback.snd B.hom Dr.ι, (IsPullback.of_hasPullback B.hom Dr.ι).paste_horiz hB, ⟨⟨p, hpD⟩, hp⟩,
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hL _) (pull_isLB hD _) (lbIso_pull_pull hD _ _).symm hAr⟩

end GlobalTheory.DiagAmpleLocus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalRestrictionRelAmpleLocusOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_restriction_relAmple_locus_open : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.DiagAmpleLocus.diag_relAmple_locus) | (exact GlobalTheory.DiagAmpleLocus.diag_relAmple_locus) | (intros; apply GlobalTheory.DiagAmpleLocus.diag_relAmple_locus  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusKernelKilledSymmetricBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenKernelKilledNearPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKernelKilledOfBaseFaithfullyFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKernelKilledOfBaseFaithfullyFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibre

theorem one_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have : u = 1 := mul_eq_left.1 hu
  rw [← this]
  rfl

theorem pow_left_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (n : ℕ) : (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_left_push h T
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih hx

theorem comp_pow_pt {S : Scheme.{0}} {G A B : Over S} [GrpObj G] (f : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end GlobalTheory.KerKilledFibre

namespace GlobalTheory.KerKilledFibre

theorem fibreKilled_of_base : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, GlobalTheory.KerKilledNear.FibreKilled d G P (g.base t) := by
  intro d S' _ G _ _ P _ hP _ _ _ T g A' _ _ φ φ₂ P' hpb hsq hP' hiso _ H t T' x hT' hgen
  obtain ⟨f, hf⟩ := hT'
  obtain ⟨c, hc⟩ := hgen
  let r : Spec (T.residueField t) ⟶ Spec (S'.residueField (g.base t)) := Spec.map (g.residueFieldMap t)
  have hr : r ≫ S'.fromSpecResidueField (g.base t) = T.fromSpecResidueField t ≫ g :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g t
  let p1 : pullback f r ⟶ T'.left := pullback.fst f r
  let p2 : pullback f r ⟶ Spec (T.residueField t) := pullback.snd f r
  let T'' : Over T := Over.mk (p2 ≫ T.fromSpecResidueField t)
  have hw : p1 ≫ T'.hom = T''.hom ≫ g := by
    show p1 ≫ T'.hom = (p2 ≫ T.fromSpecResidueField t) ≫ g
    rw [hf, ← Category.assoc, pullback.condition, Category.assoc, hr, Category.assoc]
  have hxw : (p1 ≫ x.left) ≫ G.hom = T''.hom ≫ g := by rw [Category.assoc, Over.w x]; exact hw
  let x'' : T'' ⟶ A' := Over.homMk (hpb.1.lift (p1 ≫ x.left) T''.hom hxw) (hpb.1.lift_snd _ _ _)
  have hx''φ : x''.left ≫ φ = p1 ≫ x.left := hpb.1.lift_fst _ _ _

  let Y : Over S' := Over.mk ((A' ⊗ T'').hom ≫ g)
  let a : Y ⟶ G := Over.homMk ((fst A' T'').left ≫ φ) (by
    show ((fst A' T'').left ≫ φ) ≫ G.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hpb.1.w, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (fst A' T'')))
  let b : Y ⟶ T' := Over.homMk ((snd A' T'').left ≫ p1) (by
    show ((snd A' T'').left ≫ p1) ≫ T'.hom = (A' ⊗ T'').hom ≫ g
    rw [Category.assoc, hw, ← Category.assoc]
    exact congrArg (· ≫ g) (Over.w (snd A' T'')))
  let m := (lift a b).left
  let ψ := (lift (snd G T' ≫ x) (fst G T')).left
  let ψ'' := (lift (snd A' T'' ≫ x'') (fst A' T'')).left
  have heq : ψ'' ≫ φ₂ = m ≫ ψ := by
    have k1 : ψ ≫ (fst G G).left = (snd G T' ≫ x).left := by rw [← Over.comp_left, lift_fst]
    have k2 : ψ'' ≫ (fst A' A').left = (snd A' T'' ≫ x'').left := by rw [← Over.comp_left, lift_fst]
    have k3 : m ≫ (snd G T').left = b.left := by rw [← Over.comp_left, lift_snd]
    have k4 : ψ ≫ (snd G G).left = (fst G T').left := by rw [← Over.comp_left, lift_snd]
    have k5 : ψ'' ≫ (snd A' A').left = (fst A' T'').left := by rw [← Over.comp_left, lift_snd]
    have k6 : m ≫ (fst G T').left = a.left := by rw [← Over.comp_left, lift_fst]
    apply Over.tensorObj_ext
    · show ψ'' ≫ φ₂ ≫ (fst G G).left = m ≫ ψ ≫ (fst G G).left
      rw [hsq.1, reassoc_of% k2, k1]
      simp only [Over.comp_left, Category.assoc]
      rw [reassoc_of% k3, hx''φ]
      show _ = ((snd A' T'').left ≫ p1) ≫ x.left
      rw [Category.assoc]
    · show ψ'' ≫ φ₂ ≫ (snd G G).left = m ≫ ψ ≫ (snd G G).left
      rw [hsq.2, reassoc_of% k5, k4, k6]
      rfl
  obtain ⟨w, hwg⟩ := hiso
  obtain ⟨c1, hc1⟩ := gen_chartPull
    (chartPullSame P (fun _ : PUnit => ψ'' ≫ φ₂) (fun _ => ψ) (fun _ => 1) m (fun _ => heq)) c hc
  obtain ⟨c2, hc2⟩ := exists_down ((isGen_iff w).1 hwg) hP hP' (φ' := fun _ : PUnit => ψ'')
    (ε := fun _ => 1) c1 hc1
  have hx'' : x'' ^ d = 1 := H T'' x'' ⟨c2, hc2⟩

  let ρ : Over.mk (T''.hom ≫ g) ⟶ T' := Over.homMk p1 hw
  have hρ : (ρ ≫ x).left = x''.left ≫ φ := hx''φ.symm
  have e1 : ((ρ ≫ x) ^ d).left = (1 : Over.mk (T''.hom ≫ g) ⟶ G).left := by
    rw [pow_left_push hpb x'' (ρ ≫ x) hρ d, hx'', one_left_push hpb T'']
  have e2 : p1 ≫ (x ^ d).left = p1 ≫ (1 : T' ⟶ G).left := by
    have := congrArg CommaMorphism.left ((comp_pow_pt ρ x d).trans
      ((Over.OverMorphism.ext e1).trans (MonObj.comp_one ρ).symm))
    exact this
  have : Flat r := inferInstance
  have : Surjective r := ⟨Function.surjective_to_subsingleton _⟩
  have : Epi p1 := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi p1).1 e2)

end GlobalTheory.KerKilledFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreKernelKilledOfBaseFaithfullyFlatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_kernelKilled_of_base_faithfullyFlat : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, GlobalTheory.KerKilledNear.FibreKilled d G P (g.base t) := by
  first | (exact @GlobalTheory.KerKilledFibre.fibreKilled_of_base) | (exact GlobalTheory.KerKilledFibre.fibreKilled_of_base) | (intros; apply GlobalTheory.KerKilledFibre.fibreKilled_of_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenKernelKilledNearPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledNear

theorem kerKilledOn_near : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, ∃ V : S'.Opens, g.base t ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' _ G _ _ P hA hP hg₁ hg₂ hsym T g A' _ _ φ φ₂ P' hpb hsq hP' hiso hd hamp hker t
  obtain ⟨Ua, hUa, hUa'⟩ := GlobalTheory.T.diagonal_restriction_relAmple_locus_open S' G P hA hP
  obtain ⟨Ud, hUd, hUd'⟩ := GlobalTheory.T.natCast_unit_locus_open S' d
  have hsa : g.base t ∈ Ua := hUa' T g A' φ φ₂ P' hpb hsq hP' hiso hamp ⟨t, rfl⟩
  have hsd : g.base t ∈ Ud := hUd' T g hd ⟨t, rfl⟩
  exact GlobalTheory.T.kernelKilledOverOpen_near_of_fibre d S' G P hA hP hg₁ hg₂ hsym (Ua ⊓ Ud) (fun V hV => hUa V (hV.trans inf_le_left))
    (hUd _ inf_le_right) (g.base t) ⟨hsa, hsd⟩
    (GlobalTheory.T.fibre_kernelKilled_of_base_faithfullyFlat d S' G P hA hP hg₁ hg₂ hsym T g A' φ φ₂ P' hpb hsq hP' hiso hd hker t)

end GlobalTheory.KerKilledNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenKernelKilledNearPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_kernel_killed_near_point : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → ∀ t : T, ∃ V : S'.Opens, g.base t ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  first | (exact @GlobalTheory.KerKilledNear.kerKilledOn_near) | (exact GlobalTheory.KerKilledNear.kerKilledOn_near) | (intros; apply GlobalTheory.KerKilledNear.kerKilledOn_near  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusKernelKilledSymmetricBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledLocus

theorem exists_open_kerKilled_locus : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G), (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen, s.IsGen) → x ^ d = 1) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → Set.range g.base ⊆ (U : Set S') := by
  intro d S' _ G _ _ P hG hP h1 h2 hs
  refine ⟨sSup {V | GlobalTheory.KerKilledLocus.KerKilledOn d G P V}, ?_, ?_⟩
  · intro V hV
    refine GlobalTheory.T.kernelKilledOverOpen_of_local d S' G P V ?_
    intro p hp
    obtain ⟨W, hW, hpW⟩ := (TopologicalSpace.Opens.mem_sSup).1 (hV hp)
    exact ⟨W, hpW, hW⟩
  · intro T g A' _ _ φ φ₂ P' hpb hsq hP' hiso hu hamp hker
    rintro _ ⟨t, rfl⟩
    obtain ⟨V, hV, hK⟩ := GlobalTheory.T.exists_open_kernel_killed_near_point d S' G P hG hP h1 h2 hs T g A' φ φ₂ P' hpb hsq hP' hiso hu hamp hker t
    exact (TopologicalSpace.Opens.mem_sSup).2 ⟨V, hK, hV⟩

end GlobalTheory.KerKilledLocus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusKernelKilledSymmetricBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_locus_kernel_killed_symmetric_bundle : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ (T : Over V.toScheme) (x : T ⟶ (Over.pullback V.ι).obj G), (∃ s : ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (snd ((Over.pullback V.ι).obj G) T ≫ x) (fst ((Over.pullback V.ι).obj G) T)).left).Gen, s.IsGen) → x ^ d = 1) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → IsUnit ((d : ℕ) : Γ(T, ⊤)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → (∀ (T' : Over T) (x : T' ⟶ A'), (∃ s : (P'.pull (lift (snd A' T' ≫ x) (fst A' T')).left).Gen, s.IsGen) → x ^ d = 1) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.KerKilledLocus.exists_open_kerKilled_locus) | (exact GlobalTheory.KerKilledLocus.exists_open_kerKilled_locus) | (intros; apply GlobalTheory.KerKilledLocus.exists_open_kerKilled_locus  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEndomorphismImageCommutesBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEndomorphismImageCommutesBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ImgPB

@[reassoc]
theorem tensorHom_fst_left {B : Scheme.{0}} {X Y Z W : Over B} (f : X ⟶ Y) (h : Z ⟶ W) :
    (f ⊗ₘ h).left ≫ (fst Y W).left = (fst X Z).left ≫ f.left := by
  rw [← Over.comp_left, tensorHom_fst, Over.comp_left]

@[reassoc]
theorem tensorHom_snd_left {B : Scheme.{0}} {X Y Z W : Over B} (f : X ⟶ Y) (h : Z ⟶ W) :
    (f ⊗ₘ h).left ≫ (snd Y W).left = (snd X Z).left ≫ h.left := by
  rw [← Over.comp_left, tensorHom_snd, Over.comp_left]

theorem image_idem_pullback : ∀ (S' T : Scheme.{0}) (g : T ⟶ S') (A G : Over S') [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G) (ε : A ⟶ A) (A' G' : Over T) [GrpObj A'] [IsCommMonObj A'] [GrpObj G'] [IsCommMonObj G'] (inc' : G' ⟶ A') (pr' : A' ⟶ G') (ε' : A' ⟶ A') (ψ : A'.left ⟶ A.left) (ψ₂ : (G2 A').left ⟶ (G2 A).left), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = ε → IsMonHom inc' → IsMonHom pr' → inc' ≫ pr' = 𝟙 G' → pr' ≫ inc' = ε' → IsGrpPullback A' A g ψ → IsSquare ψ ψ₂ → ε'.left ≫ ψ = ψ ≫ ε.left → ∃ (φ : G'.left ⟶ G.left) (φ₂ : (G2 G').left ⟶ (G2 G).left), IsGrpPullback G' G g φ ∧ IsSquare φ φ₂ ∧ inc'.left ≫ ψ = φ ≫ inc.left ∧ (inc' ⊗ₘ inc').left ≫ ψ₂ = φ₂ ≫ (inc ⊗ₘ inc).left := by
  intro S' T g A G _ _ _ _ inc pr ε A' G' _ _ _ _ inc' pr' ε' ψ ψ₂ hinc hpr hip hpi hinc' hpr' hip' hpi' hψ hsq hεψ
  have hε' : inc' ≫ ε' = inc' := by rw [← hpi', ← Category.assoc, hip', Category.id_comp]
  have key : inc'.left ≫ ψ = inc'.left ≫ ψ ≫ pr.left ≫ inc.left := by
    rw [← Over.comp_left, hpi, ← hεψ, ← Category.assoc, ← Over.comp_left, hε']
  have hipl : inc.left ≫ pr.left = 𝟙 _ := by rw [← Over.comp_left, hip]; rfl
  have hipl' : inc'.left ≫ pr'.left = 𝟙 _ := by rw [← Over.comp_left, hip']; rfl
  have e2' : inc ≫ ε ≫ pr = 𝟙 G := by rw [← hpi, Category.assoc, reassoc_of% hip, hip]
  have e2 : inc.left ≫ ε.left ≫ pr.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.comp_left, e2']; rfl
  have e1 : pr'.left ≫ inc'.left ≫ ψ ≫ pr.left = ψ ≫ ε.left ≫ pr.left := by
    rw [← Category.assoc, ← Over.comp_left, hpi', ← Category.assoc, hεψ, Category.assoc]
  have hψp := hψ.1
  refine ⟨inc'.left ≫ ψ ≫ pr.left, (inc' ⊗ₘ inc').left ≫ ψ₂ ≫ (pr ⊗ₘ pr).left, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    key.trans (by simp only [Category.assoc]), ?_⟩
  · have w : (inc'.left ≫ ψ ≫ pr.left) ≫ G.hom = G'.hom ≫ g := by
      rw [Category.assoc, Category.assoc, Over.w pr, hψp.w, ← Category.assoc, Over.w inc']
    refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk _
      (fun s => hψp.lift (s.fst ≫ inc.left) s.snd (by rw [Category.assoc, Over.w inc]; exact s.condition) ≫ pr'.left)
      ?_ ?_ ?_)
    · intro s
      simp only [Category.assoc]
      rw [e1, hψp.lift_fst_assoc, Category.assoc, e2, Category.comp_id]
    · intro s
      rw [Category.assoc, Over.w pr', hψp.lift_snd]
    · intro s m hm1 hm2
      have hm : m ≫ inc'.left = hψp.lift (s.fst ≫ inc.left) s.snd
          (by rw [Category.assoc, Over.w inc]; exact s.condition) := by
        apply hψp.hom_ext
        · rw [hψp.lift_fst, ← hm1, Category.assoc, key]
          simp only [Category.assoc]
        · rw [hψp.lift_snd, Category.assoc, Over.w inc', hm2]
      calc m = m ≫ inc'.left ≫ pr'.left := by rw [hipl', Category.comp_id]
        _ = _ := by rw [← Category.assoc, hm]
  · intro U x y x₀ y₀ hx hy
    have h1 : (x₀ ≫ inc).left = (x ≫ inc').left ≫ ψ := by
      rw [Over.comp_left, hx, Over.comp_left]
      simp only [Category.assoc]
      rw [← key]
    have h2 : (y₀ ≫ inc).left = (y ≫ inc').left ≫ ψ := by
      rw [Over.comp_left, hy, Over.comp_left]
      simp only [Category.assoc]
      rw [← key]
    have hm := hψ.2 U (x ≫ inc') (y ≫ inc') (x₀ ≫ inc) (y₀ ≫ inc) h1 h2
    calc (x₀ * y₀).left = ((x₀ * y₀) ≫ inc).left ≫ pr.left := by
          rw [Over.comp_left, Category.assoc, hipl, Category.comp_id]
      _ = ((x * y) ≫ inc').left ≫ ψ ≫ pr.left := by
          rw [MonObj.mul_comp, MonObj.mul_comp, hm, Category.assoc]
      _ = _ := by rw [Over.comp_left, Category.assoc]
  · simp only [Category.assoc, tensorHom_fst_left, reassoc_of% hsq.1, tensorHom_fst_left_assoc]
  · simp only [Category.assoc, tensorHom_snd_left, reassoc_of% hsq.2, tensorHom_snd_left_assoc]
  · apply Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components
    · simp only [Category.assoc, tensorHom_fst_left, reassoc_of% hsq.1, hsq.1, tensorHom_fst_left_assoc]
      rw [← key]
    · simp only [Category.assoc, tensorHom_snd_left, reassoc_of% hsq.2, hsq.2, tensorHom_snd_left_assoc]
      rw [← key]

end GlobalTheory.ImgPB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEndomorphismImageCommutesBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_endomorphism_image_commutes_base_change : ∀ (S' T : Scheme.{0}) (g : T ⟶ S') (A G : Over S') [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G) (ε : A ⟶ A) (A' G' : Over T) [GrpObj A'] [IsCommMonObj A'] [GrpObj G'] [IsCommMonObj G'] (inc' : G' ⟶ A') (pr' : A' ⟶ G') (ε' : A' ⟶ A') (ψ : A'.left ⟶ A.left) (ψ₂ : (G2 A').left ⟶ (G2 A).left), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = ε → IsMonHom inc' → IsMonHom pr' → inc' ≫ pr' = 𝟙 G' → pr' ≫ inc' = ε' → IsGrpPullback A' A g ψ → IsSquare ψ ψ₂ → ε'.left ≫ ψ = ψ ≫ ε.left → ∃ (φ : G'.left ⟶ G.left) (φ₂ : (G2 G').left ⟶ (G2 G).left), IsGrpPullback G' G g φ ∧ IsSquare φ φ₂ ∧ inc'.left ≫ ψ = φ ≫ inc.left ∧ (inc' ⊗ₘ inc').left ≫ ψ₂ = φ₂ ≫ (inc ⊗ₘ inc).left := by
  first | (exact @GlobalTheory.ImgPB.image_idem_pullback) | (exact GlobalTheory.ImgPB.image_idem_pullback) | (intros; apply GlobalTheory.ImgPB.image_idem_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsFormulasOfIdempotentImagePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsFormulasOfIdempotentImagePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZRelLevs

theorem zrel_levs : ∀ (h h' M : ℕ) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' T : Scheme.{0}) (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g → ZRel e jl o κ c' w' actw' → (∀ a, g ≫ (z.lev (jl a) ≫ act e).left = g ≫ (z.lev (jl a)).left) ∧ ∀ a, g ≫ (z.lev a).left = g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
  intro h h' M O _ e jl n o κ S' T t z act g c' w' actw' hpb hz
  obtain ⟨φ, φ₂, hφ, -, -, hl, ha⟩ := hpb
  obtain ⟨inc, pr, -, -, hip, hpi, -, hc, hw⟩ := hz
  have key : ∀ b (oo : O), (w'.lev b ≫ actw' oo).left ≫ φ = g ≫ (z.lev b ≫ act oo).left := by
    intro b oo
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hl, Category.assoc]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← key, ← hl]
    congr 2
    rw [← hc, Category.assoc, ← hpi, ← Category.assoc inc, hip, Category.id_comp]
  · rw [← hl, hw a]
    have e1 : ((List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left ≫ φ =
        (pushHom hφ (𝟙_ (Over T)) (List.ofFn fun k => c'.lev (κ k a) ≫ inc ≫ actw' (o k)).prod).left := rfl
    rw [e1, map_list_prod, List.map_ofFn]
    have e2 : g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left =
        (toUnit (Over.mk ((𝟙_ (Over T)).hom ≫ g)) ≫
          (List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
      rw [Over.comp_left, Over.toUnit_left]
      rfl
    rw [e2, GlobalTheory.comp_list_prod_ofFn]
    congr 3
    funext k
    apply Over.OverMorphism.ext
    show (c'.lev (κ k a) ≫ inc ≫ actw' (o k)).left ≫ φ = _
    rw [← Category.assoc, hc, key]
    simp only [Over.comp_left, Over.toUnit_left, Over.mk_hom]
    rfl

end GlobalTheory.ZRelLevs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsFormulasOfIdempotentImagePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_sections_formulas_of_idempotent_image_pullback : ∀ (h h' M : ℕ) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' T : Scheme.{0}) (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g → ZRel e jl o κ c' w' actw' → (∀ a, g ≫ (z.lev (jl a) ≫ act e).left = g ≫ (z.lev (jl a)).left) ∧ ∀ a, g ≫ (z.lev a).left = g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
  first | (exact @GlobalTheory.ZRelLevs.zrel_levs) | (exact GlobalTheory.ZRelLevs.zrel_levs) | (intros; apply GlobalTheory.ZRelLevs.zrel_levs  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTorsionFamiliesEqualLocusOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTorsionFamiliesEqualLocusOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TorsEqOpen

theorem exists_open_eqLocus {S X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion (pullback.diagonal f)]
    (u v : S ⟶ X) (huv : u ≫ f = v ≫ f) :
    ∃ U : S.Opens, (∀ V : S.Opens, V ≤ U → V.ι ≫ u = V.ι ≫ v) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ S), g ≫ u = g ≫ v → Set.range g.base ⊆ (U : Set S) := by
  refine ⟨(pullback.lift u v huv) ⁻¹ᵁ (pullback.diagonal f).opensRange, ?_, ?_⟩
  · intro V hV
    have hr : Set.range (V.ι ≫ pullback.lift u v huv).base ⊆ Set.range (pullback.diagonal f).base := by
      rintro _ ⟨p, rfl⟩
      have hp : V.ι.base p ∈ V := by
        have h0 : V.ι.base p ∈ Set.range V.ι.base := ⟨p, rfl⟩
        rwa [Scheme.Opens.range_ι] at h0
      have := hV hp
      simpa using this
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) (V.ι ≫ pullback.lift u v huv) hr
    have h1 := congrArg (· ≫ pullback.fst f f) hl
    have h2 := congrArg (· ≫ pullback.snd f f) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, pullback.lift_fst,
      pullback.lift_snd, Category.comp_id] at h1 h2
    rw [← h1, ← h2]
  · intro T g hg
    rintro _ ⟨p, rfl⟩
    have e : g ≫ pullback.lift u v huv = g ≫ u ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hg]
    have e2 := congrArg (fun h => h.base p) e
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e2
    show (pullback.lift u v huv).base (g.base p) ∈ (pullback.diagonal f).opensRange
    rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]
    exact ⟨_, e2.symm⟩

end GlobalTheory.TorsEqOpen

namespace GlobalTheory.TorsEqOpen

theorem comp_pow_pt {S : Scheme.{0}} {X Y G : Over S} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem eq_of_eq_single {S : Scheme.{0}} {κ : Type} [Fintype κ] [DecidableEq κ] {A Z W : Over S} [GrpObj A] [IsCommMonObj A]
    (x y : (κ → ℤ) → (W ⟶ A)) (hx : ∀ a b, x (a + b) = x a * x b) (hy : ∀ a b, y (a + b) = y a * y b)
    (φ : Z ⟶ W) (hφ : ∀ i, φ ≫ x (Pi.single i 1) = φ ≫ y (Pi.single i 1)) (a : κ → ℤ) :
    φ ≫ x a = φ ≫ y a := by
  let F : (κ → ℤ) →+ Additive (Z ⟶ A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (φ ≫ x a)) (fun a b => by
      rw [hx, MonObj.comp_mul]; rfl)
  let G : (κ → ℤ) →+ Additive (Z ⟶ A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (φ ≫ y a)) (fun a b => by
      rw [hy, MonObj.comp_mul]; rfl)
  have hFG : F = G := by
    refine AddMonoidHom.functions_ext _ F G fun i k => ?_
    have e : (Pi.single i k : κ → ℤ) = k • Pi.single i 1 := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [e, map_zsmul, map_zsmul]
    congr 1
    simpa [F, G] using congrArg Additive.ofMul (hφ i)
  exact congrArg Additive.toMul (DFunLike.congr_fun hFG a)

end GlobalTheory.TorsEqOpen

namespace GlobalTheory

theorem torsFamily_eq_isOpen : ∀ (m M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M))
    (A : Over S') [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → 1 ≤ M →
    ∀ (x y : (Fin m ⊕ Fin m → ℤ) → (𝟙_ (Over S') ⟶ A)), (∀ a b, x (a + b) = x a * x b) →
    (∀ a b, y (a + b) = y a * y b) → (∀ a, x a ^ M = 1) → (∀ a, y a ^ M = 1) →
    ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ a, V.ι ≫ (x a).left = V.ι ≫ (y a).left) ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ S'), (∀ a, g ≫ (x a).left = g ≫ (y a).left) →
        Set.range g.base ⊆ (U : Set S') := by
  intro m M S' _ t A _ _ hA hM x y hx hy hxM hyM
  have hu : IsUnit (M : Γ(S', ⊤)) := by
    have h1 : IsUnit (M : cycAway M) := isUnit_natCast (by omega)
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of (cycAway M))).inv.hom
    have h3 := h2.map t.appTop.hom
    simpa using h3
  haveI := hA.smooth
  haveI : Etale (𝟙 A ^ M).left := GlobalTheory.GrpTangent.etale_id_pow A hu
  have hpow : ∀ z : 𝟙_ (Over S') ⟶ A, z ^ M = 1 →
      z.left ≫ (𝟙 A ^ M).left = (1 : 𝟙_ (Over S') ⟶ A).left := by
    intro z hz
    rw [← Over.comp_left, TorsEqOpen.comp_pow_pt, Category.comp_id, hz]
  choose U hU1 hU2 using fun i : Fin m ⊕ Fin m =>
    TorsEqOpen.exists_open_eqLocus (S := S') (𝟙 A ^ M).left (x (Pi.single i 1)).left (y (Pi.single i 1)).left
      ((hpow _ (hxM _)).trans (hpow _ (hyM _)).symm)
  refine ⟨⟨⋂ i, (U i : Set S'), isOpen_iInter_of_finite fun i => (U i).2⟩, ?_, ?_⟩
  · intro V hV a
    have hVi : ∀ i, V ≤ U i := fun i => (show (V : Set S') ⊆ U i from
      (show (V : Set S') ⊆ ⋂ i, (U i : Set S') from hV).trans (Set.iInter_subset _ i))
    have key := TorsEqOpen.eq_of_eq_single x y hx hy (toUnit (Over.mk V.ι)) (fun i =>
      Over.OverMorphism.ext (by
        rw [Over.comp_left, Over.comp_left, Over.toUnit_left]
        exact hU1 i V (hVi i))) a
    have := congrArg Over.Hom.left key
    rwa [Over.comp_left, Over.comp_left, Over.toUnit_left] at this
  · intro T g hg
    exact Set.subset_iInter fun i => hU2 i T g (hg _)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTorsionFamiliesEqualLocusOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_torsion_families_equal_locus_open : ∀ (m M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (A : Over S') [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → 1 ≤ M → ∀ (x y : (Fin m ⊕ Fin m → ℤ) → (𝟙_ (Over S') ⟶ A)), (∀ a b, x (a + b) = x a * x b) → (∀ a b, y (a + b) = y a * y b) → (∀ a, x a ^ M = 1) → (∀ a, y a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → ∀ a, V.ι ≫ (x a).left = V.ι ≫ (y a).left) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S'), (∀ a, g ≫ (x a).left = g ≫ (y a).left) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.torsFamily_eq_isOpen) | (exact GlobalTheory.torsFamily_eq_isOpen) | (intros; apply GlobalTheory.torsFamily_eq_isOpen  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSemiAbelianHomRetract
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSemiAbelianHomRetract
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isAbelianScheme_of_retract_of_isSemiAbelian : ∀ (S : Scheme.{0}) (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G), IsAbelianScheme A → IsSemiAbelian G → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme G := by
  intro S A G _ _ _ _ inc pr hA hG _ _ h
  have hApr : IsProper A.hom := hA.proper
  have hsep : IsSeparated G.hom := hG.separated
  have hpr : IsSeparated pr.left := by
    have e : pr.left ≫ G.hom = A.hom := Over.w pr
    have : IsSeparated (pr.left ≫ G.hom) := by rw [e]; infer_instance
    exact IsSeparated.of_comp pr.left G.hom
  have hid : inc.left ≫ pr.left = 𝟙 G.left := by rw [← Over.comp_left, h, Over.id_left]
  have hci : IsClosedImmersion inc.left := by
    have : IsClosedImmersion (inc.left ≫ pr.left) := by rw [hid]; infer_instance
    exact IsClosedImmersion.of_comp inc.left pr.left
  refine ⟨hG.comm, hG.smooth, ?_, hG.geomConnected⟩
  have e : inc.left ≫ A.hom = G.hom := Over.w inc
  rw [← e]
  infer_instance

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSemiAbelianHomRetractStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_of_semiAbelian_hom_retract : ∀ (S : Scheme.{0}) (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G), IsAbelianScheme A → IsSemiAbelian G → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme G := by
  first | (exact @GlobalTheory.isAbelianScheme_of_retract_of_isSemiAbelian) | (exact GlobalTheory.isAbelianScheme_of_retract_of_isSemiAbelian) | (intros; apply GlobalTheory.isAbelianScheme_of_retract_of_isSemiAbelian  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusIdempotentImageSiegel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdemLocus

section Help
variable {S S' : Scheme.{0}}

theorem secPull_congr {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hp : IsGrpPullback A' A f φ) {x y : 𝟙_ (Over S) ⟶ A} (hxy : f ≫ x.left = f ≫ y.left) :
    GlobalTheory.SiegelPull.secPull hp x = GlobalTheory.SiegelPull.secPull hp y := by
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · rw [GlobalTheory.SiegelPull.secPull_left, GlobalTheory.SiegelPull.secPull_left, hxy]
  · rw [Over.w (GlobalTheory.SiegelPull.secPull hp x), Over.w (GlobalTheory.SiegelPull.secPull hp y)]

theorem secPull_map (f : S' ⟶ S) {G A : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
    (m : G ⟶ A) (x : 𝟙_ (Over S) ⟶ G) :
    GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback f G) x ≫ (Over.pullback f).map m =
      GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback f A) (x ≫ m) := by
  apply Over.OverMorphism.ext
  apply (Pdiv.PullbackComparison.isGrpPullback f A).1.hom_ext
  · rw [GlobalTheory.SiegelPull.secPull_left, Over.comp_left, Category.assoc]
    show _ ≫ _ ≫ pullback.fst A.hom f = _
    rw [Pdiv.PullbackComparison.pullback_map_left_fst', ← Category.assoc]
    show (_ ≫ Pdiv.PullbackComparison.pφ f G) ≫ _ = _
    rw [GlobalTheory.SiegelPull.secPull_left, Over.comp_left, Category.assoc]
  · rw [Over.w, Over.w]

theorem secPull_prod {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hp : IsGrpPullback A' A f φ) {n : ℕ} (y : Fin n → (𝟙_ (Over S) ⟶ A)) :
    GlobalTheory.SiegelPull.secPull hp (List.ofFn y).prod = (List.ofFn fun k => GlobalTheory.SiegelPull.secPull hp (y k)).prod := by
  apply GlobalTheory.SiegelPull.push_injective hp
  rw [GlobalTheory.SiegelPull.push_secPull', GlobalTheory.comp_list_prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext k
  exact (GlobalTheory.SiegelPull.push_secPull' hp (y k)).symm

end Help

end GlobalTheory.IdemLocus

namespace GlobalTheory.IdemLocus

theorem image_bundle_rig {S : Scheme.{0}} (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G]
    (P : LB (G2 A).left) (inc : G ⟶ A) [IsMonHom inc]
    (r₁ : ∃ s : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, s.IsGen)
    (r₂ : ∃ s : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, s.IsGen)
    (sy : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) :
    (∃ s : ((P.pull (inc ⊗ₘ inc).left).pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) ∧
    (∃ s : ((P.pull (inc ⊗ₘ inc).left).pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) ∧
    LBIso (P.pull (inc ⊗ₘ inc).left) ((P.pull (inc ⊗ₘ inc).left).pull (lift (snd G G) (fst G G)).left) := by
  have e₁ : (lift (1 : G ⟶ G) (𝟙 G)).left ≫ (inc ⊗ₘ inc).left = inc.left ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp [lift_map, comp_lift, MonObj.one_comp, MonObj.comp_one]
  have e₂ : (lift (𝟙 G) (1 : G ⟶ G)).left ≫ (inc ⊗ₘ inc).left = inc.left ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp [lift_map, comp_lift, MonObj.one_comp, MonObj.comp_one]
  have e₃ : (lift (snd G G) (fst G G)).left ≫ (inc ⊗ₘ inc).left =
      (inc ⊗ₘ inc).left ≫ (lift (snd A A) (fst A A)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp [lift_map, comp_lift]
  obtain ⟨t₁, ht₁⟩ := r₁
  obtain ⟨t₂, ht₂⟩ := r₂
  exact ⟨gen_chartPull (chartPullLinComb P (inc ⊗ₘ inc).left _ _ _ inc.left (fun _ => e₁)) t₁ ht₁,
    gen_chartPull (chartPullLinComb P (inc ⊗ₘ inc).left _ _ _ inc.left (fun _ => e₂)) t₂ ht₂,
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
      (chartPullLinComb P _ _ _ _ (inc ⊗ₘ inc).left (fun _ => e₃)) sy⟩

end GlobalTheory.IdemLocus

namespace GlobalTheory.IdemLocus

theorem image_bundle_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G]
    [IsCommMonObj G] (P : LB (G2 A).left) (hP : P.IsLB) (inc : G ⟶ A) :
    LBIso ((P.pull (inc ⊗ₘ inc).left).pull (Pdiv.PullbackComparison.pφ₂ f G))
      ((P.pull (Pdiv.PullbackComparison.pφ₂ f A)).pull ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left) := by
  set_option backward.isDefEq.respectTransparency false in
    have hm : ((Over.pullback f).map inc).left ≫ Pdiv.PullbackComparison.pφ f A = Pdiv.PullbackComparison.pφ f G ≫ inc.left :=
      Pdiv.PullbackComparison.pullback_map_left_fst' f inc
    have key : Pdiv.PullbackComparison.pφ₂ f G ≫ (inc ⊗ₘ inc).left =
        ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left ≫ Pdiv.PullbackComparison.pφ₂ f A := by
      apply Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components
      · have ht : (inc ⊗ₘ inc).left ≫ (fst A A).left = (fst G G).left ≫ inc.left := by
          rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
        have ht' : ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left ≫
            (fst ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left =
            (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ ((Over.pullback f).map inc).left := by
          rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
        simp only [Category.assoc]
        rw [ht, reassoc_of% (Pdiv.PullbackComparison.pφ₂_fst f G), Pdiv.PullbackComparison.pφ₂_fst f A, reassoc_of% ht', hm]
      · have ht : (inc ⊗ₘ inc).left ≫ (snd A A).left = (snd G G).left ≫ inc.left := by
          rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
        have ht' : ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left ≫
            (snd ((Over.pullback f).obj A) ((Over.pullback f).obj A)).left =
            (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ ((Over.pullback f).map inc).left := by
          rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
        simp only [Category.assoc]
        rw [ht, reassoc_of% (Pdiv.PullbackComparison.pφ₂_snd f G), Pdiv.PullbackComparison.pφ₂_snd f A, reassoc_of% ht', hm]
    have e₁ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP (inc ⊗ₘ inc).left))
      (Pdiv.PullbackComparison.pφ₂ f G)
    have e₂ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP (Pdiv.PullbackComparison.pφ₂ f A)))
      ((Over.pullback f).map inc ⊗ₘ (Over.pullback f).map inc).left
    rw [key] at e₁
    exact LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂.symm

end GlobalTheory.IdemLocus

namespace GlobalTheory.IdemLocus

theorem adj_pullback' {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] (A : Over S) [GrpObj A] [IsCommMonObj A]
    (Q : LB (G2 A).left) (bar : O → O) (act : O → (A ⟶ A)) (hQ : Q.IsLB) (hA : Adj A Q bar act) :
    Adj ((Over.pullback f).obj A) (Q.pull (Pdiv.PullbackComparison.pφ₂ f A)) bar (fun a => (Over.pullback f).map (act a)) := by
  set_option backward.isDefEq.respectTransparency false in
    have hw : Pdiv.PullbackComparison.pφ f A ≫ A.hom = ((Over.pullback f).obj A).hom ≫ f := pullback.condition
    have hA' : Adj A (Q.pull (𝟙 _)) bar act := fun a => by
      have e₁ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hQ (𝟙 (G2 A).left)))
        (lift (fst A A ≫ act a) (snd A A)).left
      have e₂ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hQ (𝟙 (G2 A).left)))
        (lift (fst A A) (snd A A ≫ act (bar a))).left
      rw [Category.comp_id] at e₁ e₂
      exact LBIso.trans (pull_isLB (pull_isLB hQ _) _) (pull_isLB hQ _) (pull_isLB (pull_isLB hQ _) _) e₁
        (LBIso.trans (pull_isLB hQ _) (pull_isLB hQ _) (pull_isLB (pull_isLB hQ _) _) (hA a) e₂.symm)
    have key := ActUnr.adj_along hw act (fun a => (Over.pullback f).map (act a))
      (fun a => Pdiv.PullbackComparison.pullback_map_left_fst' f (act a)) Q (𝟙 _) bar hA'
    have hsq : ActUnr.sqMap hw ≫ 𝟙 _ = Pdiv.PullbackComparison.pφ₂ f A := by
      rw [Category.comp_id]
      apply Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components
      · rw [ActUnr.sqMap_fst, Pdiv.PullbackComparison.pφ₂_fst]
      · rw [ActUnr.sqMap_snd, Pdiv.PullbackComparison.pφ₂_snd]
    rw [hsq] at key
    exact key

end GlobalTheory.IdemLocus

namespace GlobalTheory.IdemLocus

theorem exists_open_locus : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (U : S'.Opens) (c : SiegPre h M (zetaAway M) (U.ι ≫ t)) (w : SiegPre h' M (zetaAway M) (U.ι ≫ t)) (actw : O → (w.A ⟶ w.A)), SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(U.toScheme, ⊤)) ∧ w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act U.ι ∧ ZRel e jl o κ c w actw ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)), IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g ∧ ZRel e jl o κ c' w' actw') → Set.range g.base ⊆ (U : Set S') := by
  set_option backward.isDefEq.respectTransparency false in
    intro h h' M d O _ bar e jl n o κ S' _ t z act hh hM hMo hd hMd hz hRA hAdj hee
    have hee' : act e ≫ act e = act e := by rw [← hRA.2.2.1, hee]
    haveI hae := hRA.1 e
    obtain ⟨G, _, _, inc, pr, hGs, hinc, hpr, hip, hpi⟩ :=
      GlobalTheory.Mum.IdemImage.isSemiAbelian_image S' z.A (GlobalTheory.isSemiAbelian_of_isAbelianScheme z.A z.ab) (act e) (hRA.1 e)
        hee'
    haveI := hinc
    haveI := hpr
    have hGab : IsAbelianScheme G := GlobalTheory.T.isAbelianScheme_of_semiAbelian_hom_retract S' z.A G inc pr z.ab hGs hinc hpr hip
    let Pe : LB (G2 G).left := z.P.pull (inc ⊗ₘ inc).left
    have hPe : Pe.IsLB := pull_isLB z.isLB _
    obtain ⟨hr₁, hr₂, hsy⟩ := image_bundle_rig z.A G z.P inc z.rig₁ z.rig₂ z.symm
    let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G) := fun a => z.lev (jl a) ≫ pr
    have lev_add : ∀ a b, lev (a + b) = lev a * lev b := fun a b => by
      simp only [lev, map_add (f := _), z.lev_add, MonObj.mul_comp]
    have lev_tors : ∀ a, lev a ^ M = 1 := fun a => by
      simp only [lev, ← MonObj.pow_comp, z.lev_tors, MonObj.one_comp]

    have hM1 : 1 ≤ M := by omega
    let x₂ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ z.A) := fun a => z.lev (jl a) ≫ act e
    let y₂ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ z.A) := fun a => z.lev (jl a)
    let y₃ : (Fin h' ⊕ Fin h' → ℤ) → (𝟙_ (Over S') ⟶ z.A) :=
      fun a => (List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod
    have hy₃ : ∀ a, y₃ a = ∏ k, z.lev (jl (κ k a)) ≫ act (o k) := fun a => List.prod_ofFn
    obtain ⟨U₁, hU₁, hT₁⟩ := GlobalTheory.T.natCast_unit_locus_open S' d
    obtain ⟨U₂, hU₂, hT₂⟩ := GlobalTheory.T.additive_torsion_families_equal_locus_open h M S' t z.A z.ab hM1 x₂ y₂
      (fun a b => by simp only [x₂, map_add (f := _), z.lev_add, MonObj.mul_comp])
      (fun a b => by simp only [y₂, map_add (f := _), z.lev_add])
      (fun a => by simp only [x₂, ← MonObj.pow_comp, z.lev_tors, MonObj.one_comp])
      (fun a => by simp only [y₂, z.lev_tors])
    obtain ⟨U₃, hU₃, hT₃⟩ := GlobalTheory.T.additive_torsion_families_equal_locus_open h' M S' t z.A z.ab hM1 z.lev y₃ z.lev_add
      (fun a b => by
        haveI := fun k => hRA.1 (o k)
        simp only [hy₃, map_add (f := _), z.lev_add, MonObj.mul_comp, Finset.prod_mul_distrib])
      z.lev_tors
      (fun a => by
        haveI := fun k => hRA.1 (o k)
        simp only [hy₃, ← Finset.prod_pow, ← MonObj.pow_comp, z.lev_tors, MonObj.one_comp, Finset.prod_const_one])
    obtain ⟨U₄, hU₄, hT₄⟩ := GlobalTheory.T.isOpen_symplecticLevel_locus h M S' t G Pe lev hGab hPe hr₁ hr₂ hsy hM hMo lev_add lev_tors
    obtain ⟨U₅, hU₅, hT₅⟩ := GlobalTheory.T.diagonal_restriction_relAmple_locus_open S' G Pe hGab hPe
    obtain ⟨U₆, hU₆, hT₆⟩ := GlobalTheory.T.exists_open_locus_kernel_killed_symmetric_bundle d S' G Pe hGab hPe hr₁ hr₂ hsy
    let U : S'.Opens := U₁ ⊓ U₂ ⊓ U₃ ⊓ U₄ ⊓ U₅ ⊓ U₆
    have l₁ : U ≤ U₁ := inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    have l₂ : U ≤ U₂ := inf_le_left.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
    have l₃ : U ≤ U₃ := inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
    have l₄ : U ≤ U₄ := inf_le_left.trans (inf_le_left.trans inf_le_right)
    have l₅ : U ≤ U₅ := inf_le_left.trans inf_le_right
    have l₆ : U ≤ U₆ := inf_le_right
    have pbG := Pdiv.PullbackComparison.isGrpPullback U.ι G
    have hS := hU₄ U l₄
    let c : SiegPre h M (zetaAway M) (U.ι ≫ t) :=
      { A := (Over.pullback U.ι).obj G
        ab := GlobalTheory.isAbelianScheme_pullback_obj U.ι G hGab
        P := Pe.pull (Pdiv.PullbackComparison.pφ₂ U.ι G)
        isLB := pull_isLB hPe _
        rig₁ := by
          obtain ⟨t₁, ht₁⟩ := hr₁
          exact gen_chartPull (chartPullLinComb Pe _ _ _ _ (Pdiv.PullbackComparison.pφ U.ι G)
            (fun _ => Pdiv.PullbackComparison.lift_one_id U.ι G)) t₁ ht₁
        rig₂ := by
          obtain ⟨t₂, ht₂⟩ := hr₂
          exact gen_chartPull (chartPullLinComb Pe _ _ _ _ (Pdiv.PullbackComparison.pφ U.ι G)
            (fun _ => Pdiv.PullbackComparison.lift_id_one U.ι G)) t₂ ht₂
        symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Pe _ _ rfl)
          (chartPullLinComb Pe _ _ _ _ (Pdiv.PullbackComparison.pφ₂ U.ι G) (fun _ => Pdiv.PullbackComparison.lift_swap U.ι G)) hsy
        lev := fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι G) (lev a)
        lev_add := hS.1
        lev_tors := hS.2.1
        geom := hS.2.2 }
    let w : SiegPre h' M (zetaAway M) (U.ι ≫ t) := GlobalTheory.LowChart.siegPull z U.ι (U.ι ≫ t) rfl
    let actw : O → (w.A ⟶ w.A) := fun a => (Over.pullback U.ι).map (act a)
    refine ⟨U, c, w, actw, ⟨hU₅ U l₅, hU₆ U l₆⟩, hU₁ U l₁, GlobalTheory.LowChart.principal_siegPull z U.ι _ rfl hz,
      ActUnr.isRAct_pullback U.ι z.A act hRA, adj_pullback' U.ι z.A z.P bar act z.isLB hAdj, ?_, ?_, ?_⟩

    · exact ⟨Pdiv.PullbackComparison.pφ U.ι z.A, Pdiv.PullbackComparison.pφ₂ U.ι z.A, Pdiv.PullbackComparison.isGrpPullback U.ι z.A,
        Pdiv.PullbackComparison.isSquare U.ι z.A, Pdiv.PullbackComparison.gen_refl _ (pull_isLB z.isLB _),
        fun a => GlobalTheory.SiegelPull.secPull_left (Pdiv.PullbackComparison.isGrpPullback U.ι z.A) (z.lev a), fun a => Pdiv.PullbackComparison.pullback_map_left_fst' U.ι (act a)⟩
    · refine ⟨(Over.pullback U.ι).map inc, (Over.pullback U.ι).map pr,
        (by exact (inferInstance : IsMonHom ((Over.pullback U.ι).map inc))),
        (by exact (inferInstance : IsMonHom ((Over.pullback U.ι).map pr))), ?_, ?_, ?_, ?_, ?_⟩
      · exact (CategoryTheory.Functor.map_comp _ _ _).symm.trans ((congrArg _ hip).trans (CategoryTheory.Functor.map_id _ _))
      · exact (CategoryTheory.Functor.map_comp _ _ _).symm.trans (congrArg _ hpi)
      · exact image_bundle_pull U.ι z.A G z.P z.isLB inc
      · intro a
        show GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι G) (z.lev (jl a) ≫ pr) ≫ (Over.pullback U.ι).map inc =
          GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι z.A) (z.lev (jl a))
        rw [secPull_map, Category.assoc, hpi]
        exact secPull_congr _ (hU₂ U l₂ a)
      · intro a
        show GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι z.A) (z.lev a) = _
        rw [secPull_congr _ (hU₃ U l₃ a), secPull_prod]
        congr 1
        apply congrArg List.ofFn
        funext k
        show _ = GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback U.ι G) (z.lev (jl (κ k a)) ≫ pr) ≫ (Over.pullback U.ι).map inc ≫
          (Over.pullback U.ι).map (act (o k))
        rw [← Category.assoc, secPull_map, secPull_map]
        simp only [Category.assoc, reassoc_of% hpi]
        apply secPull_congr
        have := hU₂ U l₂ (κ k a)
        simp only [x₂, y₂, Over.comp_left] at this ⊢
        rw [reassoc_of% this]
    · intro T g c' hdT hker ⟨w', actw', hpb, hzr⟩
      obtain ⟨hl₂, hl₃⟩ := GlobalTheory.T.level_sections_formulas_of_idempotent_image_pullback h h' M O e jl n o κ S' T t z act g c' w' actw' hpb hzr
      obtain ⟨inc', pr', hinc', hpr', hip', hpi', hP', hl', -⟩ := hzr
      obtain ⟨ψ, ψ₂, hψ, hsq, hw', hlw, hact⟩ := hpb
      obtain ⟨φ, φ₂, hφ, hsqφ, hiφ, hiφ₂⟩ := GlobalTheory.T.idempotent_endomorphism_image_commutes_base_change S' T g z.A G inc pr (act e) w'.A c'.A inc' pr' (actw' e)
        ψ ψ₂ hinc hpr hip hpi hinc' hpr' hip' hpi' hψ hsq (hact e)
      have hcP : LBIso c'.P (Pe.pull φ₂) := by
        have e₁ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp hw' (inc' ⊗ₘ inc').left
        rw [hiφ₂] at e₁
        have e₂ := GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl hPe) φ₂
        exact LBIso.trans c'.isLB (pull_isLB w'.isLB _) (pull_isLB hPe _) hP'
          (LBIso.trans (pull_isLB w'.isLB _) (pull_isLB z.isLB _) (pull_isLB hPe _) e₁ e₂.symm)
      have hcl : ∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left := fun a => by
        have h₀ : (c'.lev a).left ≫ φ ≫ inc.left = g ≫ (z.lev (jl a)).left := by
          rw [← hiφ, ← Category.assoc, ← Over.comp_left, hl' a, hlw]
        calc (c'.lev a).left ≫ φ = (c'.lev a).left ≫ φ ≫ (inc ≫ pr).left := by
              rw [hip, Over.id_left, Category.comp_id]
          _ = ((c'.lev a).left ≫ φ ≫ inc.left) ≫ pr.left := by rw [Over.comp_left]; simp only [Category.assoc]
          _ = g ≫ (lev a).left := by rw [h₀]; simp only [lev, Over.comp_left, Category.assoc]
      intro x hx
      simp only [U, TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff]
      exact ⟨⟨⟨⟨⟨hT₁ T g hdT hx, hT₂ T g hl₂ hx⟩, hT₃ T g hl₃ hx⟩, hT₄ T g c' φ φ₂ hφ hsqφ hcP hcl hx⟩,
        hT₅ T g c'.A φ φ₂ c'.P hφ hsqφ c'.isLB hcP hker.1 hx⟩,
        hT₆ T g c'.A φ φ₂ c'.P hφ hsqφ c'.isLB hcP hdT hker.1 hker.2 hx⟩

end GlobalTheory.IdemLocus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusIdempotentImageSiegelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_locus_idempotent_image_siegel : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (U : S'.Opens) (c : SiegPre h M (zetaAway M) (U.ι ≫ t)) (w : SiegPre h' M (zetaAway M) (U.ι ≫ t)) (actw : O → (w.A ⟶ w.A)), SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(U.toScheme, ⊤)) ∧ w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act U.ι ∧ ZRel e jl o κ c w actw ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)), IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g ∧ ZRel e jl o κ c' w' actw') → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.IdemLocus.exists_open_locus) | (exact GlobalTheory.IdemLocus.exists_open_locus) | (intros; apply GlobalTheory.IdemLocus.exists_open_locus  <;> assumption)
end
