module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLieBasisComplex
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.DerivZero

theorem exists_lift_isMonHom {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H]
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hG : IsGrpPullback G' G j φ)
    (hH : IsGrpPullback H' H j ψ) (f : G ⟶ H) [IsMonHom f] :
    ∃ f' : G' ⟶ H', IsMonHom f' ∧ f'.left ≫ ψ = φ ≫ f.left := by
  have w : (φ ≫ f.left) ≫ H.hom = G'.hom ≫ j := by
    rw [Category.assoc, Over.w f]
    exact hG.1.w
  obtain ⟨f', hf'⟩ : ∃ f' : G' ⟶ H', f'.left ≫ ψ = φ ≫ f.left :=
    ⟨Over.homMk (hH.1.lift (φ ≫ f.left) G'.hom w) (hH.1.lift_snd _ _ w), hH.1.lift_fst _ _ w⟩
  have hpt : ∀ {T : Over S'} (x : T ⟶ G'), ∃ x₀ : Over.mk (T.hom ≫ j) ⟶ G, x₀.left = x.left ≫ φ := by
    intro T x
    refine ⟨Over.homMk (x.left ≫ φ) ?_, rfl⟩
    dsimp
    rw [Category.assoc, hG.1.w, ← Category.assoc, Over.w x]
  have hmul : ∀ {T : Over S'} (x y : T ⟶ G'), (x * y) ≫ f' = (x ≫ f') * (y ≫ f') := by
    intro T x y
    obtain ⟨x₀, hx₀⟩ := hpt x
    obtain ⟨y₀, hy₀⟩ := hpt y
    apply Over.OverMorphism.ext
    apply hH.1.hom_ext
    · have e1 := hG.2 T x y x₀ y₀ hx₀ hy₀
      have e2 := hH.2 T (x ≫ f') (y ≫ f') (x₀ ≫ f) (y₀ ≫ f)
        (by simp only [Over.comp_left, hx₀, Category.assoc, hf'])
        (by simp only [Over.comp_left, hy₀, Category.assoc, hf'])
      have e3 : (x₀ * y₀) ≫ f = (x₀ ≫ f) * (y₀ ≫ f) := by
        simp [Hom.mul_def]
      rw [← e2, ← e3]
      simp only [Over.comp_left, Category.assoc, hf', e1]
    · simp only [Over.w]
  refine ⟨f', ⟨?_, ?_⟩, hf'⟩
  · have h1 := hmul (1 : 𝟙_ (Over S') ⟶ G') 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ (Over S') ⟶ G') ≫ f' = 1 := by simpa using h1.symm
    simpa [Hom.one_def] using h2
  · have h3 := hmul (fst G' G') (snd G' G')
    simpa [Hom.mul_def] using h3

end GlobalTheory.DerivZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.DiffCoord

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

theorem isTangent_comp_hom (f : G ⟶ G') [IsMonHom f] {v : epsR R ⟶ G} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem isLieComb_comp_hom (f : G ⟶ G') [IsMonHom f] {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)}
    {w : epsR R ⟶ G} (h : IsLieComb c v w) : IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu, Category.assoc]
  · exact (map_list_prod (IsMonHom.monoidHom f (epsR R)) (List.ofFn u)).trans (by rw [List.map_ofFn]; rfl)

theorem exists_linearMap [IsCommMonObj G'] (f : G ⟶ G') [IsMonHom f] {n m : ℕ} {v : Fin n → (epsR R ⟶ G)}
    {v' : Fin m → (epsR R ⟶ G')} (hv : IsLieBasis v) (hv' : IsLieBasis v') :
    ∃ M : (Fin n → R) →ₗ[R] (Fin m → R), ∀ c w, IsLieComb c v w → IsLieComb (M c) v' (w ≫ f) := by
  choose A hA using fun i => (hv'.2 _ (isTangent_comp_hom f (hv.1 i))).exists
  refine ⟨Fintype.linearCombination R A, fun c w h => ?_⟩
  rw [Fintype.linearCombination_apply]
  exact (LieComb.lieComb_algebra R G' m v' hv'.1).2.2.1 n A _ c _ hA (isLieComb_comp_hom f h)

theorem existsUnique_isDiffOf : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P)
    (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (f : P.A ⟶ P'.A), IsMonHom f → (∃! M, F.IsDiffOf F' f M) ∧
    ∃ f₀ : F.P₀.A ⟶ F'.P₀.A, IsMonHom f₀ ∧ f₀.left ≫ F'.φ = F.φ ≫ f.left ∧
      ∀ M, F.IsDiffOf F' f M → ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀) := by
  intro K _ _ P F P' F' f hf
  obtain ⟨f₀, hf₀, e⟩ := DerivZero.exists_lift_isMonHom F.fib.2.1 F'.fib.2.1 f
  have := F'.P₀.isAb.comm
  obtain ⟨M, hM⟩ := exists_linearMap f₀ F.basis F'.basis
  have hd : F.IsDiffOf F' f M := by
    rintro u c ⟨hu, w, hw, hc⟩
    refine ⟨isTangent_comp_hom f hu, w ≫ f₀, ?_, hM c w hc⟩
    unfold IsVecOver at hw ⊢
    rw [Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, hw, Category.assoc]
  have hcoord : ∀ u c c', F'.IsCoord u c → F'.IsCoord u c' → c = c' := by
    rintro u c c' ⟨-, w, hw, hc⟩ ⟨-, w', hw', hc'⟩
    obtain rfl : w = w' := Over.OverMorphism.ext (F'.fib.2.1.1.hom_ext (hw.trans hw'.symm) ((Over.w _).trans (Over.w _).symm))
    exact (F'.basis.2 w ((LieComb.lieComb_algebra K _ _ F'.v F'.basis.1).2.1 c w hc)).unique hc hc'
  have huniq : ∀ N, F.IsDiffOf F' f N → N = M := fun N hN => by
    refine LinearMap.ext_on (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).2 fun c hc => ?_
    refine Submodule.span_induction (p := fun c _ => N c = M c) ?_ ?_ ?_ ?_ hc
    · rintro c ⟨u, hu⟩
      exact hcoord _ _ _ (hN u c hu) (hd u c hu)
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _), map_add (f := _), hx, hy]
    · intro r x _ hx
      rw [← algebraMap_smul K r x, map_smul, map_smul, hx]
  refine ⟨⟨M, hd, huniq⟩, f₀, hf₀, e, fun N hN => ?_⟩
  rw [huniq N hN]
  exact hM

end GlobalTheory.CM.DiffCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_differential_monHom_lieBasis : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (f : P.A ⟶ P'.A), IsMonHom f → (∃! M, F.IsDiffOf F' f M) ∧ ∃ f₀ : F.P₀.A ⟶ F'.P₀.A, IsMonHom f₀ ∧ f₀.left ≫ F'.φ = F.φ ≫ f.left ∧ ∀ M, F.IsDiffOf F' f M → ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀) := by
  first | exact @GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf | exact GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf | (intros; apply GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.PairingFibre

variable {S S' : Scheme.{0}} {s : S' ⟶ S}

theorem exists_hom {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H] [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hG : IsGrpPullback G' G s φ) (hH : IsGrpPullback H' H s ψ)
    (w : G ⟶ H) [IsMonHom w] : ∃ w' : G' ⟶ H', IsMonHom w' ∧ w'.left ≫ ψ = φ ≫ w.left := by
  let w' : G' ⟶ H' := Over.homMk (hH.1.lift (φ ≫ w.left) G'.hom (by rw [Category.assoc, Over.w, hG.1.w]))
    (hH.1.lift_snd _ _ _)
  have hw : w'.left ≫ ψ = φ ≫ w.left := hH.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G'), Geo.Tor.pushPt hH.1.w (x ≫ w') = Geo.Tor.pushPt hG.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have mul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ w' = (x ≫ w') * (y ≫ w') := by
    intro T x y
    apply SymBaseChange.pushPt_injective hH
    have a : Geo.Tor.pushPt hG.1.w (x * y) = Geo.Tor.pushPt hG.1.w x * Geo.Tor.pushPt hG.1.w y := map_mul (Geo.Tor.pushHom hG T) x y
    have b : Geo.Tor.pushPt hH.1.w ((x ≫ w') * (y ≫ w')) = Geo.Tor.pushPt hH.1.w (x ≫ w') * Geo.Tor.pushPt hH.1.w (y ≫ w') :=
      map_mul (Geo.Tor.pushHom hH T) _ _
    rw [pa, a, b, pa, pa, MonObj.mul_comp]
  refine ⟨w', ⟨?_, ?_⟩, hw⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S') ⟶ G') ≫ w' = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem cube_pull {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LBIso L' (L.pull φ)) {T : Over S} {T' : Over S'} (U : T'.left ⟶ T.left)
    (hU : U ≫ T.hom = T'.hom ≫ s) {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (hx : ∀ i, (x' i).left ≫ φ = U ≫ (x i).left) : LBIso (cubeLB G' x' L') ((cubeLB G x L).pull U) := by
  have hc : (cubeLB G x L).IsLB := DVR.linComb_isLB L hL _ _
  refine LBIso.trans (B := cubeLB G' x' (L.pull φ)) (DVR.linComb_isLB L' hL' _ _)
    (DVR.linComb_isLB _ (Geo.Tor.pull_isLB hL φ) _ _) (Geo.Tor.pull_isLB hc U) (PowPrimitive.lbIso_linComb w _ _) ?_
  exact LBIso.chartPull (Geo.Tor.chartPullLinComb L φ _ _ _ U fun I =>
    Geo.Tor.psum_push h x' x (Over.homMk U hU) (fun i => Over.OverMorphism.ext (hx i)) I.down)
    (Geo.Tor.chartPullPull _ U U rfl) (PolBaseChange.lbIso_refl hc)

theorem exists_gen_cube_one {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (T : Over S) :
    ∃ t : LB.Gen (cubeLB G (fun _ : Fin 2 => (1 : T ⟶ G)) L), t.IsGen := by
  refine (PrimNorm.hasGen_iff hL _ _).2 ?_
  have hp (I : Finset (Fin 2)) : psum G (fun _ : Fin 2 => (1 : T ⟶ G)) I = 1 := by
    unfold psum
    induction (List.finRange 2).filter (· ∈ I) with
    | nil => rfl
    | cons k l ih => exact (congrArg ((1 : T ⟶ G) * ·) ih).trans (_root_.mul_one _)
  simp_rw [hp]
  rw [show (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) =
    {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} by decide]
  classical
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp

theorem cube_zero {X Y G : Over S} [GrpObj X] [GrpObj Y] [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (f₁ : X ⟶ G) (f₂ : Y ⟶ G) [IsMonHom f₁] [IsMonHom f₂] :
    LBIso (cubeLB G (fun _ : Fin 2 => (1 : 𝟙_ (Over S) ⟶ G)) L)
      ((cubeLB G ![fst X Y ≫ f₁, snd X Y ≫ f₂] L).pull (eSec (X ⊗ Y))) := by
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  refine cube_pull (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) hL hL
    (LBIso.chartPull (Geo.Tor.chartPullId L) (Geo.Tor.chartPullPull L _ (𝟙 _) rfl) (PolBaseChange.lbIso_refl hL)) _
    (by rw [eSec, Over.w, Category.comp_id]) _ _ fun i => ?_
  rw [eSec, ← Over.comp_left, ← Over.comp_left]
  congr 1
  fin_cases i <;> simp [Hom.one_def]

theorem weilEq_iff {X Y A B : Over S} {X' Y' A' B' : Over S'} [GrpObj X] [GrpObj Y] [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B] [GrpObj X'] [GrpObj Y'] [GrpObj A'] [GrpObj B']
    {x : X'.left ⟶ X.left} {y : Y'.left ⟶ Y.left} {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}
    (hX : IsGrpPullback X' X s x) (hY : IsGrpPullback Y' Y s y) (hA : IsGrpPullback A' A s a)
    (hB : IsGrpPullback B' B s b) {L : LB A.left} {M : LB B.left} {L' : LB A'.left} {M' : LB B'.left}
    (hL : L.IsLB) (hM : M.IsLB) (hL' : L'.IsLB) (hM' : M'.IsLB) (wL : LBIso L' (L.pull a)) (wM : LBIso M' (M.pull b))
    {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B} {f₁' : X' ⟶ A'} {f₂' : Y' ⟶ A'} {g₁' : X' ⟶ B'}
    {g₂' : Y' ⟶ B'} (e₁ : f₁'.left ≫ a = x ≫ f₁.left) (e₂ : f₂'.left ≫ a = y ≫ f₂.left)
    (e₃ : g₁'.left ≫ b = x ≫ g₁.left) (e₄ : g₂'.left ≫ b = y ≫ g₂.left) {k : Type} [Field k] (t : Sp k ⟶ S') :
    WeilEq L' f₁' f₂' M' g₁' g₂' t ↔ WeilEq L f₁ f₂ M g₁ g₂ (t ≫ s) := by
  have key : ∀ (n : ℕ) (p : Over.mk t ⟶ X') (q : Over.mk t ⟶ Y') (c : kˣ),
      ((Out.WeilIs A' L' n (p ≫ f₁') (q ≫ f₂') (unitOn c) ↔ Out.WeilIs B' M' n (p ≫ g₁') (q ≫ g₂') (unitOn c)) ↔
      (Out.WeilIs A L n (Geo.Tor.pushHom hX _ p ≫ f₁) (Geo.Tor.pushHom hY _ q ≫ f₂) (unitOn c) ↔
        Out.WeilIs B M n (Geo.Tor.pushHom hX _ p ≫ g₁) (Geo.Tor.pushHom hY _ q ≫ g₂) (unitOn c))) := by
    intro n p q c
    refine iff_congr (weilIs_grpPullback_of_comm S S' A A' s a L L' hL hL' hA wL _ _ _ _ _ _ _ ?_ ?_)
      (weilIs_grpPullback_of_comm S S' B B' s b M M' hM hM' hB wM _ _ _ _ _ _ _ ?_ ?_)
    all_goals
      show (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _
      simp only [Category.assoc, e₁, e₂, e₃, e₄]
  have pw : ∀ {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ)
      (n : ℕ) (p : Over.mk t ⟶ G'), p ^ n = 1 ↔ Geo.Tor.pushHom h _ p ^ n = 1 := fun h n p => by
    rw [← map_pow]
    exact (map_eq_one_iff _ fun u v e => SymBaseChange.pushPt_injective h e).symm
  have su : ∀ {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ)
      (p₀ : Over.mk (t ≫ s) ⟶ G), ∃ p : Over.mk t ⟶ G', Geo.Tor.pushHom h _ p = p₀ := fun h p₀ =>
    ⟨Over.homMk (h.1.lift p₀.left t (Over.w p₀)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  constructor
  · intro H n p₀ q₀ c hn hp hq
    obtain ⟨p, rfl⟩ := su hX p₀
    obtain ⟨q, rfl⟩ := su hY q₀
    exact (key n p q c).1 (H n p q c hn ((pw hX n p).2 hp) ((pw hY n q).2 hq))
  · intro H n p q c hn hp hq
    exact (key n p q c).2 (H n _ _ c hn ((pw hX n p).1 hp) ((pw hY n q).1 hq))

theorem lamEq_weilEq_over_ring : Out.Laws → ∀ (R : Type) [CommRing R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k),
    (LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β)) ∧ (IsDedekindDomain R → Function.Injective β → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β) → LamEq A.L f₁ f₂ B.L g₁ g₂) := by
  intro laws R _ X Y A B f₁ f₂ g₁ g₂ _ _ _ _ k _ _ _ β
  have bc : ∀ P : Out.PolAV (Sp R), ∃ (P' : Out.PolAV (Sp k)) (φ : P'.A.left ⟶ P.A.left),
      IsGrpPullback P'.A P.A (spMap β) φ ∧ LBIso P'.L (P.L.pull φ) := fun P => by
    obtain ⟨P', φ, hφ, -, hm, t, ht⟩ := laws.polBaseChange _ _ (spMap β) P
    refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl
  obtain ⟨X', x, hX, -⟩ := bc X
  obtain ⟨Y', y, hY, -⟩ := bc Y
  obtain ⟨A', a, hA, wL⟩ := bc A
  obtain ⟨B', b, hB, wM⟩ := bc B
  have := A.isAb.comm
  have := B.isAb.comm
  have := A'.isAb.comm
  have := B'.isAb.comm
  obtain ⟨f₁', m₁, e₁⟩ := exists_hom hX hA f₁
  obtain ⟨f₂', m₂, e₂⟩ := exists_hom hY hA f₂
  obtain ⟨g₁', m₃, e₃⟩ := exists_hom hX hB g₁
  obtain ⟨g₂', m₄, e₄⟩ := exists_hom hY hB g₂
  have W := weilEq_iff hX hY hA hB A.isLB B.isLB A'.isLB B'.isLB wL wM e₁ e₂ e₃ e₄ (𝟙 (Sp k))
  rw [Category.id_comp] at W
  let π : Over.mk ((X'.A ⊗ Y'.A).hom ≫ spMap β) ⟶ X.A ⊗ Y.A :=
    lift (Geo.Tor.pushPt hX.1.w (fst X'.A Y'.A)) (Geo.Tor.pushPt hY.1.w (snd X'.A Y'.A))
  have π₁ : π.left ≫ (fst X.A Y.A).left = (fst X'.A Y'.A).left ≫ x := by
    rw [← Over.comp_left, lift_fst]; rfl
  have π₂ : π.left ≫ (snd X.A Y.A).left = (snd X'.A Y'.A).left ≫ y := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hN : (cubeLB A.A ![fst X.A Y.A ≫ f₁, snd X.A Y.A ≫ f₂] A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hN' : (cubeLB B.A ![fst X.A Y.A ≫ g₁, snd X.A Y.A ≫ g₂] B.L).IsLB := DVR.linComb_isLB _ B.isLB _ _
  have hP : (cubeLB A'.A ![fst X'.A Y'.A ≫ f₁', snd X'.A Y'.A ≫ f₂'] A'.L).IsLB := DVR.linComb_isLB _ A'.isLB _ _
  have hP' : (cubeLB B'.A ![fst X'.A Y'.A ≫ g₁', snd X'.A Y'.A ≫ g₂'] B'.L).IsLB := DVR.linComb_isLB _ B'.isLB _ _
  have cA := cube_pull hA A.isLB A'.isLB wL (T' := X'.A ⊗ Y'.A) π.left (Over.w π)
    ![fst X'.A Y'.A ≫ f₁', snd X'.A Y'.A ≫ f₂'] ![fst X.A Y.A ≫ f₁, snd X.A Y.A ≫ f₂] fun i => by
      fin_cases i
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₁, reassoc_of% π₁]
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₂, reassoc_of% π₂]
  have cB := cube_pull hB B.isLB B'.isLB wM (T' := X'.A ⊗ Y'.A) π.left (Over.w π)
    ![fst X'.A Y'.A ≫ g₁', snd X'.A Y'.A ≫ g₂'] ![fst X.A Y.A ≫ g₁, snd X.A Y.A ≫ g₂] fun i => by
      fin_cases i
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₃, reassoc_of% π₁]
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₄, reassoc_of% π₂]
  refine ⟨fun H => W.1 (T.weil_pairing_eq_of_isomorphic_cube_pairings laws k X' Y' A' B' _ _ _ _ m₁ m₂ m₃ m₄ ?_), fun hR hβ H => ?_⟩
  · exact cA.trans hP (Geo.Tor.pull_isLB hN _) hP' (LBIso.trans (Geo.Tor.pull_isLB hN _) (Geo.Tor.pull_isLB hN' _) hP'
      (PowPrimitive.lbIso_linComb H _ _) cB.symm)
  · have H' := GlobalTheory.CM.lamEq_of_weilEq laws k X' Y' A' B' _ _ _ _ m₁ m₂ m₃ m₄ (W.2 H)
    have H'' := cA.symm.trans (Geo.Tor.pull_isLB hN _) hP (Geo.Tor.pull_isLB hN' _) (LBIso.trans hP hP' (Geo.Tor.pull_isLB hN' _) H' cB)
    let F := pullback.fst (X.A ⊗ Y.A).hom (spMap β)
    let p := pullback.snd (X.A ⊗ Y.A).hom (spMap β)
    have wF : F ≫ (X.A ⊗ Y.A).hom = p ≫ spMap β := pullback.condition
    let u : Over.mk p ⟶ X'.A := Over.homMk (hX.1.lift (F ≫ (fst X.A Y.A).left) p
      (by rw [Category.assoc, Over.w, wF])) (hX.1.lift_snd _ _ _)
    let v : Over.mk p ⟶ Y'.A := Over.homMk (hY.1.lift (F ≫ (snd X.A Y.A).left) p
      (by rw [Category.assoc, Over.w, wF])) (hY.1.lift_snd _ _ _)
    have hu : u.left ≫ x = F ≫ (fst X.A Y.A).left := hX.1.lift_fst _ _ _
    have hv : v.left ≫ y = F ≫ (snd X.A Y.A).left := hY.1.lift_fst _ _ _
    have hr : F = (lift u v).left ≫ π.left := by
      refine pullback.hom_ext (f := X.A.hom) (g := Y.A.hom) ?_ ?_
      · show F ≫ (fst X.A Y.A).left = (_ ≫ _) ≫ (fst X.A Y.A).left
        rw [Category.assoc, π₁, ← Category.assoc, ← Over.comp_left, lift_fst, hu]
      · show F ≫ (snd X.A Y.A).left = (_ ≫ _) ≫ (snd X.A Y.A).left
        rw [Category.assoc, π₂, ← Category.assoc, ← Over.comp_left, lift_snd, hv]
    refine T.lineBundleIso_descends_field_to_dedekindDomain R k β hβ (X.A ⊗ Y.A) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ X.isAb Y.isAb) _ F p
      (IsPullback.of_hasPullback _ _) _ _ hN hN' ?_
      (LBIso.chartPull (Geo.Tor.chartPullSame _ _ _ _ (lift u v).left fun _ => hr)
        (Geo.Tor.chartPullSame _ _ _ _ (lift u v).left fun _ => hr) H'')
    obtain ⟨t, ht⟩ := exists_gen_cube_one A.isLB (𝟙_ _)
    obtain ⟨t', ht'⟩ := exists_gen_cube_one B.isLB (𝟙_ _)
    exact (cube_zero A.isLB f₁ f₂).symm.trans (Geo.Tor.pull_isLB hN _) (DVR.linComb_isLB _ A.isLB _ _) (Geo.Tor.pull_isLB hN' _)
      (LBIso.trans (DVR.linComb_isLB _ A.isLB _ _) (DVR.linComb_isLB _ B.isLB _ _) (Geo.Tor.pull_isLB hN' _)
        (IsoDescent.lbIso_of_gens A.isLB B.isLB _ _ _ _ t ht t' ht') (cube_zero B.isLB g₁ g₂))

end GlobalTheory.PairingFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring : Out.Laws → ∀ (R : Type) [CommRing R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k),
  (LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β)) ∧ (IsDedekindDomain R → Function.Injective β → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β) → LamEq A.L f₁ f₂ B.L g₁ g₂) := by
  first | exact @GlobalTheory.PairingFibre.lamEq_weilEq_over_ring | exact GlobalTheory.PairingFibre.lamEq_weilEq_over_ring | (intros; apply GlobalTheory.PairingFibre.lamEq_weilEq_over_ring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.IsogSum

variable {S : Scheme.{0}}

theorem isMonHom_of_points {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (a b : T ⟶ G), (a * b) ≫ f = a ≫ f * b ≫ f) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · have h1 := h (𝟙_ _) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ _ ⟶ G) ≫ f = 1 := by simpa using h1
    simpa [Hom.one_def] using h2
  · simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp]
      using h (G ⊗ G) (fst G G) (snd G G)

theorem comp_prod {T G H : Over S} [GrpObj H] [IsCommMonObj H] {n : ℕ} (x : T ⟶ G)
    (a : Fin n → (G ⟶ H)) : x ≫ ∏ i, a i = ∏ i, x ≫ a i :=
  map_prod (MonoidHom.mk' (fun u : G ⟶ H => x ≫ u) fun _ _ => MonObj.comp_mul _ _ _) a Finset.univ

theorem exists_point {Q G' G H' H T : Over S} [GrpObj G'] [GrpObj G] [GrpObj H'] [GrpObj H] {p q : ℕ}
    (pG : Out.IsPowGrp G' G p) (pH : Out.IsPowGrp H' H q) (u : Q ⟶ G') (v : Q ⟶ H')
    [IsIso (lift u v)] (a : Fin p → (T ⟶ G)) (b : Fin q → (T ⟶ H)) :
    ∃ x : T ⟶ Q, (∀ i, x ≫ u ≫ pG.pr i = a i) ∧ ∀ i, x ≫ v ≫ pH.pr i = b i := by
  have hu : inv (lift u v) ≫ u = fst _ _ := by rw [IsIso.inv_comp_eq, lift_fst]
  have hv : inv (lift u v) ≫ v = snd _ _ := by rw [IsIso.inv_comp_eq, lift_snd]
  obtain ⟨c, hc⟩ : ∃ c : T ⟶ G', ∀ i, c ≫ pG.pr i = a i :=
    ⟨pG.lim.lift (Fan.mk T a), fun i => pG.lim.fac (Fan.mk T a) ⟨i⟩⟩
  obtain ⟨d, hd⟩ : ∃ d : T ⟶ H', ∀ i, d ≫ pH.pr i = b i :=
    ⟨pH.lim.lift (Fan.mk T b), fun i => pH.lim.fac (Fan.mk T b) ⟨i⟩⟩
  refine ⟨lift c d ≫ inv (lift u v), fun i => ?_, fun i => ?_⟩
  · rw [Category.assoc, reassoc_of% hu, lift_fst_assoc, hc]
  · rw [Category.assoc, reassoc_of% hv, lift_snd_assoc, hd]

end GlobalTheory.LamF.IsogSum

namespace GlobalTheory.LamF

theorem exists_inverse_isogeny_of_sum : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) (p q : ℕ) (φ : Fin p → (A.A ⟶ B.A)) (φ' : Fin q → (A'.A ⟶ B.A)), (∀ i, IsMonHom (φ i)) → (∀ i, IsMonHom (φ' i)) → B.g = p * A.g + q * A'.g → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ (x : Fin p → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A)) (x' : Fin q → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A'.A)), y = (List.ofFn fun i => x i ≫ φ i).prod * (List.ofFn fun i => x' i ≫ φ' i).prod) → ∃ (N : ℕ) (ψ : Fin p → (B.A ⟶ A.A)) (ψ' : Fin q → (B.A ⟶ A'.A)), 0 < N ∧ (∀ (Tb : Over (Sp (𝓞 K))) (x : Tb ⟶ B.A), padd B.A (psumPt fun i => x ≫ ψ i ≫ φ i) (psumPt fun i => x ≫ ψ' i ≫ φ' i) = pnsmulPt N x) ∧ ∀ (Tb : Over (Sp (𝓞 K))) (a : Fin p → (Tb ⟶ A.A)) (a' : Fin q → (Tb ⟶ A'.A)), (∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ i = pnsmulPt N (a i)) ∧ ∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ' i = pnsmulPt N (a' i) := by
  intro hU hL hE K _ _ σ A A' B p q φ φ' hφ hφ' hg hs
  obtain ⟨P, pP, hP⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A p
  obtain ⟨P', pP', hP'⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A' q
  obtain ⟨Q, u, v, hu, hv, huv, hQ⟩ := GlobalTheory.T.exists_prod_polAV_add_g hL (𝓞 K) P P'
  haveI := pP.hom
  haveI := pP'.hom
  let Φ : Q.A ⟶ B.A := (∏ i, u ≫ pP.pr i ≫ φ i) * ∏ i, v ≫ pP'.pr i ≫ φ' i
  have hΦ : ∀ {T : Over (Sp (𝓞 K))} (x : T ⟶ Q.A),
      x ≫ Φ = (∏ i, (x ≫ u ≫ pP.pr i) ≫ φ i) * ∏ i, (x ≫ v ≫ pP'.pr i) ≫ φ' i := by
    intro T x
    simp only [Φ, MonObj.comp_mul, IsogSum.comp_prod, Category.assoc]
  have hm : IsMonHom Φ := IsogSum.isMonHom_of_points Φ fun T a b => by
    simp only [hΦ, MonObj.mul_comp, Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _
  obtain ⟨N, ψ, hN, hψ, h1, h2⟩ := GlobalTheory.T.exists_inverse_isogeny_of_surjective_points hU hL hE K σ Q B Φ (by rw [hQ, hP, hP', hg]) hm fun y => by
    obtain ⟨a, b, hab⟩ := hs y
    obtain ⟨x, hx, hx'⟩ := IsogSum.exists_point pP pP' u v a b
    refine ⟨x, ?_⟩
    rw [hΦ, hab, List.prod_ofFn, List.prod_ofFn]
    simp only [hx, hx']
  have padd_eq_mul {G T : Over (Sp (𝓞 K))} [GrpObj G] (a b : T ⟶ G) :
      padd G a b = a * b := rfl
  have pnsmulPt_eq_pow {G T : Over (Sp (𝓞 K))} [GrpObj G] (n : ℕ) (a : T ⟶ G) :
      pnsmulPt n a = a ^ n := by
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  have psumPt_eq_prod {G T : Over (Sp (𝓞 K))} [GrpObj G] {n : ℕ} (f : Fin n → (T ⟶ G)) :
      psumPt f = (List.ofFn f).prod := by
    rw [List.prod_eq_foldr]
    rfl
  refine ⟨N, fun i => ψ ≫ u ≫ pP.pr i, fun i => ψ ≫ v ≫ pP'.pr i, hN, fun T x => ?_, fun T a b => ?_⟩
  · rw [padd_eq_mul, pnsmulPt_eq_pow, psumPt_eq_prod, psumPt_eq_prod, List.prod_ofFn, List.prod_ofFn]
    have := hΦ (x ≫ ψ)
    rw [Category.assoc, h2, MonObj.comp_pow, Category.comp_id] at this
    simpa only [Category.assoc] using this.symm
  · obtain ⟨x, hx, hx'⟩ := IsogSum.exists_point pP pP' u v a b
    have key : padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => b k ≫ φ' k) ≫ ψ = x ^ N := by
      have : x ≫ Φ = padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => b k ≫ φ' k) := by
        rw [padd_eq_mul, psumPt_eq_prod, psumPt_eq_prod, List.prod_ofFn, List.prod_ofFn, hΦ]
        simp only [hx, hx']
      rw [← this, Category.assoc, h1, MonObj.comp_pow, Category.comp_id]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [← Category.assoc, key, MonObj.pow_comp, hx, pnsmulPt_eq_pow]
    · rw [← Category.assoc, key, MonObj.pow_comp, hx', pnsmulPt_eq_pow]

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHomsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_isogeny_sum_of_cm_homs : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) (p q : ℕ) (φ : Fin p → (A.A ⟶ B.A)) (φ' : Fin q → (A'.A ⟶ B.A)), (∀ i, IsMonHom (φ i)) → (∀ i, IsMonHom (φ' i)) → B.g = p * A.g + q * A'.g → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ (x : Fin p → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A)) (x' : Fin q → (Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A'.A)), y = (List.ofFn fun i => x i ≫ φ i).prod * (List.ofFn fun i => x' i ≫ φ' i).prod) → ∃ (N : ℕ) (ψ : Fin p → (B.A ⟶ A.A)) (ψ' : Fin q → (B.A ⟶ A'.A)), 0 < N ∧ (∀ (Tb : Over (Sp (𝓞 K))) (x : Tb ⟶ B.A), padd B.A (psumPt fun i => x ≫ ψ i ≫ φ i) (psumPt fun i => x ≫ ψ' i ≫ φ' i) = pnsmulPt N x) ∧ ∀ (Tb : Over (Sp (𝓞 K))) (a : Fin p → (Tb ⟶ A.A)) (a' : Fin q → (Tb ⟶ A'.A)), (∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ i = pnsmulPt N (a i)) ∧ ∀ i, padd B.A (psumPt fun k => a k ≫ φ k) (psumPt fun k => a' k ≫ φ' k) ≫ ψ' i = pnsmulPt N (a' i) := by
  first | exact @GlobalTheory.LamF.exists_inverse_isogeny_of_sum | exact GlobalTheory.LamF.exists_inverse_isogeny_of_sum | (intros; apply GlobalTheory.LamF.exists_inverse_isogeny_of_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.NormHom

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A C : Over S} {A' C' : Over S'}
  [GrpObj A] [GrpObj C] [GrpObj A'] [GrpObj C'] {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_comp (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} {p' : A' ⟶ C'}
    (e : p'.left ≫ ψ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h' T (x ≫ p') = pushHom h T x ≫ p :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, e, Category.assoc])

theorem exists_monHom_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) (p : A ⟶ C) [IsMonHom p] :
    ∃ p' : A' ⟶ C', IsMonHom p' ∧ p'.left ≫ ψ = φ ≫ p.left := by
  obtain ⟨p', e⟩ : ∃ p' : A' ⟶ C', p'.left ≫ ψ = φ ≫ p.left :=
    ⟨Over.homMk (h'.1.lift (φ ≫ p.left) A'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h'.1.lift_snd _ _ _),
      h'.1.lift_fst _ _ _⟩
  refine ⟨p', ?_, e⟩
  have h1 : (1 : 𝟙_ (Over S') ⟶ A') ≫ p' = 1 := by
    apply push_inj h'
    rw [push_comp h h' e, map_one, map_one, MonObj.one_comp]
  have h2 : (fst A' A' * snd A' A') ≫ p' = (fst A' A' ≫ p') * (snd A' A' ≫ p') := by
    apply push_inj h'
    rw [push_comp h h' e, map_mul, map_mul, MonObj.mul_comp, push_comp h h' e, push_comp h h' e]
  constructor
  · simpa [Hom.one_def] using h1
  · rw [Hom.mul_def, Hom.mul_def] at h2
    have e1 : lift (fst A' A' ≫ p') (snd A' A' ≫ p') = p' ⊗ₘ p' := by ext <;> simp
    simpa [e1] using h2
end

theorem isVecOver_comp {R R' : Type} [CommRing R] [CommRing R'] {s : R →+* R'} {A C : Over (Sp R)}
    {A' C' : Over (Sp R')} {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'}
    (hv : IsVecOver s φ v v') {p : A ⟶ C} {p' : A' ⟶ C'} (e : p'.left ≫ ψ = φ ≫ p.left) :
    IsVecOver s ψ (v ≫ p) (v' ≫ p') := by
  unfold IsVecOver at hv ⊢
  rw [Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, hv, Category.assoc]

theorem lieNormSq_comp : ThetaUnifAV → Out.Laws → ∀ (R : Type) [CommRing R] (P P' : Out.PolAV (Sp R)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (v : epsR R ⟶ P.A) (a : R) (s : R →+* ℂ) (r r' : ℝ), IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → IsTangent v → IsLieComb ![a] ![v] (v ≫ g) → IsLieNormSq P v s r → IsLieNormSq P' (v ≫ f) s r' → r' = (s a).re * r := by
  rintro hU hL R _ P P' f g v a s r r' hf hg hlam hv hc ⟨Q, φ, v₁, u, Hm, χ, w, hφ, hv₁, hA, hw, rfl⟩
    ⟨Q', φ', v₁', u', Hm', χ', w', hφ', hv₁', hA', hw', rfl⟩
  obtain ⟨f₁, hf₁, ef⟩ := exists_monHom_lift hφ.2.1 hφ'.2.1 f
  obtain ⟨g₁, hg₁, eg⟩ := exists_monHom_lift hφ.2.1 hφ.2.1 g
  obtain ⟨-, -, -, -, t₁, t₂, -⟩ := GlobalTheory.T.appellHumbert_unif_tangent_weilPairing hU Q Q.g u Hm χ hA
  obtain ⟨-, -, -, -, t₁', t₂', -⟩ := GlobalTheory.T.appellHumbert_unif_tangent_weilPairing hU Q' Q'.g u' Hm' χ' hA'
  obtain ⟨F, hF, -, hFd, -⟩ :=
    GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' f₁ hf₁
  obtain ⟨G, hG, -, hGd, -⟩ :=
    GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g u u t₁ t₂ g₁ hg₁
  have ht : IsTangent v₁ := hv₁.isTangent hφ.2.1 hv
  have hlam₁ : LamEq Q'.L f₁ f₁ Q.L g₁ (𝟙 Q.A) :=
    GlobalTheory.T.isCubeLBPairingIso_baseChange _ _ (spMap s) P.A P.A P'.A P.A Q.A Q.A Q'.A Q.A φ φ φ' φ hφ.2.1.1.w hφ.2.1.1.w hφ'.2.1 hφ.2.1
      P'.L P.L Q'.L Q.L P'.isLB P.isLB Q'.isLB Q.isLB hφ'.2.2 hφ.2.2 f f g (𝟙 _) f₁ f₁ g₁ (𝟙 _) ef ef eg
      (by simp) hlam
  have hweil := GlobalTheory.T.weil_pairing_eq_of_isomorphic_cube_pairings hL ℂ Q Q Q' Q f₁ f₁ g₁ (𝟙 _) hf₁ hf₁ hg₁ inferInstance hlam₁
  have hherm := (GlobalTheory.T.weilEq_iff_hermForm_eq_complex hU hL Q Q Q' Q u u u' u Hm' Hm χ' χ hA' hA f₁ f₁ g₁ (𝟙 _) F F G LinearMap.id
    hF hF hG (fun z => by simp)).1 hweil w w
  have e₁ : v₁' = v₁ ≫ f₁ :=
    (existsUnique_isVecOver hφ'.2.1.1 (v ≫ f)).unique hv₁' (isVecOver_comp hv₁ ef)
  subst e₁
  have e₂ : w' = F w := (t₁' _ (hFd w v₁ ht hw).1).unique hw' (hFd w v₁ ht hw).2
  have hc₁ := (GlobalTheory.lieComb_baseChange R ℂ s P.A Q.A φ hφ.2.1 1 ![v] (v ≫ g) ![a] ![v₁] (v₁ ≫ g₁)
    (fun j => by fin_cases j; exact hv₁) hc).1 (isVecOver_comp hv₁ eg)
  have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb Q.A Q.L Q.g 1 u ![w] ![v₁] _ _
    (fun j => by fin_cases j; exact ht) (fun j => by fin_cases j; exact hw) hc₁
  have e₃ : G w = s a • w := by
    have := (t₁ _ (hGd w v₁ ht hw).1).unique (hGd w v₁ ht hw).2 hd
    simpa using this
  have him : (hermForm Hm w w).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    have hH : ∀ i j, (starRingEnd ℂ) (Hm i j) = Hm j i := fun i j => hA.1.apply j i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj, hH]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e₂, hherm, e₃, LinearMap.id_apply]
  have e₄ : hermForm Hm (s a • w) w = s a * hermForm Hm w w := by
    rw [hermForm, hermForm, smul_dotProduct, smul_eq_mul]
  rw [e₄, Complex.mul_re, him]
  ring

end GlobalTheory.NormHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebraSquaredLength_comp_pairing_hom : ThetaUnifAV → Out.Laws → ∀ (R : Type) [CommRing R] (P P' : Out.PolAV (Sp R)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (v : epsR R ⟶ P.A) (a : R) (s : R →+* ℂ) (r r' : ℝ), IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → IsTangent v → IsLieComb ![a] ![v] (v ≫ g) → IsLieNormSq P v s r → IsLieNormSq P' (v ≫ f) s r' → r' = (s a).re * r := by
  first | exact @GlobalTheory.NormHom.lieNormSq_comp | exact GlobalTheory.NormHom.lieNormSq_comp | (intros; apply GlobalTheory.NormHom.lieNormSq_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsModelAtIntegralIffMemLieLat
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeEqValuationRingIffIsLocalization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem range_eq_valuationRing_iff_isLocalization :
    ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) (R : Type) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K] [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) R K], (∀ y : K, y ∈ Set.range (algebraMap R K) ↔ p.valuation K y ≤ 1) ↔ IsLocalization p.asIdeal.primeCompl R := by
  intro K _ _ p R _ _ _ _ _ _
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have htow : ∀ a : 𝓞 K, algebraMap R K (algebraMap (𝓞 K) R a) = algebraMap (𝓞 K) K a :=
    fun a => (IsScalarTower.algebraMap_apply (𝓞 K) R K a).symm
  have hone : ∀ s : p.asIdeal.primeCompl, p.valuation K (algebraMap (𝓞 K) K s) = 1 :=
    fun s => (p.valuation_eq_one_iff_notMem (K := K)).2 s.2
  have hne : ∀ s : p.asIdeal.primeCompl, algebraMap (𝓞 K) K s ≠ 0 := by
    intro s h
    have := hone s
    rw [h, map_zero] at this
    exact zero_ne_one this
  constructor
  · intro h
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · intro s
      obtain ⟨r, hr⟩ := (h (algebraMap (𝓞 K) K s)⁻¹).2 (by rw [map_inv₀, hone s, inv_one])
      refine IsUnit.of_mul_eq_one r (hinj ?_)
      rw [map_mul, htow, hr, map_one, mul_inv_cancel₀ (hne s)]
    · intro z
      obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer (algebraMap R K z)
        ((h _).1 ⟨z, rfl⟩)
      refine ⟨(n, d), hinj ?_⟩
      rw [map_mul, htow, htow]
      exact hnd
    · intro x y hxy
      refine ⟨1, ?_⟩
      have h2 : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K y := by
        rw [← htow, ← htow, hxy]
      rw [IsFractionRing.injective (𝓞 K) K h2]
  · intro h y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj p.asIdeal.primeCompl z
      have h2 := congrArg (fun t => p.valuation K (algebraMap R K t)) hnd
      simp only [map_mul, htow, hone] at h2
      rw [(_root_.mul_one _).symm.trans h2]
      exact p.valuation_le_one n
    · intro hy
      obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer y hy
      refine ⟨IsLocalization.mk' R n d, ?_⟩
      apply mul_right_cancel₀ (hne d)
      rw [hnd, ← htow, ← htow, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.LamF
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isModelAt_integral_iff_mem_lieLat : ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), IsModelAt A x φ p M → ∀ c : Fin x.P.g → K, (∀ m, p.valuation K (Matrix.vecMul c M⁻¹ m) ≤ 1) ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat := by
  intro K _ _ A x φ hf p M hM c
  obtain ⟨R, _, _, _, _, _, ρ, xR, φR, hg, hρ, hval, hfib, hdet, hw⟩ := hM
  letI : Algebra (𝓞 K) R := ρ.toAlgebra
  haveI : IsScalarTower (𝓞 K) R K := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI : IsLocalization p.asIdeal.primeCompl R := (range_eq_valuationRing_iff_isLocalization K p R).1 hval
  have hG : IsGrpPullback xR.P.A A.A (spMap (algebraMap (𝓞 K) R)) φR := hfib.1
  have n : IsGrpPullback x.P.A A.A (spMap (algebraMap R K) ≫ spMap (algebraMap (𝓞 K) R)) φ :=
    hf.2.1.congr (by rw [spMap_comp_spMap]; exact congrArg spMap hρ.symm) rfl
  have w : φ ≫ A.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap (algebraMap (𝓞 K) R) :=
    n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := hG.1.lift_fst _ _ w
  have e₂ := hG.1.lift_snd _ _ w
  generalize hG.1.lift _ _ w = ψ at e₁ e₂
  have hψ : IsGrpPullback x.P.A xR.P.A (spMap (algebraMap R K)) ψ := hG.cancel (e₁ ▸ n) e₂
  choose wK hwK hwK' using hw
  have hb : IsLieBasis (fun k : Fin x.P.g => xR.v (k.cast hg.symm)) := by
    have key : ∀ (m : ℕ) (h : xR.P.g = m), IsLieBasis (fun k : Fin m => xR.v (k.cast h.symm)) := by
      intro m h
      subst h
      exact xR.basis
    exact key _ hg
  have hov : ∀ k, IsVecOver (algebraMap R K) ψ (xR.v (k.cast hg.symm)) (wK k) := by
    intro k
    refine hG.1.hom_ext ?_ ?_
    · rw [Category.assoc, e₁, hwK' k, Category.assoc, points_sums_eq_products.2]
    · rw [Category.assoc, Category.assoc, e₂, Over.w (xR.v _), ← Category.assoc, Over.w (wK k)]
      exact (PolFibre.spMap_dual_hom _).symm
  obtain ⟨h1, h2⟩ := GlobalTheory.T.lieLattice_localization_modelLieAlgebra K A (GenFib.mk x.P φ hf x.v x.basis) R p.asIdeal.primeCompl xR.P.A φR ψ _ wK M
    hG hψ e₁ hb fun i => ⟨hov i, hwK i⟩
  have hU : IsUnit M.det := hdet.isUnit
  constructor
  · intro hc
    choose a ha using fun m => (hval _).2 (hc m)
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite p.asIdeal.primeCompl a
    choose b hb' using ht
    choose s hs hs' using h1
    have hcM : c = ∑ i, Matrix.vecMul c M⁻¹ i • M i := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hU, Matrix.vecMul_one]
    refine ⟨(∏ i, s i) * t, Submonoid.mul_mem p.asIdeal.primeCompl (Submonoid.prod_mem _ fun i _ => hs i) t.2, ?_⟩
    rw [hcM, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : (t : 𝓞 K) • Matrix.vecMul c M⁻¹ i = algebraMap (𝓞 K) K (b i) := by
      rw [← ha, IsScalarTower.algebraMap_apply (𝓞 K) R K, hb', Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
    rw [mul_smul, ← smul_assoc (t : 𝓞 K), e, algebraMap_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul,
      smul_comm (s i)]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hs' i))
  · rintro ⟨s, hs, hc⟩ m
    obtain ⟨a, ha⟩ := h2 _ hc
    have e : s • Matrix.vecMul c M⁻¹ = fun i => algebraMap R K (a i) := by
      rw [← Matrix.smul_vecMul]
      erw [ha]
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hU, Matrix.vecMul_one]
    have e' : algebraMap (𝓞 K) K s * Matrix.vecMul c M⁻¹ m = algebraMap R K (a m) := by
      rw [← Algebra.smul_def]
      exact congrFun e m
    have h3 := (hval _).1 ⟨a m, e'.symm⟩
    rwa [map_mul, (p.valuation_eq_one_iff_notMem (K := K)).2 hs, _root_.one_mul] at h3

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open Formalism.L2.Pj hiding combT combT_eig combT_tan comp_prodT dualMap_comp_alg dualMap_comp_epsMul epsMul_comp_alg grpPull_prod isCombAtG_iff isComb_iff isEigV_kapI_iff isTan_kapI kapI kapI_kap_assoc kap_kapI_assoc ovT reframe_basis smT smT_left smT_zero_kap spMap_comp' spMap_frac_cancel
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LamT.LocLie

open GlobalTheory.IntRebase
open Formalism.L2.PjFree (spMap_comp' epsMul_comp_alg)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem comb_eq {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) {a : Fin m → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) :
    (combT x (fun j => IntRebase.ovT (t := Xo.univ.t) (hv j)) a).left = w :=
  (isCombAtG_iff Xo.univ.t x (fun j => IntRebase.ovT (t := Xo.univ.t) (hv j)) _ _).1 h

theorem lieInt_change (T : CDVR) (io : c.F →+* T.Fr) {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)}
    {x : Sp T.Fr ⟶ Xo.X} (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left))
    (hu : ∀ τ j, IsTanAt x (u τ j)) (h : LieInt T io m1 m2 u)
    (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (hk : ∀ τ, IsUnit (k τ).det) :
    LieInt T io m1 m2 (fun τ i => (combT x (fun j => IntRebase.ovT (t := Xo.univ.t) (hu τ j))
      (fun j => algebraMap T.V T.Fr (k τ j i))).left) := by
  obtain ⟨ub, htan, heig, hbas, hlift⟩ := h
  let Ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (tEpsG (𝟙 (Sp T.V)) ⟶ G.G) := fun τ j => kap ≫ ub τ j
  have hUb0 : ∀ τ j, smT (𝟙 (Sp T.V)) 0 (Ub τ j) = 1 := fun τ j => smT_zero_kap _ (htan τ j)
  have hUbE : ∀ τ j (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) →
      Ub τ j ≫ G.act.act a = smT (𝟙 (Sp T.V)) z (Ub τ j) := fun τ j =>
    (isEigV_kapI_iff io G τ _).1 (by rw [kapI_kap_assoc]; exact heig τ j)
  refine ⟨fun τ i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i), ?_, ?_, ?_, ?_⟩
  · intro τ i
    exact isTan_kapI _ (combT_tan _ _ (hUb0 τ) _)
  · intro τ i
    refine (isEigV_kapI_iff io G τ _).2 fun a z hz => ?_
    have := G.act.hom a
    exact combT_eig _ _ _ _ (fun j => hUbE τ j a z hz) _
  · intro τ w hw he
    have h1 : ∃! a : Fin (Dw.mult τ) → T.V, kap ≫ w = combT (𝟙 (Sp T.V)) (Ub τ) a := by
      obtain ⟨a, ha, hu⟩ := hbas τ w hw he
      refine ⟨a, (isComb_iff _ _ _).1 (by rw [kapI_kap_assoc]; exact ha), fun b hb => hu b ?_⟩
      have h2 := (isComb_iff (ub τ) b (kap ≫ w)).2 hb
      rw [kapI_kap_assoc] at h2
      exact h2
    obtain ⟨a, ha, hu⟩ := reframe_basis _ (Ub τ) (hUb0 τ) (k τ) (hk τ) _ h1
    have e : (fun i => kap ≫ (kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i))) =
        fun i => combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i) := funext fun i => kap_kapI_assoc _
    refine ⟨a, ?_, fun b hb => hu b ?_⟩
    · have h2 := (isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) a (kap ≫ w)).2
        (by rw [e]; exact ha)
      rw [kapI_kap_assoc] at h2
      exact h2
    · have h2 := (isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) b (kap ≫ w)).1
        (by rw [kapI_kap_assoc]; exact hb)
      rw [e] at h2
      exact h2
  · intro τ i
    choose u' hu1 hu2 using hlift τ
    have hδ : spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)) ≫
        spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
        spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
      rw [spMap_comp', spMap_comp']
      show spMap ((Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [dualMap_comp_alg]
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2 j, Category.assoc, Over.w (ub τ j)]
      exact hδ
    let T' : Over (Sp T.Fr) := Over.mk (spMap (algebraMap T.Fr (DualNumber T.Fr)))
    let cf : Fin (Dw.mult τ) → T.Fr := fun j => algebraMap T.V T.Fr (k τ j i)
    let Y : Fin (Dw.mult τ) → (T' ⟶ t'.G) := fun j => Over.homMk (spMap (epsMul (cf j)) ≫ u' j) (by
      show (spMap (epsMul (cf j)) ≫ u' j) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr))
      rw [Category.assoc, hov, spMap_comp', epsMul_comp_alg])
    refine ⟨(∏ j, Y j).left, ?_, ?_⟩
    · have hA := grpPull_prod m1.cart T' Finset.univ Y
        (fun j => smT x (cf j) (IntRebase.ovT (t := Xo.univ.t) (hu τ j))) (fun j => by
          show spMap (epsMul (cf j)) ≫ u τ j = (spMap (epsMul (cf j)) ≫ u' j) ≫ m1.φ
          rw [Category.assoc, hu1])
      exact hA.symm
    · let δ : Over.mk (T'.hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ epsOver T.V T.V :=
        Over.homMk (spMap (Formalism.L2.Pj.dualMap (algebraMap T.V T.Fr))) hδ
      have hB := grpPull_prod m2.cart T' Finset.univ Y
        (fun j => δ ≫ kapI ≫ smT (𝟙 (Sp T.V)) (k τ j i) (Ub τ j)) (fun j => by
          simp only [Over.comp_left, δ, kapI, IntRebase.kap, Ub, smT_left, Over.homMk_left, Category.id_comp, Y,
            Category.assoc]
          rw [hu2 j, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul])
      rw [← hB, ← comp_prodT, ← comp_prodT]
      rfl

end GlobalTheory.LamT.LocLie


open GlobalTheory.LamT.LocLie in
theorem GlobalTheory.LamT.lieInt_exists_and_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → (∃ g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr), (∀ b, IsUnit (g b).det) ∧ ∀ (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg g a y y' → LieInt T io m1 m2 y'.u) ∧ (LieInt T io m1 m2 y.u → ∀ (X : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.V)) (a : T.Fr) (y' : FrPt Xo c T.Fr), (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T.V T.Fr)) a y y' → LieInt T io m1 m2 y'.u) := by
  intro E _ _ _ H Dw l Xo c T io G t' x m1 m2
  let _ := io.toAlgebra
  intro y hy
  subst hy
  refine ⟨?_, fun h X a y' hX hch => ?_⟩
  · obtain ⟨ub, u, hint, ht, he, hb, hcf⟩ := lieFree Xo c T io G t' y.x m1 m2 y.x_over y.u y.tan y.eig y.basis
    choose cf hd hz hc using hcf
    refine ⟨fun b => Matrix.of (cf b), fun b => ?_, fun a y' hch => ?_⟩
    · show IsUnit (Matrix.of (cf b)).det
      rw [Matrix.det_of_isLowerTriangular (Matrix.of (cf b)) (fun i j hij => hz b i j hij)]
      exact IsUnit.prod_univ_iff.2 (hd b)
    · have e : y'.u = u := funext fun τ => funext fun i =>
        (comb_eq (y.tan τ) (hch.2.1 τ i)).symm.trans (comb_eq (y.tan τ) (hc τ i))
      rw [e]
      exact ⟨ub, hint⟩
  · have h2 := lieInt_change T io m1 m2 y.u y.tan h (fun τ => (X τ).transpose)
      (fun τ => by rw [Matrix.det_transpose]; exact hX τ)
    have e : y'.u = _ := funext fun τ => funext fun i => (comb_eq (y.tan τ) (hch.2.1 τ i)).symm
    rw [e]
    exact h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIntegralEigenbasisOfFrameAtLocalModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open Formalism.L2.Pj hiding combT combT_eig combT_tan comp_prodT dualMap_comp_alg dualMap_comp_epsMul epsMul_comp_alg grpPull_prod isCombAtG_iff isComb_iff isEigV_kapI_iff isTan_kapI kapI kapI_kap_assoc kap_kapI_assoc ovT reframe_basis smT smT_left smT_zero_kap spMap_comp' spMap_frac_cancel
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, y.x = x → (∃ g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr), (∀ b, IsUnit (g b).det) ∧ ∀ (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg g a y y' → LieInt T io m1 m2 y'.u) ∧ (LieInt T io m1 m2 y.u → ∀ (X : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.V)) (a : T.Fr) (y' : FrPt Xo c T.Fr), (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T.V T.Fr)) a y y' → LieInt T io m1 m2 y'.u) := by
  first | exact @GlobalTheory.LamT.lieInt_exists_and_change | exact GlobalTheory.LamT.lieInt_exists_and_change | (intros; apply GlobalTheory.LamT.lieInt_exists_and_change <;> assumption)
end
end
