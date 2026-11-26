module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerFibreConjugateEvaluationIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoSharpTorsionGivesFactorIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoEqCoordinatewisePower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoGrpPullbackIdentityTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoGrpPullbackIdentityTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreTransport

theorem exists_compare {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ G₂ : Over S'} [GrpObj G₁] [GrpObj G₂]
    {f₁ f₂ : S' ⟶ S} {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f₁ φ₁)
    (h₂ : IsGrpPullback G₂ G f₂ φ₂) (hf : f₁ = f₂) :
    ∃ e : G₁.left ⟶ G₂.left, IsGrpPullback G₁ G₂ (𝟙 S') e ∧ e ≫ φ₂ = φ₁ := by
  subst hf
  refine ⟨h₂.1.lift φ₁ G₁.hom h₁.1.w, IsGrpPullback.cancel h₂ ?_ ?_, h₂.1.lift_fst _ _ _⟩
  · rw [h₂.1.lift_fst, Category.id_comp]; exact h₁
  · rw [h₂.1.lift_snd]; simp

theorem isGrpPullback_of_isIso {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] (e : G₁ ⟶ G₂)
    [IsMonHom e] [IsIso e] : IsGrpPullback G₁ G₂ (𝟙 S) e.left := by
  haveI : IsIso e.left := inferInstanceAs (IsIso ((Over.forget S).map e))
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let k : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = k ≫ x ≫ e := Over.OverMorphism.ext (by simp [k, hx])
  have ey : y₀ = k ≫ y ≫ e := Over.OverMorphism.ext (by simp [k, hy])
  rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [k]

theorem transport : ∀ (V V₁ K : Type) [CommRing V] [CommRing V₁] [Field K] (B : Over (Sp V)) [GrpObj B] (ρ : V →+* V₁) (ev : V₁ →+* K) (σ : K ≃+* K) (f₁ : (Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B) ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj ((Over.pullback (spMap ρ)).obj B)), IsMonHom f₁ → IsIso f₁ → ∃ f : ((Over.pullback (spMap (ev.comp ρ))).obj B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B) (𝟙 _) f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B)).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj B).left), y ≫ pullback.fst B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) ≫ pullback.fst B.hom (spMap ρ) → y ≫ pullback.snd B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) → x ≫ f₁.left ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap (σ.toRingHom.comp ev)) ≫ pullback.fst B.hom (spMap ρ) = y ≫ f ≫ pullback.fst B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  intro V V₁ K _ _ _ B _ ρ ev σ f₁ hm hi
  have sp : ∀ t : V₁ →+* K, spMap (t.comp ρ) = spMap t ≫ spMap ρ := fun t => by
    simp only [spMap, ← Spec.map_comp]; rfl
  have two : ∀ t : V₁ →+* K, IsGrpPullback ((Over.pullback (spMap t)).obj ((Over.pullback (spMap ρ)).obj B)) B
      (spMap t ≫ spMap ρ) (pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap t) ≫ pullback.fst B.hom (spMap ρ)) :=
    fun t => (isGrpPullback_pullback _ (spMap t)).comp (isGrpPullback_pullback B (spMap ρ))
  obtain ⟨e₀, h₀, w₀⟩ := exists_compare (isGrpPullback_pullback B (spMap (ev.comp ρ))) (two ev) (sp ev)
  obtain ⟨e₁, h₁, w₁⟩ := exists_compare (two (σ.toRingHom.comp ev))
    (isGrpPullback_pullback B (spMap (σ.toRingHom.comp (ev.comp ρ)))) (sp (σ.toRingHom.comp ev)).symm
  refine ⟨e₀ ≫ f₁.left ≫ e₁, ?_, fun T x y hy₁ hy₂ => ?_⟩
  · have := h₀.comp ((isGrpPullback_of_isIso f₁).comp h₁)
    rwa [Category.id_comp, Category.id_comp] at this
  · have hx : x = y ≫ e₀ := by
      refine (two ev).1.hom_ext ?_ ?_
      · rw [Category.assoc, w₀]; exact hy₁.symm
      · rw [Category.assoc, h₀.1.w, Category.comp_id]; exact hy₂.symm
    rw [hx, Category.assoc, Category.assoc, Category.assoc, w₁]

end GlobalTheory.FibreTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoGrpPullbackIdentityTransportStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_iso_grpPullback_identity_transport : ∀ (V V₁ K : Type) [CommRing V] [CommRing V₁] [Field K] (B : Over (Sp V)) [GrpObj B] (ρ : V →+* V₁) (ev : V₁ →+* K) (σ : K ≃+* K) (f₁ : (Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B) ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj ((Over.pullback (spMap ρ)).obj B)), IsMonHom f₁ → IsIso f₁ → ∃ f : ((Over.pullback (spMap (ev.comp ρ))).obj B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj B) (𝟙 _) f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj ((Over.pullback (spMap ρ)).obj B)).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj B).left), y ≫ pullback.fst B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) ≫ pullback.fst B.hom (spMap ρ) → y ≫ pullback.snd B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd ((Over.pullback (spMap ρ)).obj B).hom (spMap ev) → x ≫ f₁.left ≫ pullback.fst ((Over.pullback (spMap ρ)).obj B).hom (spMap (σ.toRingHom.comp ev)) ≫ pullback.fst B.hom (spMap ρ) = y ≫ f ≫ pullback.fst B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  first | exact @GlobalTheory.FibreTransport.transport | exact GlobalTheory.FibreTransport.transport | (intros; apply GlobalTheory.FibreTransport.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeEighthPowerProductMonHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeEighthPowerProductMonHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem baseChange_eighthPower_product_monHom : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (G H : Over S) [GrpObj G] [GrpObj H] (pr : Fin 8 → (G ⟶ H)), (∀ a, IsMonHom (pr a)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ pr a = y a) → (∀ a, IsMonHom ((Over.pullback t).map (pr a))) ∧ ∀ (T : Over S') (y : Fin 8 → (T ⟶ (Over.pullback t).obj H)), ∃! x : T ⟶ (Over.pullback t).obj G, ∀ a, x ≫ (Over.pullback t).map (pr a) = y a := by
  intro S S' t G H _ _ pr hmon hlim
  refine ⟨fun a => by haveI := hmon a; infer_instance, ?_⟩
  let c : Fan (fun _ : Fin 8 => H) := Fan.mk G pr
  have hc : IsLimit c := by
    refine Fan.IsLimit.mk c (fun s => (hlim s.pt s.proj).choose) (fun s j => ?_) (fun s m hm => ?_)
    · exact (hlim s.pt s.proj).choose_spec.1 j
    · exact (hlim s.pt s.proj).choose_spec.2 m hm
  intro T y
  let s : Fan (fun _ : Fin 8 => (Over.pullback t).obj H) := Fan.mk T y
  have hs : IsLimit (Fan.mk ((Over.pullback t).obj G) (fun a => (Over.pullback t).map (pr a))) :=
    isLimitFanMkObjOfIsLimit (Over.pullback t) (fun _ : Fin 8 => H) pr hc
  refine ⟨hs.lift s, fun a => hs.fac s ⟨a⟩, fun x hx => ?_⟩
  exact hs.uniq s x (by rintro ⟨a⟩; exact hx a)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeEighthPowerProductMonHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_pullback_pr_and_unique_lift_fin_eight : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (G H : Over S) [GrpObj G] [GrpObj H] (pr : Fin 8 → (G ⟶ H)), (∀ a, IsMonHom (pr a)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ pr a = y a) → (∀ a, IsMonHom ((Over.pullback t).map (pr a))) ∧ ∀ (T : Over S') (y : Fin 8 → (T ⟶ (Over.pullback t).obj H)), ∃! x : T ⟶ (Over.pullback t).obj G, ∀ a, x ≫ (Over.pullback t).map (pr a) = y a := by
  first | exact @GlobalTheory.baseChange_eighthPower_product_monHom | exact GlobalTheory.baseChange_eighthPower_product_monHom | (intros; apply GlobalTheory.baseChange_eighthPower_product_monHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerIsoDiagonalOfLPowerTorsionAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerIsoDiagonalOfLPowerTorsionAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerDiagonal

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

theorem isMonHom_of_points {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    (h1 : ∀ T : C, (1 : T ⟶ X) ≫ f = 1)
    (hm : ∀ (T : C) (x y : T ⟶ X), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · simpa only [MonObj.one_eq_one] using h1 (𝟙_ C)
  · simpa only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd] using
      hm (X ⊗ X) (fst X X) (snd X X)

theorem exists_sections {G H : C} [MonObj G] [MonObj H] {n : Type} [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a) :
    ∃ j : n → (H ⟶ G), (∀ b, IsMonHom (j b)) ∧ (∀ b, j b ≫ p b = 𝟙 H) ∧
      ∀ b c, c ≠ b → j b ≫ p c = 1 := by
  classical
  have hex := fun b => (hu H (fun c => if c = b then 𝟙 H else 1)).exists
  choose j hj using hex
  have key : ∀ {T : C} (x : T ⟶ H) (b c : n), x ≫ j b ≫ p c = if c = b then x else 1 := by
    intro T x b c
    rw [hj b c]
    split_ifs <;> simp
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  refine ⟨j, fun b => ?_, fun b => by simpa using key (𝟙 H) b b,
    fun b c hcb => by simpa [hcb] using key (𝟙 H) b c⟩
  apply isMonHom_of_points
  · intro T
    apply ext
    intro a
    haveI := hp a
    rw [Category.assoc, key, MonObj.one_comp]
    split_ifs <;> rfl
  · intro T x y
    apply ext
    intro a
    haveI := hp a
    simp only [Category.assoc, key, MonObj.mul_comp]
    split_ifs <;> simp

theorem hom_ext_sections {G H H' : C} [MonObj G] [MonObj H] [MonObj H']
    {n : Type} [Finite n] [DecidableEq n]
    (p : n → (G ⟶ H)) (hp : ∀ a, IsMonHom (p a))
    (hu : ∀ (T : C) (y : n → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ p a = y a)
    (j : n → (H ⟶ G)) (h1 : ∀ b, j b ≫ p b = 𝟙 H) (h2 : ∀ b c, c ≠ b → j b ≫ p c = 1)
    (f g : G ⟶ H') [IsMonHom f] [IsMonHom g] (h : ∀ b, j b ≫ f = j b ≫ g) : f = g := by
  classical
  haveI := Fintype.ofFinite n
  have ext : ∀ {T : C} (x y : T ⟶ G), (∀ a, x ≫ p a = y ≫ p a) → x = y := fun {T} x y h =>
    (hu T fun a => y ≫ p a).unique h (fun _ => rfl)
  have hcomp : ∀ {K : C} [MonObj K] (k : G ⟶ K) [IsMonHom k] (l : List n),
      (l.map fun b => p b ≫ j b).prod ≫ k = (l.map fun b => p b ≫ j b ≫ k).prod := by
    intro K _ k _ l
    induction l with
    | nil => simp
    | cons b l ih => simp [MonObj.mul_comp, ih]
  have hlist : ∀ (c : n) (l : List n), l.Nodup →
      (l.map fun b => p b ≫ j b ≫ p c).prod = if c ∈ l then p c else 1 := by
    intro c l hl
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.map_cons, List.prod_cons, ih (List.nodup_cons.mp hl).2]
      by_cases hbc : b = c
      · subst hbc
        have hnot : b ∉ l := (List.nodup_cons.mp hl).1
        simp [h1, hnot]
      · simp [h2 b c (Ne.symm hbc), Ne.symm hbc]
  have hs : (Finset.univ.toList.map fun b => p b ≫ j b).prod = 𝟙 G := by
    apply ext
    intro c
    haveI := hp c
    rw [hcomp (p c), hlist c _ (Finset.nodup_toList _)]
    simp
  calc f = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ f := by rw [hs, Category.id_comp]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ f).prod := hcomp f _
    _ = (Finset.univ.toList.map fun b => p b ≫ j b ≫ g).prod := by simp only [h]
    _ = (Finset.univ.toList.map fun b => p b ≫ j b).prod ≫ g := (hcomp g _).symm
    _ = g := by rw [hs, Category.id_comp]

end General

theorem exists_diagonal : ∀ (K : Type) [Field K] [IsAlgClosed K] (G₀ G₁ H₀ H₁ : Over (Sp K)) [GrpObj G₀] [GrpObj G₁] [GrpObj H₀] [GrpObj H₁] [IsCommMonObj H₀] [IsCommMonObj H₁], IsSemiAbelian H₀ → IsSemiAbelian H₁ → ∀ (l : ℕ), l.Prime → (l : K) ≠ 0 → ∀ (p₀ : Fin 8 → (G₀ ⟶ H₀)) (p₁ : Fin 8 → (G₁ ⟶ H₁)), (∀ a, IsMonHom (p₀ a)) → (∀ a, IsMonHom (p₁ a)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₀)), ∃! x : T ⟶ G₀, ∀ a, x ≫ p₀ a = y a) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₁)), ∃! x : T ⟶ G₁, ∀ a, x ≫ p₁ a = y a) → ∀ (F : G₀ ⟶ G₁), IsMonHom F → IsIso F → (∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ G₀), (∃ k : ℕ, z ^ (l ^ k) = 1) → (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ p₀ a = z' ≫ p₀ a' → z ≫ F ≫ p₁ a = z' ≫ F ≫ p₁ a') → ∃ f₁ : H₀ ⟶ H₁, IsMonHom f₁ ∧ IsIso f₁ ∧ ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
  intro K _ _ G₀ G₁ H₀ H₁ _ _ _ _ _ _ hH₀ hH₁ l hl hlK p₀ p₁ hp₀ hp₁ hu₀ hu₁ F hF hFi htor
  classical
  obtain ⟨j₀, hj₀m, hj₀1, hj₀2⟩ := exists_sections p₀ hp₀ hu₀
  obtain ⟨j₁, hj₁m, hj₁1, hj₁2⟩ := exists_sections p₁ hp₁ hu₁
  haveI := hF
  haveI := hFi
  haveI := fun a => hp₀ a
  haveI := fun a => hp₁ a
  haveI := fun b => hj₀m b
  have hpj : ∀ b a : Fin 8, j₀ b ≫ p₀ a = if a = b then 𝟙 H₀ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₀1 a
    · exact hj₀2 b a h
  have hpj₁ : ∀ b a : Fin 8, j₁ b ≫ p₁ a = if a = b then 𝟙 H₁ else 1 := by
    intro b a
    split_ifs with h
    · subst h; exact hj₁1 a
    · exact hj₁2 b a h

  have htors : ∀ (b : Fin 8) (y : 𝟙_ (Over (Sp K)) ⟶ H₀) (k : ℕ), y ^ (l ^ k) = 1 →
      ∃ k : ℕ, (y ≫ j₀ b) ^ (l ^ k) = 1 := by
    intro b y k hy
    haveI := hj₀m b
    exact ⟨k, by rw [← MonObj.pow_comp, hy, MonObj.one_comp]⟩

  have hoff : ∀ b a : Fin 8, a ≠ b → j₀ b ≫ F ≫ p₁ a = 1 := by
    intro b a hab
    haveI := hj₀m b
    haveI := hp₁ a
    refine GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ inferInstance
      (fun _ _ y k hy => ?_)
    have := htor (y ≫ j₀ b) 1 (htors b y k hy) ⟨0, _root_.one_pow _⟩ a a
      (by rw [Category.assoc, hpj, if_neg hab, MonObj.comp_one, MonObj.one_comp])
    rw [MonObj.one_comp (F ≫ p₁ a)] at this
    simpa [Category.assoc] using this

  have hdiag : ∀ a : Fin 8, j₀ a ≫ F ≫ p₁ a = j₀ 0 ≫ F ≫ p₁ 0 := by
    intro a
    haveI := hj₀m a
    haveI := hj₀m 0
    haveI := hp₁ a
    haveI := hp₁ 0
    have hpt : ∀ (T : Over (Sp K)) (x : T ⟶ H₀),
        x ≫ ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) =
          (x ≫ j₀ a ≫ F ≫ p₁ a) * (x ≫ j₀ 0 ≫ F ≫ p₁ 0)⁻¹ := by
      intro T x
      rw [MonObj.comp_mul, GrpObj.comp_inv]
    have hmon : IsMonHom ((j₀ a ≫ F ≫ p₁ a) * (j₀ 0 ≫ F ≫ p₁ 0)⁻¹) := by
      apply isMonHom_of_points
      · intro T
        rw [hpt, MonObj.one_comp, MonObj.one_comp, _root_.inv_one, _root_.mul_one]
      · intro T x y
        rw [hpt, hpt, hpt, MonObj.mul_comp, MonObj.mul_comp, _root_.mul_inv, _root_.mul_mul_mul_comm]
    have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one K H₀ H₁ hH₀ hH₁ l hl hlK _ hmon
      (fun _ _ y k hy => by
        have := htor (y ≫ j₀ a) (y ≫ j₀ 0) (htors a y k hy) (htors 0 y k hy) a 0
          (by rw [Category.assoc, Category.assoc, hpj, hpj, if_pos rfl, if_pos rfl])
        rw [hpt, _root_.mul_inv_eq_one]
        simpa [Category.assoc] using this)
    exact _root_.mul_inv_eq_one.mp h1
  let f₁ : H₀ ⟶ H₁ := j₀ 0 ≫ F ≫ p₁ 0
  haveI : IsMonHom f₁ := by
    haveI := hj₀m 0
    haveI := hp₁ 0
    dsimp [f₁]
    infer_instance
  have hcomm : ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
    intro a
    haveI := hp₁ a
    haveI := hp₀ a
    refine hom_ext_sections p₀ hp₀ hu₀ j₀ hj₀1 hj₀2 _ _ (fun b => ?_)
    rw [← Category.assoc (j₀ b) (p₀ a), hpj]
    split_ifs with hab
    · subst hab
      rw [Category.id_comp, hdiag]
    · rw [hoff b a hab, MonObj.one_comp]
  have hsec : j₀ 0 ≫ F = f₁ ≫ j₁ 0 := by
    refine (hu₁ H₀ fun a => (f₁ ≫ j₁ 0) ≫ p₁ a).unique (fun a => ?_) (fun _ => rfl)
    rw [Category.assoc, hcomm, ← Category.assoc, hpj, Category.assoc, hpj₁]
    split_ifs
    · simp
    · rw [MonObj.one_comp, MonObj.comp_one]
  refine ⟨f₁, inferInstance, ⟨⟨j₁ 0 ≫ inv F ≫ p₀ 0, ?_, ?_⟩⟩, hcomm⟩
  · rw [← Category.assoc, ← hsec, Category.assoc, IsIso.hom_inv_id_assoc, hj₀1]
  · rw [Category.assoc, Category.assoc, ← hcomm, IsIso.inv_hom_id_assoc, hj₁1]

end GlobalTheory.PowerDiagonal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerIsoDiagonalOfLPowerTorsionActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_iso_diagonal_of_lPower_torsion_action : ∀ (K : Type) [Field K] [IsAlgClosed K] (G₀ G₁ H₀ H₁ : Over (Sp K)) [GrpObj G₀] [GrpObj G₁] [GrpObj H₀] [GrpObj H₁] [IsCommMonObj H₀] [IsCommMonObj H₁], IsSemiAbelian H₀ → IsSemiAbelian H₁ → ∀ (l : ℕ), l.Prime → (l : K) ≠ 0 → ∀ (p₀ : Fin 8 → (G₀ ⟶ H₀)) (p₁ : Fin 8 → (G₁ ⟶ H₁)), (∀ a, IsMonHom (p₀ a)) → (∀ a, IsMonHom (p₁ a)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₀)), ∃! x : T ⟶ G₀, ∀ a, x ≫ p₀ a = y a) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ H₁)), ∃! x : T ⟶ G₁, ∀ a, x ≫ p₁ a = y a) → ∀ (F : G₀ ⟶ G₁), IsMonHom F → IsIso F → (∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ G₀), (∃ k : ℕ, z ^ (l ^ k) = 1) → (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ p₀ a = z' ≫ p₀ a' → z ≫ F ≫ p₁ a = z' ≫ F ≫ p₁ a') → ∃ f₁ : H₀ ⟶ H₁, IsMonHom f₁ ∧ IsIso f₁ ∧ ∀ a, F ≫ p₁ a = p₀ a ≫ f₁ := by
  first | exact @GlobalTheory.PowerDiagonal.exists_diagonal | exact GlobalTheory.PowerDiagonal.exists_diagonal | (intros; apply GlobalTheory.PowerDiagonal.exists_diagonal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoEqCoordinatewisePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PoincDiag

@[reassoc]
theorem mapFst {S S' : Scheme.{0}} (t : S' ⟶ S) {X Y : Over S} (φ : X ⟶ Y) :
    ((Over.pullback t).map φ).left ≫ pullback.fst Y.hom t = pullback.fst X.hom t ≫ φ.left := by
  simp only [Over.pullback_map_left]; exact pullback.lift_fst _ _ _

theorem mapSnd {S S' : Scheme.{0}} (t : S' ⟶ S) {X Y : Over S} (φ : X ⟶ Y) :
    ((Over.pullback t).map φ).left ≫ pullback.snd Y.hom t = pullback.snd X.hom t := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

theorem abBC : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → IsAbelianScheme ((Over.pullback (spMap f)).obj B) ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap f)).obj B).hom := by
  intro R R' _ _ f B _ g hB hd
  exact GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f B _ _ g
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B (spMap f)) hB hd

theorem torsPull : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (X : Over S) [GrpObj X] (z : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X) (y : Over.mk t ⟶ X) (n : ℕ), y.left = z.left ≫ pullback.fst X.hom t → z ^ n = 1 → y ^ n = 1 := by
  intro S S' t X _ z y n hy hz
  have hgp := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback X t
  let k : Over.mk ((𝟙_ (Over S')).hom ≫ t) ⟶ Over.mk t := Over.homMk (𝟙 _) (by simp)
  have hw : ((1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X).left ≫ pullback.fst X.hom t) ≫ X.hom = (Over.mk t).hom := by
    have e := Over.w (1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X)
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simp only [Over.pullback_obj_hom] at e
    rw [e]
    simp
  let u : Over.mk t ⟶ X := Over.homMk ((1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X).left ≫ pullback.fst X.hom t) hw
  have hu : u = 1 := by
    have h := hgp.2 (𝟙_ (Over S')) 1 1 (k ≫ u) (k ≫ u) (by simp [k, u]) (by simp [k, u])
    rw [← MonObj.comp_mul, _root_.mul_one] at h
    have e : u * u = u := Over.OverMorphism.ext (by simpa [k, u] using h)
    exact mul_eq_left.1 e
  have hp : ∀ m : ℕ, (y ^ m).left = (z ^ m).left ≫ pullback.fst X.hom t := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero]
      rw [← hu]
      rfl
    | succ m ih =>
      have h := hgp.2 (𝟙_ (Over S')) (z ^ m) z (k ≫ y ^ m) (k ≫ y) (by simp [k, ih]) (by simp [k, hy])
      rw [← MonObj.comp_mul, ← pow_succ, ← pow_succ] at h
      simpa [k] using h
  apply Over.OverMorphism.ext
  rw [hp n, hz, ← hu]
  rfl

theorem fibreIso_eq_pow : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → ∃ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ ∧ ∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  intro l hl hodd W hW j hj V V₁ _ _ _ _ _ hlu Q ρ hρ D pr w hpr huniv hw K _ _ ev σ f hf hL htor
  haveI := D.P.isAb.comm
  have hfw : f ≫ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).hom = ((Over.pullback (spMap ev)).obj D.P.A).hom := by
    simpa using hf.1.w
  let F : (Over.pullback (spMap ev)).obj D.P.A ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A := Over.homMk f hfw
  haveI : IsIso f := hf.1.isIso_fst_of_isIso
  haveI hFi : IsIso F := by
    have : IsIso ((Over.forget _).map F) := by change IsIso f; infer_instance
    exact isIso_of_reflects_iso F (Over.forget _)
  haveI hFm : IsMonHom F := GlobalTheory.AmpleRigid.isMonHom_of_mul_comp F
    (fun T x y => GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id F hf x y)
  obtain ⟨hm₀, hu₀⟩ := GlobalTheory.T.isMonHom_pullback_pr_and_unique_lift_fin_eight _ _ (spMap ev) D.P.A _ pr hpr huniv
  obtain ⟨hm₁, hu₁⟩ := GlobalTheory.T.isMonHom_pullback_pr_and_unique_lift_fin_eight _ _ (spMap (σ.toRingHom.comp ev)) D.P.A _ pr hpr huniv
  have hBab := abBC V V₁ ρ Q.B Q.g Q.isAb Q.smoothDim
  have hB₀ := (abBC V₁ K ev _ Q.g hBab.1 hBab.2).1
  have hB₁ := (abBC V₁ K (σ.toRingHom.comp ev) _ Q.g hBab.1 hBab.2).1
  have hlK : (l : K) ≠ 0 := by
    have := hlu.map ev
    rw [map_natCast] at this
    exact this.ne_zero

  have key : ∀ (z : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap ev)).obj D.P.A), (∃ k : ℕ, z ^ (l ^ k) = 1) → ∀ a,
      (z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a)).left ≫
          pullback.fst ((Over.pullback (spMap ρ)).obj Q.B).hom (spMap (σ.toRingHom.comp ev)) =
        spMap σ.toRingHom ≫ (z ≫ (Over.pullback (spMap ev)).map (pr a)).left ≫
          pullback.fst ((Over.pullback (spMap ρ)).obj Q.B).hom (spMap ev) := by
    rintro z ⟨k, hk⟩ a
    have hzw : z.left ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ := by simpa using Over.w z
    have hyw : (z.left ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ D.P.A.hom = (Over.mk (spMap ev)).hom := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hzw, Category.id_comp]; rfl
    let y : Over.mk (spMap ev) ⟶ D.P.A := Over.homMk (z.left ≫ pullback.fst D.P.A.hom (spMap ev)) hyw
    have hy : y ^ (l ^ k) = 1 := torsPull _ _ (spMap ev) D.P.A z y (l ^ k) rfl hk
    have h := htor y ⟨k, hy⟩ z.left rfl hzw
    simp only [Over.comp_left, Category.assoc]
    rw [mapFst, mapFst]
    change z.left ≫ f ≫ _ = _
    rw [reassoc_of% h]
    rfl
  have htors : ∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap ev)).obj D.P.A), (∃ k : ℕ, z ^ (l ^ k) = 1) →
      (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ (Over.pullback (spMap ev)).map (pr a) = z' ≫ (Over.pullback (spMap ev)).map (pr a') →
      z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a) = z' ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a') := by
    intro z z' hz hz' a a' he
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [key z hz a, key z' hz' a', he]
    · exact (Over.w (z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a))).trans
        (Over.w (z' ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a'))).symm
  obtain ⟨f₁', hm, hiso, hco⟩ := GlobalTheory.T.eighthPower_iso_diagonal_of_lPower_torsion_action K _ _ _ _ (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB₀)
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB₁) l hl hlK _ _ hm₀ hm₁ hu₀ hu₁ F hFm hFi htors
  obtain ⟨f₁, hf₁, hcoord⟩ := GlobalTheory.T.fibre_iso_grpPullback_identity_transport V V₁ K Q.B ρ ev σ f₁' hm hiso
  refine ⟨f₁, hf₁, fun a T x y h1 h2 => ?_⟩
  have hc : f ≫ ((Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a)).left =
      ((Over.pullback (spMap ev)).map (pr a)).left ≫ f₁'.left := congrArg (·.left) (hco a)
  have := hcoord T (x ≫ ((Over.pullback (spMap ev)).map (pr a)).left) y
    (by rw [h1, Category.assoc, mapFst_assoc]) (by rw [h2, Category.assoc, mapSnd])
  rw [← this, Category.assoc, ← reassoc_of% hc, mapFst_assoc]

end GlobalTheory.PoincDiag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoEqCoordinatewisePowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighth_power_fibre_iso_eq_coordinatewise_power : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → ∃ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ ∧ ∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  first | exact @GlobalTheory.PoincDiag.fibreIso_eq_pow | exact GlobalTheory.PoincDiag.fibreIso_eq_pow | (intros; apply GlobalTheory.PoincDiag.fibreIso_eq_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8WeightedBundleIsoPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8WeightedBundleIsoPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.MumKeep

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem exists_fibre_point : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁)
    (D : DegPre V₁) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
    (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) →
    ∀ (K : Type) [Field K] (ev : V₁ →+* K) (T : Over (Sp K)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap (ev.comp ρ))).obj Q.B)),
    ∃ x : T.left ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, x ≫ pullback.snd D.P.A.hom (spMap ev) = T.hom ∧
      ∀ a, x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
        (y a).left ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  intro V V₁ _ _ _ _ Q ρ D pr hu K _ ev T y
  have cond : ∀ a, ((y a).left ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ))) ≫ Q.B.hom = (T.hom ≫ spMap ev) ≫ spMap ρ :=
    fun a => by
      have hw : (y a).left ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = T.hom := Over.w (y a)
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, spMap_comp', Category.assoc]
  let y' : Fin 8 → (Over.mk (T.hom ≫ spMap ev) ⟶ (Over.pullback (spMap ρ)).obj Q.B) := fun a =>
    Over.homMk (pullback.lift ((y a).left ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ))) (T.hom ≫ spMap ev) (cond a))
      (pullback.lift_snd _ _ _)
  obtain ⟨x', hx', -⟩ := hu _ y'
  refine ⟨pullback.lift x'.left T.hom (Over.w x'), pullback.lift_snd _ _ _, fun a => ?_⟩
  rw [pullback.lift_fst_assoc, ← Category.assoc, ← Over.comp_left, hx' a]
  exact pullback.lift_fst _ _ _

theorem lam_eq_zero_of_unimodular : ∀ {S : Scheme.{0}} [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (N : GlobalTheory.CechPic.Pic A.left) (W : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose).det = 1 →
    (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∑ ab : Fin 8 × Fin 8, W ab.1 ab.2 • GlobalTheory.CechPic.lam N (y ab.1) (y ab.2) = 0) →
    GlobalTheory.CechPic.lam N (fst A A) (snd A A) = 0 := by
  intro S _ A _ _ hA N W hW h
  have hB1 : ∀ (T : Over S) (x x' y : T ⟶ A), GlobalTheory.CechPic.lam N (x * x') y =
      GlobalTheory.CechPic.lam N x y + GlobalTheory.CechPic.lam N x' y := fun T x x' y => GlobalTheory.SquareSym.lam_mul_left hA N x x' y
  have hB2 : ∀ (T : Over S) (x y : T ⟶ A), GlobalTheory.CechPic.lam N x y = GlobalTheory.CechPic.lam N y x :=
    fun T x y => GlobalTheory.CechPic.lam_comm N x y
  have hform : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), GlobalTheory.MatrixBundle.form (GlobalTheory.CechPic.lam N) W y y = 0 :=
    fun T y => h T y
  have hE : ∀ (T : Over S) (x y : Fin 8 → (T ⟶ A)),
      GlobalTheory.MatrixBundle.form (GlobalTheory.CechPic.lam N) (W + W.transpose) x y = 0 := by
    intro T x y
    have := GlobalTheory.MatrixBundle.form_mul_self (hB1 T) (hB2 T) W x y
    rw [hform, hform, hform, zero_add, zero_add] at this
    exact this.symm
  have key := GlobalTheory.MatrixBundle.form_single_right (hB1 _) (hB2 _) (W + W.transpose)
    (fun u => fst A A ^ ((W + W.transpose).adjugate 0 u)) 0 (snd A A)
  rw [hE] at key
  have hp : ∏ u, (fst A A ^ ((W + W.transpose).adjugate 0 u)) ^ ((W + W.transpose) u 0) = fst A A := by
    simp only [← zpow_mul]
    have zs : ∀ (s : Finset (Fin 8)) (e : Fin 8 → ℤ), ∏ u ∈ s, fst A A ^ e u = fst A A ^ ∑ u ∈ s, e u := by
      intro s e
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
    rw [zs]
    have : ∑ u, (W + W.transpose).adjugate 0 u * (W + W.transpose) u 0 = 1 := by
      have e := congrFun (congrFun (Matrix.adjugate_mul (W + W.transpose)) 0) 0
      rw [Matrix.mul_apply, hW] at e
      simpa using e
    rw [this, zpow_one]
  rw [hp] at key
  exact key.symm

theorem sq_unique {S X : Scheme.{0}} {G : Over S} (ψ ψ' : X ⟶ (G ⊗ G).left)
    (h₁ : ψ ≫ (fst G G).left = ψ' ≫ (fst G G).left) (h₂ : ψ ≫ (snd G G).left = ψ' ≫ (snd G G).left) : ψ = ψ' := by
  let a : Over.mk (ψ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk ψ rfl
  let a' : Over.mk (ψ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk ψ' (by
    show ψ' ≫ (G ⊗ G).hom = ψ ≫ (G ⊗ G).hom
    rw [← Over.w (fst G G), ← Category.assoc, ← h₁, Category.assoc])
  have : a = a' := CartesianMonoidalCategory.hom_ext _ _
    (Over.OverMorphism.ext (by simpa [a, a'] using h₁)) (Over.OverMorphism.ext (by simpa [a, a'] using h₂))
  exact congrArg (fun z => z.left) this

theorem lbIso_lam_of_lam_sub : ∀ {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (hL : L.IsLB)
    (G₀ G₁ : Over S') [GrpObj G₀] [IsCommMonObj G₀] [GrpObj G₁] [IsCommMonObj G₁] (t₀ t₁ : S' ⟶ S)
    (p₀ : G₀.left ⟶ G.left) (p₁ : G₁.left ⟶ G.left), IsGrpPullback G₀ G t₀ p₀ → IsGrpPullback G₁ G t₁ p₁ →
    ∀ (f₁ : G₀.left ⟶ G₁.left), IsGrpPullback G₀ G₁ (𝟙 _) f₁ → ∀ (f₂ : (G2 G₀).left ⟶ (G2 G₁).left), IsSquare f₁ f₂ →
    ∀ (ψ₀ : (G2 G₀).left ⟶ (G2 G).left) (ψσ : (G2 G₁).left ⟶ (G2 G).left), IsSquare p₀ ψ₀ → IsSquare p₁ ψσ →
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.pull (f₁ ≫ p₁) (GlobalTheory.CechPic.cls L hL) - GlobalTheory.CechPic.pull p₀ (GlobalTheory.CechPic.cls L hL))
      (fst G₀ G₀) (snd G₀ G₀) = 0 →
    LBIso ((abelian₂ G L).pull ψ₀) ((abelian₂ G L).pull (f₂ ≫ ψσ)) := by
  intro S S' G _ _ L hL G₀ G₁ _ _ _ _ t₀ t₁ p₀ p₁ g₀ g₁ f₁ hf₁ f₂ hf₂ ψ₀ ψσ hψ₀ hψσ hN
  have hLam : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hid : LBIso (abelian₂ G L) ((abelian₂ G L).pull (𝟙 _)) :=
    (GlobalTheory.CechPic.cls_eq_iff hLam (pull_isLB hLam _)).1 (by rw [GlobalTheory.CechPic.cls_pull hLam, GlobalTheory.CechPic.pull_id])
  have refl : ∀ {X : Scheme.{0}} {A : LB X} (hA : A.IsLB), LBIso A A := fun hA => (GlobalTheory.CechPic.cls_eq_iff hA hA).1 rfl
  obtain ⟨β₀, hβ₀, H₀⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ t₀ G G₀ p₀ g₀
  obtain ⟨β₁, hβ₁, H₁⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (𝟙 _ ≫ t₁) G G₀ (f₁ ≫ p₁) (hf₁.comp g₁)
  have i₀ := H₀ L (L.pull p₀) _ (abelian₂ G L) (𝟙 _) hL (pull_isLB hL _) hLam (refl (pull_isLB hL _)) hid
  have i₁ := H₁ L (L.pull (f₁ ≫ p₁)) _ (abelian₂ G L) (𝟙 _) hL (pull_isLB hL _) hLam (refl (pull_isLB hL _)) hid
  have e₀ : β₀ = ψ₀ := sq_unique _ _ (hβ₀.1.trans hψ₀.1.symm) (hβ₀.2.trans hψ₀.2.symm)
  have e₁ : β₁ = f₂ ≫ ψσ := sq_unique _ _ (hβ₁.1.trans (by rw [Category.assoc, hψσ.1, ← Category.assoc f₂, hf₂.1, Category.assoc]))
    (hβ₁.2.trans (by rw [Category.assoc, hψσ.2, ← Category.assoc f₂, hf₂.2, Category.assoc]))
  rw [Category.comp_id, e₀] at i₀
  rw [Category.comp_id, e₁] at i₁
  have hl₀ : (abelian₂ G₀ (L.pull p₀)).IsLB := LB.isLB_linComb (pull_isLB hL _) _ _
  have hl₁ : (abelian₂ G₀ (L.pull (f₁ ≫ p₁))).IsLB := LB.isLB_linComb (pull_isLB hL _) _ _
  have k₀ : GlobalTheory.CechPic.cls (abelian₂ G₀ (L.pull p₀)) hl₀ =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls (L.pull p₀) (pull_isLB hL _)) (fst G₀ G₀) (snd G₀ G₀) :=
    GlobalTheory.CechPic.cls_cube_two _ _ _ _
  have k₁ : GlobalTheory.CechPic.cls (abelian₂ G₀ (L.pull (f₁ ≫ p₁))) hl₁ =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls (L.pull (f₁ ≫ p₁)) (pull_isLB hL _)) (fst G₀ G₀) (snd G₀ G₀) :=
    GlobalTheory.CechPic.cls_cube_two _ _ _ _
  rw [GlobalTheory.CechPic.cls_pull hL] at k₀ k₁
  have hlam : GlobalTheory.CechPic.lam (GlobalTheory.CechPic.pull (f₁ ≫ p₁) (GlobalTheory.CechPic.cls L hL)) (fst G₀ G₀) (snd G₀ G₀) =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.pull p₀ (GlobalTheory.CechPic.cls L hL)) (fst G₀ G₀) (snd G₀ G₀) := by
    have := GlobalTheory.AdditionGraph.lam_add (GlobalTheory.CechPic.pull (f₁ ≫ p₁) (GlobalTheory.CechPic.cls L hL) -
      GlobalTheory.CechPic.pull p₀ (GlobalTheory.CechPic.cls L hL)) (GlobalTheory.CechPic.pull p₀ (GlobalTheory.CechPic.cls L hL)) (fst G₀ G₀) (snd G₀ G₀)
    rw [sub_add_cancel, hN, zero_add] at this
    exact this
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hLam _) (pull_isLB hLam _)).1 ?_
  rw [(GlobalTheory.CechPic.cls_eq_iff (pull_isLB hLam _) hl₀).2 i₀.symm,
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hLam _) hl₁).2 i₁.symm, k₀, k₁, hlam]

theorem pushed_mul_one : ∀ {S₁ S₂ S X : Scheme.{0}} (G₁ : Over S₁) [GrpObj G₁] (G₂ : Over S₂) [GrpObj G₂] (G : Over S) [GrpObj G]
    (t₁ : S₁ ⟶ S) (t₂ : S₂ ⟶ S) (φ₁ : G₁.left ⟶ G.left) (φ₂ : G₂.left ⟶ G.left),
    IsGrpPullback G₁ G t₁ φ₁ → IsGrpPullback G₂ G t₂ φ₂ →
    ∀ (P₁ : Over S₁) (P₂ : Over S₂) (u v : P₁ ⟶ G₁) (u' v' : P₂ ⟶ G₂) (z₁ : X ⟶ P₁.left) (z₂ : X ⟶ P₂.left),
    z₁ ≫ P₁.hom ≫ t₁ = z₂ ≫ P₂.hom ≫ t₂ →
    z₁ ≫ u.left ≫ φ₁ = z₂ ≫ u'.left ≫ φ₂ → z₁ ≫ v.left ≫ φ₁ = z₂ ≫ v'.left ≫ φ₂ →
    z₁ ≫ (u * v).left ≫ φ₁ = z₂ ≫ (u' * v').left ≫ φ₂ ∧
      z₁ ≫ (1 : P₁ ⟶ G₁).left ≫ φ₁ = z₂ ≫ (1 : P₂ ⟶ G₂).left ≫ φ₂ := by
  intro S₁ S₂ S X G₁ _ G₂ _ G _ t₁ t₂ φ₁ φ₂ h₁ h₂ P₁ P₂ u v u' v' z₁ z₂ hb hu hv
  let j₁ : Over.mk (z₁ ≫ P₁.hom) ⟶ P₁ := Over.homMk z₁ rfl
  let j₂ : Over.mk (z₂ ≫ P₂.hom) ⟶ P₂ := Over.homMk z₂ rfl
  have hb' : (Over.mk (z₁ ≫ P₁.hom)).hom ≫ t₁ = (Over.mk (z₂ ≫ P₂.hom)).hom ≫ t₂ := by
    simpa only [Over.mk_hom, Category.assoc] using hb

  have m₁ : ∀ a b : P₁ ⟶ G₁, (pushPt h₁.1.w (j₁ ≫ a) * pushPt h₁.1.w (j₁ ≫ b)).left = z₁ ≫ (a * b).left ≫ φ₁ :=
    fun a b => by
      rw [h₁.2 _ (j₁ ≫ a) (j₁ ≫ b) _ _ rfl rfl, ← MonObj.comp_mul]
      simp [j₁]
  have m₂ : ∀ a b : P₂ ⟶ G₂, (pushPt h₂.1.w (j₂ ≫ a) * pushPt h₂.1.w (j₂ ≫ b)).left = z₂ ≫ (a * b).left ≫ φ₂ :=
    fun a b => by
      rw [h₂.2 _ (j₂ ≫ a) (j₂ ≫ b) _ _ rfl rfl, ← MonObj.comp_mul]
      simp [j₂]
  have l₁ : ∀ a : P₁ ⟶ G₁, (pushPt h₁.1.w (j₁ ≫ a)).left = z₁ ≫ a.left ≫ φ₁ := fun a => by
    simp [pushPt, j₁]
  have l₂ : ∀ a : P₂ ⟶ G₂, (pushPt h₂.1.w (j₂ ≫ a)).left = z₂ ≫ a.left ≫ φ₂ := fun a => by
    simp [pushPt, j₂]
  refine ⟨?_, ?_⟩
  · rw [← m₁, ← m₂]
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.mul_left_congr hb' _ _ _ _ ((l₁ u).trans (hu.trans (l₂ u').symm))
      ((l₁ v).trans (hv.trans (l₂ v').symm))
  ·
    have i₁ : pushPt h₁.1.w (j₁ ≫ (1 : P₁ ⟶ G₁)) = 1 := by
      have k : pushPt h₁.1.w (j₁ ≫ (1 : P₁ ⟶ G₁)) * pushPt h₁.1.w (j₁ ≫ (1 : P₁ ⟶ G₁)) =
          pushPt h₁.1.w (j₁ ≫ (1 : P₁ ⟶ G₁)) := Over.OverMorphism.ext (by rw [m₁, _root_.mul_one, l₁])
      exact mul_eq_left.mp k
    have i₂ : pushPt h₂.1.w (j₂ ≫ (1 : P₂ ⟶ G₂)) = 1 := by
      have k : pushPt h₂.1.w (j₂ ≫ (1 : P₂ ⟶ G₂)) * pushPt h₂.1.w (j₂ ≫ (1 : P₂ ⟶ G₂)) =
          pushPt h₂.1.w (j₂ ≫ (1 : P₂ ⟶ G₂)) := Over.OverMorphism.ext (by rw [m₂, _root_.mul_one, l₂])
      exact mul_eq_left.mp k
    have oc : ∀ {a b : X ⟶ S} (h : a = b), (1 : Over.mk a ⟶ G).left = (1 : Over.mk b ⟶ G).left := by
      intro a b h; subst h; rfl
    rw [← l₁, ← l₂, i₁, i₂]
    exact oc hb'

theorem fibre_iso_keeps_lam : ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → ∀ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ → (∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) → ∀ (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsSquare f₁ f₂ → ∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ)) := by
  intro W hW V V₁ _ _ _ _ Q ρ D pr w hpr hu hw K _ _ ev σ f hf hfL f₁ hf₁ hco f₂ hf₂ ψ₀ ψσ hψ₀ hψσ
  have gK := isGrpPullback_pullback Q.B (spMap (ev.comp ρ))
  have gσ := isGrpPullback_pullback Q.B (spMap (σ.toRingHom.comp (ev.comp ρ)))
  have gρ := isGrpPullback_pullback Q.B (spMap ρ)
  have g₁ := hf₁.comp gσ
  refine lbIso_lam_of_lam_sub Q.B Q.M.L Q.M.isLB _ _ _ _ _ _ gK gσ f₁ hf₁ f₂ hf₂ ψ₀ ψσ hψ₀ hψσ ?_
  refine lam_eq_zero_of_unimodular _ (GlobalTheory.isAbelianScheme_pullback_obj _ _ Q.isAb) _ W hW.2 ?_
  intro T y
  obtain ⟨x, hx1, hx2⟩ := exists_fibre_point V V₁ Q ρ D pr hu K ev T y

  have hLC := LB.isLB_linComb Q.M.isLB
    (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
    (fun k => -(W k.1.1 k.1.2 * negε k.2))
  have A2 : ∀ {X : Scheme.{0}} (z : X ⟶ D.P.A.left), GlobalTheory.CechPic.pull z (GlobalTheory.CechPic.cls D.P.L D.P.isLB) =
      ∑ k : (Fin 8 × Fin 8) × Fin 4, (-(W k.1.1 k.1.2 * negε k.2)) •
        GlobalTheory.CechPic.pull (z ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ))
          (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) := by
    intro X z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(GlobalTheory.CechPic.cls_eq_iff D.P.isLB hLC).2 ⟨w, hw⟩, GlobalTheory.CechPic.cls_linComb Q.M.isLB, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, ← GlobalTheory.CechPic.pull_comp]
  have e0 : GlobalTheory.CechPic.pull (pullback.fst D.P.A.hom (spMap ev)) (GlobalTheory.CechPic.cls D.P.L D.P.isLB) =
      GlobalTheory.CechPic.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev))) (GlobalTheory.CechPic.cls D.P.L D.P.isLB) := by
    have := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB D.P.isLB _) (pull_isLB D.P.isLB _)).2 hfL
    rwa [GlobalTheory.CechPic.cls_pull D.P.isLB, GlobalTheory.CechPic.cls_pull D.P.isLB] at this
  have e1 := congrArg (GlobalTheory.CechPic.pull x) e0
  rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, A2, A2] at e1
  have h0 : ∀ a b i, (x ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ lamPts (pr a) (pr b) i ≫ pullback.fst Q.B.hom (spMap ρ) =
      lamPts (y a) (y b) i ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
    intro a b i
    have base : (x ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ D.P.A.hom ≫ spMap ρ = 𝟙 T.left ≫ T.hom ≫ spMap (ev.comp ρ) := by
      rw [Category.assoc, pullback.condition_assoc, ← Category.assoc x, hx1, spMap_comp', Category.id_comp]
    have hc : ∀ a, (x ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) =
        𝟙 T.left ≫ (y a).left ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := fun a => by
      rw [Category.id_comp, Category.assoc]; exact hx2 a
    obtain ⟨hm, h1⟩ := pushed_mul_one _ _ Q.B _ _ _ _ gρ gK D.P.A T (pr a) (pr b) (y a) (y b) _ _ base (hc a) (hc b)
    fin_cases i
    · simpa [lamPts] using hm
    · simpa [lamPts] using hc a
    · simpa [lamPts] using hc b
    · simpa [lamPts] using h1
  have h1 : ∀ a b i, (x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev))) ≫ lamPts (pr a) (pr b) i ≫
      pullback.fst Q.B.hom (spMap ρ) =
      lamPts (y a) (y b) i ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
    intro a b i
    have hfw : f ≫ pullback.snd D.P.A.hom (spMap (σ.toRingHom.comp ev)) = pullback.snd D.P.A.hom (spMap ev) := by
      exact (hf.1.w).trans (Category.comp_id _)
    have base : (x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev))) ≫ D.P.A.hom ≫ spMap ρ =
        𝟙 T.left ≫ T.hom ≫ 𝟙 _ ≫ spMap (σ.toRingHom.comp (ev.comp ρ)) := by
      rw [Category.assoc, Category.assoc, pullback.condition_assoc, ← Category.assoc f, hfw, ← Category.assoc x, hx1,
        Category.id_comp, Category.id_comp]
      simp only [spMap_comp', Category.assoc]
    have hc : ∀ a, (x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev))) ≫ (pr a).left ≫
        pullback.fst Q.B.hom (spMap ρ) =
        𝟙 T.left ≫ (y a).left ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := fun a => by
      have hyS : (y a).left ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) := by
        rw [hx1]; exact Over.w (y a)
      have := hco a T.left x (y a).left (hx2 a).symm hyS
      simpa only [Category.id_comp, Category.assoc] using this
    obtain ⟨hm, h1⟩ := pushed_mul_one _ _ Q.B _ _ _ _ gρ g₁ D.P.A T (pr a) (pr b) (y a) (y b) _ _ base (hc a) (hc b)
    fin_cases i
    · simpa [lamPts] using hm
    · simpa [lamPts] using hc a
    · simpa [lamPts] using hc b
    · simpa [lamPts] using h1
  simp_rw [h0, h1] at e1

  set c₀ : GlobalTheory.CechPic.Pic ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left :=
    GlobalTheory.CechPic.pull (pullback.fst Q.B.hom (spMap (ev.comp ρ))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) with hc₀
  set c₁ : GlobalTheory.CechPic.Pic ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left :=
    GlobalTheory.CechPic.pull (f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) with hc₁
  have L : ∀ a b, GlobalTheory.CechPic.lam (c₁ - c₀) (y a) (y b) =
      ∑ i : Fin 4, (-negε i) • (GlobalTheory.CechPic.pull (lamPts (y a) (y b) i ≫ f₁ ≫
        pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) -
        GlobalTheory.CechPic.pull (lamPts (y a) (y b) i ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)))
          (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB)) := by
    intro a b
    simp only [hc₀, hc₁, GlobalTheory.CechPic.lam, Fin.sum_univ_four, negε, lamPts, map_sub, GlobalTheory.CechPic.pull_comp]
    simp
    abel
  have e2 : ∑ ab : Fin 8 × Fin 8, W ab.1 ab.2 • GlobalTheory.CechPic.lam (c₁ - c₀) (y ab.1) (y ab.2) =
      ∑ k : (Fin 8 × Fin 8) × Fin 4, (-(W k.1.1 k.1.2 * negε k.2)) • GlobalTheory.CechPic.pull (lamPts (y k.1.1) (y k.1.2) k.2 ≫
        f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) -
      ∑ k : (Fin 8 × Fin 8) × Fin 4, (-(W k.1.1 k.1.2 * negε k.2)) • GlobalTheory.CechPic.pull (lamPts (y k.1.1) (y k.1.2) k.2 ≫
        pullback.fst Q.B.hom (spMap (ev.comp ρ))) (GlobalTheory.CechPic.cls Q.M.L Q.M.isLB) := by
    rw [← Finset.sum_sub_distrib]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [L, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_sub, show W ab.1 ab.2 * -negε i = -(W ab.1 ab.2 * negε i) by ring]
  refine e2.trans ?_
  rw [← e1, sub_self]

end GlobalTheory.Poinc.Sep.MumKeep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8WeightedBundleIsoPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_e8_weighted_bundle_iso_pullback : ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → ∀ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ → (∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) → ∀ (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsSquare f₁ f₂ → ∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ)) := by
  first | exact @GlobalTheory.Poinc.Sep.MumKeep.fibre_iso_keeps_lam | exact GlobalTheory.Poinc.Sep.MumKeep.fibre_iso_keeps_lam | (intros; apply GlobalTheory.Poinc.Sep.MumKeep.fibre_iso_keeps_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoSharpTorsionGivesFactorIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.Poinc.Sep.conj_fibre_eighth_root : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  intro l hl hlo W hW j hj V V₁ _ _ _ _ _ hlu Q ρ hρ D e hSh K _ _ ev σ f hf hL ht hc a p hpf hps
  obtain ⟨pr, w, hmon, huniv, hwgen, hc4, -⟩ := hSh
  obtain ⟨f₁, hf₁, hcomp⟩ := GlobalTheory.T.eighth_power_fibre_iso_eq_coordinatewise_power l hl hlo W hW j hj V V₁ hlu Q ρ hρ D pr w hmon huniv hwgen K ev σ f hf hL ht
  have hw : f₁ ≫ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).hom = ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).hom := by
    simpa using hf₁.1.w
  let f' : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) := Over.homMk f₁ hw
  have hsq : IsSquare f₁ (f' ⊗ₘ f').left := by
    constructor
    · rw [← Over.comp_left, tensorHom_fst]; rfl
    · rw [← Over.comp_left, tensorHom_snd]; rfl
  refine ⟨f₁, (f' ⊗ₘ f').left, hf₁, hsq, ?_, ?_⟩
  · intro ψ₀ ψσ h0 hσ
    exact GlobalTheory.T.exists_e8_weighted_bundle_iso_pullback W hW V V₁ Q ρ D pr w hmon huniv hwgen K ev σ f hf hL f₁ hf₁ hcomp _ hsq ψ₀ ψσ h0 hσ
  · let mu0 : Fin 8 → Q.X := Pi.single 0 a
    have hsec : (spMap ev ≫ (D.c (e mu0)).left) ≫ D.P.A.hom = 𝟙 _ ≫ spMap ev := by
      rw [Category.assoc, Over.w]; simp
    let q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left := pullback.lift (spMap ev ≫ (D.c (e mu0)).left) (𝟙 _) hsec
    have hq1 : q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu0)).left := pullback.lift_fst _ _ _
    have hq2 : q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ := pullback.lift_snd _ _ _
    have hspc : spMap (ev.comp ρ) = spMap ev ≫ spMap ρ := by
      simp [spMap]
    have e1 : p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = q ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr 0).left ≫ pullback.fst Q.B.hom (spMap ρ) := by
      rw [hpf, reassoc_of% hq1, ← Over.comp_left_assoc, hc4, hspc, Category.assoc]
      simp [mu0]
    have e2 : p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = q ≫ pullback.snd D.P.A.hom (spMap ev) := by
      rw [hps, hq2]
    have h1 := hcomp 0 _ q p e1 e2
    have h2 := hc mu0 q hq1 hq2
    rw [← h1, reassoc_of% h2, e1]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoSharpTorsionGivesFactorIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_fibre_iso_sharp_torsion_gives_factor_iso : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  first | exact @GlobalTheory.Poinc.Sep.conj_fibre_eighth_root | exact GlobalTheory.Poinc.Sep.conj_fibre_eighth_root | (intros; apply GlobalTheory.Poinc.Sep.conj_fibre_eighth_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartFibreConjugateIsoMumford
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.Poinc.Sep.conj_fibre_core : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  intro g l hl hlo W hW
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.e8Power_fibre_conjugate_evaluation_iso g l hl hlo W hW
  refine ⟨max j₀ 1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu σ hσ a p hpf hps
  obtain ⟨f, hf, hL, ht, hc⟩ :=
    hj₀ j (le_of_max_le_left hj) V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu σ hσ
  exact GlobalTheory.T.eighthPower_fibre_iso_sharp_torsion_gives_factor_iso l hl hlo W hW j (le_of_max_le_right hj) V V₁ hlu Q ρ hρ D e hSh
    K ev σ f hf hL ht hc a p hpf hps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartFibreConjugateIsoMumfordStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianPart_fibre_conjugate_iso_mumford : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  first | exact @GlobalTheory.Poinc.Sep.conj_fibre_core | exact GlobalTheory.Poinc.Sep.conj_fibre_core | (intros; apply GlobalTheory.Poinc.Sep.conj_fibre_core <;> assumption)
end
