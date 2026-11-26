module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferential
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.EndLoc.ActUnr

section Chart

variable {X Y₁ Y₂ Z W : Scheme.{0}}

def chartPullPullAlong (L : LB X) (a₁ : Y₁ ⟶ X) (a₂ : Z ⟶ Y₁) (c₁ : Y₂ ⟶ X) (c₂ : W ⟶ Y₂) (h : Z ⟶ W)
    (e : a₂ ≫ a₁ = h ≫ c₂ ≫ c₁) : ChartPull ((L.pull a₁).pull a₂) ((L.pull c₁).pull c₂) h where
  idx J := fun _ _ => J PUnit.unit PUnit.unit
  le J y hy := by
    have h₁ := mem_pull.1 (mem_pull.1 hy)
    have h₂ : (a₂ ≫ a₁) y ∈ L.U (J PUnit.unit PUnit.unit) := by simpa using h₁
    rw [e] at h₂
    exact mem_pull.2 (mem_pull.2 (by simpa using h₂))
  g y J J' hj hj' := by
    have hc : ∀ K : PUnit → PUnit → L.ι, y ∈ ((L.pull a₁).pull a₂).U K →
        h y ∈ ((L.pull c₁).pull c₂).U (fun _ _ => K PUnit.unit PUnit.unit) := fun K hK => by
      have h₁ := mem_pull.1 (mem_pull.1 hK)
      have h₂ : (a₂ ≫ a₁) y ∈ L.U (K PUnit.unit PUnit.unit) := by simpa using h₁
      rw [e] at h₂
      exact mem_pull.2 (mem_pull.2 (by simpa using h₂))
    have l₁ := gm_pull_g (L.pull a₁) a₂ (𝟙 Z) y J J' hj hj'
    rw [Category.id_comp] at l₁
    have l₂ := gm_pull_g L a₁ a₂ y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hj) (mem_pull.1 hj')
    have l₃ := gm_pull_g (L.pull c₁) c₂ h y (fun _ _ => J PUnit.unit PUnit.unit)
      (fun _ _ => J' PUnit.unit PUnit.unit) (hc J hj) (hc J' hj')
    have l₄ := gm_pull_g L c₁ (h ≫ c₂) y (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
      (mem_pull.1 (hc J hj)) (mem_pull.1 (hc J' hj'))
    rw [l₁, l₂, l₃, l₄, e, Category.assoc]

theorem lbIso_pullPull_along (Q : LB X) (φ₂ : Y₁ ⟶ X) (m₁ m₂ : Y₁ ⟶ Y₁) (φ₂' : Y₂ ⟶ X) (m₁' m₂' : Y₂ ⟶ Y₂)
    (u : Y₂ ⟶ Y₁) (hφ : φ₂' = u ≫ φ₂) (h₁ : m₁' ≫ u = u ≫ m₁) (h₂ : m₂' ≫ u = u ≫ m₂)
    (H : LBIso ((Q.pull φ₂).pull m₁) ((Q.pull φ₂).pull m₂)) :
    LBIso ((Q.pull φ₂').pull m₁') ((Q.pull φ₂').pull m₂') :=
  LBIso.chartPull
    (chartPullPullAlong Q φ₂' m₁' φ₂ m₁ u (by rw [hφ, ← Category.assoc, h₁, Category.assoc]))
    (chartPullPullAlong Q φ₂' m₂' φ₂ m₂ u (by rw [hφ, ← Category.assoc, h₂, Category.assoc])) H

end Chart

section Square

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {B : Over S'} {φ : B.left ⟶ G.left}

def sqMap (w : φ ≫ G.hom = B.hom ≫ f) : (B ⊗ B).left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst B B)) (pushPt w (snd B B))).left

theorem sqMap_fst (w : φ ≫ G.hom = B.hom ≫ f) : sqMap w ≫ (fst G G).left = (fst B B).left ≫ φ :=
  congrArg (fun z => z.left) (lift_fst (pushPt w (fst B B)) (pushPt w (snd B B)))

theorem sqMap_snd (w : φ ≫ G.hom = B.hom ≫ f) : sqMap w ≫ (snd G G).left = (snd B B).left ≫ φ :=
  congrArg (fun z => z.left) (lift_snd (pushPt w (fst B B)) (pushPt w (snd B B)))

theorem left_hom_ext {H Z : Scheme.{0}} {G : Over H} {x y : Z ⟶ (G ⊗ G).left}
    (h1 : x ≫ (fst G G).left = y ≫ (fst G G).left) (h2 : x ≫ (snd G G).left = y ≫ (snd G G).left) : x = y := by
  have hw : y ≫ (G ⊗ G).hom = x ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← h1, Category.assoc]
  let x' : Over.mk (x ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk x rfl
  let y' : Over.mk (x ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk y hw
  have : x' = y' := CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext h1) (Over.OverMorphism.ext h2)
  exact congrArg (fun t => t.left) this

theorem lift_left_comp_sqMap (w : φ ≫ G.hom = B.hom ≫ f) (x' y' : B ⊗ B ⟶ B) (x y : G ⊗ G ⟶ G)
    (hx : x'.left ≫ φ = sqMap w ≫ x.left) (hy : y'.left ≫ φ = sqMap w ≫ y.left) :
    (lift x' y').left ≫ sqMap w = sqMap w ≫ (lift x y).left := by
  apply left_hom_ext
  · rw [Category.assoc, sqMap_fst, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, sqMap_snd, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc,
      ← Over.comp_left, lift_snd]

end Square

section Act

variable {O : Type} [Ring O]

theorem isRAct_pullback {H T : Scheme.{0}} (g : T ⟶ H) (AH : Over H) [GrpObj AH] (act : O → (AH ⟶ AH))
    (h : IsRAct AH act) : IsRAct ((Over.pullback g).obj AH) (fun a => (Over.pullback g).map (act a)) := by
  refine ⟨fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩
  · haveI := h.1 a
    infer_instance
  · dsimp only
    rw [h.2.1]
    exact (Over.pullback g).map_id _
  · dsimp only
    rw [h.2.2.1, Functor.map_comp]
  · dsimp only
    rw [h.2.2.2, Functor.map_mul]

theorem isRAct_conj {T : Scheme.{0}} {B C : Over T} [GrpObj B] [GrpObj C] (e : B ≅ C) [IsMonHom e.hom]
    (act : O → (C ⟶ C)) (h : IsRAct C act) : IsRAct B (fun a => e.hom ≫ act a ≫ e.inv) := by
  refine ⟨fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩
  · haveI := h.1 a
    infer_instance
  · simp only [h.2.1, Category.id_comp, Iso.hom_inv_id]
  · simp only [h.2.2.1, Category.assoc, Iso.inv_hom_id_assoc]
  · dsimp only
    rw [h.2.2.2, MonObj.mul_comp, MonObj.comp_mul]

theorem adj_along {H T : Scheme.{0}} {AH : Over H} {AT : Over T} [GrpObj AH] [GrpObj AT] {g : T ⟶ H}
    {χ : AT.left ⟶ AH.left} (w : χ ≫ AH.hom = AT.hom ≫ g) (act : O → (AH ⟶ AH)) (v : O → (AT ⟶ AT))
    (hv : ∀ a, (v a).left ≫ χ = χ ≫ (act a).left) {X : Scheme.{0}} (Q : LB X) (φ₂ : (AH ⊗ AH).left ⟶ X)
    (bar : O → O) (h : Adj AH (Q.pull φ₂) bar act) : Adj AT (Q.pull (sqMap w ≫ φ₂)) bar v := fun a =>
  lbIso_pullPull_along Q φ₂ _ _ (sqMap w ≫ φ₂) _ _ (sqMap w) rfl
    (lift_left_comp_sqMap w _ _ _ _
      (by rw [Over.comp_left, Category.assoc, hv, ← Category.assoc, ← sqMap_fst w, Category.assoc, Over.comp_left])
      (by rw [sqMap_snd]))
    (lift_left_comp_sqMap w _ _ _ _ (by rw [sqMap_fst])
      (by rw [Over.comp_left, Category.assoc, hv, ← Category.assoc, ← sqMap_snd w, Category.assoc, Over.comp_left]))
    (h a)

end Act

end GlobalTheory.EndLoc.ActUnr

namespace GlobalTheory.EndLoc


open ActUnr in
theorem formallyUnramified_actRep : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left)
    (O : Type) [Ring O] (bar : O → O) (R : ActRep A Q bar), IsAbelianScheme A → FormallyUnramified R.π := by
  intro S A _ _ Q O _ bar Rp hA
  refine FormallyUnramified.of_hom_ext _ fun R R₀ q hq hsq g₁ g₂ hi hg ↦ ?_
  let f : Spec R ⟶ S := g₁ ≫ Rp.π
  let AT : Over (Spec R) := (Over.pullback f).obj A
  let ψ : AT.left ⟶ A.left := pullback.fst A.hom f
  have hAT : IsGrpPullback AT A f ψ := isGrpPullback_pullback A f
  have hAbT : IsAbelianScheme AT := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have build : ∀ g : Spec R ⟶ Rp.H, g ≫ Rp.π = f → ∃ (v : O → (AT ⟶ AT)) (χ : AT.left ⟶ Rp.AH.left)
      (φ₂' : (AT ⊗ AT).left ⟶ (A ⊗ A).left),
      IsRAct AT v ∧ IsSquare ψ φ₂' ∧ Adj AT (Q.pull φ₂') bar v ∧ IsGrpPullback AT Rp.AH g χ ∧ χ ≫ Rp.φ = ψ ∧
        ∀ a, (v a).left ≫ χ = χ ≫ (Rp.act a).left := by
    intro g hgf
    have h' : IsGrpPullback ((Over.pullback g).obj Rp.AH) A f (pullback.fst Rp.AH.hom g ≫ Rp.φ) :=
      ((isGrpPullback_pullback Rp.AH g).comp Rp.pb).congr hgf rfl
    obtain ⟨e, he, heφ⟩ := grpPullback_iso hAT h'
    haveI := he
    have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
    let χ : AT.left ⟶ Rp.AH.left := e.hom.left ≫ pullback.fst Rp.AH.hom g
    let v : O → (AT ⟶ AT) := fun a ↦ e.hom ≫ (Over.pullback g).map (Rp.act a) ≫ e.inv
    have hχφ : χ ≫ Rp.φ = ψ := by simp only [χ, Category.assoc]; exact heφ
    have hw : χ ≫ Rp.AH.hom = AT.hom ≫ g := by
      simp only [χ]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      congr 1
      exact Over.w e.hom
    have hv : ∀ a, (v a).left ≫ χ = χ ≫ (Rp.act a).left := fun a ↦ by
      have hm : ((Over.pullback g).map (Rp.act a)).left ≫ pullback.fst Rp.AH.hom g =
          pullback.fst Rp.AH.hom g ≫ (Rp.act a).left := pullback.lift_fst _ _ _
      simp only [v, χ, Over.comp_left, Category.assoc]
      rw [reassoc_of% hie, hm]
    have hR : IsRAct AT v := isRAct_conj e _ (isRAct_pullback g Rp.AH Rp.act Rp.isAct)
    refine ⟨v, χ, sqMap hw ≫ Rp.φ₂, hR, ⟨?_, ?_⟩, adj_along hw Rp.act v hv Q Rp.φ₂ bar Rp.adj,
      Rp.pb.cancel ((hAT.congr hgf.symm hχφ.symm)) hw, hχφ, hv⟩
    · rw [Category.assoc, Rp.sq.1, ← Category.assoc, sqMap_fst, Category.assoc, hχφ]
    · rw [Category.assoc, Rp.sq.2, ← Category.assoc, sqMap_snd, Category.assoc, hχφ]
  obtain ⟨v₁, χ₁, φ₂₁, hR₁, hsq₁, hadj₁, hpb₁, hχ₁φ, hχ₁u⟩ := build g₁ rfl
  obtain ⟨v₂, χ₂, -, hR₂, -, -, hpb₂, hχ₂φ, hχ₂u⟩ := build g₂ hg.symm
  let I : Ideal R := RingHom.ker q.hom
  have hI : IsNilpotent I := ⟨2, hsq⟩
  let j : Sp (R ⧸ I) ⟶ Sp R := spMap (Ideal.Quotient.mk I)
  have hj : j ≫ g₁ = j ≫ g₂ := by
    let ε : (R ⧸ I) ≃+* R₀ := RingHom.quotientKerEquivOfSurjective hq
    have hε : Spec.map q = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ j := by
      rw [← Spec.map_comp]
      congr 1
    haveI : IsIso (CommRingCat.ofHom ε.toRingHom) := ε.toCommRingCatIso.isIso_hom
    rw [hε, Category.assoc, Category.assoc] at hi
    exact (cancel_epi _).1 hi
  have hχ : pullback.fst AT.hom j ≫ χ₁ = pullback.fst AT.hom j ≫ χ₂ := by
    apply Rp.pb.1.hom_ext
    · rw [Category.assoc, Category.assoc, hχ₁φ, hχ₂φ]
    · rw [Category.assoc, Category.assoc, hpb₁.1.w, hpb₂.1.w, pullback.condition_assoc, pullback.condition_assoc, hj]
  have hv : ∀ a, v₁ a = v₂ a := fun a ↦ by
    haveI := hR₁.1 a
    haveI := hR₂.1 a
    refine GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq I hI AT AT hAbT (v₁ a) (v₂ a) ?_
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [show ((Over.pullback j).map (v₁ a)).left ≫ pullback.fst AT.hom j =
          pullback.fst AT.hom j ≫ (v₁ a).left from pullback.lift_fst _ _ _,
        show ((Over.pullback j).map (v₂ a)).left ≫ pullback.fst AT.hom j =
          pullback.fst AT.hom j ≫ (v₂ a).left from pullback.lift_fst _ _ _]
      apply hAT.1.hom_ext
      · calc (pullback.fst AT.hom j ≫ (v₁ a).left) ≫ ψ
            = pullback.fst AT.hom j ≫ (v₁ a).left ≫ χ₁ ≫ Rp.φ := by rw [hχ₁φ, Category.assoc]
          _ = pullback.fst AT.hom j ≫ χ₁ ≫ (Rp.act a).left ≫ Rp.φ := by rw [reassoc_of% (hχ₁u a)]
          _ = pullback.fst AT.hom j ≫ χ₂ ≫ (Rp.act a).left ≫ Rp.φ := by rw [reassoc_of% hχ]
          _ = pullback.fst AT.hom j ≫ (v₂ a).left ≫ χ₂ ≫ Rp.φ := by rw [reassoc_of% (hχ₂u a)]
          _ = (pullback.fst AT.hom j ≫ (v₂ a).left) ≫ ψ := by rw [hχ₂φ, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w (v₁ a), Over.w (v₂ a)]
    · rw [show ((Over.pullback j).map (v₁ a)).left ≫ pullback.snd AT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _,
        show ((Over.pullback j).map (v₂ a)).left ≫ pullback.snd AT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _]
  obtain ⟨g, -, hg'⟩ := Rp.rep (Spec R) f AT ψ φ₂₁ v₁ hAT hsq₁ hR₁ hadj₁
  have e1 := hg' g₁ ⟨rfl, χ₁, hpb₁, hχ₁φ, hχ₁u⟩
  have e2 := hg' g₂ ⟨hg.symm, χ₂, hpb₂, hχ₂φ, fun a ↦ by rw [hv a]; exact hχ₂u a⟩
  rw [e1, e2]

end GlobalTheory.EndLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyUnramified_adjointRingAction_scheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left) (O : Type) [Ring O] (bar : O → O) (R : ActRep A Q bar), IsAbelianScheme A → FormallyUnramified R.π := by
  first | exact @GlobalTheory.EndLoc.formallyUnramified_actRep | exact GlobalTheory.EndLoc.formallyUnramified_actRep | (intros; apply GlobalTheory.EndLoc.formallyUnramified_actRep; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansion
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.LatValRam

section Sz

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_mul {r₁ r₂ : ℝ} {x y : ℂ} (hx : Sz l lam r₁ x) (hy : Sz l lam r₂ y) :
    Sz l lam (r₁ + r₂) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (hx : Sz l lam r x) (h : r ≤ r') : Sz l lam r' x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem norm_nat_le (n : ℕ) : ‖(n : ℂ_[l])‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))

theorem sz_nat (n : ℕ) : Sz l lam 0 (n : ℂ) := by
  refine ⟨natCast_mem _ n, ?_⟩
  have : (⟨(n : ℂ), natCast_mem _ n⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) := rfl
  rw [this, map_natCast, Real.rpow_zero]
  exact norm_nat_le n

theorem sz_one : Sz l lam 0 1 := by simpa using sz_nat (l := l) (lam := lam) 1

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_neg_one_pow_mul {r : ℝ} {x : ℂ} (n : ℕ) (hx : Sz l lam r x) : Sz l lam r ((-1) ^ n * x) := by
  rcases neg_one_pow_eq_or ℂ n with h | h
  · rwa [h, one_mul]
  · rw [h, neg_one_mul]; exact sz_neg hx

theorem sz_pow {r : ℝ} {x : ℂ} (hx : Sz l lam r x) (n : ℕ) : Sz l lam (n * r) (x ^ n) := by
  induction n with
  | zero => simpa using sz_one (l := l) (lam := lam)
  | succ n ih =>
    have := sz_mul ih hx
    rw [pow_succ]
    convert this using 1
    push_cast; ring

theorem sz_prod {ι : Type} (s : Finset ι) (r : ι → ℝ) (x : ι → ℂ) (h : ∀ i ∈ s, Sz l lam (r i) (x i)) :
    Sz l lam (∑ i ∈ s, r i) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sz_one (l := l) (lam := lam)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact sz_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Sz

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := by
  have hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ i)
    have e : i = j := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
    subst e
    have hr : ComplexEmbedding.IsReal (φ i) := ComplexEmbedding.isReal_iff.mpr hij.symm
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  have hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) hij
      · simp only [Sum.elim_inl] at hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij)]
      · exact absurd hij (hreal i j)
      · exact absurd hij.symm (hreal j i)
      · simp only [Sum.elim_inr] at hij
        have hij' : φ i = φ j := by
          simpa using congrArg ComplexEmbedding.conjugate hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij')]
    · intro σ
      obtain ⟨k, hk, -⟩ := h σ
      rcases hk with hk | hk
      · exact ⟨Sum.inl k, hk.symm⟩
      · exact ⟨Sum.inr k, hk.symm⟩
  have h1 := Fintype.card_of_bijective hbij
  rw [Fintype.card_sum, NumberField.Embeddings.card E ℂ] at h1
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  omega

theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  induction n with
  | zero =>
    have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hk]; ring
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [this, Real.Gamma_nat_eq_factorial]
  | succ n ih =>
    have hpos : (k : ℝ) + n ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]
    ring

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

theorem per_factor (a b Ω r π : ℂ) (k n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hΩ : Ω ≠ 0) (hr : r ≠ 0) (hpi : π ≠ 0)
    (f : ℂ) (hf : f ≠ 0) :
    (b / a) ^ n / (a ^ k * f) * (f * ((a * b * r / (2 * π))⁻¹) ^ n * (a / Ω) ^ (k + 2 * n)) =
      (2 * π / r) ^ n / Ω ^ (k + 2 * n) := by
  simp only [inv_div, div_pow, pow_add, pow_mul, mul_pow]
  have h1 : a ^ n ≠ 0 := pow_ne_zero _ ha
  have h2 : b ^ n ≠ 0 := pow_ne_zero _ hb
  have h3 : r ^ n ≠ 0 := pow_ne_zero _ hr
  have h4 : Ω ^ k ≠ 0 := pow_ne_zero _ hΩ
  have h5 : (Ω ^ 2) ^ n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hΩ)
  have h6 : a ^ k ≠ 0 := pow_ne_zero _ ha
  field_simp
  ring

theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl


open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (ValGe_vp betaBound_vp c_vp cE_vp a0 n_vp) in
theorem latIntRam : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → Expansion → LatIntRam := by
  intro hSt hEx E _ _ _ _ I _ d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy hc κ S hS
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  rw [GlobalTheory.T.powerIntegralValuationLowerBound_iff_forall_embedding]
  intro lam
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)
  have hΩ0 : Ω ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ (by rw [← hΩ]; simp)
  obtain ⟨a, b, hab, hT⟩ := hEx E I d φ s hF hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy hc lam Ω hΩ
  have hCM : IsCMType φ := hF.2.2.2.2.2.2.1
  have hcard := card_eq_finrank hCM
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := hcard ▸ hF.2.2.2.2.2.1
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  have hTg := hT g κ u hg hu
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hF.1.pos)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hper : ∀ i, (b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ)) *
      (((κ i).factorial : ℂ) * ((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
        (a i / Ω) ^ (2 * s + 2 * κ i)) =
      (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i) := by
    intro i
    exact per_factor _ _ _ _ _ _ _ (hab i).1 (hab i).2.1 hΩ0 hsd hpi _ (by exact_mod_cast (Nat.factorial_pos _).ne')
  have hX : ((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ =
      (-1) ^ (∑ i, κ i) * ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 *
        ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))))) *
        ∏ i, (((κ i).factorial : ℂ) * ((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
          (a i / Ω) ^ (2 * s + 2 * κ i)) := by
    have hQF := Finset.prod_congr (s₁ := (Finset.univ : Finset I)) rfl (fun i _ => hper i)
    have hR : ∏ i, (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ κ i / Ω ^ (2 * s + 2 * κ i) =
        (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) / Ω ^ (Fintype.card I • (2 * s) + 2 * ∑ i, κ i) := by
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum]
    have hM : Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ = Fintype.card I • (2 * s) + 2 * ∑ i, κ i := by
      simp [Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK, mul_comm]
    have hsq : ((-1 : ℂ) ^ (∑ i, κ i)) * (-1) ^ (∑ i, κ i) = 1 := by
      rw [← mul_pow]; norm_num
    rw [hDg, risingFactor_eq, cmPeriodConstant_eq_of_card_cmType hcard d s hs κ, hM]
    calc _ = ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℝ) : ℂ) *
          (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * S 0 *
          ((2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) /
            Ω ^ (Fintype.card I • (2 * s) + 2 * ∑ i, κ i)) := by
            push_cast; ring
      _ = _ := by
        rw [← hR, ← hQF, Finset.prod_mul_distrib]
        linear_combination (-(((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℝ) : ℂ) *
          (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) * S 0 *
          (∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ)))) *
          (∏ i, (((κ i).factorial : ℂ) * ((a i * b i * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))⁻¹) ^ κ i *
              (a i / Ω) ^ (2 * s + 2 * κ i))))) * hsq
  have hSzX : Sz l lam (betaBound_vp d s κ 𝔣 z l / 12)
      (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) := by
    rw [hX, mul_assoc]
    refine sz_neg_one_pow_mul _ (sz_mono (sz_mul hTg (sz_prod Finset.univ
      (fun i => (0 + ((κ i : ℕ) : ℝ) * (c_vp 𝔣 l + if l = d then 1 / 2 else 0)) +
        ((2 * s + 2 * κ i : ℕ) : ℝ) * (a0 𝔣 l : ℝ)) _
      (fun i _ => sz_mul (sz_mul (sz_nat _) (sz_pow (hab i).2.2.2 _)) (sz_pow (hab i).2.2.1 _)))) (le_of_eq ?_))
    simp only [betaBound_vp, n_vp, if_neg hc, Formalism.PairingDivisionLocalBalance.nl, Formalism.PairingDivisionLocalBalance.wtM, Formalism.PairingDivisionLocalBalance.absK]
    push_cast
    simp only [zero_add, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  have hβ : beta E d s κ Λ (S 0) = (((C0 E d (2 * s) κ : ℝ) : ℂ) * S 0 / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12 := by
    rw [beta, div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm 12]
  rw [hβ]
  convert sz_pow hSzX 12 using 1
  push_cast
  ring

end GlobalTheory.LatValRam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansionStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → Expansion → LatIntRam := by
  first | exact @GlobalTheory.LatValRam.latIntRam | exact GlobalTheory.LatValRam.latIntRam | (intros; apply GlobalTheory.LatValRam.latIntRam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrameIntegers

theorem isFrame_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → IsFrame p C (RingHom.id O) := by
  intro p hp C _ _ _ v O _ _ hnu _ _ hv
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hmapp : algebraMap O C (p : O) = (p : C) := map_natCast _ _
  have hvp1 : v (p : C) < 1 := by
    have h1 := hv.map_le_one (p : O)
    rw [hmapp] at h1
    rcases lt_or_eq_of_le h1 with h | h
    · exact h
    · exact absurd (hv.isUnit_of_one (by rw [hmapp]; exact Ne.isUnit hpC) (by rw [hmapp]; exact h)) hnu.out
  have hint : ∀ z : ℤ, v (z : C) ≤ 1 := by
    intro z
    have := hv.map_le_one (z : O)
    rwa [map_intCast] at this
  refine ⟨Function.surjective_id, hv.hom_inj, ?_, Ne.isUnit hpC, ?_, ?_, ?_, inferInstance⟩
  · intro q
    obtain ⟨k, hk⟩ : ∃ k : ℕ, v (p : C) ^ k * v q ≤ 1 := by
      by_cases hq : v q = 0
      · exact ⟨0, by simp [hq]⟩
      · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr (pos_iff_ne_zero.mpr hq)) hvp1
        refine ⟨k, ?_⟩
        calc v (p : C) ^ k * v q ≤ (v q)⁻¹ * v q := mul_le_mul_of_nonneg_right hk.le zero_le
          _ = 1 := inv_mul_cancel₀ hq
    have hle : v ((p : C) ^ k * q) ≤ 1 := by rw [map_mul, map_pow]; exact hk
    obtain ⟨b, hb⟩ := hv.exists_of_le_one hle
    exact ⟨k, b, hb.symm⟩
  · intro n hn
    have hB : (n : C) * (Nat.gcdA n p : C) + (p : C) * (Nat.gcdB n p : C) = 1 := by
      have h := Nat.gcd_eq_gcd_ab n p
      rw [Nat.Coprime.gcd_eq_one hn] at h
      exact_mod_cast h.symm
    have hvn : v (n : C) = 1 := by
      have h1 : v (n : C) ≤ 1 := by exact_mod_cast hint n
      by_contra hne
      have hlt : v (n : C) < 1 := lt_of_le_of_ne h1 hne
      have a1 : v ((n : C) * (Nat.gcdA n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt
      have a2 : v ((p : C) * (Nat.gcdB n p : C)) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hvp1
      have := Valuation.map_add_lt v a1 a2
      rw [hB, map_one] at this
      exact lt_irrefl _ this
    have hnC : (n : C) ≠ 0 := by
      intro h; rw [h, map_zero] at hvn; exact zero_ne_one hvn
    have hmapn : algebraMap O C (n : O) = (n : C) := map_natCast _ _
    exact hv.isUnit_of_one (by rw [hmapn]; exact Ne.isUnit hnC) (by rw [hmapn]; exact hvn)
  · intro x hx
    simp only [RingHom.id_apply] at hx
    subst hx
    exact ⟨0, rfl, by simp [hp0]⟩
  · intro a ha
    have hpO : (p : O) ≠ 0 := by
      intro h; apply hpC; rw [← hmapp, h, map_zero]
    exact (mul_eq_zero.mp ha).resolve_left hpO

end GlobalTheory.FrameIntegers
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegersStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → IsFrame p C (RingHom.id O) := by
  first | exact @GlobalTheory.FrameIntegers.isFrame_integers | exact GlobalTheory.FrameIntegers.isFrame_integers | (intros; apply GlobalTheory.FrameIntegers.isFrame_integers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.ValEx

theorem nat_bound (p N m : ℕ) (hp : 2 ≤ p) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ a v : ℕ, M ≤ a → p ^ v ≤ a → N * (m + v) ≤ a := by
  set T := 2 * N + m + 1 with hT
  have hT2 : T < 2 ^ T := Nat.lt_two_pow_self
  have hA : ∀ v, 2 * T ≤ v → N * (m + v) ≤ 2 ^ v := by
    intro v hv
    induction v, hv using Nat.le_induction with
    | base =>
      have hNT : N ≤ T := by omega
      have h1 : N * (m + 2 * T) ≤ T * T := by nlinarith [Nat.mul_le_mul_right m hNT]
      have h2 : T * T ≤ 2 ^ T * 2 ^ T := Nat.mul_le_mul hT2.le hT2.le
      calc N * (m + 2 * T) ≤ T * T := h1
        _ ≤ 2 ^ T * 2 ^ T := h2
        _ = 2 ^ (2 * T) := by rw [← pow_add, two_mul]
    | succ v hv ih =>
      have h3 : N ≤ 2 ^ v := by
        have : 2 ^ T ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [pow_succ]; nlinarith
  refine ⟨N * (m + 2 * T) + 1, by omega, fun a v ha hv => ?_⟩
  by_cases hvK : 2 * T ≤ v
  · calc N * (m + v) ≤ 2 ^ v := hA v hvK
      _ ≤ p ^ v := Nat.pow_le_pow_left hp v
      _ ≤ a := hv
  · have : N * (m + v) ≤ N * (m + 2 * T) := Nat.mul_le_mul_left _ (by omega)
    omega

def img (B : Type) {Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (p m : ℕ) : AddSubgroup Q where
  carrier := {x | ∃ b : B, x = algebraMap B Q ((p : B) ^ m * b)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [mul_add, map_add (f := _)]⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by rw [mul_neg, map_neg]⟩

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type} [Fintype σ] [DecidableEq σ]

def box (σ : Type) [Fintype σ] (n : ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => n

def psum (z : σ → B) (f : MvPowerSeries σ Q) (n : ℕ) : Q :=
  MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q (box σ n) f)

theorem psum_eq (z : σ → B) (f : MvPowerSeries σ Q) (n : ℕ) :
    psum z f n = ∑ α ∈ Finset.Iic (box σ n),
      coeff α f * algebraMap B Q (α.prod fun i e => z i ^ e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [psum, trunc', truncFinset_apply, map_sum, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_finsuppProd]
  simp [map_pow]

theorem exists_lt_of_not_mem_box {n : ℕ} {α : σ →₀ ℕ} (h : α ∉ Finset.Iic (box σ n)) :
    ∃ i, n < α i := by
  simpa [box, Finset.mem_Iic, Finsupp.le_def] using h

theorem box_mono {n n' : ℕ} (h : n ≤ n') : Finset.Iic (box σ n) ⊆ Finset.Iic (box σ n') :=
  Finset.Iic_subset_Iic.2 (Finsupp.le_def.2 fun i => by simpa [box] using h)

theorem term_mem (p : ℕ) [hp : Fact p.Prime] (hunit : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B))
    (z : σ → B) (hz : ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) (m : ℕ) :
    ∃ M : ℕ, ∀ (α : σ →₀ ℕ) (i : σ), M ≤ α i →
      coeff α f * algebraMap B Q (α.prod fun i e => z i ^ e) ∈ img B p m := by
  choose Nf hNf using hz
  set N := ∑ i, Nf i
  have hN : ∀ i, (p : B) ∣ z i ^ N := fun i => (hNf i).trans
    (pow_dvd_pow _ (Finset.single_le_sum (fun j _ => Nat.zero_le (Nf j)) (Finset.mem_univ i)))
  obtain ⟨M, hM1, hM⟩ := nat_bound p N m hp.out.two_le
  refine ⟨M, fun α i hi => ?_⟩
  have ha0 : α i ≠ 0 := by omega
  obtain ⟨v, u, hu, hau⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 p hp.out.ne_one
  have hcop : Nat.Coprime u p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu)
  obtain ⟨U, hU⟩ := hunit u hcop
  have hle : N * (m + v) ≤ α i := hM (α i) v hi (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) ⟨u, hau⟩)
  have hdz : (p : B) ^ (m + v) ∣ z i ^ (α i) :=
    (pow_dvd_pow_of_dvd (hN i) (m + v)).trans (by rw [← pow_mul]; exact pow_dvd_pow _ hle)
  have hprod : z i ^ (α i) ∣ α.prod fun j e => z j ^ e := by
    have hi' : i ∈ α.support := Finsupp.mem_support_iff.2 ha0
    unfold Finsupp.prod
    exact Finset.dvd_prod_of_mem (fun j => z j ^ α j) hi'
  obtain ⟨r, hr⟩ := hdz.trans hprod
  obtain ⟨b, -, hb⟩ := hf α i
  refine ⟨b * ↑U⁻¹ * r, ?_⟩
  rw [hr]
  rw [hau] at hb
  have hUU : (u : Q) * algebraMap B Q (↑U⁻¹ : B) = 1 := by
    rw [← map_natCast (algebraMap B Q), ← map_mul, ← hU, Units.mul_inv, map_one]
  simp only [map_mul, map_pow, map_natCast]
  push_cast at hb
  linear_combination ((p : Q) ^ m * algebraMap B Q (↑U⁻¹ : B) * algebraMap B Q r) * hb -
    (coeff α f * (p : Q) ^ (m + v) * algebraMap B Q r) * hUU

theorem cauchy (p : ℕ) [Fact p.Prime] (hunit : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B))
    (z : σ → B) (hz : ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) (m : ℕ) :
    ∃ M : ℕ, ∀ n n' : ℕ, M ≤ n → n ≤ n' → psum z f n' - psum z f n ∈ img B p m := by
  obtain ⟨M, hM⟩ := term_mem p hunit z hz f hf m
  refine ⟨M, fun n n' hn hnn' => ?_⟩
  rw [psum_eq, psum_eq, ← Finset.sum_sdiff (box_mono hnn'), add_sub_cancel_right]
  refine AddSubgroup.sum_mem _ fun α hα => ?_
  obtain ⟨i, hi⟩ := exists_lt_of_not_mem_box (Finset.mem_sdiff.1 hα).2
  exact hM α i (by omega)

end GlobalTheory.QLog.ValEx

namespace GlobalTheory.QLog


open ValEx in
theorem existsUnique_hasVal_of_dIn : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ]
    [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) →
    ∀ f : MvPowerSeries σ Q, DIn (⊤ : Ideal B) f → ∃! q : Q, HasVal p z f q := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz f hf
  haveI := hF.complete
  have hI : ∀ (k : ℕ) (x : B), x ∈ ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B) ↔
      ∃ e, x = (p : B) ^ k * e := by
    intro k x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩; exact ⟨e, by rw [← he, mul_comm]⟩
    · rintro ⟨e, he⟩; exact ⟨e, by rw [he, mul_comm]⟩
  choose M hM using cauchy p hF.unit_coprime z hz f hf
  set K : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1), M k with hK
  have hMK : ∀ m, M m ≤ K m := fun m =>
    Finset.single_le_sum (fun k _ => Nat.zero_le (M k)) (Finset.mem_range.2 (Nat.lt_succ_self m))
  have hKmono : Monotone K := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  have h0 : ∀ n, psum z f (K n) - psum z f (K 0) ∈ img B p 0 := fun n =>
    hM 0 (K 0) (K n) (hMK 0) (hKmono (Nat.zero_le n))
  choose b hb using h0
  have hcau : ∀ {k n : ℕ}, k ≤ n →
      b k ≡ b n [SMOD ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B)] := by
    intro k n hkn
    rw [SModEq.sub_mem, hI]
    obtain ⟨e, he⟩ := hM k (K k) (K n) (hMK k) (hKmono hkn)
    refine ⟨-e, hF.inj ?_⟩
    have hbk := hb k
    have hbn := hb n
    simp only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbk hbn he ⊢
    linear_combination hbn - hbk - he
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' b hcau
  have huniq : ∀ q1 q2, HasVal p z f q1 → HasVal p z f q2 → q1 = q2 := by
    intro q1 q2 h1 h2
    have hd : ∀ m, ∃ e : B, q1 - q2 = algebraMap B Q ((p : B) ^ m * e) := by
      intro m
      obtain ⟨N1, hN1⟩ := h1 m
      obtain ⟨N2, hN2⟩ := h2 m
      obtain ⟨e1, he1⟩ := hN1 (max N1 N2) (le_max_left _ _)
      obtain ⟨e2, he2⟩ := hN2 (max N1 N2) (le_max_right _ _)
      exact ⟨e1 - e2, by rw [mul_sub, map_sub, ← he1, ← he2]; ring⟩
    obtain ⟨c, hc⟩ := hd 0
    have hc0 : c = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {(p : B)}) c fun n => ?_
      rw [SModEq.sub_mem, sub_zero, hI]
      obtain ⟨e, he⟩ := hd n
      exact ⟨e, hF.inj (by rw [← he, hc, pow_zero, one_mul])⟩
    rw [← sub_eq_zero, hc, hc0, mul_zero, map_zero]
  have hq : HasVal p z f (psum z f (K 0) + algebraMap B Q L) := fun m => ⟨K m, fun N' hN' => by
    obtain ⟨e1, he1⟩ := (hI m _).1 (SModEq.sub_mem.1 (hL m))
    obtain ⟨e2, he2⟩ := hM m (K m) N' (hMK m) hN'
    have hbm := hb m
    have he1' := congrArg (algebraMap B Q) he1
    refine ⟨-e1 - e2, ?_⟩
    change psum z f (K 0) + algebraMap B Q L - psum z f N' = _
    simp only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbm he1' he2 ⊢
    linear_combination -hbm - he1' - he2⟩
  exact ⟨_, hq, fun q' hq' => huniq _ _ hq' hq⟩

end GlobalTheory.QLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffsStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_hasPAdicPowerSeriesValue_of_diffCoeffs : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ f : MvPowerSeries σ Q, DIn (⊤ : Ideal B) f → ∃! q : Q, HasVal p z f q := by
  first | exact @GlobalTheory.QLog.existsUnique_hasVal_of_dIn | exact GlobalTheory.QLog.existsUnique_hasVal_of_dIn | (intros; apply GlobalTheory.QLog.existsUnique_hasVal_of_dIn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

open Classical in
theorem coeff_prod_pow_of_embedding {σ τ R : Type} [CommRing R] (j : σ → τ) (hj : Function.Injective j)
    (a : τ → MvPowerSeries σ R) (ha : ∀ s, a (j s) = X s) (h0 : ∀ t, t ∉ Set.range j → a t = 0)
    (d : τ →₀ ℕ) (α : σ →₀ ℕ) :
    coeff α (d.prod fun t e => a t ^ e) = if d = α.mapDomain j then 1 else 0 := by
  classical
  by_cases h : ∀ t, t ∉ Set.range j → d t = 0
  · obtain ⟨β, rfl⟩ := (Finsupp.mem_range_mapDomain_iff j hj d).mpr h
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    simp only [ha]
    rw [Finsupp.prod]
    simp only [X_pow_eq]
    rw [prod_monomial, Finset.prod_const_one]
    have hs : (∑ i ∈ β.support, Finsupp.single i (β i)) = β := Finsupp.sum_single β
    rw [hs, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hj).eq_iff, eq_comm]
  · push_neg at h
    obtain ⟨t, ht, hdt⟩ := h
    have hne : d ≠ α.mapDomain j := by
      intro hd
      have : d ∈ Set.range (Finsupp.mapDomain j) := ⟨α, hd.symm⟩
      exact hdt (((Finsupp.mem_range_mapDomain_iff j hj d).mp this) t ht)
    rw [if_neg hne, Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hdt)
      (by rw [h0 t ht, zero_pow hdt]), map_zero]

theorem coeff_subst_of_embedding {σ τ R : Type} [CommRing R] [Finite τ] (j : σ → τ)
    (hj : Function.Injective j)
    (a : τ → MvPowerSeries σ R) (ha : ∀ s, a (j s) = X s) (h0 : ∀ t, t ∉ Set.range j → a t = 0)
    (g : MvPowerSeries τ R) (α : σ →₀ ℕ) :
    coeff α (subst a g) = coeff (α.mapDomain j) g := by
  classical
  have hsub : HasSubst a := hasSubst_of_constantCoeff_zero (fun t => by
    by_cases ht : t ∈ Set.range j
    · obtain ⟨s, rfl⟩ := ht
      rw [ha]; exact constantCoeff_X s
    · rw [h0 t ht]; exact map_zero _)
  rw [coeff_subst hsub, finsum_eq_single _ (α.mapDomain j)]
  · rw [coeff_prod_pow_of_embedding j hj a ha h0, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    rw [coeff_prod_pow_of_embedding j hj a ha h0, if_neg hd, smul_zero]

theorem coeff_subst_restrict_sum {R ι κ : Type} [CommRing R] [Fintype ι] [Fintype κ]
    (g : MvPowerSeries (ι ⊕ κ) R) :
    (∀ α : ι →₀ ℕ, coeff α (subst (Sum.elim (fun i => (X i : MvPowerSeries ι R)) (fun _ => 0)) g) =
      coeff (α.mapDomain Sum.inl) g) ∧
    (∀ α : κ →₀ ℕ, coeff α (subst (Sum.elim (fun _ => 0) (fun i => (X i : MvPowerSeries κ R))) g) =
      coeff (α.mapDomain Sum.inr) g) := by
  refine ⟨fun α => coeff_subst_of_embedding Sum.inl Sum.inl_injective _ (fun _ => rfl) ?_ g α,
    fun α => coeff_subst_of_embedding Sum.inr Sum.inr_injective _ (fun _ => rfl) ?_ g α⟩
  · rintro (i | k) h
    · exact absurd ⟨i, rfl⟩ h
    · rfl
  · rintro (i | k) h
    · rfl
    · exact absurd ⟨k, rfl⟩ h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariablesStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_restrict_sum_variables : ∀ {R ι κ : Type} [CommRing R] [Fintype ι] [Fintype κ] (g : MvPowerSeries (ι ⊕ κ) R), (∀ α : ι →₀ ℕ, coeff α (subst (Sum.elim (fun i => (X i : MvPowerSeries ι R)) (fun _ => 0)) g) = coeff (α.mapDomain Sum.inl) g) ∧ (∀ α : κ →₀ ℕ, coeff α (subst (Sum.elim (fun _ => 0) (fun i => (X i : MvPowerSeries κ R))) g) = coeff (α.mapDomain Sum.inr) g) := by
  first | exact @GlobalTheory.coeff_subst_restrict_sum | exact GlobalTheory.coeff_subst_restrict_sum | (intros; apply GlobalTheory.coeff_subst_restrict_sum <;> assumption)
end
end
