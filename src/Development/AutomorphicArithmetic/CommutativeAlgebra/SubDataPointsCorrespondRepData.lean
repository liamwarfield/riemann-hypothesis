module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyKernelPointsIffOfIsPIsog
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentable

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIsoOfPIsogenyKernelEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

section SlopeTestRemainingChoices
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace UpperTheory.EvaluationPowerKernel

variable {S : Scheme.{0}}

private theorem eq_one_of_geom {Z B : Over S} [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (g : Z ⟶ B) (hg : g ^ n = 1)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ Z), y ≫ g = 1) : g = 1 := by
  obtain ⟨_, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hn
  haveI := hfin
  haveI := het
  haveI := GlobalTheory.HTTorsRep.mono_ι (A := B) n
  have hw : g ≫ mulN B n = toUnit Z ≫ η := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, comp_pow, Category.comp_id, hg]
    rfl
  let g' : Z ⟶ torsion B n := pullback.lift g (toUnit Z) hw
  have hg' : g' ≫ torsion.ι B n = g := pullback.lift_fst _ _ _
  let e : Z ⟶ torsion B n := toUnit Z ≫ GlobalTheory.HTTorsRep.torsEta n
  have he : e ≫ torsion.ι B n = 1 := by
    have hEta : GlobalTheory.HTTorsRep.torsEta n ≫ torsion.ι B n = η[B] := pullback.lift_fst _ _ _
    simp only [e, Category.assoc, hEta]
    rfl
  have hrange : Set.range (𝟙 Z.left) ⊆ Set.range (GlobalTheory.FinEt.agreeι g' e) := by
    have := GlobalTheory.LevCover.range_subset_of_geom (𝟙 Z) (Set.range (GlobalTheory.FinEt.agreeι g' e))
      (fun k _ _ x y => by
        rw [Category.comp_id, ← GlobalTheory.FinEt.comp_eq_comp_iff_range, ← Over.comp_left, ← Over.comp_left]
        congr 1
        rw [← cancel_mono (torsion.ι B n), Category.assoc, Category.assoc, hg', he, h k x y]
        simp)
    simpa using this
  have key : g' = e := by
    apply Over.OverMorphism.ext
    have h2 := (GlobalTheory.FinEt.comp_eq_comp_iff_range g' e (𝟙 Z.left)).2 hrange
    simpa using h2
  rw [← hg', key, he]

end UpperTheory.EvaluationPowerKernel

namespace UpperTheory.EvaluationPowerKernel

variable {S : Scheme.{0}}

private theorem comp_eq_one_of_ker {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (hC : IsAbelianScheme C) {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (ψ₁ : A ⟶ B) (ψ₁' : B ⟶ A) (ψ₂ : A ⟶ C) [IsMonHom ψ₁'] [IsMonHom ψ₂] (h1 : ψ₁ ≫ ψ₁' = (𝟙 A) ^ n)
    (hg : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ A), g ≫ ψ₁ = 1 → g ≫ ψ₂ = 1)
    {Z : Over S} (x : Z ⟶ A) (hx : x ≫ ψ₁ = 1) : x ≫ ψ₂ = 1 := by
  have hxn : x ^ n = 1 := by
    have e : x ≫ (𝟙 A) ^ n = x ^ n := by rw [comp_pow, Category.comp_id]
    rw [← e, ← h1, ← Category.assoc, hx]
    simp
  apply eq_one_of_geom hC hn (x ≫ ψ₂)
  · rw [← pow_comp, hxn]
    simp
  · intro k _ _ s y
    rw [← Category.assoc]
    apply hg k s (y ≫ x)
    rw [Category.assoc, hx]
    simp

private theorem exists_factor {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hC : IsAbelianScheme C)
    {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤)))
    (ψ₁ : A ⟶ B) (ψ₁' : B ⟶ A) (ψ₂ : A ⟶ C) [IsMonHom ψ₁] [IsMonHom ψ₁'] [IsMonHom ψ₂]
    (h1 : ψ₁ ≫ ψ₁' = (𝟙 A) ^ n) (h2 : ψ₁' ≫ ψ₁ = (𝟙 B) ^ n)
    (hker : ∀ (Z : Over S) (x : Z ⟶ A), x ≫ ψ₁ = 1 → x ≫ ψ₂ = 1) :
    ∃ φ : B ⟶ C, IsMonHom φ ∧ ψ₁ ≫ φ = ψ₂ := by
  obtain ⟨_, _, _, _⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S A n hA hn
  obtain ⟨_, _, _, _⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S B n hB hn
  haveI : EffectiveEpi (Over.Hom.left ((𝟙 A) ^ n)) := inferInstance
  haveI : EffectiveEpi (Over.Hom.left ((𝟙 B) ^ n)) := inferInstance
  have e1 : ψ₁.left ≫ ψ₁'.left = Over.Hom.left ((𝟙 A) ^ n) := by rw [← Over.comp_left, h1]
  have e2 : ψ₁'.left ≫ ψ₁.left = Over.Hom.left ((𝟙 B) ^ n) := by rw [← Over.comp_left, h2]
  haveI : Epi (ψ₁.left ≫ ψ₁'.left) := by rw [e1]; infer_instance
  haveI : Epi ψ₁'.left := epi_of_epi ψ₁.left ψ₁'.left
  haveI : EffectiveEpi (ψ₁'.left ≫ ψ₁.left) := by rw [e2]; infer_instance
  haveI : EffectiveEpi ψ₁.left := effectiveEpi_of_effectiveEpi_epi_comp ψ₁.left ψ₁'.left
  have compat : ∀ {W : Scheme} (a b : W ⟶ A.left), a ≫ ψ₁.left = b ≫ ψ₁.left →
      a ≫ ψ₂.left = b ≫ ψ₂.left := by
    intro W a b hab
    have hb : b ≫ A.hom = a ≫ A.hom := by
      rw [← Over.w ψ₁, ← Category.assoc, ← hab, Category.assoc]
    let Z : Over S := Over.mk (a ≫ A.hom)
    let a' : Z ⟶ A := Over.homMk a rfl
    let b' : Z ⟶ A := Over.homMk b hb
    have q1 : a' ≫ ψ₁ = b' ≫ ψ₁ := by
      ext
      simpa [a', b'] using hab
    have q2 : (a' / b') ≫ ψ₁ = 1 := by
      rw [GrpObj.div_comp, q1, div_self']
    have q3 := hker Z (a' / b') q2
    rw [GrpObj.div_comp, div_eq_one] at q3
    have := congrArg Over.Hom.left q3
    simpa [a', b'] using this
  let φ₀ : B.left ⟶ C.left := EffectiveEpi.desc ψ₁.left ψ₂.left compat
  have hfac : ψ₁.left ≫ φ₀ = ψ₂.left := EffectiveEpi.fac _ _ _
  have hw : φ₀ ≫ C.hom = B.hom := by
    rw [← cancel_epi ψ₁.left, ← Category.assoc, hfac, Over.w, Over.w]
  let φ : B ⟶ C := Over.homMk φ₀ hw
  have hφ : ψ₁ ≫ φ = ψ₂ := by
    ext
    simp [φ, hfac]
  refine ⟨φ, GlobalTheory.rigidity_holds S B C hB hC φ ?_, hφ⟩
  rw [← IsMonHom.one_hom ψ₁, Category.assoc, hφ, IsMonHom.one_hom]

end UpperTheory.EvaluationPowerKernel

namespace UpperTheory.EvaluationPowerKernel

variable {S : Scheme.{0}}

open GlobalTheory.AbDual GlobalTheory.CechPic in
private theorem evc_pow_left {B T Y : Over S} [GrpObj B] {Q : LB (B ⊗ T).left} (hQ : Q.IsLB)
    (hadd : IsAdditive Q) (a : Y ⟶ B) (t : Y ⟶ T) (m : ℕ) : evc hQ (a ^ m) t = m • evc hQ a t := by
  have key := (isAdditive_iff hQ).1 hadd
  induction m with
  | zero => simp [IsAdditive.evc_one hQ hadd]
  | succ k ih => rw [pow_succ, key, ih, succ_nsmul]

open GlobalTheory.AbDual GlobalTheory.CechPic in
private theorem evc_pow_right {B T Y : Over S} [GrpObj B] [GrpObj T] {Q : LB (B ⊗ T).left} (hQ : Q.IsLB)
    (hadd : IsAdditive (swap Q)) (a : Y ⟶ B) (t : Y ⟶ T) (m : ℕ) : evc hQ a (t ^ m) = m • evc hQ a t := by
  have hs : (swap Q).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hQ _
  have key := (isAdditive_iff hs).1 hadd
  rw [← evc_swap hQ hs, ← evc_swap hQ hs]
  induction m with
  | zero => simp [IsAdditive.evc_one hs hadd]
  | succ k ih => rw [pow_succ, key, ih, succ_nsmul]

open GlobalTheory.AbDual GlobalTheory.CechPic in
private theorem pull_square_pow_eq_sq_smul {B : Over S} [GrpObj B] [IsCommMonObj B] {Q : LB (G2 B).left} (hQ : Q.IsLB)
    (a₁ : IsAdditive Q) (s₁ : IsAdditive (swap Q)) (n : ℕ) :
    pull (sq2 ((𝟙 B) ^ n)) (cls Q hQ) = (n * n) • cls Q hQ := by
  have e1 : (cls Q hQ) = evc hQ (fst B B) (snd B B) := by
    simp only [evc]
    have : lift (fst B B) (snd B B) = 𝟙 (B ⊗ B) := by ext <;> simp
    rw [this, Over.id_left, pull_id]
  have e2 : pull (sq2 ((𝟙 B) ^ n)) (cls Q hQ) = evc hQ ((fst B B) ^ n) ((snd B B) ^ n) := by
    simp only [evc, sq2]
    rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id]
  rw [e2, evc_pow_left hQ a₁, evc_pow_right hQ s₁, ← e1, smul_smul, mul_comm]

end UpperTheory.EvaluationPowerKernel

namespace UpperTheory.EvaluationPowerKernel

variable {S : Scheme.{0}}

open GlobalTheory.AbDual GlobalTheory.CechPic in
private theorem lbIso_of_pull {B : Over S} [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) {Q₁ Q₂ : LB (G2 B).left} (h₁ : Q₁.IsLB) (h₂ : Q₂.IsLB)
    (r₁ : ∃ t : (Q₁.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen)
    (r₁' : ∃ t : (Q₁.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (Q₂.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen)
    (r₂' : ∃ t : (Q₂.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen)
    (hp : pull (sq2 ((𝟙 B) ^ n)) (cls Q₁ h₁) = pull (sq2 ((𝟙 B) ^ n)) (cls Q₂ h₂)) : LBIso Q₁ Q₂ := by
  have hM : (Q₁.div Q₂).IsLB := LB.isLB_div h₁ h₂
  have hc' : cls (Q₁.div Q₂) hM = cls Q₁ h₁ - cls Q₂ h₂ := cls_div h₁ h₂ hM
  have ax1 : pull (lift (1 : B ⟶ B) (𝟙 B)).left (cls (Q₁.div Q₂) hM) = 0 := by
    rw [hc', map_sub, ← cls_pull h₁ _ (pull_isLB h₁ _), ← cls_pull h₂ _ (pull_isLB h₂ _),
      (cls_eq_zero_iff _).2 r₁, (cls_eq_zero_iff _).2 r₂, sub_zero]
  have ax2 : pull (lift (𝟙 B) (1 : B ⟶ B)).left (cls (Q₁.div Q₂) hM) = 0 := by
    rw [hc', map_sub, ← cls_pull h₁ _ (pull_isLB h₁ _), ← cls_pull h₂ _ (pull_isLB h₂ _),
      (cls_eq_zero_iff _).2 r₁', (cls_eq_zero_iff _).2 r₂', sub_zero]
  have hadd := additive_of_cube GlobalTheory.CubeTop.cubeTheorem hB hB hM
    ((triv_ev_iff hM 1 (𝟙 B)).2 ax1) ((triv_ev_iff hM (𝟙 B) 1).2 ax2)
  have htors : (n * n) • cls (Q₁.div Q₂) hM = 0 := by
    rw [← pull_square_pow_eq_sq_smul hM hadd.1 hadd.2 n, hc', map_sub, hp, sub_self]
  have hfin : cls (Q₁.div Q₂) hM = 0 := by
    let A' : Over B.left := (Over.pullback B.hom).obj B
    have hA' : IsAbelianScheme A' := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback B.hom B hB
    have hkS : IsUnit ((n * n : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_mul]
      exact hn.mul hn
    have hkB : IsUnit ((n * n : ℕ) : Γ(B.left, ⊤)) := by
      have := hkS.map (B.hom.appTop).hom
      simpa using this
    have e0 : Over.Hom.left (1 : 𝟙_ (Over B.left) ⟶ A') = (lift (1 : B ⟶ B) (𝟙 B)).left := by
      have e1 : (1 : 𝟙_ (Over B.left) ⟶ A') = η := by
        show toUnit _ ≫ η = η
        rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
      have e2 : (1 : B ⟶ B).left = B.hom ≫ (η : 𝟙_ (Over S) ⟶ B).left := by
        show (toUnit B ≫ η).left = _
        rw [Over.comp_left]
        congr 1
      apply pullback.hom_ext
      · have h := GlobalTheory.TorsFrameInt.one_comm (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B B.hom)
        rw [e1, h]
        show _ = (lift (1 : B ⟶ B) (𝟙 B)).left ≫ (fst B B).left
        rw [← Over.comp_left, lift_fst, e2]
      · show _ = (lift (1 : B ⟶ B) (𝟙 B)).left ≫ (snd B B).left
        rw [← Over.comp_left, lift_snd]
        exact Over.w (1 : 𝟙_ (Over B.left) ⟶ A')
    refine (cls_eq_zero_iff hM).2 ?_
    refine GlobalTheory.RigTorsTriv.triv_of_geometricFibres B.left A' hA' (Q₁.div Q₂) hM ?_ (n * n) hkB ?_ ?_
    · refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
      rw [cls_pull hM, e0]
      exact ax1
    · refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
      rw [cls_linComb hM]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
      exact (congrArg (fun z => (n * n) • z) (pull_id (cls (Q₁.div Q₂) hM))).trans htors
    · intro K _ _ y
      refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
      rw [cls_pull hM]
      obtain ⟨_, hfK, _, hsK⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S B (n * n) hB hkS
      obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section
        (pullback.snd (Over.Hom.left ((𝟙 B) ^ (n * n))) y)
      let y' := s ≫ pullback.fst (Over.Hom.left ((𝟙 B) ^ (n * n))) y
      have hy' : y' ≫ Over.Hom.left ((𝟙 B) ^ (n * n)) = y := by
        simp only [y', Category.assoc, pullback.condition]
        rw [← Category.assoc, hs, Category.id_comp]
      let g := pullback.fst A'.hom y
      let W : Over S := Over.mk (g ≫ pullback.fst B.hom B.hom ≫ B.hom)
      let a : W ⟶ B := Over.homMk (g ≫ pullback.fst B.hom B.hom) (by simp [W])
      have hyB : y' ≫ B.hom = y ≫ B.hom := by
        have hw := Over.w ((𝟙 B) ^ (n * n))
        calc y' ≫ B.hom = y' ≫ Over.Hom.left ((𝟙 B) ^ (n * n)) ≫ B.hom := by rw [hw]
          _ = y ≫ B.hom := by rw [← Category.assoc, hy']
      let t : W ⟶ B := Over.homMk (pullback.snd A'.hom y ≫ y') (by
        show (pullback.snd A'.hom y ≫ y') ≫ B.hom = g ≫ pullback.fst B.hom B.hom ≫ B.hom
        rw [Category.assoc, hyB, ← Category.assoc, ← pullback.condition, Category.assoc]
        show g ≫ pullback.snd B.hom B.hom ≫ B.hom = _
        rw [← pullback.condition])
      have htk : t ^ (n * n) = t ≫ (𝟙 B) ^ (n * n) := by
        rw [comp_pow, Category.comp_id]
      have hg : pullback.fst A'.hom y = (lift a (t ^ (n * n))).left := by
        apply pullback.hom_ext
        · show _ = (lift a (t ^ (n * n))).left ≫ (fst B B).left
          rw [← Over.comp_left, lift_fst]
          rfl
        · show _ = (lift a (t ^ (n * n))).left ≫ (snd B B).left
          rw [← Over.comp_left, lift_snd, htk, Over.comp_left]
          show g ≫ A'.hom = (pullback.snd A'.hom y ≫ y') ≫ _
          rw [Category.assoc, hy', pullback.condition]
      rw [hg]
      change evc hM a (t ^ (n * n)) = 0
      rw [evc_pow_right hM hadd.2]
      show (n * n) • pull (lift a t).left (cls (Q₁.div Q₂) hM) = 0
      rw [← map_nsmul, htors, map_zero]
  rw [hc', sub_eq_zero] at hfin
  exact (cls_eq_iff h₁ h₂).1 hfin

end UpperTheory.EvaluationPowerKernel

namespace UpperTheory.EvaluationPowerKernel

variable {S : Scheme.{0}}

private theorem grpSchemeSquareProductMap_comp {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (f : A ⟶ B) (g : B ⟶ C) : sq2 (f ≫ g) = sq2 f ≫ sq2 g := by
  simp only [sq2, ← Over.comp_left]
  congr 1
  ext <;> simp [Category.assoc]

private theorem square_axis_left_comm {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] :
    (lift (1 : A ⟶ A) (𝟙 A)).left ≫ sq2 f = f.left ≫ (lift (1 : B ⟶ B) (𝟙 B)).left := by
  simp only [sq2, ← Over.comp_left]
  congr 1
  ext <;> simp

private theorem square_axis_right_comm {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (f : A ⟶ B) [IsMonHom f] :
    (lift (𝟙 A) (1 : A ⟶ A)).left ≫ sq2 f = f.left ≫ (lift (𝟙 B) (1 : B ⟶ B)).left := by
  simp only [sq2, ← Over.comp_left]
  congr 1
  ext <;> simp

end UpperTheory.EvaluationPowerKernel

open GlobalTheory.CechPic in
private theorem UpperTheory.EvaluationPowerKernel.main :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (c : ℕ) (T : Scheme.{0}) (s : T ⟶ Sp R) (o o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (g : Over.mk x ⟶ o.A), g ≫ ψ₁ = 1 ↔ g ≫ ψ₂ = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 T), ψ₁.left ≫ m.φ = ψ₂.left := by
  intro p _ D R _ b N hN hNp hpR c T s o o₁ o₂ ψ₁ ψ₂ h1 h2 hgeom
  obtain ⟨⟨k, hck⟩, hm1, hact1, heta1, ⟨hpol1⟩, ψ₁', hm1', h11, h12⟩ := h1
  obtain ⟨_, hm2, hact2, heta2, ⟨hpol2⟩, ψ₂', hm2', h21, h22⟩ := h2
  haveI := hm1
  haveI := hm2
  haveI := hm1'
  haveI := hm2'
  have hpT : IsUnit ((p : ℕ) : Γ(T, ⊤)) := by
    have e1 := hpR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    have e2 := e1.map (s.appTop).hom
    simpa using e2
  have hc : IsUnit ((c : ℕ) : Γ(T, ⊤)) := by
    rw [hck, Nat.cast_pow]
    exact hpT.pow k
  have epi1 : ∀ {X : Over T} (u v : o₁.A ⟶ X), ψ₁ ≫ u = ψ₁ ≫ v → u = v := by
    intro X u v huv
    obtain ⟨_, _, _, _⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective T o₁.A c o₁.ab hc
    have e : ((𝟙 o₁.A) ^ c) ≫ u = ((𝟙 o₁.A) ^ c) ≫ v := by
      rw [← h12, Category.assoc, Category.assoc, huv]
    ext
    rw [← cancel_epi (Over.Hom.left ((𝟙 o₁.A) ^ c)), ← Over.comp_left, ← Over.comp_left, e]
  have epi2 : ∀ {X : Over T} (u v : o₂.A ⟶ X), ψ₂ ≫ u = ψ₂ ≫ v → u = v := by
    intro X u v huv
    obtain ⟨_, _, _, _⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective T o₂.A c o₂.ab hc
    have e : ((𝟙 o₂.A) ^ c) ≫ u = ((𝟙 o₂.A) ^ c) ≫ v := by
      rw [← h22, Category.assoc, Category.assoc, huv]
    ext
    rw [← cancel_epi (Over.Hom.left ((𝟙 o₂.A) ^ c)), ← Over.comp_left, ← Over.comp_left, e]
  have ker12 := fun Z x hx => UpperTheory.EvaluationPowerKernel.comp_eq_one_of_ker o₂.ab hc ψ₁ ψ₁' ψ₂ h11
    (fun k _ _ x g hg => (hgeom k x g).1 hg) (Z := Z) x hx
  have ker21 := fun Z x hx => UpperTheory.EvaluationPowerKernel.comp_eq_one_of_ker o₁.ab hc ψ₂ ψ₂' ψ₁ h21
    (fun k _ _ x g hg => (hgeom k x g).2 hg) (Z := Z) x hx
  obtain ⟨φ, hφm, hφ⟩ := UpperTheory.EvaluationPowerKernel.exists_factor o.ab o₁.ab o₂.ab hc ψ₁ ψ₁' ψ₂ h11 h12 ker12
  obtain ⟨φ', hφm', hφ'⟩ := UpperTheory.EvaluationPowerKernel.exists_factor o.ab o₂.ab o₁.ab hc ψ₂ ψ₂' ψ₁ h21 h22 ker21
  haveI := hφm
  have hinv1 : φ ≫ φ' = 𝟙 _ := epi1 _ _ (by rw [← Category.assoc, hφ, hφ', Category.comp_id])
  have hinv2 : φ' ≫ φ = 𝟙 _ := epi2 _ _ (by rw [← Category.assoc, hφ', hφ, Category.comp_id])
  let e : o₁.A ≅ o₂.A := ⟨φ, φ', hinv1, hinv2⟩
  haveI : IsMonHom e.hom := hφm
  refine ⟨⟨φ.left, sq2 φ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso e, ?_, ?_, ?_, ?_⟩, ?_⟩
  · constructor
    · show (lift (fst _ _ ≫ φ) (snd _ _ ≫ φ)).left ≫ (fst o₂.A o₂.A).left = _
      rw [← Over.comp_left, lift_fst, Over.comp_left]
    · show (lift (fst _ _ ≫ φ) (snd _ _ ≫ φ)).left ≫ (snd o₂.A o₂.A).left = _
      rw [← Over.comp_left, lift_snd, Over.comp_left]
  · intro c'
    have : o₁.act.act c' ≫ φ = φ ≫ o₂.act.act c' := by
      apply epi1
      rw [← Category.assoc, ← hact1, Category.assoc, hφ, hact2, ← Category.assoc, hφ]
    rw [← Over.comp_left, this, Over.comp_left]
  · have hQ2 : (o₂.P.pull (sq2 φ)).IsLB := pull_isLB o₂.isLB _
    refine UpperTheory.EvaluationPowerKernel.lbIso_of_pull o₁.ab hc o₁.isLB hQ2 o₁.rig₁ o₁.rig₂ ?_ ?_ ?_
    · refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ2 _)).1 ?_
      rw [GlobalTheory.CechPic.cls_pull hQ2, GlobalTheory.CechPic.cls_pull o₂.isLB, ← GlobalTheory.CechPic.pull_comp,
        UpperTheory.EvaluationPowerKernel.square_axis_left_comm φ, GlobalTheory.CechPic.pull_comp,
        ← GlobalTheory.CechPic.cls_pull o₂.isLB _ (pull_isLB o₂.isLB _),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o₂.rig₁, map_zero]
    · refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ2 _)).1 ?_
      rw [GlobalTheory.CechPic.cls_pull hQ2, GlobalTheory.CechPic.cls_pull o₂.isLB, ← GlobalTheory.CechPic.pull_comp,
        UpperTheory.EvaluationPowerKernel.square_axis_right_comm φ, GlobalTheory.CechPic.pull_comp,
        ← GlobalTheory.CechPic.cls_pull o₂.isLB _ (pull_isLB o₂.isLB _),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o₂.rig₂, map_zero]
    · have eq1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _)
        (pull_isLB o₁.isLB (sq2 ψ₁))).2 hpol1
      have eq2 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _)
        (pull_isLB o₂.isLB (sq2 ψ₂))).2 hpol2
      rw [GlobalTheory.CechPic.cls_pull o₁.isLB] at eq1
      rw [GlobalTheory.CechPic.cls_pull o₂.isLB] at eq2
      rw [GlobalTheory.CechPic.cls_pull o₂.isLB, ← h12, UpperTheory.EvaluationPowerKernel.grpSchemeSquareProductMap_comp, GlobalTheory.CechPic.pull_comp,
        GlobalTheory.CechPic.pull_comp, ← eq1, ← GlobalTheory.CechPic.pull_comp (sq2 ψ₁) (sq2 φ),
        ← UpperTheory.EvaluationPowerKernel.grpSchemeSquareProductMap_comp, hφ, ← eq2]
  · intro y
    rw [heta1, ← Over.comp_left, Category.assoc, hφ, ← heta2, Category.id_comp]
  · rw [← Over.comp_left, hφ]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_iso_of_pIsogeny_kernel_eq :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (c : ℕ) (T : Scheme.{0}) (s : T ⟶ Sp R) (o o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (g : Over.mk x ⟶ o.A), g ≫ ψ₁ = 1 ↔ g ≫ ψ₂ = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 T), ψ₁.left ≫ m.φ = ψ₂.left :=
  UpperTheory.EvaluationPowerKernel.main
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

namespace UpperTheory.KernelTorsionPullback

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem exists_equiv_points_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ Φ : (T ⟶ G') ≃ (Over.mk (T.hom ≫ f) ⟶ G),
      (∀ x, (Φ x).left = x.left ≫ φ) ∧ (∀ x, Φ x = 1 ↔ x = 1) := by
  let Φ : (T ⟶ G') ≃ (Over.mk (T.hom ≫ f) ⟶ G) :=
    { toFun := fun x => Over.homMk (x.left ≫ φ) (by
        show _ = T.hom ≫ f
        rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w])
      invFun := fun y => Over.homMk (hp.1.lift y.left T.hom (Over.w y)) (by simp)
      left_inv := fun x => by
        apply Over.OverMorphism.ext
        apply hp.1.hom_ext
        · simp
        · simp
      right_inv := fun y => by
        apply Over.OverMorphism.ext
        simp }
  have hl : ∀ x, (Φ x).left = x.left ≫ φ := fun x => rfl
  have h1 : Φ 1 = 1 := by
    have hm := hp.2 T 1 1 (Φ 1) (Φ 1) (hl 1) (hl 1)
    have hsq : Φ 1 * Φ 1 = Φ 1 := by
      apply Over.OverMorphism.ext
      rw [hm, _root_.mul_one]
      rfl
    exact mul_left_cancel (a := Φ 1) (by rw [hsq, _root_.mul_one])
  refine ⟨Φ, hl, fun x => ⟨fun hx => Φ.injective (by rw [hx, h1]), fun hx => by rw [hx, h1]⟩⟩

private theorem isTj_of_pull {Y S : Scheme.{0}} {σ : Y ⟶ Sp R} {σ₁ : S ⟶ Sp R} {f : S ⟶ Y} {r : ℤ}
    {w : Ideal (𝓞 D.F)} {j : ℕ} {o o' : Obj b N σ} {o₁ o₁' : Obj b N σ₁}
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) {ψ : o.A ⟶ o'.A} {ψ₁ : o₁.A ⟶ o₁'.A}
    (e : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ) (h : IsTj r w j o o' ψ) : IsTj r w j o₁ o₁' ψ₁ := by
  intro k _ _ _ x
  obtain ⟨h1, h2⟩ := h k (x ≫ f)
  obtain ⟨Φ, hΦl, hΦ1⟩ := exists_equiv_points_of_isGrpPullback m.cart (Over.mk x)
  obtain ⟨Φ', hΦ'l, hΦ'1⟩ := exists_equiv_points_of_isGrpPullback m'.cart (Over.mk x)
  have hψ : ∀ g, Φ' (g ≫ ψ₁) = Φ g ≫ ψ := by
    intro g
    apply Over.OverMorphism.ext
    rw [hΦ'l, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, e]
  have hk1 : ∀ g, g ≫ ψ₁ = 1 ↔ Φ g ≫ ψ = 1 := by
    intro g
    rw [← hψ, hΦ'1]
  have hkill : ∀ v g, KilledBy o₁ v g ↔ KilledBy o v (Φ g) := by
    intro v g
    apply forall₂_congr
    intro a _
    have hc : Φ (g ≫ o₁.act.act ((algebraMap (𝓞 D.F) D.O) a))
        = Φ g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) a) := by
      apply Over.OverMorphism.ext
      rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, m.act]
    rw [← hc, hΦ1]
  constructor
  · intro g hg hex
    rw [hkill]
    obtain ⟨e0, he⟩ := hex
    exact h1 (Φ g) ((hk1 g).mp hg) ⟨e0, (hkill _ g).mp he⟩
  · rw [← h2]
    exact Nat.card_congr (Φ.subtypeEquiv (fun g => by rw [hk1, hkill]))

private theorem exists_equiv_points_mk_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : T.hom ≫ f = g) :
    ∃ Φ : (T ⟶ G') ≃ (Over.mk g ⟶ G),
      (∀ x, (Φ x).left = x.left ≫ φ) ∧ (∀ x, Φ x = 1 ↔ x = 1) := by
  subst hg
  exact exists_equiv_points_of_isGrpPullback hp T

private theorem ker_iff {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s}
    (Rd : RepData b N r w j c s o) (Sd : SubData w j o) {k : Type} [Field k] (y : Sp k ⟶ Rd.Y.left) {x : Sp k ⟶ S}
    (e : y ≫ Rd.Y.hom = x) {t : Sp k ⟶ Sp R} {ox o₁ : Obj b N t} (m : ObjMap ox o x) (my : ObjMap ox Rd.o₀ y)
    (hm : my.φ ≫ Rd.m₀.φ = m.φ) (n : ObjMap o₁ Rd.o' y) (ψ₁ : ox.A ⟶ o₁.A)
    (hψ : my.φ ≫ Rd.ψ.left = ψ₁.left ≫ n.φ) (hK : KerGeo Rd Sd y) (h : Over.mk (𝟙 (Sp k)) ⟶ ox.A)
    (a : Over.mk x ⟶ o.A) (ha : a.left = h.left ≫ m.φ) :
    (h ≫ ψ₁ = 1 ∧ ∃ e : ℕ, KilledBy ox (uIdeal D r ^ e) h) ↔ InSub Sd.i a := by
  subst e
  obtain ⟨Φ, hΦl, hΦ1⟩ := exists_equiv_points_mk_of_isGrpPullback my.cart (Over.mk (𝟙 (Sp k))) y (Category.id_comp y)
  obtain ⟨Φ', hΦ'l, hΦ'1⟩ := exists_equiv_points_mk_of_isGrpPullback n.cart (Over.mk (𝟙 (Sp k))) y (Category.id_comp y)
  have key := hK (Φ h) a (by rw [hΦl, Category.assoc, hm, ha])
  rw [← key]
  have hψ' : Φ' (h ≫ ψ₁) = Φ h ≫ Rd.ψ := by
    apply Over.OverMorphism.ext
    rw [hΦ'l, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, hψ]
  have hk : ∀ v, KilledBy ox v h ↔ KilledBy Rd.o₀ v (Φ h) := by
    intro v
    apply forall₂_congr
    intro c _
    have hc : Φ (h ≫ ox.act.act ((algebraMap (𝓞 D.F) D.O) c))
        = Φ h ≫ Rd.o₀.act.act ((algebraMap (𝓞 D.F) D.O) c) := by
      apply Over.OverMorphism.ext
      rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, my.act]
    rw [← hc, hΦ1]
  rw [← hψ', hΦ'1]
  exact and_congr Iff.rfl (exists_congr fun _ => hk _)

end UpperTheory.KernelTorsionPullback

private theorem exists_objMap_same_phi_of_eq {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f f' : S' ⟶ S}
    (hf : f = f') (n : ObjMap o' o f) : ∃ n' : ObjMap o' o f', n'.φ = n.φ := by
  subst hf
  exact ⟨n, rfl⟩

open UpperTheory.KernelTorsionPullback in
theorem UpperTheory.subData_points_correspond_repData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (Sd : SubData w j o) (k : Type) [Field k] [IsAlgClosed k] (y₁ y₂ : Sp k ⟶ Rd.Y.left), y₁ ≫ Rd.Y.hom = y₂ ≫ Rd.Y.hom → KerGeo Rd Sd y₁ → KerGeo Rd Sd y₂ → y₁ = y₂ := by
  intro p _ D R _ _ b N hN hcop hp hm1 r w j c hw hu hc S _ s o Rd Sd k _ _ y₁ y₂ hy hK₁ hK₂
  obtain ⟨x, hx⟩ : ∃ x, y₁ ≫ Rd.Y.hom = x := ⟨_, rfl⟩
  have hx2 : y₂ ≫ Rd.Y.hom = x := hy ▸ hx
  obtain ⟨ox, ⟨my₁⟩⟩ := IsogRep.exists_pull y₁ Rd.o₀ (s' := x ≫ s) (by rw [← hx, Category.assoc])
  obtain ⟨o₁, ⟨n₁⟩⟩ := IsogRep.exists_pull y₁ Rd.o' (s' := x ≫ s) (by rw [← hx, Category.assoc])
  obtain ⟨ψ₁, hiso₁, hsq₁⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N c _ _ _ _ y₁ Rd.o₀ Rd.o' ox o₁ my₁ n₁ Rd.ψ Rd.isog
  have htj₁ : IsTj r w j ox o₁ ψ₁ := isTj_of_pull my₁ n₁ hsq₁ Rd.tj
  obtain ⟨mc, hmc⟩ := IsogRep.exists_comp my₁ Rd.m₀
  obtain ⟨m, hmφ⟩ := exists_objMap_same_phi_of_eq hx mc
  obtain ⟨my₂, hmy₂⟩ := IsogRep.exists_factor hN hcop hx2 Rd.m₀ m
  obtain ⟨o₂, ⟨n'⟩⟩ := IsogRep.exists_pull y₂ Rd.o' (s' := x ≫ s) (by rw [← hx2, Category.assoc])
  obtain ⟨ψ₂, hiso₂, hsq₂⟩ := GlobalTheory.T.isPIsogenyOfSimilitude_pullback_objects p D R b N c _ _ _ _ y₂ Rd.o₀ Rd.o' ox o₂ my₂ n' Rd.ψ Rd.isog
  have hker : ∀ h : 𝟙_ (Over (Sp k)) ⟶ ox.A,
      (h ≫ ψ₁ = 1 ∧ ∃ e, KilledBy ox (uIdeal D r ^ e) h) ↔
        (h ≫ ψ₂ = 1 ∧ ∃ e, KilledBy ox (uIdeal D r ^ e) h) := by
    intro h
    let a : Over.mk x ⟶ o.A := Over.homMk (h.left ≫ m.φ) (by
      show _ = x
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w h]
      exact Category.id_comp x)
    rw [ker_iff Rd Sd y₁ hx m my₁ (by rw [hmφ, hmc]) n₁ ψ₁ hsq₁ hK₁ h a rfl,
      ker_iff Rd Sd y₂ hx2 m my₂ hmy₂ n' ψ₂ hsq₂ hK₂ h a rfl]
  have hgeo := isogeny_kernel_points_iff_of_isPIsog p D R b N hp r w c hw hu k (x ≫ s) ox o₁ o₂ ψ₁ ψ₂ hiso₁ hiso₂ hker
  obtain ⟨mm, hmm⟩ := exists_iso_of_pIsogeny_kernel_eq p D R b N hN hcop hp c (Sp k) (x ≫ s) ox o₁ o₂ ψ₁ ψ₂ hiso₁ hiso₂ hgeo
  obtain ⟨nc, hnc⟩ := IsogRep.exists_comp mm n'
  obtain ⟨n₂, hn₂⟩ := exists_objMap_same_phi_of_eq (Category.id_comp y₂) nc
  exact (Rd.univ (Sp k) x ox o₁ m ψ₁ hiso₁ htj₁).unique ⟨hx, my₁, n₁, hsq₁⟩
    ⟨hx2, my₂, n₂, by rw [hn₂, hnc, ← Category.assoc, hmm, hsq₂]⟩
