module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueEqRootMulThetaOperatorValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueEqRootMulThetaOperatorValue
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.TwCompare

open GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam

section Move

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {P : PolAV S} {P₀ : PolAV S'} {a : P₀.A.left ⟶ P.A.left}
  (hp : IsGrpPullback P₀.A P.A f a) {w : LB.Iso P₀.L (P.L.pull a)} (hw : w.IsGen)


include hp hw in
theorem exists_frames {T : Over S} {T' : Over S'} {g : T'.left ⟶ T.left}
    {rig : LB.Gen (P.L.pull (eSec P.A))} (hrig : rig.IsGen) {I : Type} {x : I → (T ⟶ P.A)} {x' : I → (T' ⟶ P₀.A)}
    (hx : ∀ i, (x' i).left ≫ a = g ≫ (x i).left) {n : ℕ}
    {τ : ∀ i, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (x i).left) (fun _ => 1))}
    (H : ∀ i, IsTorsFrame P rig n (x i) (τ i)) :
    ∃ (rig' : LB.Gen (P₀.L.pull (eSec P₀.A)))
      (τ' : ∀ i, LB.Gen (LB.LinComb P₀.L (Y := T'.left) (K := Fin 1) (fun _ => (x' i).left) (fun _ => 1))),
      GenThrough w (fun _ : PUnit => eSec P₀.A) (fun _ : PUnit => eSec P.A) (fun _ => 1) rig' rig f ∧
      (∀ i, IsTorsFrame P₀ rig' n (x' i) (τ' i)) ∧
      ∀ i, GenThrough w (fun _ : Fin 1 => (x' i).left) (fun _ : Fin 1 => (x i).left) (fun _ => 1) (τ' i) (τ i) g := by
  obtain ⟨rig', -, Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec P₀.A) (φ := fun _ => eSec P.A)
    (ε := fun _ => 1) (h := f) hw P.isLB P₀.isLB (fun _ => PolBaseChange.eSec_comm hp) rig hrig
  choose τ' hτ' Hτ using fun i => exists_gen_through (φ' := fun _ : Fin 1 => (x' i).left) (h := g) hw P.isLB P₀.isLB
    (fun _ => hx i) (τ i) (H i).2.1
  refine ⟨rig', τ', Hr, fun i => FrameMove.isTorsFrame_move hp hw (fun Z r z J J' hJ hJ' =>
    (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))) (hx i) (H i) (hτ' i)
    (fun z J J' hJ hJ' => ?_), Hτ⟩
  have := Hτ i _ (𝟙 _) z J J' hJ hJ'
  rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this


include hw in
theorem isTwVal_move {T T₀ : Over S} {T' : Over S'} {σ : T'.left ⟶ T.left} (hσ : σ ≫ T.hom = T'.hom ≫ f)
    {β : T ⟶ T₀} {g : T'.left ⟶ T₀.left} (hg : g ≫ T₀.hom = T'.hom ≫ f) (hβ : σ ≫ β.left = g)
    {θ : LB.Sec (LPow P.A P.L 1 T₀)} {θ₁ : LB.Sec (LPow P₀.A P₀.L 1 T')} (hθ : SecRel hp g hg w θ₁ θ)
    {z₀ : T₀ ⟶ P.A} {y : T' ⟶ P₀.A} {τ τ₁}
    (hτ : GenThrough w (fun _ : Fin 1 => y.left) (fun _ : Fin 1 => z₀.left) (fun _ => 1) τ₁ τ g)
    {N m : ℕ} {X H : T' ⟶ P₀.A} {x h : T ⟶ P.A} (hN : X ^ N = 1) (hx : σ ≫ x.left = X.left ≫ a)
    (hh : σ ≫ h.left = H.left ≫ a) (hy : H ^ m = y) {v : Γ(T.left, ⊤)} (E : IsTwVal P N m θ τ β x h v) :
    ∃ (α : LB.Gen (LB.LinComb P₀.L (K := Fin 2) ![(snd T' P₀.A).left, (snd T' P₀.A ^ m).left] ![(N : ℤ), -1]))
      (U : ThetaGrp P₀.A P₀.L N T'), α.IsGen ∧ SymLift P₀.A P₀.L N N X U ∧ ∀ (z : T'.left) J, Good P₀.L z J →
        gs σ z ⊤ v * (val α (ptSecT P₀.A H).left z J * val τ₁ (𝟙 _) z J).val =
          (tval U (ptSecT P₀.A H).left z J).val * ((val α (ptSecT P₀.A (X * H)).left z J).val *
            VVRank.sv P₀.A θ₁ (ptSecT P₀.A ((X * H) ^ m)).left z J) := by
  have := P₀.isAb.comm
  have hL₀ := P.isLB
  have hL₁ := P₀.isLB
  obtain ⟨α₀, U₀, hα₀, hU₀, E⟩ := E
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp σ hσ hw hL₀ hL₁ (psi_pow hp σ hσ m) α₀ hα₀
  obtain ⟨U, hU, hU'⟩ := symLift_move hp σ hσ hw hL₀ hL₁ hx hN hU₀
  have e : psi hp σ hσ ≫ (β ▷ P.A).left = psi hp g hg := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst', psi_fst',
        Category.assoc, hβ]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', psi_snd']
  have hθ' : SecRel hp σ hσ w θ₁ (VVRank.pullS P.A 1 β θ) := fun Z r z J J' hJ hJ' => by
    rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc, e]
    exact hθ Z r z J J' hJ hJ'
  obtain ⟨s₀, hs₀⟩ := VVRank.exists_isTwistPull P.A (ψ := mulT P.A T m) (m := snd T P.A ^ m) (hm := lift_snd _ _)
    (a := N) (b := 1) hL₀ hα₀ (VVRank.pullS P.A 1 β θ)
  obtain ⟨s, hs⟩ := exists_secRel hp σ hσ hw hL₀ hL₁ s₀
  have h₁ : IsTwistPull P₀.A P₀.L (mulT P₀.A T' m) (snd T' P₀.A ^ m) (lift_snd _ _) N 1 α θ₁ s :=
    isTwistPull_move hp σ hσ hL₀ hL₁ (psi_pow hp σ hσ m) hα vα hθ' hs hs₀
  obtain ⟨s₀', hs₀'⟩ : ∃ t, IsActOf P.A P.L (N : ℤ) U₀ s₀ t := VVRank.exists_isTwistPull P.A hL₀ U₀.isGen s₀
  obtain ⟨s', hs'⟩ := exists_secRel hp σ hσ hw hL₀ hL₁ s₀'
  have h₂ := hU' _ _ _ _ hs hs' hs₀'
  refine ⟨α, U, hα, hU, fun z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' hL₀ z
  have E' := E _ σ z J hJ
  have a₀ := VVRank.sv_of_isTwistPull P.A hs₀' (σ ≫ (ptSecT P.A h).left) z hJ
  have a₁ := VVRank.sv_of_isTwistPull P.A hs₀ (σ ≫ (ptSecT P.A (x * h)).left) z hJ
  have b₀ := VVRank.sv_of_isTwistPull P₀.A h₂ (ptSecT P₀.A H).left z hJ'
  have b₁ := VVRank.sv_of_isTwistPull P₀.A h₁ (ptSecT P₀.A (X * H)).left z hJ'
  rw [Category.assoc, ThetaCompare.pt_mulT, VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc] at a₁
  rw [Category.assoc, ThetaCompare.pt_translT, congrArg (fun q => ptSecT P.A (q * h)) hU₀.pt_eq, a₁] at a₀
  rw [ThetaCompare.pt_mulT] at b₁
  rw [ThetaCompare.pt_translT, congrArg (fun q => ptSecT P₀.A (q * H)) hU.pt_eq, b₁] at b₀
  have c₀ := hs' _ (ptSecT P₀.A H).left z J J' hJ hJ'
  have c₁ := vα _ (ptSecT P₀.A H).left z J J' hJ hJ'
  have c₂ := hτ _ (𝟙 _) z J J' hJ hJ'
  have e₂ : (ptSecT P₀.A H).left ≫ (snd T' P₀.A ^ m).left = y.left := by
    rw [← Over.comp_left, SymLiftOdd.comp_pow', ThetaCompare.pt_snd, hy]
  rw [psi_ptSec hp σ hσ hh] at c₀ c₁
  rw [e₂] at c₁
  rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at c₂
  have E₂ : gs σ z ⊤ v * (val α₀ (σ ≫ (ptSecT P.A h).left) z J * val τ g z J).val =
      VVRank.sv P.A s₀' (σ ≫ (ptSecT P.A h).left) z J := by
    rw [← hβ, a₀, ← _root_.mul_assoc, ← Units.val_mul]
    exact E'
  rw [c₀, b₀, c₁, c₂] at E₂
  refine (Units.mul_right_inj _).1 (Eq.trans ?_ E₂)
  rw [mul_left_comm, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

end Move

theorem frame_ratio_pow {S : Scheme.{0}} (P : PolAV S) {T : Over S} {N M m : ℕ} {rig : LB.Gen (P.L.pull (eSec P.A))}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1])}
    (hα : α.IsGen)
    (hn : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L rig T ((N : ℤ) - 1)))
    {h w : T ⟶ P.A} (hw : w = h ^ m) {τ τ'} (hτ : IsTorsFrame P rig M h τ) (hτ' : IsTorsFrame P rig M w τ')
    {y : T.left} {J} (hJ : Good P.L y J) :
    (val α (ptSecT P.A h).left y J * val τ' (𝟙 _) y J * (val τ (𝟙 _) y J ^ N)⁻¹) ^ (M ^ 2) = 1 := by
  subst hw
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨β, hβ⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P M T
  have rα := ThetaCompare.Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rβ := ThetaCompare.Reg.two (y := y) (J := J) β hβ (snd T P.A) (snd T P.A ^ M) rfl rfl
  have c := (((rα.pow hJ (M ^ 2)).mul hJ (rβ.pull hJ (snd T P.A ^ m))).mul hJ
    ((rβ.pow hJ N).mul hJ (rα.pull hJ (snd T P.A ^ M))).inv).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul, mul_comm m M]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module) h 1
  simp only [SymLiftOdd.comp_pow', ThetaCompare.pt_snd, hτ.1, one_pow] at c
  have a₂ := ThetaCompare.torsFrame_pow hG P hβ hτ hJ
  have a₃ := ThetaCompare.torsFrame_pow hG P hβ hτ' hJ
  have a₄ := val_corr hJ hn (𝟙 T.left)
  rw [val_pull hJ, ThetaCompare.val_rigT _ _ hJ, Category.id_comp] at a₄
  apply Additive.ofMul.injective
  replace c := congrArg Additive.ofMul c
  replace a₂ := congrArg Additive.ofMul a₂
  replace a₃ := congrArg Additive.ofMul a₃
  replace a₄ := congrArg Additive.ofMul a₄
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one] at c a₂ a₃ a₄ ⊢
  linear_combination (norm := module) c + a₃ - N • a₂ + (M ^ 2) • a₄

theorem sv_cross {K : Type} [Field K] (P : PolAV (Sp K)) (θ θ' : LB.Sec (LPow P.A P.L 1 (baseOver (Sp K))))
    (p q : baseOver (Sp K) ⟶ P.A) (z : (baseOver (Sp K)).left) {J} (hJ : Good P.L z J) :
    VVRank.sv P.A θ (ptSecT P.A p).left z J * VVRank.sv P.A θ' (ptSecT P.A q).left z J =
      VVRank.sv P.A θ' (ptSecT P.A p).left z J * VVRank.sv P.A θ (ptSecT P.A q).left z J := by
  obtain ⟨V, hV, hθ⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny P z
  obtain ⟨t, ht⟩ := hθ K (𝟙 _) (by
    rintro _ ⟨v, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) v z]
    exact hV)
  obtain ⟨r, hr⟩ := ht θ
  obtain ⟨r', hr'⟩ := ht θ'
  have a₁ := ThetaCompare.sval_smul (T := baseOver (Sp K)) hr p hJ
  have a₂ := ThetaCompare.sval_smul (T := baseOver (Sp K)) hr q hJ
  have a₃ := ThetaCompare.sval_smul (T := baseOver (Sp K)) hr' p hJ
  have a₄ := ThetaCompare.sval_smul (T := baseOver (Sp K)) hr' q hJ
  refine (congrArg₂ (· * ·) a₁ a₄).trans (Eq.trans ?_ (congrArg₂ (· * ·) a₃ a₂).symm)
  ring

theorem exists_cst_bij {K : Type} [Field K] (z : (baseOver (Sp K)).left) :
    ∃ c : K →+* (baseOver (Sp K)).left.presheaf.stalk z, Function.Bijective c ∧
      ∀ a, gs (𝟙 (baseOver (Sp K)).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = c a := by
  refine ⟨((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom,
    ⟨RingHom.injective _, fun s => ?_⟩, fun _ => gs_eq (𝟙 _) z ⊤ trivial _⟩
  obtain ⟨U, hU, t, rfl⟩ := (Sp K).presheaf.germ_exist s
  obtain rfl : U = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim (α := PrimeSpectrum K) q z]
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 t
  exact ⟨b, rfl⟩

theorem isValueAt_act {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (t h : S.Gam) {σ}
    (H : IsActOf ρ.P.A ρ.P.L S.N (ρ.U t) (ρ.s ρ.i₀) σ) :
    IsValueAt ρ.P.A ρ.P.L S.N σ (ρ.pt h) (powFrame ρ.P.A ρ.P.L (ρ.pt h) (ρ.fr h) S.N)
      (fn (∑ l, algebraMap o S.R (S.ρ t l ρ.i₀) * ⟨S.ev h l, S.ev_mem h l⟩ : S.R)) := by
  refine isValueAt_of_sv ρ.P.isLB fun y J hJ => ?_
  let g : S.R →+* (baseOver (Sp S.R)).left.presheaf.stalk y :=
    ((Sp S.R).presheaf.germ ⊤ y trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom
  have hgs : ∀ b : S.R, gs (𝟙 (baseOver (Sp S.R)).left) y ⊤ (fn b) = g b := fun b => gs_eq _ y ⊤ trivial _
  have b₂ := EvCrd.sval_sum (ρ.U_act t ρ.i₀ σ H) (ρ.pt h) hJ
  simp only [fun l => ThetaCompare.sval_valueAt (ρ.ev_val l h) hJ, hgs, ← _root_.mul_assoc, ← Finset.sum_mul] at b₂
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Category.id_comp, hgs, map_sum]
  simp only [map_mul]
  exact b₂

theorem exists_generic_data {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real)
    {P₀ : PolAV (Sp Ω)} {a : P₀.A.left ⟶ ρ.P.A.left} (hp : IsGrpPullback P₀.A ρ.P.A (spMap S.R.val.toRingHom) a)
    (lb : LBIso P₀.L (ρ.P.L.pull a)) {X : S.Gam → (baseOver (Sp Ω) ⟶ P₀.A)}
    (hX : ∀ b, (X b).left ≫ a = spMap S.R.val.toRingHom ≫ (ρ.pt b).left) (hpow : ∀ (n : ℕ) b, X (n • b) = X b ^ n) :
    ∃ (rig : LB.Gen (P₀.L.pull (eSec P₀.A)))
      (τ : ∀ b, LB.Gen (LB.LinComb P₀.L (Y := (baseOver (Sp Ω)).left) (K := Fin 1) (fun _ => (X b).left) (fun _ => 1)))
      (θ : LB.Sec (LPow P₀.A P₀.L 1 (baseOver (Sp Ω))))
      (α : LB.Gen (LB.LinComb P₀.L (K := Fin 2)
        ![(snd (baseOver (Sp Ω)) P₀.A).left, (snd (baseOver (Sp Ω)) P₀.A ^ (ρ.n ^ ρ.k)).left] ![(S.N : ℤ), -1])),
      α.IsGen ∧ (∀ b, IsTorsFrame P₀ rig (S.r * S.N) (X b) (τ b)) ∧
      (∀ b, IsValueAt P₀.A P₀.L 1 θ (X b) (τ b) (fn (S.th b))) ∧
      LB.Gen.Corr P₀.L _ _ _ _ (LB.pullGen P₀.L _ _ α (ptSecT P₀.A 1).left)
        (rigT P₀.A P₀.L rig (baseOver (Sp Ω)) ((S.N : ℤ) - 1)) ∧
      ∀ (t : S.Gam) (U : ThetaGrp P₀.A P₀.L S.N (baseOver (Sp Ω))), SymLift P₀.A P₀.L S.N S.N (X (S.r • t)) U →
        ∀ (h : S.Gam) (z : (baseOver (Sp Ω)).left) J, Good P₀.L z J →
          (tval U (ptSecT P₀.A (X h)).left z J).val * ((val α (ptSecT P₀.A (X (S.r • t) * X h)).left z J).val *
            VVRank.sv P₀.A θ (ptSecT P₀.A ((X (S.r • t) * X h) ^ (ρ.n ^ ρ.k))).left z J) =
          gs (𝟙 _) z ⊤ (fn (∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j)) * (val (τ h) (𝟙 _) z J ^ S.N).val := by
  obtain ⟨w, hw⟩ := lb
  have hL₀ := ρ.P.isLB
  have hL₁ := P₀.isLB
  have := P₀.isAb.comm
  let g : (baseOver (Sp Ω)).left ⟶ (baseOver (Sp S.R)).left := spMap S.R.val.toRingHom
  have hg : g ≫ (baseOver (Sp S.R)).hom = (baseOver (Sp Ω)).hom ≫ spMap S.R.val.toRingHom :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  obtain ⟨rig, τ, vrig, hτ, vτ⟩ := exists_frames hp hw (T := baseOver (Sp S.R)) (g := g) ρ.rig_gen hX ρ.fr_tors
  obtain ⟨θ, hθ⟩ := exists_secRel hp g hg hw hL₀ hL₁ ρ.th₁
  obtain ⟨s, hs⟩ := exists_secRel hp g hg hw hL₀ hL₁ (ρ.s ρ.i₀)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp g hg hw hL₀ hL₁ (psi_pow hp g hg (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have h₁ : IsTwistPull P₀.A P₀.L (mulT P₀.A _ (ρ.n ^ ρ.k)) (snd _ P₀.A ^ (ρ.n ^ ρ.k)) (lift_snd _ _) S.N 1 α θ s :=
    isTwistPull_move hp g hg hL₀ hL₁ (psi_pow hp g hg (ρ.n ^ ρ.k)) hα vα hθ hs ρ.s_zero
  refine ⟨rig, τ, θ, α, hα, hτ, fun b => ?_, ThetaGeom.norm_move hp g hg hL₀ hL₁ vrig vα ρ.α_norm,
    fun t U hU h z J hJ => ?_⟩
  · have q := isValueAt_move hp g hg hL₀ hL₁ (hX b).symm (vτ b) hθ (ρ.th_val b)
    rw [spMap_appTop_fn] at q
    exact q
  · have hN : X (S.r • t) ^ S.N = 1 := by
      rw [hpow, ← pow_mul]
      exact (hτ t).1
    have hodd : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
    obtain ⟨U₂, hU₂, hU'⟩ := symLift_move hp g hg hw hL₀ hL₁ (hX (S.r • t)).symm hN (ρ.U_sym t)
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ, IsActOf ρ.P.A ρ.P.L (S.N : ℤ) (ρ.U t) (ρ.s ρ.i₀) σ :=
      VVRank.exists_isTwistPull ρ.P.A hL₀ (ρ.U t).isGen _
    obtain ⟨σ, hσ⟩ := exists_secRel hp g hg hw hL₀ hL₁ σ₀
    have q := isValueAt_move hp g hg hL₀ hL₁ (hX h).symm (ThetaGeom.genThrough_pow g (vτ h) S.N) hσ
      (isValueAt_act ρ t h hσ₀)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [spMap_appTop_fn, map_sum] at q
    have q' := sv_of_isValueAt q (𝟙 _) z hJ
    have b₀ := VVRank.sv_of_isTwistPull P₀.A (hU' _ _ _ _ hs hσ hσ₀) (ptSecT P₀.A (X h)).left z hJ
    have b₁ := VVRank.sv_of_isTwistPull P₀.A h₁ (ptSecT P₀.A (X (S.r • t) * X h)).left z hJ
    rw [ThetaCompare.pt_mulT] at b₁
    rw [ThetaCompare.pt_translT, congrArg (fun q => ptSecT P₀.A (q * X h)) hU₂.pt_eq, b₁] at b₀
    rw [Category.id_comp, ThetaGeom.val_powFrame, zpow_natCast, b₀] at q'
    have u : tval U (ptSecT P₀.A (X h)).left z J = tval U₂ (ptSecT P₀.A (X h)).left z J :=
      val_corr hJ (SymLiftOdd.symLift_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns P₀.isAb hL₁ hodd U U₂ hU hU₂) _
    rw [u]
    exact q'

theorem twVal_eq_root_mul : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] [ArithBase o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left) (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)), IsGenLab ρ ρ' lab φ P₀ a a' x → ∀ (m : ℕ), S'.N = m ^ 2 → ∀ (κ x₀ : S.Gam) (h : S'.Gam), m • h = lab κ → ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (t : S'.Gam) (v : Ω'), IsTwVal ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • t)) (x h) ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom v) → v * S'.th (lab x₀) = ξ * φ (S.th x₀) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := by
  intro o Ω o' Ω' _ _ _ _ _ _ _ _ S S' ρ ρ' lab φ P₀ a a' x hgen m hm κ x₀ h hκ
  obtain ⟨hp, hp', ⟨w, hw⟩, lb', hpt, hlab⟩ := hgen
  obtain rfl : m = ρ'.n ^ ρ'.k := Nat.pow_left_injective two_ne_zero (hm.symm.trans ρ'.N_eq)
  choose u hu hua hua' using hpt
  have := P₀.isAb.comm
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨X, hX, hX'⟩ : ∃ X : S'.Gam → (baseOver (Sp Ω') ⟶ P₀.A), (∀ b, (X b).left ≫ a = (x b).left) ∧
      ∀ b, (X b).left ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt b).left := ⟨fun b => Over.homMk (u b) (hu b), hua, hua'⟩
  have hadd : ∀ b c, X (b + c) = X b * X c := fun b c => by
    refine Over.OverMorphism.ext (hp'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [hX', ρ'.pt_add]
    exact over_mul hp' (T := baseOver (Sp Ω')) (T₀ := baseOver (Sp S'.R)) _
      ((Category.comp_id _).trans (Category.id_comp _).symm) (hX' b).symm (hX' c).symm
  have hpow : ∀ (n : ℕ) b, X (n • b) = X b ^ n := fun n b => by
    induction n with
    | zero =>
      have h := hadd 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  obtain ⟨rig₂, τ₂, θ₂, α₂, hα₂, hτ₂, hθ₂, hn₂, hact⟩ := exists_generic_data ρ' hp' lb' hX' hpow
  let g : (baseOver (Sp Ω')).left ⟶ (baseOver (Sp S.R)).left := spMap (φ.comp S.R.val.toRingHom)
  have hg : g ≫ (baseOver (Sp S.R)).hom = (baseOver (Sp Ω')).hom ≫ spMap (φ.comp S.R.val.toRingHom) :=
    (Category.comp_id _).trans (Category.id_comp _).symm
  have hy : ∀ k, (X (lab k)).left ≫ a = g ≫ (ρ.pt k).left := fun k => by
    rw [hX, hlab]
    rfl
  obtain ⟨rig₁, τ₁, -, hτ₁, vτ₁⟩ := exists_frames hp hw (T := baseOver (Sp S.R)) (g := g) ρ.rig_gen
    (x' := fun k => X (lab k)) hy ρ.fr_tors
  obtain ⟨θ₁, hθ₁⟩ := exists_secRel hp g hg hw ρ.P.isLB P₀.isLB ρ.th₁
  have hv₁ := isValueAt_move hp g hg ρ.P.isLB P₀.isLB (hy x₀).symm (vτ₁ x₀) hθ₁ (ρ.th_val x₀)
  rw [spMap_appTop_fn] at hv₁
  let z : (baseOver (Sp Ω')).left := IsLocalRing.closedPoint Ω'
  obtain ⟨J, hJ⟩ := exists_good' P₀.isLB z
  obtain ⟨c, hc, hcv⟩ := exists_cst_bij z
  have hh : X (lab κ) = X h ^ (ρ'.n ^ ρ'.k) := by rw [← hκ, hpow]
  have r₁ := frame_ratio_pow P₀ hα₂ hn₂ hh (hτ₂ h) (hτ₂ (lab κ)) hJ
  have r₂ := (DivDeep.torsFrame_two_levels P₀ (hτ₁ κ) (hτ₂ (lab κ)) hJ).trans
    (DivDeep.torsFrame_two_levels P₀ (hτ₁ x₀) (hτ₂ (lab x₀)) hJ).symm
  obtain ⟨ξ, hξ⟩ := hc.2 (val (τ₂ h) (𝟙 _) z J ^ S'.N * val (τ₁ x₀) (𝟙 _) z J *
    (val α₂ (ptSecT P₀.A (X h)).left z J * val (τ₁ κ) (𝟙 _) z J * val (τ₂ (lab x₀)) (𝟙 _) z J)⁻¹).val
  have p₁ : 0 < S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  have p₂ : 0 < S'.r * S'.N := Nat.mul_pos S'.r_pos (by have := S'.N_ge; omega)
  refine ⟨ξ, ⟨(S.r * S.N) ^ 2 * (S'.r * S'.N) ^ 2, by positivity, hc.1 ?_⟩, fun t v E => hc.1 ?_⟩
  · rw [map_pow, hξ, map_one, ← Units.val_pow_eq_pow_val, Units.val_eq_one]
    apply Additive.ofMul.injective
    replace r₁ := congrArg Additive.ofMul r₁
    replace r₂ := congrArg Additive.ofMul r₂
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div, ofMul_one] at r₁ r₂ ⊢
    linear_combination (norm := module) -((S.r * S.N) ^ 2 • r₁) - r₂
  · have hN : X (S'.r • t) ^ S'.N = 1 := by
      rw [hpow, ← pow_mul]
      exact (hτ₂ t).1
    obtain ⟨α, U, hα, hU, e₁⟩ := isTwVal_move hp hw (T := genPt (φ.comp S.R.val.toRingHom)) (T' := baseOver (Sp Ω'))
      (σ := 𝟙 (Sp Ω')) rfl hg (Category.id_comp _) hθ₁ (vτ₁ κ) hN ((Category.id_comp _).trans (hX _).symm)
      ((Category.id_comp _).trans (hX _).symm) hh.symm E
    replace e₁ := (congrArg (· * _) (hcv v)).symm.trans (e₁ z J hJ)
    have e₂ := (hact t U hU h z J hJ).trans (congrArg (· * _) (hcv _))
    have e₃ := sv_cross P₀ θ₁ θ₂ ((X (S'.r • t) * X h) ^ (ρ'.n ^ ρ'.k)) (X (lab x₀)) z hJ
    have e₄ : VVRank.sv P₀.A θ₁ (ptSecT P₀.A (X (lab x₀))).left z J = c (φ (S.th x₀)) * (val (τ₁ x₀) (𝟙 _) z J).val :=
      (ThetaCompare.sval_valueAt hv₁ hJ).trans (congrArg (· * _) (hcv _))
    have e₅ : VVRank.sv P₀.A θ₂ (ptSecT P₀.A (X (lab x₀))).left z J =
        c (S'.th (lab x₀)) * (val (τ₂ (lab x₀)) (𝟙 _) z J).val :=
      (ThetaCompare.sval_valueAt (hθ₂ _) hJ).trans (congrArg (· * _) (hcv _))
    have e₆ := ((ThetaCompare.Reg.two (y := z) (J := J) α hα _ _ rfl rfl).mul hJ
      (ThetaCompare.Reg.two (y := z) (J := J) α₂ hα₂ _ _ rfl rfl).inv).const hG P₀.isAb P₀.isLB hJ
      (fun U _ h => mul_inv_cancel _) (X (S'.r • t) * X h) (X h)
    rw [e₄, e₅] at e₃
    rw [map_mul, map_mul, map_mul, hξ]
    have key : ∀ {R : Type} [CommRing R] (v th th' E s₁ s₂ : R) (aH aX bH bX u tk t0 t0' tN : Rˣ),
        v * (aH * tk).val = u.val * (aX.val * s₁) → u.val * (bX.val * s₂) = E * tN.val →
        s₁ * (th' * t0'.val) = s₂ * (th * t0.val) → aX * bX⁻¹ = aH * bH⁻¹ →
        v * th' = (tN * t0 * (bH * tk * t0')⁻¹).val * th * E := by
      intro R _ v th th' E s₁ s₂ aH aX bH bX u tk t0 t0' tN h₁ h₂ h₃ h₄
      obtain rfl : aX = aH * bH⁻¹ * bX := by rw [← h₄, inv_mul_cancel_right]
      have k₁ := tk.mul_inv
      have k₂ := t0'.mul_inv
      refine (Units.mul_left_inj (aH * tk * t0')).1 ?_
      simp only [mul_inv, Units.val_mul] at h₁ ⊢
      linear_combination (th' * t0'.val) * h₁ + (u.val * aH.val * bH⁻¹.val * bX.val) * h₃ +
        (aH.val * bH⁻¹.val * th * t0.val) * h₂ -
        (tN.val * t0.val * bH⁻¹.val * th * E * aH.val) * (t0'.val * t0'⁻¹.val) * k₁ -
        (tN.val * t0.val * bH⁻¹.val * th * E * aH.val) * k₂
    exact key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ e₃ e₆

end GlobalTheory.UPoinc.TwCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueEqRootMulThetaOperatorValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] [ArithBase o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left) (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)), IsGenLab ρ ρ' lab φ P₀ a a' x → ∀ (m : ℕ), S'.N = m ^ 2 → ∀ (κ x₀ : S.Gam) (h : S'.Gam), m • h = lab κ → ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (t : S'.Gam) (v : Ω'), IsTwVal ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • t)) (x h) ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom v) → v * S'.th (lab x₀) = ξ * φ (S.th x₀) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := by
  first | exact @GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | exact GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | (intros; apply GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.USum

theorem isTwVal_unique {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀))
    {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1)))
    (β : T ⟶ T₀) (x h : T ⟶ P.A) (v v' : Γ(T.left, ⊤)) (hN : Odd N) (H : IsTwVal P N m θ τ β x h v)
    (H' : IsTwVal P N m θ τ β x h v') : v = v' := by
  obtain ⟨α, U, hα, hU, e⟩ := H
  obtain ⟨α', U', hα', hU', e'⟩ := H'
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hc := GlobalTheory.SymLiftOdd.symLift_unique hG P.isAb P.isLB hN U U' hU hU'
  obtain ⟨c, hcv⟩ := GlobalTheory.SymLiftOdd.exists_const P.isLB (fst T P.A).left (lift (𝟙 T) (1 : T ⟶ P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (GlobalTheory.SymLiftOdd.surj_fst hG P.isAb T)
    (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen P.L _ _ _ _ α (LB.invGen P.L _ _ α') hα (DVR.invGen_isGen _ _ _ _ hα'))
  refine fn_ext fun y _ => ?_
  choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart P.isLB (χ y)
  have hJ' : Good P.L y J := hJ
  have r : ∀ w : T ⟶ P.A, val α (𝟙 _ ≫ (ptSecT P.A w).left) y J =
      val α' (𝟙 _ ≫ (ptSecT P.A w).left) y J * gm (𝟙 T.left) y ⊤ c := fun w => by
    have k := hcv _ (𝟙 _ ≫ (ptSecT P.A w).left) y J hJ'
    have k₂ : (𝟙 _ ≫ (ptSecT P.A w).left) ≫ (fst T P.A).left = 𝟙 T.left := by
      rw [Category.id_comp, ← Over.comp_left, ptSecT, lift_fst]; rfl
    rw [k₂, val_mul hJ', val_inv] at k
    rw [← k, mul_comm, inv_mul_cancel_right]
  have t : GlobalTheory.CommPairing.tval U (𝟙 _ ≫ (ptSecT P.A h).left) y J =
      GlobalTheory.CommPairing.tval U' (𝟙 _ ≫ (ptSecT P.A h).left) y J := val_corr hJ' hc _
  have e₁ := e _ (𝟙 _) y J hJ'
  have e₂ := e' _ (𝟙 _) y J hJ'
  rw [r, r, t] at e₁
  refine (Units.mul_left_inj (val α' (𝟙 _ ≫ (ptSecT P.A h).left) y J * gm (𝟙 T.left) y ⊤ c *
    val τ (𝟙 _ ≫ β.left) y J)).1 (e₁.trans ?_)
  simp only [Units.val_mul] at e₂ ⊢
  linear_combination (-(gm (𝟙 T.left) y ⊤ c).val) * e₂

end GlobalTheory.UPoinc.USum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTwistedThetaValue_unique : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v v' : Γ(T.left, ⊤)), Odd N → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x h v' → v = v' := by
  first | exact @GlobalTheory.UPoinc.USum.isTwVal_unique | exact GlobalTheory.UPoinc.USum.isTwVal_unique | (intros; apply GlobalTheory.UPoinc.USum.isTwVal_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueTranslateOrthogonalTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueTranslateOrthogonalTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.USum


open GlobalTheory.ThetaCompare GlobalTheory.CommPairing in
theorem isTwVal_transl : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) (k : T ⟶ P.A), k ^ m = 1 → WeilIs P.A P.L N x k 1 → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x (h * k) v := by
  intro B P N m T₀ T θ z₀ τ β x h v k hk hw H
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, U, hα, hU, H⟩ := H
  refine ⟨α, U, hα, hU, fun Z r z J hJ => ?_⟩
  have e₀ : (translT P.A k).left ≫ (snd T P.A).left = (translPt P.A k).left := by
    rw [← Over.comp_left, translT, lift_snd]
  have e₁ : (translT P.A k).left ≫ (snd T P.A ^ m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, SymLiftOdd.comp_pow', translT, lift_snd,
      show translPt P.A k = (fst T P.A ≫ k) * snd T P.A from rfl, mul_pow, ← SymLiftOdd.comp_pow', hk,
      MonObj.comp_one, _root_.one_mul]
  obtain ⟨d, hd, hv⟩ := exists_gen P.isLB (K' := Fin 2) (φ' := ![(snd T P.A).left, (translPt P.A k).left])
    (ε' := ![(N : ℤ), -(N : ℤ)]) (fun V _ g => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, e₀, e₁, neg_neg, zpow_neg, zpow_one, _root_.mul_assoc]
      rw [inv_inv, mul_left_comm (g (snd T P.A ^ m).left)⁻¹, inv_mul_cancel, _root_.mul_one])
    (LB.mulGen P.L _ _ _ _ α (LB.invGen P.L _ _ (LB.pullGen P.L _ _ α (translT P.A k).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  let D : ThetaGrp P.A P.L N T := ⟨k, d, hd⟩
  have hD : ∀ s : Z ⟶ (T ⊗ P.A).left,
      tval D s z J = val α s z J * (val α (s ≫ (translT P.A k).left) z J)⁻¹ := fun s =>
    (hv Z s z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg (val α s z J * ·)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  have hx : U.pt = x := hU.pt_eq
  have hc : CommIsOf P.A P.L N U D 1 :=
    (GlobalLift.weilIs_iff_commIsOf hG P.isAb P.isLB U D 1).1 (hx ▸ hw)
  have q := val_corr hJ hc (r ≫ (ptSecT P.A h).left)
  have q₁ : val (constGen P.A P.L (1 : Γ(T.left, ⊤)ˣ)) (r ≫ (ptSecT P.A h).left) z J = 1 := by
    refine ((gm_res _ z le_top (Set.mem_iInter.2 fun k => k.elim) _).trans
      (gm_pull _ (fst T P.A).left z ⊤ trivial 1)).trans (map_one _)
  have q₂ : tval U (r ≫ (ptSecT P.A h).left) z J * tval D ((r ≫ (ptSecT P.A h).left) ≫ (translT P.A U.pt).left) z J =
      tval D (r ≫ (ptSecT P.A h).left) z J * tval U ((r ≫ (ptSecT P.A h).left) ≫ (translT P.A k).left) z J * 1 :=
    ((val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _))).symm.trans (q.trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _))) q₁)))
  simp only [hD, Category.assoc, pt_translT, hx, _root_.mul_one] at q₂
  have p₁ : (x * (h * k)) ^ m = (x * h) ^ m := by
    rw [← _root_.mul_assoc, mul_pow, hk, _root_.mul_one]
  have p₂ : k * (x * h) = x * (h * k) := by rw [mul_comm k, _root_.mul_assoc]
  rw [p₂, mul_comm k h] at q₂
  rw [p₁]
  have H' := H Z r z J hJ
  set a₁ := val α (r ≫ (ptSecT P.A h).left) z J
  set a₂ := val α (r ≫ (ptSecT P.A (h * k)).left) z J
  set a₃ := val α (r ≫ (ptSecT P.A (x * h)).left) z J
  set a₄ := val α (r ≫ (ptSecT P.A (x * (h * k))).left) z J
  set u₁ := tval U (r ≫ (ptSecT P.A h).left) z J
  set u₂ := tval U (r ≫ (ptSecT P.A (h * k)).left) z J
  set t := val τ (r ≫ β.left) z J
  have f₁ : a₂ * t = (a₂ * a₁⁻¹) * (a₁ * t) := by
    rw [_root_.mul_assoc, inv_mul_cancel_left]
  have f₂ : u₂ * a₄ = (a₂ * a₁⁻¹) * (u₁ * a₃) := by
    apply Additive.ofMul.injective
    replace q₂ := congrArg Additive.ofMul q₂
    simp only [ofMul_mul, ofMul_inv] at q₂ ⊢
    linear_combination (norm := module) -q₂
  rw [f₁, f₂, Units.val_mul _ (a₁ * t), Units.val_mul _ (u₁ * a₃), mul_left_comm, H', _root_.mul_assoc]

end GlobalTheory.UPoinc.USum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueTranslateOrthogonalTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTwistedThetaValue_translate_orthogonal_torsion : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) (k : T ⟶ P.A), k ^ m = 1 → WeilIs P.A P.L N x k 1 → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x (h * k) v := by
  first | exact @GlobalTheory.UPoinc.USum.isTwVal_transl | exact GlobalTheory.UPoinc.USum.isTwVal_transl | (intros; apply GlobalTheory.UPoinc.USum.isTwVal_transl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaValueSubsingletonBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaValueSubsingletonBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section

namespace GlobalTheory.UPoinc.USum

theorem exists_isTwVal_of_subsingleton : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A), Subsingleton T.left → Odd m → N = m ^ 2 → τ.IsGen → x ^ N = 1 → h ^ m = β ≫ z₀ → ∃ v, IsTwVal P N m θ τ β x h v := by
  intro B P N m T₀ T θ z₀ τ β x h hT hm hN hτ hx hh
  subst hN
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hL := P.isLB
  obtain ⟨α, hα⟩ : ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left]
      ![((m ^ 2 : ℕ) : ℤ), -1]), α.IsGen := by
    rw [Nat.cast_pow]
    exact GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨U, hU⟩ : ∃ U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T, SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U := by
    rcases isEmpty_or_nonempty T.left with he | ⟨⟨p⟩⟩
    · exact GlobalTheory.GlobalLift.exists_symLift_empty hL (m ^ 2) x
    · obtain ⟨V, hV, H⟩ := GlobalTheory.EmbLocal.exists_symLift_near hG P (k := m ^ 2) hm.pow x hx p
      obtain ⟨θ', hθ'⟩ := H T (𝟙 T) (by
        rintro _ ⟨q, rfl⟩
        rwa [Subsingleton.elim ((𝟙 T : T ⟶ T).left q) p])
      rw [Category.id_comp] at hθ'
      exact ⟨θ', hθ'⟩
  rcases U with ⟨pt, φU, hφU⟩
  obtain rfl : x = pt := hU.pt_eq.symm
  obtain ⟨s, hs⟩ := GlobalTheory.VVRank.exists_isTwistPull P.A (ψ := mulT P.A T m) (m := snd T P.A ^ m) (hm := lift_snd _ _)
    (a := ((m ^ 2 : ℕ) : ℤ)) (b := 1) hL hα (GlobalTheory.VVRank.pullS P.A 1 β θ)
  obtain ⟨σ, hσ⟩ := GlobalTheory.VVRank.exists_isTwistPull P.A (ψ := translT P.A x) (m := translPt P.A x)
    (hm := lift_snd _ _) hL hφU s
  have e₁ : (ptSecT P.A h).left ≫ (snd T P.A).left = h.left := GlobalTheory.ThetaPtMove.ptSecT_snd h
  have e₂ : (ptSecT P.A h).left ≫ (snd T P.A ^ m).left = (h ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, GlobalTheory.ThetaCompare.pt_snd]
  have e₃ : β.left ≫ z₀.left = (h ^ m).left := by rw [← Over.comp_left, hh]
  obtain ⟨τ', hτ', vτ'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hL (φ' := fun _ : Fin 1 => h.left)
    (ε' := fun _ => ((m ^ 2 : ℕ) : ℤ))
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, zpow_neg, zpow_one]
      group)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A h).left) (LB.pullGen P.L _ _ τ β.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.pullGen_isGen _ _ _ _ hτ _))
  obtain ⟨v, hv⟩ := GlobalTheory.ThetaPtExist.exists_isValueAt hL σ h τ' hτ'
  refine ⟨v, α, ⟨x, φU, hφU⟩, hα, hU, fun Z r z J hJ => ?_⟩
  have q1 := GlobalTheory.ThetaPtMove.sv_of_isValueAt hv r z hJ
  have q2 := GlobalTheory.VVRank.sv_of_isTwistPull P.A hσ (r ≫ (ptSecT P.A h).left) z hJ
  have q3 := GlobalTheory.VVRank.sv_of_isTwistPull P.A hs (r ≫ (ptSecT P.A (x * h)).left) z hJ
  have q4 := GlobalTheory.VVRank.sv_pullS P.A 1 β θ (r ≫ (ptSecT P.A ((x * h) ^ m)).left) z hJ
  rw [Category.assoc, GlobalTheory.ThetaCompare.pt_translT] at q2
  rw [Category.assoc, GlobalTheory.ThetaCompare.pt_mulT] at q3
  rw [vτ' Z r z J hJ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_mul hJ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ] at q1
  rw [← q1, q2, q3, q4, Units.val_mul, Category.assoc, _root_.mul_assoc]
  rfl

end GlobalTheory.UPoinc.USum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedThetaValueSubsingletonBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedThetaValue_subsingleton_base : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A), Subsingleton T.left → Odd m → N = m ^ 2 → τ.IsGen → x ^ N = 1 → h ^ m = β ≫ z₀ → ∃ v, IsTwVal P N m θ τ β x h v := by
  first | exact @GlobalTheory.UPoinc.USum.exists_isTwVal_of_subsingleton | exact GlobalTheory.UPoinc.USum.exists_isTwVal_of_subsingleton | (intros; apply GlobalTheory.UPoinc.USum.exists_isTwVal_of_subsingleton <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.UPoinc.USum

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}

theorem exists_isGenLab (h : USame ρ ρ' lab φ) :
    ∃ P₀ a a' x, IsGenLab ρ ρ' lab φ P₀ a a' x ∧ ∀ b b', x (b + b') = x b * x b' := by
  obtain ⟨P₀, a, a', h₁, h₂, l₁, l₂, hpt⟩ := h
  obtain ⟨w, hw, hadd, -⟩ := GalAct.exists_generic_labels ρ' h₂
  obtain ⟨e, he⟩ := GalAct.exists_mulEquiv_points h₁ (𝟙 _) _ (Category.id_comp _)
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨P₀, a, a', fun b => e (w b), ⟨h₁, h₂, l₁, l₂, fun b => ⟨(w b).left, Over.w (w b), (he _).symm, hw b⟩,
    fun k => ?_⟩, fun b b' => by simp only [hadd, map_mul]⟩
  obtain ⟨v, hv, hv'⟩ := hpt k
  obtain rfl : v = (w (lab k)).left := (cancel_mono a').1 (hv'.trans (hw _).symm)
  exact Over.OverMorphism.ext ((he _).trans hv)

theorem weil_move {B B' : Scheme.{0}} {P : PolAV B} {P₀ : PolAV B'} {f : B' ⟶ B} {a : P₀.A.left ⟶ P.A.left}
    (h : IsGrpPullback P₀.A P.A f a) (l : LBIso P₀.L (P.L.pull a)) (k : ℤ) (w w' : Over.mk (𝟙 B') ⟶ P₀.A)
    {g : B' ⟶ B} (hg : 𝟙 _ ≫ f = g) (x x' : Over.mk g ⟶ P.A) (hx : x.left = w.left ≫ a) (hx' : x'.left = w'.left ≫ a)
    (c : Γ(B', ⊤)ˣ) : WeilIs P₀.A P₀.L k w w' c ↔ WeilIs P.A P.L k x x' c := by
  subst hg
  have := P₀.isAb.comm
  exact weilIs_grpPullback_of_comm' _ _ P.A P₀.A f a P.L P₀.L P.isLB P₀.isLB h l (Over.mk (𝟙 B')) k w w' x x' c hx hx'

theorem map_unitOn {R K : Type} [CommRing R] [CommRing K] (y : R →+* K) (c : Rˣ) :
    Units.map (spMap y).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map y.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

variable {P₀ : PolAV (Sp Ω')} {a : P₀.A.left ⟶ ρ.P.A.left} {a' : P₀.A.left ⟶ ρ'.P.A.left}
  {x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)}

theorem IsGenLab.weil (h : IsGenLab ρ ρ' lab φ P₀ a a' x) (b b' : S'.Gam) : ∃ c : Ω'ˣ,
    (c : Ω') = algebraMap o' Ω' (S'.ζ ^ (S'.r * S'.N * (eStd S'.g _ b b').val)) ∧
      WeilIs ρ.P.A ρ.P.L (S'.r * S'.N : ℕ) (x b) (x b') (unitOn c) := by
  obtain ⟨h₁, h₂, l₁, l₂, hw, -⟩ := h
  have hpos : (S'.r * S'.N) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Nat.mul_ne_zero (by have := S'.r_pos; omega) (by have := S'.N_ge; omega))
  obtain ⟨c₀, hc₀⟩ := ((S'.prim.isUnit hpos).pow (S'.r * S'.N * (eStd S'.g _ b b').val)).map (algebraMap o' S'.R)
  have H := CommPairing.weilIs_pull GlobalTheory.abelianSchemeLaws_all.1.globalFns ρ'.P.isAb ρ'.P.isLB
    (genTo S'.R.val.toRingHom) (ρ'.weil b b' c₀ hc₀)
  obtain ⟨w, e₀, e₁, e₂⟩ := hw b
  obtain ⟨w', e₀', e₁', e₂'⟩ := hw b'
  refine ⟨Units.map S'.R.val.toRingHom.toMonoidHom c₀, congrArg Subtype.val hc₀, ?_⟩
  rw [← map_unitOn]
  exact (weil_move h₁ l₁ _ (Over.homMk w e₀) (Over.homMk w' e₀') (Category.id_comp _) _ _ e₁.symm e₁'.symm _).1
    ((weil_move h₂ l₂ _ (Over.homMk w e₀) (Over.homMk w' e₀') (Category.id_comp _) _ _ e₂.symm e₂'.symm _).2 H)

theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1 (congrArg Units.val h))

theorem IsGenLab.weil_conj (h : IsGenLab ρ ρ' lab φ P₀ a a' x) (σ : Ω' →+* Ω')
    (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)) (hs : s.left = spMap σ)
    {g : S'.Gam → S'.Gam} (hg : ∀ b, x (g b) = s ≫ x b) (b b' : S'.Gam) :
    σ (algebraMap o' Ω' (S'.ζ ^ (S'.r * S'.N * (eStd S'.g _ b b').val))) =
      algebraMap o' Ω' (S'.ζ ^ (S'.r * S'.N * (eStd S'.g _ (g b) (g b')).val)) := by
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨c, hc, H⟩ := h.weil b b'
  obtain ⟨c', hc', H'⟩ := h.weil (g b) (g b')
  have H₂ := CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB s H
  rw [← hg, ← hg] at H₂
  have e := CommutatorPairing.weilIs_unique hG ρ.P.isAb ρ.P.isLB H₂ H'
  rw [hs] at e
  rw [← hc, ← hc']
  exact congrArg Units.val (unitOn_injective ((map_unitOn σ c).symm.trans e))

section Add

variable (hadd : ∀ b b', x (b + b') = x b * x b')
include hadd

theorem pt_zero : x 0 = 1 := by
  have := hadd 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem pt_nsmul (n : ℕ) (b : S'.Gam) : x (n • b) = x b ^ n := by
  induction n with
  | zero => rw [zero_smul, pt_zero hadd, pow_zero]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem pt_pow_level (b : S'.Gam) : x b ^ (S'.N * S'.r) = 1 := by
  have h0 : (S'.N * S'.r) • b = 0 := by
    funext i
    simp [nsmul_eq_mul, mul_comm S'.N]
  rw [← pt_nsmul hadd, h0, pt_zero hadd]

theorem IsGenLab.weil_one [ArithBase o Ω] [ArithBase o' Ω'] (h : IsGenLab ρ ρ' lab φ P₀ a a' x) {t k : S'.Gam}
    (hk : S'.N • k = 0) (he : eStd S'.g _ t k = 0) : WeilIs ρ.P.A ρ.P.L S'.N (x (S'.r • t)) (x k) 1 := by
  obtain ⟨c, hc, H⟩ := h.weil t k
  have := ArithBase.ded (o := o) (Ω := Ω)
  have := ArithBase.char (o := o') (Ω := Ω')
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  obtain rfl : c = 1 := Units.ext (by rw [hc, he]; simp)
  rw [show unitOn (1 : Ω'ˣ) = 1 from map_one _, mul_comm S'.r, Nat.cast_mul] at H
  rw [pt_nsmul hadd]
  refine ((GlobalTheory.abelianSchemeLaws_all.1.weil _ ρ.P S'.N _).2.2.2 S'.r _ _ 1 ?_ (pt_pow_level hadd t)
    (by rw [← pt_nsmul hadd, hk, pt_zero hadd])).1 H
  have hu : IsUnit ((S'.N * S'.r : ℕ) : Ω') := IsUnit.mk0 _ (Nat.cast_ne_zero.2
    (Nat.mul_ne_zero (by have := S'.N_ge; omega) (by have := S'.r_pos; omega)))
  simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom

end Add


variable (ρ x) in
def TV (m : ℕ) (t h : S'.Gam) (κ : S.Gam) (v : Ω') : Prop :=
  IsTwVal ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • t)) (x h) ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom v)

theorem odd_level (ρ' : S'.Real) : Odd S'.N := by rw [ρ'.N_eq]; exact ρ'.n_odd.pow.pow

theorem TV.unique (ρ' : S'.Real) {m : ℕ} {t h : S'.Gam} {κ : S.Gam} {v v' : Ω'} (H : TV ρ x m t h κ v)
    (H' : TV ρ x m t h κ v') : v = v' :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv).1
    (GlobalTheory.T.isTwistedThetaValue_unique _ _ _ _ _ _ _ _ _ _ (odd_level ρ') H H')

theorem TV.ex (hx : IsGenLab ρ ρ' lab φ P₀ a a' x) (hadd : ∀ b b', x (b + b') = x b * x b') {m : ℕ} (hm : S'.N = m ^ 2)
    (t : S'.Gam) {h : S'.Gam} {κ : S.Gam} (hh : m • h = lab κ) : ∃ v, TV ρ x m t h κ v := by
  have hodd : Odd m := (Nat.odd_pow_iff two_ne_zero).1 (hm ▸ odd_level ρ')
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_twistedThetaValue_subsingleton_base ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • t)) (x h)
    (inferInstanceAs (Subsingleton (PrimeSpectrum Ω'))) hodd hm (ρ.fr_tors κ).2.1
    (by rw [pt_nsmul hadd, ← pow_mul, mul_comm, pt_pow_level hadd]) (by rw [← pt_nsmul hadd, hh, hx.2.2.2.2.2])
  obtain ⟨v, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv).2 v
  exact ⟨v, hv⟩

theorem TV.transl [ArithBase o Ω] [ArithBase o' Ω'] (hx : IsGenLab ρ ρ' lab φ P₀ a a' x)
    (hadd : ∀ b b', x (b + b') = x b * x b') {m : ℕ} (hm : S'.N = m ^ 2) {t h k : S'.Gam} {κ : S.Gam} {v : Ω'}
    (hk : m • k = 0) (he : eStd S'.g _ t k = 0) (H : TV ρ x m t h κ v) : TV ρ x m t (h + k) κ v := by
  rw [TV, hadd]
  exact GlobalTheory.T.isTwistedThetaValue_translate_orthogonal_torsion _ _ _ _ _ _ _ _ _ _ (by rw [← pt_nsmul hadd, hk, pt_zero hadd])
    (hx.weil_one hadd ((congrArg (· • k) hm).trans (by rw [sq, mul_smul, hk, smul_zero])) he) H

theorem TV.conj (σ : Ω' →+* Ω')
    (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)) (hs : s.left = spMap σ)
    (g : S'.Gam →+ S'.Gam) (hg : ∀ b, x (g b) = s ≫ x b) {m : ℕ} {t h : S'.Gam} {κ : S.Gam} {v : Ω'}
    (H : TV ρ x m t h κ v) : TV ρ x m (g t) (g h) κ (σ v) := by
  have H' := GlobalTheory.T.isTwistedThetaValue_pullback_base_change _ _ _ _ _ _ _ _ _ s H
  have e : s ≫ genTo (φ.comp S.R.val.toRingHom) = genTo _ := Over.OverMorphism.ext (Over.w s)
  rw [e, ← hg, ← hg, map_nsmul, hs] at H'
  have e' := congrArg (fun q => q.hom v) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))
  exact (congrArg (IsTwVal ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • g t)) (x (g h))) e').mpr H'

instance neZero_level (S : ThetaSys o Ω) : NeZero (S.r * S.N) :=
  ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩

theorem zeta_pow_eq_one_iff [ArithBase o' Ω'] (e : ZMod (S'.r * S'.N)) :
    algebraMap o' Ω' (S'.ζ ^ (S'.r * S'.N * e.val)) = 1 ↔ e = 0 := by
  rw [map_pow, (S'.prim.map_of_injective ArithBase.inj).pow_eq_one_iff_dvd, sq,
    Nat.mul_dvd_mul_iff_left (NeZero.pos _), ← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]

theorem zetaN_pow_level : S'.ζN ^ S'.N = 1 := by
  rw [ThetaSys.ζN, ← pow_mul, ← S'.prim.pow_eq_one]
  congr 1
  ring

theorem zetaN_pow_cast (e : ZMod (S'.r * S'.N)) :
    S'.ζN ^ (ZMod.castHom (dvd_mul_left S'.N S'.r) (ZMod S'.N) e).val = (S'.ζ ^ (S'.r * S'.N * e.val)) ^ S'.r := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ zetaN_pow_level, ThetaSys.ζN, ← pow_mul,
    ← pow_mul]
  congr 1
  ring

theorem zetaN_neg_mul (c : ZMod S'.N) : S'.ζN ^ (-c).val * S'.ζN ^ c.val = 1 := by
  have : NeZero S'.N := ⟨by have := S'.N_ge; omega⟩
  rw [← pow_add, pow_eq_pow_mod _ zetaN_pow_level, ← ZMod.val_add, neg_add_cancel, ZMod.val_zero, pow_zero]


variable (S') in
def partV (H : AddSubgroup S'.Gam) (i : S'.J) (a h : S'.Gam) : Ω' :=
  ∑ j, algebraMap o' Ω' (S'.proj (S'.perp H) (wtChar S' _ a) j i) * S'.ev h j

theorem partV_eq (H : AddSubgroup S'.Gam) [Fintype (S'.perp H)] (i : S'.J) (a h : S'.Gam) :
    partV S' H i a h = algebraMap o' Ω' (Ring.inverse (Nat.card (S'.perp H) : o')) *
      ∑ t : S'.perp H, algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ a t)).val) *
        ∑ j, algebraMap o' Ω' (S'.ρ t j i) * S'.ev h j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [partV, ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul,
    map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring

theorem map_inverse_natCast (σ : Ω' →+* Ω') (n : ℕ) :
    σ (algebraMap o' Ω' (Ring.inverse (n : o'))) = algebraMap o' Ω' (Ring.inverse (n : o')) := by
  by_cases h : IsUnit (n : o')
  · have e : algebraMap o' Ω' (Ring.inverse (n : o')) = (n : Ω')⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_natCast (algebraMap o' Ω'), ← map_mul, Ring.inverse_mul_cancel _ h, map_one])
    rw [e, map_inv₀, map_natCast]
  · rw [Ring.inverse_non_unit _ h, map_zero, map_zero]


variable (ρ') in
def IsConj (σ : Ω' →+* Ω') (g : S'.Gam → S'.Gam) : Prop :=
  ∃ (P₀ : PolAV (Sp Ω')) (b : P₀.A.left ⟶ ρ'.P.A.left) (t : P₀.A.left ⟶ P₀.A.left),
    IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) b ∧ IsGrpPullback P₀.A P₀.A (spMap σ) t ∧
    LBIso P₀.L (ρ'.P.L.pull b) ∧ LBIso P₀.L (P₀.L.pull t) ∧
    ∀ x (w w' : Sp Ω' ⟶ P₀.A.left), w ≫ b = spMap S'.R.val.toRingHom ≫ (ρ'.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S'.R.val.toRingHom ≫ (ρ'.pt (g x)).left

theorem IsGenLab.exists_conj (hx : IsGenLab ρ ρ' lab φ P₀ a a' x) (σ : Ω' →+* Ω') (hσ : Function.Surjective σ)
    (hφ : σ.comp φ = φ) : ∃ (g : S'.Gam ≃+ S'.Gam)
      (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)), s.left = spMap σ ∧
      (∀ b, x (g b) = s ≫ x b) ∧ IsConj ρ' σ g ∧ ∀ k, g (lab k) = lab k := by
  obtain ⟨h₁, h₂, l₁, l₂, hw, hlab⟩ := hx
  have hs : spMap σ ≫ spMap (φ.comp S.R.val.toRingHom) = spMap (φ.comp S.R.val.toRingHom) :=
    GalTrans.sp_comp (by rw [← RingHom.comp_assoc, hφ])
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a = a ∧ t ≫ P₀.A.hom = P₀.A.hom ≫ spMap σ :=
    ⟨h₁.1.lift a (P₀.A.hom ≫ spMap σ) (by rw [Category.assoc, hs, h₁.1.w]), h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap σ) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (ρ.P.L.pull a) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame ρ.P.L (fun _ => a) (fun _ => a) _ t fun _ => ht₁.symm)
  obtain ⟨g, hg, hg'⟩ := GalAct.exists_label_action ρ' h₂ σ hσ ht
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨g, Over.homMk (spMap σ) hs, rfl, fun b => Over.OverMorphism.ext ?_, ⟨P₀, a', t, h₂, ht, l₂,
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, hg⟩, fun k => ?_⟩
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw b
    obtain ⟨w', -, e₁', e₂'⟩ := hw (g b)
    have c : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, e₀]; simp
    have k := ht.1.lift_fst _ _ c
    obtain rfl : w' = ht.1.lift _ _ c := (cancel_mono a').1 (e₂'.trans (hg b w _ e₂ k).symm)
    rw [← e₁', ← ht₁, reassoc_of% k, e₁]
    rfl
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw (lab k)
    refine hg' _ w e₂ (h₁.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ht₁, e₁, hlab]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hs)).symm
    · rw [Category.assoc, Category.assoc, ht₂, reassoc_of% e₀, e₀, Category.comp_id]


open Classical in
theorem exists_parts [ArithBase o Ω] [ArithBase o' Ω'] (hS : USame ρ ρ' lab φ) {m : ℕ} (hm : S'.N = m ^ 2)
    (H : AddSubgroup S'.Gam) (x₀ : S.Gam) (h₀ : S.th x₀ ≠ 0) (h₀' : S'.th (lab x₀) ≠ 0) :
    ∃ f : S'.Gam → S.Gam → Ω',
      (∀ b κ, (¬ ∃ h ∈ H, m • h = lab κ) → f b κ = 0) ∧
      (∀ b κ, ∀ h ∈ H, m • h = lab κ → ∃ (ξ : Ω') (k : ℕ), 0 < k ∧ ξ ^ k = 1 ∧
        f b κ = ξ * (partV S' H ρ'.i₀ b h / S'.th (lab x₀))) ∧
      (∀ b b', wtChar S' (S'.perp H) b = wtChar S' (S'.perp H) b' → f b = f b') ∧
      ∀ σ : Ω' →+* Ω', Function.Surjective σ → σ.comp φ = φ → ∃ g : S'.Gam ≃+ S'.Gam, IsConj ρ' σ g ∧
        (∀ k, g (lab k) = lab k) ∧ ((∀ y, g y ∈ H ↔ y ∈ H) → ∀ b κ, σ (f b κ) = f (g b) κ) := by
  obtain ⟨P₀, a, a', x, hx, hadd⟩ := exists_isGenLab hS
  have := Fintype.ofFinite (S'.perp H)
  have hV : ∀ κ, ∃ V : S'.perp H → Ω', ((¬ ∃ h ∈ H, m • h = lab κ) → V = 0) ∧
      ∀ h ∈ H, m • h = lab κ → ∀ t : S'.perp H, TV ρ x m t h κ (V t) := fun κ => by
    by_cases he : ∃ h ∈ H, m • h = lab κ
    · obtain ⟨h, hh, e⟩ := id he
      choose V hV using fun t : S'.perp H => TV.ex hx hadd hm t e
      refine ⟨V, fun hn => absurd he hn, fun h' hh' e' t => ?_⟩
      have := (hV t).transl hx hadd hm (k := h' - h) (by rw [smul_sub, e, e', sub_self]) (t.2 _ (sub_mem hh' hh))
      rwa [add_sub_cancel] at this
    · exact ⟨0, fun _ => rfl, fun h hh e => absurd ⟨h, hh, e⟩ he⟩
  choose V hV₀ hV using hV
  have hφ₀ : φ (S.th x₀) ≠ 0 := (map_ne_zero φ).2 h₀
  refine ⟨fun b κ => algebraMap o' Ω' (Ring.inverse (Nat.card (S'.perp H) : o')) *
    (∑ t : S'.perp H, algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val) * V κ t) / φ (S.th x₀),
    fun b κ hn => by simp [hV₀ κ hn], fun b κ h hh e => ?_, fun b b' e => by simp only [e], fun σ hσ hφ => ?_⟩
  · obtain ⟨ξ, ⟨k, hk, hξ⟩, hc⟩ := GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ' lab φ P₀ a a' x hx m hm κ x₀ h e
    refine ⟨ξ, k, hk, hξ, ?_⟩
    have hv : ∀ t : S'.perp H, V κ t =
        (ξ * φ (S.th x₀) / S'.th (lab x₀)) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := fun t => by
      rw [div_mul_eq_mul_div, eq_div_iff h₀']
      exact hc t _ (hV κ h hh e t)
    simp only [hv, partV_eq, mul_left_comm _ (ξ * φ (S.th x₀) / S'.th (lab x₀)), ← Finset.mul_sum]
    field_simp
  · obtain ⟨g, s, hs, hg, hc, hl⟩ := hx.exists_conj σ hσ hφ
    refine ⟨g, hc, hl, fun hH b κ => ?_⟩
    have hw := hx.weil_conj σ s hs hg
    have h0 : ∀ y y', eStd S'.g _ y y' = 0 ↔ eStd S'.g _ (g y) (g y') = 0 := fun y y' => by
      rw [← zeta_pow_eq_one_iff, ← zeta_pow_eq_one_iff, ← hw, map_eq_one_iff σ σ.injective]
    have hT : ∀ t, t ∈ S'.perp H ↔ g t ∈ S'.perp H := fun t =>
      ⟨fun ht y hy => by
        obtain ⟨y, rfl⟩ := g.surjective y
        exact (h0 _ _).1 (ht y ((hH y).1 hy)), fun ht y hy => (h0 _ _).2 (ht _ ((hH y).2 hy))⟩
    let e : S'.perp H ≃ S'.perp H := g.toEquiv.subtypeEquiv hT
    have hζ : ∀ t : S'.perp H, σ (algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val)) =
        algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) (e t))).val) := fun t => by
      have e₁ : σ (algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ b t).val)) =
          algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ (g b) (e t)).val) := by
        refine (congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_pow_cast _)).trans
          (Eq.trans ?_ (congrArg (algebraMap o' Ω') (zetaN_pow_cast _)).symm)
        rw [map_pow, map_pow, hw, ← map_pow]
        rfl
      have e₂ := congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_neg_mul (wtChar S' _ b t))
      have e₃ := congrArg (algebraMap o' Ω') (zetaN_neg_mul (wtChar S' _ (g b) (e t)))
      simp only [map_mul, map_one] at e₂ e₃
      rw [e₁] at e₂
      exact (eq_inv_of_mul_eq_one_left e₂).trans (eq_inv_of_mul_eq_one_left e₃).symm
    have hσV : ∀ t : S'.perp H, σ (V κ t) = V κ (e t) := fun t => by
      by_cases he : ∃ h ∈ H, m • h = lab κ
      · obtain ⟨h, hh, e'⟩ := he
        exact ((hV κ h hh e' t).conj σ s hs g.toAddMonoidHom hg).unique ρ'
          (hV κ (g h) ((hH h).2 hh) (by rw [← map_nsmul, e', hl]) (e t))
      · simp [hV₀ κ he]
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_div₀, map_mul, map_inverse_natCast, map_sum, show σ (φ (S.th x₀)) = φ (S.th x₀) from RingHom.congr_fun hφ _,
      ← Equiv.sum_comp e fun t => algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) t)).val) * V κ t]
    simp only [map_mul, hζ, hσV]

end GlobalTheory.UPoinc.USum
