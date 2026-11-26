module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrimCocycle

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

abbrev lamφ (B : Over S) [GrpObj B] : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
  fun I => (psum B (x2 B) I.down).left

abbrev lamε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem prod_lam {T : Over S} (x y : T ⟶ B) {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ I, h ((lift x y).left ≫ lamφ B I) ^ lamε I =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ B).left := by
  have e : ∀ I, (lift x y).left ≫ lamφ B I = (psum B ![x, y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I.down).trans
      (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum B ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ lamε I) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum B ![x, y] ∅ = 1 := rfl
  have p₁ : psum B ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum B ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum B ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem exists_normalised {L : LB B.left} (hL : L.IsLB) (t : LB.Gen (LB.LinComb L (lamφ B) lamε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (lamφ B) lamε), u.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good L z J → val₂ u z J (1 : T ⟶ B) 1 = 1 := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := lamφ B) (ε' := lamε)
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
        (c := ∏ i, k (lamφ B i) ^ lamε i) rfl
        (DVR.prod_neg _ _ (prod_lam (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B) k))) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (lift (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, fun T z J hJ => ?_⟩
  have : (lift (1 : T ⟶ B) (1 : T ⟶ B)).left ≫ (lift (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B)).left =
      (lift (1 : T ⟶ B) (1 : T ⟶ B)).left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
  rw [val₂, hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]

theorem val_mul_eq (hG : GlobalFnsSt) (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB)
    (u : LB.Gen (LB.LinComb L (lamφ B) lamε)) (hu : u.IsGen)
    (e : 𝟙_ (Over S) ⟶ G3 B) (a b c d a' b' c' d' : G3 B ⟶ B)
    (hF : ∀ (V : Type) [CommGroup V] (k : (G3 B ⟶ B) → V),
      (k (a' * b') * (k a')⁻¹ * (k b')⁻¹ * k 1) * (k (c' * d') * (k c')⁻¹ * (k d')⁻¹ * k 1) =
      (k (a * b) * (k a)⁻¹ * (k b)⁻¹ * k 1) * (k (c * d) * (k c)⁻¹ * (k d)⁻¹ * k 1))
    (ha : e ≫ a = 1) (hb : e ≫ b = 1) (hc : e ≫ c = 1) (hd : e ≫ d = 1)
    (ha' : e ≫ a' = 1) (hb' : e ≫ b' = 1) (hc' : e ≫ c' = 1) (hd' : e ≫ d' = 1)
    {T : Over S} (ρ : T ⟶ G3 B) {z : T.left} {J} (hJ : Good L z J) :
    val₂ u z J (ρ ≫ a) (ρ ≫ b) * val₂ u z J (ρ ≫ c) (ρ ≫ d) =
      val₂ u z J (ρ ≫ a') (ρ ≫ b') * val₂ u z J (ρ ≫ c') (ρ ≫ d') := by
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good L z J → ∀ a b : T ⟶ B,
      val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := fun ρ z J hJ a b => by
    rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
  have sj : Function.Surjective ((snd B (B ⊗ B)).left ≫ (snd B B).left ≫ B.hom).appTop.hom :=
    surj_comp (surj_snd hG hB _) (surj_comp (surj_snd hG hB _) (hG _ _ hB).2)
  have he : e.left ≫ (snd B (B ⊗ B)).left ≫ (snd B B).left ≫ B.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 B) {z : T'.left} {J}, Good L z J → ∀ a b c d : G3 B ⟶ B,
      val (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ u (lift a b).left) (LB.pullGen L _ _ u (lift c d).left))
        σ.left z J = val₂ u z J (σ ≫ a) (σ ≫ b) * val₂ u z J (σ ≫ c) (σ ≫ d) := fun σ z J hJ a b c d =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))
  refine (ev ρ hJ a b c d).symm.trans (Eq.trans (gen_unique' hL (fun V _ k => ?_) _ e.left he sj
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
    (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ a' b' c' d'))
  · exact (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
      (prod_lam a' b' k) (prod_lam c' d' k)).trans ((hF V fun q => k q.left).trans
      (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
        (prod_lam a b k) (prod_lam c d k)).symm)
  · refine (ev e hI a b c d).trans (Eq.trans ?_ (ev e hI a' b' c' d').symm)
    rw [ha, hb, hc, hd, ha', hb', hc', hd']

theorem primitive_cocycle : GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (O : RigLB B), (∃ t : LB.Gen (abelian₂ B O.L), t.IsGen) → ∃ t : LB.Gen (abelian₂ B O.L), t.IsGen ∧ ∀ (Z : Over S) (z : Z.left) (J : (Z.left ⟶ B.left) → O.L.ι), Geo.Tor.Good O.L z J → let v : (Z ⟶ B) → (Z ⟶ B) → (Z.left.presheaf.stalk z)ˣ := fun x y => Geo.Tor.val (L := O.L) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (ε := fun I => (-1) ^ (2 - I.down.card)) t (lift x y).left z J; (∀ x, v x 1 = 1) ∧ (∀ x y, v x y = v y x) ∧ ∀ x y w, v (x * y) w * v x y = v x (y * w) * v y w := by
  rintro hG S B _ _ hB O ⟨t, ht⟩
  obtain ⟨u, hu, h₀⟩ := exists_normalised O.isLB t ht
  refine ⟨u, hu, fun Z z J hJ => ?_⟩
  show (∀ x, val₂ u z J x 1 = 1) ∧ (∀ x y, val₂ u z J x y = val₂ u z J y x) ∧
    ∀ x y w, val₂ u z J (x * y) w * val₂ u z J x y = val₂ u z J x (y * w) * val₂ u z J y w
  let p₀ := x3 B 0
  let p₁ := x3 B 1
  let p₂ := x3 B 2
  let e : 𝟙_ (Over S) ⟶ G3 B := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have o : e ≫ (1 : G3 B ⟶ B) = 1 := MonObj.comp_one _
  have r₀ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₀ = x := fun x y w => by simp [p₀, x3]
  have r₁ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₁ = y := fun x y w => by simp [p₁, x3]
  have r₂ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₂ = w := fun x y w => by simp [p₂, x3]
  refine ⟨fun x => ?_, fun x y => ?_, fun x y w => ?_⟩
  · have := val_mul_eq hG hB O.isLB u hu e p₀ 1 1 1 1 1 1 1 (fun V _ k => by simp) e₀ o o o o o o o
      (lift x (lift x x)) hJ
    rw [r₀, MonObj.comp_one, h₀ Z z J hJ] at this
    simpa using this
  · have := val_mul_eq hG hB O.isLB u hu e p₀ p₁ 1 1 p₁ p₀ 1 1 (fun V _ k => by
      rw [mul_comm p₁ p₀, mul_right_comm (k (p₀ * p₁))]) e₀ e₁ o o e₁ e₀ o o (lift x (lift y x)) hJ
    rw [r₀, r₁] at this
    exact mul_right_cancel this
  · have := val_mul_eq hG hB O.isLB u hu e (p₀ * p₁) p₂ p₀ p₁ p₀ (p₁ * p₂) p₁ p₂ (fun V _ k => by
      rw [_root_.mul_assoc p₀ p₁ p₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) ((MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])) e₂ e₀ e₁ e₀
      ((MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])) e₁ e₂ (lift x (lift y w)) hJ
    rwa [MonObj.comp_mul, MonObj.comp_mul, r₀, r₁, r₂] at this

end GlobalTheory.PrimCocycle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyTrivialOfIsoPull
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeLawCompare

section General

variable {Y T : Scheme.{0}}

def IsGenOn (M : LB Y) (W : Y.Opens) (d : ∀ j, Γ(Y, W ⊓ M.U j)ˣ) : Prop :=
  ∀ j j' (y : Y), y ∈ W → y ∈ M.U j → y ∈ M.U j' →
    gm (𝟙 Y) y (W ⊓ M.U j) (d j) =
      gm (𝟙 Y) y (M.U j ⊓ M.U j') (M.g j j') * gm (𝟙 Y) y (W ⊓ M.U j') (d j')

theorem gen_restrict_iff (M : LB Y) (W : Y.Opens) :
    (∃ c : LB.Gen (M.pull W.ι), c.IsGen) ↔ ∃ d, IsGenOn M W d := by
  constructor
  · rintro ⟨c, hc⟩
    choose b hb using fun j : M.ι =>
      exists_ext_unit W.ι ((M.pull W.ι).U fun _ => j) (c.s fun _ => j)
    have le : ∀ j, W ⊓ M.U j ≤ W.ι ''ᵁ ((M.pull W.ι).U fun _ => j) :=
      fun j y hy => ⟨⟨y, hy.1⟩, mem_pull.2 hy.2, rfl⟩
    refine ⟨fun j => res (le j) (b j), fun j j' y hW hj hj' => ?_⟩
    let z : W.toScheme := ⟨y, hW⟩
    have hz : W.ι z ∈ W ⊓ M.U j ⊓ M.U j' := ⟨⟨hW, hj⟩, hj'⟩
    have l₁ : W ⊓ M.U j ⊓ M.U j' ≤ W ⊓ M.U j := inf_le_left
    have l₂ : W ⊓ M.U j ⊓ M.U j' ≤ M.U j ⊓ M.U j' := fun _ h => ⟨h.1.2, h.2⟩
    have l₃ : W ⊓ M.U j ⊓ M.U j' ≤ W ⊓ M.U j' := fun _ h => ⟨h.1.1, h.2⟩
    have v : ∀ i (hi : y ∈ M.U i), gm W.ι z (W ⊓ M.U i) (res (le i) (b i)) =
        gm (𝟙 _) z ((M.pull W.ι).U fun _ => i) (c.s fun _ => i) := fun i hi => by
      have h := hb i _ (𝟙 _) z (mem_pull.2 hi)
      rw [Category.id_comp] at h
      exact (gm_res W.ι z (le i) ⟨hW, hi⟩ _).trans h
    have m : (𝟙 W.toScheme : _ ⟶ _) z ∈ ((M.pull W.ι).U fun _ => j) ⊓ ((M.pull W.ι).U fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    have e := (gm_res (𝟙 _) z _ m _).symm.trans ((congrArg (gm (𝟙 _) z _) (hc (fun _ => j) (fun _ => j'))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M W.ι (𝟙 _) z _ _ m.1 m.2) (gm_res (𝟙 _) z _ m _))))
    rw [Category.id_comp] at e
    have key := gm_inj W.ι z hz hz (a := res l₁ (res (le j) (b j)))
      (b := res l₂ (M.g j j') * res l₃ (res (le j') (b j'))) (by
        rw [map_mul, gm_res W.ι z l₁ hz, gm_res W.ι z l₂ hz, gm_res W.ι z l₃ hz, v j hj, v j' hj']
        exact e)
    rw [map_mul, gm_res (𝟙 Y) (W.ι z) l₁ hz, gm_res (𝟙 Y) (W.ι z) l₂ hz, gm_res (𝟙 Y) (W.ι z) l₃ hz] at key
    exact key
  · rintro ⟨d, hd⟩
    have le : ∀ J : PUnit → M.ι, (M.pull W.ι).U J ≤ W.ι ⁻¹ᵁ (W ⊓ M.U (J PUnit.unit)) :=
      fun J z hz => ⟨z.2, mem_pull.1 hz⟩
    refine ⟨⟨fun J => res (le J) (pullU W.ι _ (d (J PUnit.unit)))⟩, fun J J' => ?_⟩
    have e : res (inf_le_left : W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤ _) (d (J PUnit.unit)) =
        res (show W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤
            M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) from fun _ h => ⟨h.1.2, h.2⟩)
          (M.g (J PUnit.unit) (J' PUnit.unit)) *
        res (show W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤
            W ⊓ M.U (J' PUnit.unit) from fun _ h => ⟨h.1.1, h.2⟩)
          (d (J' PUnit.unit)) := unit_ext fun y hy => by
      rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
      exact hd _ _ y hy.1.1 hy.1.2 hy.2
    refine unit_ext fun z hz => ?_
    have hz' : W.ι z ∈ W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) :=
      ⟨⟨z.2, mem_pull.1 hz.1⟩, mem_pull.1 hz.2⟩
    have e' := congrArg (gm W.ι z _) e
    rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz'] at e'
    have v : ∀ I : PUnit → M.ι, z ∈ (M.pull W.ι).U I →
        gm (𝟙 _) z ((M.pull W.ι).U I) (res (le I) (pullU W.ι _ (d (I PUnit.unit)))) =
          gm W.ι z (W ⊓ M.U (I PUnit.unit)) (d (I PUnit.unit)) := fun I hI =>
      (gm_res (𝟙 _) z (le I) hI _).trans ((gm_pull (𝟙 _) W.ι z _ (le I hI) _).trans
        (by rw [Category.id_comp]))
    refine ((gm_res (𝟙 _) z _ hz _).trans (v J hz.1)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull_g M W.ι (𝟙 _) z J J' hz.1 hz.2).trans ?_)
      ((gm_res (𝟙 _) z _ hz _).trans (v J' hz.2)))
    rw [Category.id_comp]

theorem locally_trivial_of_iso_pull (p : Y ⟶ T) (M : LB Y) {N : LB T} (hN : N.IsLB)
    (u : LB.Iso (N.pull p) M) (hu : u.IsGen) (t : T) :
    ∃ V : T.Opens, t ∈ V ∧ ∃ c : LB.Gen (M.pull (p ⁻¹ᵁ V).ι), c.IsGen := by
  obtain ⟨i, hi⟩ := exists_chart hN t
  refine ⟨N.U i, hi, (gen_restrict_iff M _).2 ?_⟩
  have le : ∀ j, p ⁻¹ᵁ N.U i ⊓ M.U j ≤ M.U j ⊓ (N.pull p).U fun _ => i :=
    fun j y hy => ⟨hy.2, mem_pull.2 hy.1⟩
  refine ⟨fun j => res (le j) (u.s (j, fun _ => i)), fun j j' y hW hj hj' => ?_⟩
  have hI : (𝟙 Y : Y ⟶ Y) y ∈ (N.pull p).U fun _ => i := mem_pull.2 hW
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U j ⊓ (N.pull p).U (fun _ => i) ⊓ (M.U j' ⊓ (N.pull p).U fun _ => i) :=
    ⟨⟨hj, hI⟩, hj', hI⟩
  have e := (gm_res (𝟙 Y) y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _)
    (hu (j, fun _ => i) (j', fun _ => i))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div (N.pull p) M (𝟙 Y) y (j, fun _ => i) (j', fun _ => i) hm) (gm_res (𝟙 Y) y _ hm _))))
  rw [gm_self (LB.isLB_pull hN p) (𝟙 Y) y hI, inv_one, _root_.mul_one] at e
  exact (gm_res (𝟙 Y) y (le j) ⟨hW, hj⟩ _).trans
    (e.trans (congrArg _ (gm_res (𝟙 Y) y (le j') ⟨hW, hj'⟩ _).symm))

theorem iso_pull_of_locally_trivial (p : Y ⟶ T) (hp : ∀ V : T.Opens, Function.Bijective (p.app V).hom)
    {M : LB Y} (hM : M.IsLB)
    (h : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ c : LB.Gen (M.pull (p ⁻¹ᵁ V).ι), c.IsGen) :
    ∃ N : LB T, N.IsLB ∧ ∃ u : LB.Iso (N.pull p) M, u.IsGen := by
  choose V hV hc using h
  choose d hd using fun t => (gen_restrict_iff M _).1 (hc t)
  have inj : ∀ (O : T.Opens) (a b : Γ(T, O)ˣ),
      (∀ y : Y, p y ∈ O → gm p y O a = gm p y O b) → a = b := fun O a b hab => by
    have e : pullU p O a = pullU p O b := unit_ext fun y hy => by
      rw [gm_pull (𝟙 Y) p y O hy, gm_pull (𝟙 Y) p y O hy, Category.id_comp]
      exact hab y hy
    exact Units.ext ((hp O).1 (congrArg Units.val e))
  have ratio : ∀ t t' : T, ∃ g : Γ(T, V t ⊓ V t')ˣ, ∀ j (y : Y), p y ∈ V t → p y ∈ V t' → y ∈ M.U j →
      gm p y _ g = gm (𝟙 Y) y (p ⁻¹ᵁ V t' ⊓ M.U j) (d t' j) * (gm (𝟙 Y) y (p ⁻¹ᵁ V t ⊓ M.U j) (d t j))⁻¹ := by
    intro t t'
    have l₁ : ∀ j, p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j ≤ p ⁻¹ᵁ V t ⊓ M.U j := fun j y hy => ⟨hy.1.1, hy.2⟩
    have l₂ : ∀ j, p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j ≤ p ⁻¹ᵁ V t' ⊓ M.U j := fun j y hy => ⟨hy.1.2, hy.2⟩
    have v : ∀ j (y : Y) (hy : y ∈ p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j),
        gm (𝟙 Y) y _ (res (l₂ j) (d t' j) * (res (l₁ j) (d t j))⁻¹) =
          gm (𝟙 Y) y (p ⁻¹ᵁ V t' ⊓ M.U j) (d t' j) * (gm (𝟙 Y) y (p ⁻¹ᵁ V t ⊓ M.U j) (d t j))⁻¹ :=
      fun j y hy => by rw [map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy]
    obtain ⟨a, ha⟩ := glue_unit (p ⁻¹ᵁ (V t ⊓ V t')) (fun j => p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j)
      (fun _ => inf_le_left) (fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hM y
        exact Opens.mem_iSup.2 ⟨j, hy, hj⟩)
      (fun j => res (l₂ j) (d t' j) * (res (l₁ j) (d t j))⁻¹) (fun j j' y hy => by
        rw [v j y hy.1, v j' y hy.2, hd t j j' y hy.1.1.1 hy.1.2 hy.2.2,
          hd t' j j' y hy.1.1.2 hy.1.2 hy.2.2, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
    let E := RingEquiv.ofBijective _ (hp (V t ⊓ V t'))
    let g : Γ(T, V t ⊓ V t')ˣ := Units.map E.symm.toRingHom.toMonoidHom a
    have hg : pullU p _ g = a := Units.ext (E.apply_symm_apply a.val)
    refine ⟨g, fun j y h₁ h₂ hj => ?_⟩
    have hy : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j := ⟨⟨h₁, h₂⟩, hj⟩
    have e := gm_pull (𝟙 Y) p y (V t ⊓ V t') hy.1 g
    rw [Category.id_comp, hg] at e
    rw [← e, ← v j y hy, ← ha j, gm_res _ y _ hy]
  choose g hg using ratio
  let N : LB T := ⟨T, V, g⟩
  have hN : N.IsLB := by
    refine ⟨eq_top_iff.2 fun t _ => Opens.mem_iSup.2 ⟨t, hV t⟩, fun t => inj _ _ _ fun y hy => ?_,
      fun t t' t'' => inj _ _ _ fun y hy => ?_⟩
    · obtain ⟨j, hj⟩ := exists_chart hM y
      exact (gm_res p y _ hy _).trans ((hg t t j y hy hy hj).trans
        ((mul_inv_cancel _).trans (map_one _).symm))
    · obtain ⟨j, hj⟩ := exists_chart hM y
      rw [map_mul, gm_res p y _ hy, gm_res p y _ hy, gm_res p y _ hy]
      refine (congrArg₂ (· * ·) (hg t t' j y hy.1.1 hy.1.2 hj) (hg t' t'' j y hy.1.2 hy.2 hj)).trans
        (Eq.trans ?_ (hg t t'' j y hy.1.1 hy.2 hj).symm)
      rw [mul_comm, _root_.mul_assoc, inv_mul_cancel_left]
  have le : ∀ q : M.ι × (PUnit → T), M.U q.1 ⊓ (N.pull p).U q.2 ≤ p ⁻¹ᵁ V (q.2 PUnit.unit) ⊓ M.U q.1 :=
    fun q y hy => ⟨mem_pull (L := N).1 hy.2, hy.1⟩
  refine ⟨N, hN, ⟨fun q => res (le q) (d (q.2 PUnit.unit) q.1)⟩, fun q q' => unit_ext fun y hy => ?_⟩
  have h₁ : p y ∈ V (q.2 PUnit.unit) := mem_pull (L := N).1 hy.1.2
  have h₂ : p y ∈ V (q'.2 PUnit.unit) := mem_pull (L := N).1 hy.2.2
  have eN := gm_pull_g N p (𝟙 Y) y q.2 q'.2 hy.1.2 hy.2.2
  rw [Category.id_comp] at eN
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.1 _)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div (N.pull p) M (𝟙 Y) y q q' hy).trans
    (congrArg (fun w => _ * w⁻¹) (eN.trans (hg _ _ q'.1 y h₁ h₂ hy.2.1))))
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q') hy.2 _)))).trans ?_
  rw [hd _ q.1 q'.1 y h₁ hy.1.1 hy.2.1, mul_inv_rev, inv_inv, _root_.mul_assoc, inv_mul_cancel_right]

end General

theorem bijective_app_of_restrict {Y T : Scheme.{0}} (p : Y ⟶ T) (V : T.Opens)
    (h : Function.Bijective (p ∣_ V).appTop.hom) : Function.Bijective (p.app V).hom := by
  have h₁ : IsIso (p ∣_ V).appTop := (ConcreteCategory.isIso_iff_bijective _).2 h
  have h₂ : IsIso (p.app (V.ι ''ᵁ ⊤)) :=
    @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
      (by rw [eqToHom_op]; exact Y.presheaf.map_isIso (eqToHom _)) h₁ (morphismRestrict_appTop p V).symm
  have e : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  rw [e] at h₂
  exact ConcreteCategory.bijective_of_isIso (p.app V)


open scoped CategoryTheory.Obj in
theorem bijective_app_fst (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A]
    (hA : IsAbelianScheme A) (T : Over S) (V : T.left.Opens) :
    Function.Bijective ((fst T A).left.app V).hom := by
  have hB : IsAbelianScheme ((Over.pullback (V.ι ≫ T.hom)).obj A) :=
    { comm := by have := hA.comm; infer_instance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have h₁ : Function.Bijective (pullback.snd A.hom (V.ι ≫ T.hom)).appTop.hom := hG _ _ hB
  have sq : IsPullback ((pullback.fst T.hom A.hom ⁻¹ᵁ V).ι ≫ pullback.snd T.hom A.hom)
      (pullback.fst T.hom A.hom ∣_ V) A.hom (V.ι ≫ T.hom) :=
    (isPullback_morphismRestrict (pullback.fst T.hom A.hom) V).flip.paste_horiz
      (IsPullback.of_hasPullback T.hom A.hom).flip
  have h₂ : Function.Bijective (pullback.fst T.hom A.hom ∣_ V).appTop.hom := by
    rw [← sq.isoPullback_hom_snd, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (sq.isoPullback.hom.app ⊤)).comp h₁
  exact bijective_app_of_restrict _ V h₂

end GlobalTheory.CubeLawCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GeneratorSchemeProperties
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory

namespace GenScheme

def pb {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, W)ˣ :=
  Units.map (f.appLE U W h).hom

section Calc

variable {X Y Z : Scheme.{0}}

theorem res_pb (f : Y ⟶ X) (U : X.Opens) (W W' : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (h' : W' ≤ W)
    (a : Γ(X, U)ˣ) : res h' (pb f U W h a) = pb f U W' (h'.trans h) a :=
  Units.ext (congr($(f.appLE_map h (homOfLE h').op).hom a.val))

theorem pb_res (f : Y ⟶ X) (U U' : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U') (h' : U' ≤ U)
    (a : Γ(X, U)ˣ) : pb f U' W h (res h' a) = pb f U W (h.trans (f.preimage_mono h')) a :=
  Units.ext (congr($(f.map_appLE h (homOfLE h').op).hom a.val))

theorem pb_pb (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (W : Z.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    pb g V W h' (pb f U V h a) = pb (g ≫ f) U W (h'.trans (g.preimage_mono h)) a :=
  Units.ext (congr($(Scheme.Hom.appLE_comp_appLE g f U V W h h').hom a.val))

theorem pullU_eq (f : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)ˣ) :
    pullU f U a = pb f U _ le_rfl a :=
  Units.ext (congr($(f.app_eq_appLE (U := U)).hom a.val))

theorem res_res {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a :=
  Units.ext (congr($((X.presheaf.map_comp (homOfLE h).op (homOfLE h').op).symm).hom a.val))

theorem res_self {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a :=
  Units.ext (congr($(X.presheaf.map_id (Opposite.op U)).hom a.val))

theorem pb_top_val (f : Y ⟶ X) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) (a : Γ(X, ⊤)ˣ) :
    (pb f ⊤ ⊤ h a).val = f.appTop.hom a.val := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl

end Calc

section One

variable {B Z : Scheme.{0}} (L : LB B) (b : Z ⟶ B)

def Compat (s : ∀ i : L.ι, Γ(Z, b ⁻¹ᵁ L.U i)ˣ) : Prop :=
  ∀ i i', res (Scheme.Hom.preimage_mono b (inf_le_right : L.U i ⊓ L.U i' ≤ L.U i')) (s i') =
    pullU b _ (L.g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : L.U i ⊓ L.U i' ≤ L.U i)) (s i)

variable (j : L.ι) (hj : ⊤ ≤ b ⁻¹ᵁ L.U j)

def extend (t : Γ(Z, ⊤)ˣ) (i : L.ι) : Γ(Z, b ⁻¹ᵁ L.U i)ˣ :=
  pb b (L.U j ⊓ L.U i) _ (fun x hx => ⟨hj trivial, hx⟩) (L.g j i) * res le_top t

variable {L}

theorem compat_extend (hL : L.IsLB) (t : Γ(Z, ⊤)ˣ) : Compat L b (extend L b j hj t) := by
  intro i i'
  have h := congrArg (pb b (L.U j ⊓ L.U i ⊓ L.U i') (b ⁻¹ᵁ (L.U i ⊓ L.U i'))
    (fun x hx => ⟨⟨hj trivial, hx.1⟩, hx.2⟩)) (hL.cocycle j i i')
  rw [map_mul, pb_res, pb_res, pb_res] at h
  simp only [extend, map_mul, res_pb, res_res, pullU_eq]
  rw [← h, ← _root_.mul_assoc, _root_.mul_comm (pb b _ _ _ (L.g i i'))]

theorem res_extend_self (hL : L.IsLB) (t : Γ(Z, ⊤)ˣ) : res hj (extend L b j hj t j) = t := by
  have h := congrArg (pb b (L.U j) ⊤ hj) (hL.g_self j)
  rw [pb_res, map_one] at h
  simp only [extend, map_mul, res_pb, res_res, res_self]
  rw [h, _root_.one_mul]

theorem eq_extend {s : ∀ i : L.ι, Γ(Z, b ⁻¹ᵁ L.U i)ˣ} (hs : Compat L b s) (i : L.ι) :
    s i = extend L b j hj (res hj (s j)) i := by
  have h := congrArg (res (show b ⁻¹ᵁ L.U i ≤ b ⁻¹ᵁ (L.U j ⊓ L.U i) from
    fun x hx => ⟨hj trivial, hx⟩)) (hs j i)
  rw [map_mul, res_res, res_res, res_self, pullU_eq, res_pb] at h
  rw [h, extend, res_res]

theorem compat_pb {G : Scheme.{0}} {q : G ⟶ B} {u : ∀ i : L.ι, Γ(G, q ⁻¹ᵁ L.U i)ˣ}
    (hu : Compat L q u) (g : Z ⟶ G) (hg : g ≫ q = b) :
    Compat L b fun i => pb g (q ⁻¹ᵁ L.U i) (b ⁻¹ᵁ L.U i) (by rw [← hg]; exact le_rfl) (u i) := by
  subst hg
  intro i i'
  have h := congrArg (pb g (q ⁻¹ᵁ (L.U i ⊓ L.U i')) ((g ≫ q) ⁻¹ᵁ (L.U i ⊓ L.U i')) le_rfl) (hu i i')
  rw [map_mul, pb_res, pb_res, pullU_eq, pb_pb] at h
  rw [res_pb, res_pb, pullU_eq]
  exact h

end One

section Many

variable {B : Scheme.{0}} {κ : Type} {N : κ → LB B} {G : Scheme.{0}} {q : G ⟶ B}
  {u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ}


variable (N q u) in
def Univ : Prop :=
  ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ),
    (∀ k, Compat (N k) b (s k)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i,
      (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val =
        (s k i).val

theorem exists_hom (hN : ∀ k, (N k).IsLB) (hU : Univ N q u) {Z : Scheme.{0}} (b : Z ⟶ B)
    (j : ∀ k, (N k).ι) (hj : ∀ k, ⊤ ≤ b ⁻¹ᵁ (N k).U (j k)) (t : κ → Γ(Z, ⊤)ˣ) :
    ∃ (g : Z ⟶ G) (hg : g ≫ q = b), ∀ k,
      pb g (q ⁻¹ᵁ (N k).U (j k)) ⊤ (by subst hg; exact hj k) (u k (j k)) = t k := by
  obtain ⟨g, ⟨hg, h⟩, -⟩ := hU Z b (fun k => extend (N k) b (j k) (hj k) (t k))
    fun k => compat_extend b (j k) (hj k) (hN k) (t k)
  refine ⟨g, hg, fun k => ?_⟩
  have e : pb g (q ⁻¹ᵁ (N k).U (j k)) (b ⁻¹ᵁ (N k).U (j k)) (by rw [← hg]; exact le_rfl) (u k (j k)) =
      extend (N k) b (j k) (hj k) (t k) (j k) := Units.ext (h k (j k))
  rw [← res_extend_self b (j k) (hj k) (hN k) (t k), ← e, res_pb]

theorem hom_ext (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u) {Z : Scheme.{0}}
    (j : ∀ k, (N k).ι) (g g' : Z ⟶ G) (hg : g' ≫ q = g ≫ q)
    (hj : ∀ k, ⊤ ≤ g ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)) (hj' : ∀ k, ⊤ ≤ g' ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k))
    (h : ∀ k, pb g' (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj' k) (u k (j k)) =
      pb g (q ⁻¹ᵁ (N k).U (j k)) ⊤ (hj k) (u k (j k))) : g' = g := by
  have c := fun k => compat_pb (g ≫ q) (hu k) g rfl
  have c' := fun k => compat_pb (g ≫ q) (hu k) g' hg
  refine (hU Z (g ≫ q) _ c).unique ⟨hg, fun k i => ?_⟩ ⟨rfl, fun k i => rfl⟩
  have e := eq_extend (g ≫ q) (j k) (hj k) (c k) i
  have e' := eq_extend (g ≫ q) (j k) (hj k) (c' k) i
  simp only [res_pb] at e e'
  rw [h k, ← e] at e'
  exact congrArg Units.val e'

open SplitTorus in
theorem torus_hom_ext {S : Scheme.{0}} {T : Over S} {a a' : T ⟶ splitTorus S (κ →₀ ℤ)}
    (h : ∀ k, val a (Finsupp.single k 1) = val a' (Finsupp.single k 1)) : a = a' := by
  apply (pointsEquiv T (κ →₀ ℤ)).injective
  refine Finsupp.addHom_ext' fun k => AddMonoidHom.ext_int ?_
  exact Additive.toMul.injective (Units.ext (h k))

open SplitTorus in
theorem exists_torus_hom {S : Scheme.{0}} {T : Over S} (t : κ → Γ(T.left, ⊤)ˣ) :
    ∃ a : T ⟶ splitTorus S (κ →₀ ℤ), ∀ k, val a (Finsupp.single k 1) = (t k).val := by
  refine ⟨ofVal (Finsupp.liftAddHom fun k => zmultiplesHom _ (Additive.ofMul (t k))), fun k => ?_⟩
  rw [val_ofVal]
  simp


open SplitTorus in
theorem exists_isPullback (hN : ∀ k, (N k).IsLB) (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u)
    {V : Scheme.{0}} (v : V ⟶ B) (j : ∀ k, (N k).ι) (hj : ∀ k, ⊤ ≤ v ⁻¹ᵁ (N k).U (j k)) :
    ∃ p : (splitTorus V (κ →₀ ℤ)).left ⟶ G, IsPullback p (splitTorus V (κ →₀ ℤ)).hom q v := by
  let T := splitTorus V (κ →₀ ℤ)
  have lands : ∀ {Z : Scheme.{0}} (c : Z ⟶ V) k, ⊤ ≤ (c ≫ v) ⁻¹ᵁ (N k).U (j k) :=
    fun c k => c.preimage_mono (hj k)
  have lands' : ∀ {Z : Scheme.{0}} (a : Z ⟶ G) (c : Z ⟶ V) (_ : a ≫ q = c ≫ v) k,
      ⊤ ≤ a ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := fun a c h k => by
    rw [← Scheme.Hom.comp_preimage, h]; exact lands c k
  obtain ⟨p, hp, hpu⟩ := exists_hom hN hU (T.hom ≫ v) j (lands T.hom)
    fun k => (isUnit_val (𝟙 T) (Finsupp.single k 1)).unit
  have key : ∀ {Z : Over V} (m : Z ⟶ T) k (h : ⊤ ≤ (m.left ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k)),
      (pb (m.left ≫ p) (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k))).val = val m (Finsupp.single k 1) := by
    intro Z m k h
    rw [← pb_pb m.left p _ ⊤ ⊤ (lands' p T.hom hp k) le_rfl, hpu, pb_top_val]
    exact (val_eq m _).symm
  have ex : ∀ s : PullbackCone q v, ∃ l : s.pt ⟶ T.left, l ≫ p = s.fst ∧ l ≫ T.hom = s.snd := by
    intro s
    obtain ⟨l, hl⟩ := exists_torus_hom (T := Over.mk s.snd)
      fun k => pb s.fst (q ⁻¹ᵁ (N k).U (j k)) ⊤ (lands' _ _ s.condition k) (u k (j k))
    have w : l.left ≫ T.hom = s.snd := Over.w l
    have w' : (l.left ≫ p) ≫ q = s.snd ≫ v := by
      rw [Category.assoc, hp, ← Category.assoc, w]
    refine ⟨l.left, hom_ext hu hU j _ _ (w'.trans s.condition.symm) (lands' _ _ s.condition)
      (lands' _ _ w') fun k => Units.ext ?_, w⟩
    exact (key l k _).trans (hl k)
  refine ⟨p, ⟨hp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (ex s).choose)
    (fun s => (ex s).choose_spec.1) (fun s => (ex s).choose_spec.2) fun s m h₁ h₂ => ?_⟩⟩
  obtain ⟨h₃, h₄⟩ := (ex s).choose_spec
  generalize (ex s).choose = l at h₃ h₄
  have : (Over.homMk m h₂ : Over.mk s.snd ⟶ T) = Over.homMk l h₄ := by
    refine torus_hom_ext fun k => ?_
    have hm : ⊤ ≤ (m ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := by rw [h₁]; exact lands' _ _ s.condition k
    have hl : ⊤ ≤ (l ≫ p) ⁻¹ᵁ q ⁻¹ᵁ (N k).U (j k) := by rw [h₃]; exact lands' _ _ s.condition k
    rw [← key (Over.homMk m h₂ : Over.mk s.snd ⟶ T) k hm, ← key (Over.homMk l h₄ : Over.mk s.snd ⟶ T) k hl]
    have aux : ∀ (a a' : s.pt ⟶ G) (_ : a = a') h h',
        pb a (q ⁻¹ᵁ (N k).U (j k)) ⊤ h (u k (j k)) = pb a' (q ⁻¹ᵁ (N k).U (j k)) ⊤ h' (u k (j k)) := by
      rintro a _ rfl _ _; rfl
    exact congrArg Units.val (aux _ _ (h₁.trans h₃.symm) _ _)
  exact congrArg (·.left) this

theorem prop_of_torus [Fintype κ] (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V : Scheme.{0}, P (splitTorus V (κ →₀ ℤ)).hom)
    (hN : ∀ k, (N k).IsLB) (hu : ∀ k, Compat (N k) q (u k)) (hU : Univ N q u) : P q := by
  let W : (∀ k, (N k).ι) → B.Opens := fun j =>
    ⟨⋂ k, ((N k).U (j k) : Set B), isOpen_iInter_of_finite fun k => ((N k).U (j k)).isOpen⟩
  have hW : iSup W = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    have : ∀ k, ∃ i, x ∈ (N k).U i := fun k =>
      TopologicalSpace.Opens.mem_iSup.1 ((hN k).cover.ge trivial)
    choose j hj using this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, Set.mem_iInter.2 hj⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun j => ?_
  obtain ⟨p, hp⟩ := exists_isPullback hN hu hU (W j).ι j
    fun k x _ => Set.mem_iInter.1 x.2 k
  have h := (isPullback_morphismRestrict q (W j)).flip
  rw [← h.isoIsPullback_hom_snd _ _ hp, MorphismProperty.cancel_left_of_respectsIso P]
  exact hP _

end Many

end GenScheme

theorem generatorScheme_properties :
    ∀ (B : Scheme.{0}) (κ : Type) [Fintype κ] (N : κ → LB B), (∀ k, (N k).IsLB) → ∀ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), ((∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val) → IsAffineHom q ∧ Smooth q ∧ Surjective q ∧ IsSeparated q ∧ GeometricallyConnected q := by
  intro B κ _ N hN G q u ⟨hu, hU⟩
  have hc : GeometricallyConnected q := by
    have : IsZariskiLocalAtTarget @GeometricallyConnected := by
      rw [GeometricallyConnected.eq_geometrically]; infer_instance
    exact GenScheme.prop_of_torus @GeometricallyConnected (fun V => inferInstance) hN hu hU
  have : IsZariskiLocalAtTarget @IsAffineHom :=
    HasAffineProperty.instIsZariskiLocalAtTarget (P := @IsAffineHom)
  have : IsZariskiLocalAtTarget @Smooth := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have ha : IsAffineHom q := GenScheme.prop_of_torus @IsAffineHom (fun V => inferInstance) hN hu hU
  refine ⟨ha, GenScheme.prop_of_torus @Smooth (fun V => ?_) hN hu hU, inferInstance, inferInstance, hc⟩
  have := H1.torus_dim V (κ →₀ ℤ)
  exact SmoothOfRelativeDimension.smooth (Module.finrank ℤ (κ →₀ ℤ)) _

end GlobalTheory
end
end
