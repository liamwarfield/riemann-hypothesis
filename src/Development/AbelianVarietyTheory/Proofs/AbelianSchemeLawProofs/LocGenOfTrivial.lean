module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerPow

section General

variable {X Y Y' B B' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']

theorem gen_transfer {M M' : LB Y} (e : M'.ι → M.ι) (hU : ∀ j, M'.U j ≤ M.U (e j))
    (hg : ∀ i j (y : Y), y ∈ M'.U i → y ∈ M'.U j →
      gm (𝟙 Y) y (M'.U i ⊓ M'.U j) (M'.g i j) = gm (𝟙 Y) y (M.U (e i) ⊓ M.U (e j)) (M.g (e i) (e j)))
    (h : ∃ t : LB.Gen M, t.IsGen) : ∃ t' : LB.Gen M', t'.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun j => res (hU j) (t.s (e j))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U (e i) ⊓ M.U (e j) := ⟨hU i hy.1, hU j hy.2⟩
  have h1 := congrArg (gm (𝟙 Y) y (M.U (e i) ⊓ M.U (e j))) (ht (e i) (e j))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at h1
  rw [map_mul, gm_res _ y inf_le_left hy, gm_res _ y inf_le_right hy, hg i j y hy.1 hy.2]
  exact (gm_res (𝟙 Y) y (hU i) (show y ∈ M'.U i from hy.1) _).trans
    (h1.trans (congrArg _ (gm_res (𝟙 Y) y (hU j) (show y ∈ M'.U j from hy.2) _).symm))

def HasGen (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen

theorem pull_iff (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) :
    (∃ c : LB.Gen ((LB.LinComb L φ ε).pull h), c.IsGen) ↔ HasGen L (fun k => h ≫ φ k) ε := by
  have key : ∀ (y : Y') (i j : K → L.ι), h y ∈ LB.wchart L φ i → h y ∈ LB.wchart L φ j →
      gm (𝟙 Y') y (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j)
        ((LB.LinComb L (fun k => h ≫ φ k) ε).g i j) =
      gm (𝟙 Y') y (((LB.LinComb L φ ε).pull h).U (fun _ => i) ⊓ ((LB.LinComb L φ ε).pull h).U (fun _ => j))
        (((LB.LinComb L φ ε).pull h).g (fun _ => i) (fun _ => j)) := by
    intro y i j hi hj
    refine (gm_linComb L (fun k => h ≫ φ k) ε (𝟙 Y') y i j
      (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hi k) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k)).trans ?_
    refine Eq.trans ?_ (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y (fun _ => i) (fun _ => j)
      (mem_pull.2 hi) (mem_pull.2 hj)).symm
    refine Eq.trans ?_ (gm_linComb L φ ε (𝟙 Y' ≫ h) y i j hi hj).symm
    simp only [Category.assoc]
  constructor
  · refine gen_transfer (M := (LB.LinComb L φ ε).pull h) (M' := LB.LinComb L (fun k => h ≫ φ k) ε)
      (fun j _ => j) (fun j y hy => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)) ?_
    intro i j y hi hj
    exact key y i j (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hi k) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k)
  · refine gen_transfer (M' := (LB.LinComb L φ ε).pull h) (M := LB.LinComb L (fun k => h ≫ φ k) ε)
      (fun J => J PUnit.unit) (fun J y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k) ?_
    intro i j y hi hj
    exact (key y (i PUnit.unit) (j PUnit.unit) (mem_pull.1 hi) (mem_pull.1 hj)).symm

theorem HasGen.pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : HasGen L φ ε) (h : Y' ⟶ Y) {φ' : K → (Y' ⟶ X)}
    (e : ∀ k, h ≫ φ k = φ' k) : HasGen L φ' ε := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨t, ht⟩ := H
  exact ⟨_, DVR.pullGen_isGen L φ ε t ht h⟩

theorem HasGen.comb (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y ⟶ X)} {ε'' : K'' → ℤ} (H : HasGen L φ ε) (H' : HasGen L φ' ε')
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
      (∏ k, h (φ k) ^ ε k) * (∏ k, h (φ' k) ^ ε' k)⁻¹ = ∏ k, h (φ'' k) ^ ε'' k) : HasGen L φ'' ε'' := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨t', ht'⟩ := H'
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := φ'') (ε' := ε'') (fun U _ h => by
      rw [← e U h, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib])
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t'))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ ht'))
  exact ⟨u, hu⟩

theorem hasGen_of_trivial (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) : HasGen L φ ε := by
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ h => by rw [e U h]; simp)
    (LB.oneGen L (Y := Y)) (fun i j => by
      have e1 : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
        rfl
      rw [e1, _root_.one_mul]
      exact (map_one _).trans (map_one _).symm)
  exact ⟨u, hu⟩

def LocGen (L : LB X) (π : Y ⟶ B) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ HasGen L (fun k => (π ⁻¹ᵁ V).ι ≫ φ k) ε

theorem locGen_iff (π : Y ⟶ B) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb L φ ε).pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔
      LocGen L π φ ε := by
  simp only [LocGen, pull_iff]

theorem LocGen.comb (hL : L.IsLB) {π : Y ⟶ B} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y ⟶ X)} {ε'' : K'' → ℤ} (H : LocGen L π φ ε) (H' : LocGen L π φ' ε')
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
      (∏ k, h (φ k) ^ ε k) * (∏ k, h (φ' k) ^ ε' k)⁻¹ = ∏ k, h (φ'' k) ^ ε'' k) : LocGen L π φ'' ε'' := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  obtain ⟨V', hV', t'⟩ := H' p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ?_⟩
  have a := t.pull (Y.homOfLE (show π ⁻¹ᵁ (V ⊓ V') ≤ π ⁻¹ᵁ V from fun _ h => h.1))
    (φ' := fun k => (π ⁻¹ᵁ (V ⊓ V')).ι ≫ φ k) (fun k => by rw [← Category.assoc, Scheme.homOfLE_ι])
  have a' := t'.pull (Y.homOfLE (show π ⁻¹ᵁ (V ⊓ V') ≤ π ⁻¹ᵁ V' from fun _ h => h.2))
    (φ' := fun k => (π ⁻¹ᵁ (V ⊓ V')).ι ≫ φ' k) (fun k => by rw [← Category.assoc, Scheme.homOfLE_ι])
  exact a.comb hL a' fun U _ h => e U fun q => h ((π ⁻¹ᵁ (V ⊓ V')).ι ≫ q)

theorem locGen_of_trivial (hL : L.IsLB) {π : Y ⟶ B} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (e : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = 1) : LocGen L π φ ε :=
  fun _ => ⟨⊤, trivial, hasGen_of_trivial hL fun U _ h => e U fun q => h ((π ⁻¹ᵁ ⊤).ι ≫ q)⟩

theorem HasGen.of_range {φ : K → (Y ⟶ X)} {ε : K → ℤ} {W : Y.Opens} (H : HasGen L (fun k => W.ι ≫ φ k) ε)
    (h : Y' ⟶ Y) (hW : ∀ y, h y ∈ W) {φ' : K → (Y' ⟶ X)} (e : ∀ k, h ≫ φ k = φ' k) : HasGen L φ' ε :=
  H.pull (IsOpenImmersion.lift W.ι h (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hW y))
    (fun k => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ k) (IsOpenImmersion.lift_fac _ _ _)).trans (e k)))

theorem LocGen.baseChange {π : Y ⟶ B} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : LocGen L π φ ε) {π' : Y' ⟶ B'}
    (h : Y' ⟶ Y) (g : B' ⟶ B) (sq : h ≫ π = π' ≫ g) {φ' : K → (Y' ⟶ X)} (e : ∀ k, h ≫ φ k = φ' k) :
    LocGen L π' φ' ε := by
  intro p
  obtain ⟨V, hV, t⟩ := H (g p)
  refine ⟨g ⁻¹ᵁ V, hV, t.of_range ((π' ⁻¹ᵁ (g ⁻¹ᵁ V)).ι ≫ h) (fun y => ?_) (fun k => by rw [Category.assoc, e])⟩
  exact (congrArg (fun q : Y' ⟶ B => q y.1 ∈ V) sq).mpr y.2

end General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translPt_one (T : Over S) : translPt A (1 : T ⟶ A) = snd T A := by
  show (fst T A ≫ (1 : T ⟶ A)) * snd T A = snd T A
  rw [MonObj.comp_one, _root_.one_mul]

theorem whisker_translPt {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ A) :
    g ▷ A ≫ translPt A x = translPt A (g ≫ x) := by
  simp [translPt, comp_lift_assoc]

theorem locGen_pow {L : LB A.left} (hL : L.IsLB) {T : Over S}
    (sq : ∀ x y : T ⟶ A, LocGen L (K := Fin 4) (fst T A).left
      ![(translPt A (x * y)).left, (snd T A).left, (translPt A x).left, (translPt A y).left] ![1, 1, -1, -1])
    (x : T ⟶ A) (N : ℕ) :
    LocGen L (K := Fin 3) (fst T A).left ![(translPt A (x ^ N)).left, (snd T A).left, (translPt A x).left]
      ![-1, 1 - (N : ℤ), (N : ℤ)] := by
  induction N with
  | zero =>
    refine locGen_of_trivial hL fun U _ h => ?_
    rw [pow_zero, translPt_one, Fin.prod_univ_three]
    simp
  | succ n ih =>
    refine ih.comb hL (sq (x ^ n) x) fun U _ h => ?_
    rw [pow_succ x n, Fin.prod_univ_three, Fin.prod_univ_three, Fin.prod_univ_four]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    simp
    module

theorem eq_one_of_locGen {L : LB A.left} (hK : KTriv A L) {T : Over S} (y : T ⟶ A)
    (H : LocGen L (K := Fin 2) (fst T A).left ![(translPt A y).left, (snd T A).left] ![1, -1]) : y = 1 := by
  have loc : ∀ (R : CommRingCat.{0}) (f : Spec R ⟶ T.left), f ≫ y.left = f ≫ (1 : T ⟶ A).left := by
    intro R f
    let g : Over.mk (f ≫ T.hom) ⟶ T := Over.homMk f rfl
    have H' := H.baseChange (π' := (fst (Over.mk (f ≫ T.hom)) A).left) (g ▷ A).left f
      (congrArg (fun q => q.left) (whiskerRight_fst g A))
      (φ' := ![(translPt A (g ≫ y)).left, (snd _ A).left]) (fun k => by
        fin_cases k
        · exact congrArg (fun q => q.left) (whisker_translPt g y)
        · exact congrArg (fun q => q.left) (whiskerRight_snd g A))
    have e : g ≫ y = 1 := hK R (f ≫ T.hom) (g ≫ y) ((locGen_iff _ _ _).2 H')
    exact congrArg (fun q => q.left) (e.trans (MonObj.comp_one g).symm)
  ext1
  exact T.left.affineCover.hom_ext _ _ fun i => loc _ (T.left.affineCover.f i)

theorem locGen_theta_iff {L : LB A.left} (hL : L.IsLB) (hK : KTriv A L) {T : Over S}
    (sq : ∀ x y : T ⟶ A, LocGen L (K := Fin 4) (fst T A).left
      ![(translPt A (x * y)).left, (snd T A).left, (translPt A x).left, (translPt A y).left] ![1, 1, -1, -1])
    (x : T ⟶ A) (N : ℕ) :
    LocGen L (K := Fin 2) (fst T A).left ![(snd T A).left, (translPt A x).left] ![(N : ℤ), -(N : ℤ)] ↔ x ^ N = 1 := by
  have triv : LocGen L (K := Fin 0) (fst T A).left ![] ![] := locGen_of_trivial hL fun U _ h => by simp
  have P := triv.comb hL (locGen_pow hL sq x N)
    (φ'' := ![(translPt A (x ^ N)).left, (snd T A).left, (translPt A x).left]) (ε'' := ![1, (N : ℤ) - 1, -(N : ℤ)])
    fun U _ h => by
      rw [Fin.prod_univ_three, Fin.prod_univ_three]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      simp
      module
  constructor
  · intro H
    refine eq_one_of_locGen hK _ (P.comb hL H fun U _ h => ?_)
    rw [Fin.prod_univ_three, Fin.prod_univ_two, Fin.prod_univ_two]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    simp
    module
  · intro H
    refine P.comb hL triv fun U _ h => ?_
    rw [H, translPt_one, Fin.prod_univ_three, Fin.prod_univ_two]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    simp
    module

theorem exists_theta {L : LB A.left} {T : Over S} (x : T ⟶ A) (k : ℤ) (V : T.left.Opens)
    (H : HasGen L (fun i : Fin 2 => ((fst T A).left ⁻¹ᵁ V).ι ≫ ![(snd T A).left, (translPt A x).left] i) ![k, -k]) :
    ∃ θ : ThetaGrp A L k (overRes V), θ.pt = overResι V ≫ x := by
  obtain ⟨t, ht⟩ := H.of_range (overResι V ▷ A).left (fun y =>
      (congrArg (fun q : overRes V ⊗ A ⟶ T => q.left y ∈ V) (whiskerRight_fst (overResι V) A)).mpr
        ((fst (overRes V) A).left y).2)
    (φ' := ![(snd _ A).left, (translPt A (overResι V ≫ x)).left]) (fun i => by
      fin_cases i
      · exact congrArg (fun q => q.left) (whiskerRight_snd (overResι V) A)
      · exact congrArg (fun q => q.left) (whisker_translPt (overResι V) x))
  exact ⟨⟨overResι V ≫ x, t, ht⟩, rfl⟩

end GlobalTheory.KerPow

namespace GlobalTheory


open KerPow in
theorem kerPow_of_square :
    (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left), ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4) ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left] ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ↔ x ^ N = 1) ∧ KerPowSt ∧ (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) := by
  intro sq
  have main := fun (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A) =>
    locGen_theta_iff P.isLB P.ktriv (fun x y => (locGen_iff _ _ _).1 (sq S P T x y)) x N
  have one : ∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A),
      (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
        ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ↔ x ^ N = 1 :=
    fun S P N T x => (locGen_iff _ _ _).trans (main S P N T x)
  refine ⟨one, fun S _ P N _ T x => one S P N T x, fun S P N T x hx p => ?_⟩
  obtain ⟨V, hV, H⟩ := (main S P N T x).2 hx p
  exact ⟨V, hV, exists_theta x N V H⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isGen_pull {X Y : Scheme.{0}} (M : LB X) (v : LB.Gen M) (hv : v.IsGen) (f : Y ⟶ X) :
    ∃ c : LB.Gen (M.pull f), c.IsGen := by
  have le : ∀ J : PUnit → M.ι, (M.pull f).U J ≤ f ⁻¹ᵁ M.U (J PUnit.unit) := fun J y hy => mem_pull.1 hy
  refine ⟨⟨fun J => res (le J) (pullU f _ (v.s (J PUnit.unit)))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J : PUnit → M.ι, y ∈ (M.pull f).U J →
      gm (𝟙 Y) y _ (res (le J) (pullU f _ (v.s (J PUnit.unit)))) =
        gm (𝟙 Y ≫ f) y _ (v.s (J PUnit.unit)) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  have hm : (𝟙 Y ≫ f) y ∈ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) := ⟨le J hy.1, le J' hy.2⟩
  have e := congrArg (gm (𝟙 Y ≫ f) y _) (hv (J PUnit.unit) (J' PUnit.unit))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm] at e
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (e.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))

theorem exists_isGen_of_invariant {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y'))
    (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, φ' k = m ≫ φ k)
    (u : LB.Gen (LB.LinComb L φ' ε)) (hu : u.IsGen)
    (hinv : ∀ i y J, Good L y J → val u (t i) y J = val u (𝟙 Y') y J) :
    ∃ v : LB.Gen (LB.LinComb L φ ε), v.IsGen := by
  obtain rfl : φ' = fun k => m ≫ φ k := funext hφ
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
  have le : ∀ j : K → L.ι, m ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => m ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hex : ∀ j : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ j)ˣ, pullU m _ b = res (le j) (u.s j) := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    have hJ' : Good L y J := hJ
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ LB.wchart L φ j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    refine (gm_res (t i) y (le j) (e hy) _).trans (Eq.trans ?_ (gm_res (𝟙 Y') y (le j) hy _).symm)
    refine (gen_trans hu (t i) y (le j (e hy)) (hJ'.mem _ _)).trans
      (Eq.trans ?_ (gen_trans hu (𝟙 Y') y (le j hy) (hJ'.mem _ _)).symm)
    refine congrArg₂ (· * ·) ?_ (hinv i y J hJ')
    have e3 : ∀ k, t i ≫ m ≫ φ k = 𝟙 Y' ≫ m ≫ φ k := fun k => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X => gm ψ y (L.U (j k) ⊓ L.U (J ψ)) (L.g (j k) (J ψ)) ^ ε k) (e3 k)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j : K → L.ι, y ∈ m ⁻¹ᵁ LB.wchart L φ j →
      gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (u.s j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans ((congrArg _ (hb j)).trans (gm_res (𝟙 Y') y (le j) hj _))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans
    ((gen_trans hu (𝟙 Y') y (le i hy.1) (le j hy.2)).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_linComb L φ ε (𝟙 Y' ≫ m) y i j hy.1 hy.2).trans ?_) ((gm_res _ y _ hy _).trans (val j hy.2)))
  simp only [trF, Category.assoc]

theorem weilNondeg_of_descent :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 → ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤ ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)), (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ) (x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A), x ^ n = 1 → ∃ (u : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulT P.A (baseOver (Spec (CommRingCat.of K))) n ≫ translPt P.A x).left, (snd (baseOver (Spec (CommRingCat.of K))) P.A ^ n).left] ![1, -1])) (ε : ℤ), u.IsGen ∧ (ε = 1 ∨ ε = -1) ∧ ∀ (y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (c : Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)ˣ), y ^ n = 1 → WeilIs P.A P.L n x y c → LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (translT P.A y).left) (LB.mulGen P.L _ _ _ _ u (constGen P.A P.L (c ^ ε)))) → WeilNondegSt := by
  intro hG hC K _ _ P k hk x hx hy
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨u, ε, hu, -, hcorr⟩ := hC K P k x hx
  let B := baseOver (Spec (CommRingCat.of K))
  let β : P.A ⟶ B := Over.homMk P.A.hom (Category.comp_id _)
  have hβ : ∀ {T : Over (Spec (CommRingCat.of K))} (a b : T ⟶ B), a = b := fun a b =>
    Over.OverMorphism.ext (((Category.comp_id _).symm.trans (Over.w a)).trans
      ((Category.comp_id _).symm.trans (Over.w b)).symm)
  let σ : P.A ⟶ B ⊗ P.A := lift β (𝟙 _)
  have hσ : snd B P.A ≫ σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hβ _ _
    · simp [σ]
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of K))} (y : Z ⟶ P.A), y ≫ mulA P.A k = y ^ k :=
    fun y => by rw [mulA, MonObj.comp_pow, Category.comp_id]
  have h0 : σ ≫ mulT P.A B k = mulA P.A k ≫ σ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact hβ _ _
    · simp [σ, mulT, mulA, MonObj.comp_pow]
  obtain ⟨v, hv⟩ := exists_isGen_of_invariant P.isLB (K := Fin 2)
    ![(σ ≫ translPt P.A x).left, 𝟙 _] ![1, -1] (mulA P.A k).left
    (I := {y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A // y ^ k = 1})
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => by
      rw [← Over.comp_left, hmul, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one, _root_.one_mul, mulA])
    (fun U f hf => hG K P k hk U f fun y hy => hf ⟨y, hy⟩) _
    (fun i => by
      fin_cases i
      · change (σ ≫ mulT P.A B k ≫ translPt P.A x).left = (mulA P.A k ≫ σ ≫ translPt P.A x).left
        rw [reassoc_of% h0]
      · change (σ ≫ snd B P.A ^ k).left = (mulA P.A k ≫ 𝟙 _).left
        simp [σ, mulA, MonObj.comp_pow])
    (LB.pullGen P.L _ _ u σ.left) (DVR.pullGen_isGen _ _ _ u hu _)
    (fun y z J hJ => by
      have hy' : (toUnit B ≫ y.1) ^ k = 1 := by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      have h1 := val_corr hJ (hcorr _ 1 hy' (hy _ hy')) σ.left
      have h2 : ((toUnit P.A ≫ y.1) * 𝟙 P.A) ≫ σ = σ ≫ translT P.A (toUnit B ≫ y.1) := by
        apply CartesianMonoidalCategory.hom_ext
        · exact hβ _ _
        · clear hG hC hcorr h1
          simp only [σ, translT, translPt, Hom.mul_def, Category.assoc, lift_snd, Category.comp_id,
            comp_lift_assoc, lift_fst_assoc, comp_toUnit_assoc]
      rw [val_pull hJ, val_mul hJ, one_zpow] at h1
      rw [val_pull hJ, val_pull hJ, Category.id_comp, ← Over.comp_left, h2]
      refine h1.trans ?_
      refine mul_eq_left.2 ?_
      exact (congrArg _ ((congrArg _ (map_one _)).trans (map_one _))).trans (map_one _))
  refine P.ktriv K (𝟙 _) x fun p => ⟨⊤, trivial, ?_⟩
  have h3 : (fun i => (snd B P.A).left ≫ ![(σ ≫ translPt P.A x).left, 𝟙 _] i) =
      ![(translPt P.A x).left, (snd B P.A).left] := by
    funext i
    fin_cases i
    · change (snd B P.A ≫ σ ≫ translPt P.A x).left = (translPt P.A x).left
      rw [reassoc_of% hσ]
    · exact Category.comp_id _
  have h4 : ∃ w : LB.Gen (LB.LinComb P.L
      (fun i => (snd B P.A).left ≫ ![(σ ≫ translPt P.A x).left, 𝟙 _] i) ![1, -1]), w.IsGen :=
    ⟨_, DVR.pullGen_isGen _ _ _ v hv _⟩
  rw [h3] at h4
  obtain ⟨w, hw⟩ := h4
  exact exists_isGen_pull (translDiff P.A P.L x) w hw _

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenExtend

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DvrModel

theorem gm_eq_of_corr {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {φ' : I → (Y' ⟶ X)} {ε : I → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (h : ∀ i, r ≫ φ i = r' ≫ φ' i)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r')) (z : Z)
    (a : I → L.ι) (ha : r z ∈ LB.wchart L φ a) (ha' : r' z ∈ LB.wchart L φ' a) :
    gm r z (LB.wchart L φ a) (t.s a) = gm r' z (LB.wchart L φ' a) (t'.s a) := by
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hv := val_corr hJ hc (𝟙 Z)
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at hv
  rw [gen_trans ht r z ha (Good.mem hJ φ r), gen_trans ht' r' z ha' (Good.mem hJ φ' r')]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) hv
  show gm (r ≫ φ k) z (L.U (a k) ⊓ L.U (J (r ≫ φ k))) (L.g (a k) (J (r ≫ φ k))) ^ _ =
    gm (r' ≫ φ' k) z (L.U (a k) ⊓ L.U (J (r' ≫ φ' k))) (L.g (a k) (J (r' ≫ φ' k))) ^ _
  rw [h k]

theorem res_pullU_eq_of_corr {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {φ' : I → (Y' ⟶ X)} {ε : I → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (h : ∀ i, r ≫ φ i = r' ≫ φ' i)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t r) (LB.pullGen L _ _ t' r'))
    (a : I → L.ι) {A : Z.Opens} (hA : A ≤ r ⁻¹ᵁ LB.wchart L φ a)
    (hA' : A ≤ r' ⁻¹ᵁ LB.wchart L φ' a) :
    r'.appLE (LB.wchart L φ' a) A hA' (LB.ts t' a : Γ(Y', LB.wchart L φ' a)ˣ) =
      r.appLE (LB.wchart L φ a) A hA (LB.ts t a : Γ(Y, LB.wchart L φ a)ˣ) := by
  have hur : res hA' (pullU r' (LB.wchart L φ' a) (t'.s a)) =
      res hA (pullU r (LB.wchart L φ a) (t.s a)) := by
    refine unit_ext fun z hz => ?_
    rw [gm_res _ z hA hz, gm_res _ z hA' hz, gm_pull _ r z _ (hA hz), gm_pull _ r' z _ (hA' hz),
      Category.id_comp, Category.id_comp]
    exact (gm_eq_of_corr hL ht ht' r r' h hc z a (hA hz) (hA' hz)).symm
  exact congrArg Units.val hur

theorem existsUnique_gen_extend :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t := by
  intro V _ _ _ K _ _ _ H X p e hsm hgi he eK heK L hL I _ φ ε t ρ ht hρ hc
  have hK := IsPullback.of_hasPullback p (etaK V K)
  have hs := IsPullback.of_hasPullback p
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := isIntegral_of_geometricallyIntegral hK
  have := isIntegral_of_geometricallyIntegral hs
  have hcomp : ∀ i, eK ≫ pullback.fst p (etaK V K) ≫ φ i = etaK V K ≫ e ≫ φ i := fun i => by
    rw [← Category.assoc, heK, Category.assoc]
  obtain ⟨a₀, h₀⟩ := LB.mem_of_cover (LB.isLB_linComb hL (fun i => e ≫ φ i) ε)
    (IsLocalRing.closedPoint V)
  have hA' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ =
      etaK V K ⁻¹ᵁ LB.wchart L (fun i => e ≫ φ i) a₀ := wchart_comp L _ _ _
  have hA'' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ ≤
      eK ⁻¹ᵁ LB.wchart L (fun i => pullback.fst p (etaK V K) ≫ φ i) a₀ := by
    rw [← wchart_comp, funext hcomp]
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩ := existsUnique_isUnit_appLE_eq hK hs
    (U := LB.wchart L φ) (g := fun a b ↦ LB.lcg L φ ε a b)
    (W := LB.wchart L fun k ↦ pullback.fst p (etaK V K) ≫ φ k)
    (wchart_comp L _ φ) (LB.mem_of_cover (LB.isLB_linComb hL φ ε)) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ LB.ts t a)
    (fun a b ↦ by
      have := congrArg Units.val ((LB.isGen_iff L t).1 ht a b)
      rw [LB.lcg_comp] at this
      exact this)
    (fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := LB.wchart L (fun i => e ≫ φ i) a₀) h₀
    (wchart_comp L e φ a₀).le hA' hA'' (LB.ts ρ a₀).isUnit
    (res_pullU_eq_of_corr hL ht hρ eK (etaK V K) hcomp hc a₀ hA'' hA'.le)
  refine ⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩
  · exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr a))
  · rintro ⟨r'⟩ ⟨h₁, h₂⟩
    have := huniq (fun a ↦ (r' a).val) ⟨fun a ↦ Units.isUnit _,
      fun a b ↦ congrArg Units.val (h₁ a b), fun a ↦ congrArg (fun c ↦ (LB.ts c a).val) h₂⟩
    exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))

end GlobalTheory.GenExtend
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRingStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.existsUnique_generator_extend_discreteValuationRing : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t := by
  first | exact @GlobalTheory.GenExtend.existsUnique_gen_extend | exact GlobalTheory.GenExtend.existsUnique_gen_extend | (intros; apply GlobalTheory.GenExtend.existsUnique_gen_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MulFinite

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial

theorem exists_pow_mul_eq_zero {k R : Type} [CommRing k] [CommRing R] (hk : IsField k) (φ : k →+* R)
    (a : R) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (c b : R), IsUnit c ∧ a ^ m * (c + a * b) = 0 := by
  letI := hk.toField
  obtain ⟨p, hp, h0⟩ := ha
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hq hnd
  rw [X_dvd_iff] at hnd
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hnd).map φ, ?_⟩
  rw [hq, ← X_mul_divX_add q, eval₂_mul, eval₂_pow, eval₂_X, eval₂_add, eval₂_mul, eval₂_X,
    eval₂_C] at h0
  rw [add_comm]
  exact h0

theorem isClosed_basicOpen {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [UniversallyClosed f] (a : Γ(Z, ⊤)) : IsClosed (Z.basicOpen a : Set Z) := by
  have hk : IsField Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨m, c, b, hc, e⟩ := exists_pow_mul_eq_zero hk _ a (isIntegral_appTop_of_universallyClosed f a)
  have : (Z.basicOpen a : Set Z) = (Z.basicOpen (c + a * b) : Set Z)ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    rw [Scheme.mem_basicOpen Z a z trivial, Scheme.mem_basicOpen Z (c + a * b) z trivial]
    let G : Γ(Z, ⊤) →+* Z.presheaf.stalk z := (Z.presheaf.germ ⊤ z trivial).hom
    change IsUnit (G a) ↔ ¬ IsUnit (G (c + a * b))
    have e' : G a ^ m * G (c + a * b) = 0 := by rw [← map_pow, ← map_mul, e, map_zero]
    constructor
    · intro h1 h2
      exact ((h1.pow m).mul h2).ne_zero e'
    · intro h2
      have hc' : IsUnit (G (c + a * b) + (- (G a * G b))) := by
        have := hc.map G
        simpa using this
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hc' with h | h
      · exact absurd h h2
      · exact isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h)
  rw [this]
  exact (Z.basicOpen _).isOpen.isClosed_compl

theorem locallyQuasiFinite_of_cover {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [IsProper f] {I : Type} (a : I → Γ(Z, ⊤)) (hc : ⨆ i, Z.basicOpen (a i) = ⊤)
    (ha : ∀ i, IsAffineOpen (Z.basicOpen (a i))) : LocallyQuasiFinite f := by
  have : IsZariskiLocalAtSource @LocallyQuasiFinite.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyQuasiFinite.{0}) _ hc fun i => ?_
  have : IsClosedImmersion (Z.basicOpen (a i)).ι :=
    .of_isPreimmersion _ (by simpa using isClosed_basicOpen f (a i))
  have : IsAffine (Z.basicOpen (a i)).toScheme := ha i
  have : IsFinite ((Z.basicOpen (a i)).ι ≫ f) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  infer_instance

theorem isAffineHom_fromSpecResidueField (Y : Scheme.{0}) (y : Y) :
    IsAffineHom (Y.fromSpecResidueField y) := by
  refine ⟨fun U _ => ?_⟩
  by_cases h : y ∈ U
  · have : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊤ := by
      ext x; simpa using h
    rw [this]; exact isAffineOpen_top _
  · have : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊥ := by
      ext x; simpa using h
    rw [this]; exact isAffineOpen_bot _

theorem isUnit_gs {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

theorem gs_appLE {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (V : Z.Opens) (hle : V ≤ r ⁻¹ᵁ U)
    (h : z ∈ V) (a : Γ(Y, U)) : gs (𝟙 Z) z V ((r.appLE U V hle).hom a) = gs r z U a :=
  (gs_res (𝟙 Z) z hle h _).trans ((gs_pull (𝟙 Z) r z U (hle h) a).trans (by rw [Category.id_comp]))

theorem gs_pow {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem pow_aux {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e N : ℕ) :
    ((g ^ N).val * x) ^ e * ((g ^ e * t)⁻¹).val ^ N = x ^ e * (t⁻¹).val ^ N := by
  have h : ((g ^ N) ^ e * ((g ^ e * t)⁻¹) ^ N) = (t⁻¹) ^ N := by
    rw [mul_inv, mul_pow, ← _root_.mul_assoc, inv_pow, ← pow_mul, ← pow_mul, _root_.mul_comm e N,
      mul_inv_cancel, _root_.one_mul]
  have h' : (g ^ N).val ^ e * ((g ^ e * t)⁻¹).val ^ N = (t⁻¹).val ^ N := congrArg Units.val h
  rw [mul_pow, ← h']; ring

theorem exists_fn {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (m : X ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1])) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : L.ι) (h₀ : ∀ z, m (w (r z)) ∈ L.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => (r ≫ w) ⁻¹ᵁ L.U j
  have l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  have l₂ : ∀ j, V j ≤ (r ≫ w) ⁻¹ᵁ LB.wchart L (K := Fin 2) ![𝟙 X, m] ![j, j₀] :=
    fun j z hz => Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact hz
      · exact h₀ z
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j)) (s.f (fun _ => j)) ^ e *
        ((gm (r ≫ w) z (LB.wchart L (K := Fin 2) ![𝟙 X, m] ![j, j₀]) (α.s ![j, j₀]))⁻¹).val ^ N := by
    refine ⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) ^ e *
      ((r ≫ w).appLE _ _ (l₂ j)).hom ((α.s ![j, j₀])⁻¹).val ^ N, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    · exact congrArg (· ^ e) (gs_appLE r z _ _ _ hz _)
    · refine congrArg (· ^ N) ((gs_appLE (r ≫ w) z _ _ _ hz _).trans ?_)
      exact (gs_unit (r ≫ w) z _ (l₂ j hz) _).trans (congrArg Units.val (map_inv _ _))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2),
        gen_trans hα (r ≫ w) z (l₂ j hz.1) (l₂ j' hz.2)]
      have h1 : gm ((r ≫ w) ≫ m) z (L.U j₀ ⊓ L.U j₀) (L.g j₀ j₀) = 1 := gm_self hL _ z (h₀ z)
      have t₁ : trF (L := L) (K := Fin N) (fun _ => w) (fun _ => 1) r z (fun _ => j) (fun _ => j') =
          gm (r ≫ w) z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]
      have t₂ : trF (L := L) (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1] (r ≫ w) z ![j, j₀] ![j', j₀] =
          gm (r ≫ w) z (L.U j ⊓ L.U j') (L.g j j') ^ e := by
        rw [trF, Fin.prod_univ_two]
        change gm ((r ≫ w) ≫ 𝟙 X) z (L.U j ⊓ L.U j') (L.g j j') ^ (e : ℤ) *
          gm ((r ≫ w) ≫ m) z (L.U j₀ ⊓ L.U j₀) (L.g j₀ j₀) ^ (-1 : ℤ) = _
        rw [h1, Category.comp_id]; simp
      rw [t₁, t₂]
      exact pow_aux _ _ _ _ _)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔
      IsUnit (gs r z (LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j)) (s.f (fun _ => j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ LB.wchart L (K := Fin N) (fun _ => w) k := W.basicOpen_le _ hk
    rw [sec_trans s r z (l₁ j hj) hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isFinite_of_relAmple {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsProper A.hom] (L : LB A.left)
    (hL : L.IsLB) (hA : RelAmple A L) (m : A ⟶ A) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, m.left] ![(e : ℤ), -1])) (hα : α.IsGen) :
    IsFinite m.left := by
  have hm : m.left ≫ A.hom = A.hom := Over.w m
  have : IsProper (m.left ≫ A.hom) := by rw [hm]; infer_instance
  have : IsProper m.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite m.left from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (A.hom y)) isOpen_univ
  obtain ⟨N, -, M, s, hcov, hs⟩ := hA U hU
  have hy : ∀ z, m.left (m.left.fiberι y z) = y := fun z =>
    (m.left.range_fiberι y).le ⟨z, rfl⟩
  let r : m.left.fiber y ⟶ (A.hom ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι (m.left.fiberι y) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change A.hom (m.left.fiberι y z) ∈ U
      rw [← hm, Scheme.Hom.comp_apply, hy]
      exact hyU)
  have hr : r ≫ (A.hom ⁻¹ᵁ U).ι = m.left.fiberι y := IsOpenImmersion.lift_fac _ _ _
  have := isAffineHom_fromSpecResidueField A.left y
  have : IsAffineHom (r ≫ (A.hom ⁻¹ᵁ U).ι) := by
    rw [hr]; exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)).flip this
  have : IsAffineHom r := .of_comp r (A.hom ⁻¹ᵁ U).ι
  obtain ⟨j₀, hj₀⟩ := exists_chart hL y
  have key := fun i => exists_fn L hL (A.hom ⁻¹ᵁ U).ι N (s i) m.left e he α hα r j₀ (fun z => by
    rw [← Scheme.Hom.comp_apply r, hr, hy]; exact hj₀)
  choose a ha using key
  have : IsProper (m.left.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd m.left (A.left.fromSpecResidueField y)))
  refine locallyQuasiFinite_of_cover (K := A.left.residueField y) (m.left.fiberToSpecResidueField y) a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => r ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage r

theorem isFinite_mulA :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → PolBaseChangeSt → (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left := by
  intro h _ _ S P n hn
  have H := h S P n
  rw [← Nat.cast_pow] at H
  obtain ⟨α, hα⟩ := H
  have := P.isAb.proper
  exact isFinite_of_relAmple P.A P.L P.isLB P.ample _ (n ^ 2) (by positivity) α hα

end GlobalTheory.MulFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EvVal

theorem existsUnique_sec_eq_mul_gen {Y : Scheme.{0}} (M : LB Y) (hc : ⨆ j, M.U j = ⊤)
    (s : LB.Sec M) (t : LB.Gen M) (ht : t.IsGen) :
    ∃! v : Γ(Y, ⊤), ∀ j, s.f j =
      (Y.presheaf.map (homOfLE (le_top : M.U j ≤ ⊤)).op).hom v * (t.s j).val := by
  obtain ⟨v, hv⟩ := TLinPf.glue M.U hc (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e := congrArg (fun x : Γ(Y, M.U i ⊓ M.U j)ˣ => (x⁻¹).val) (ht i j)
    simp only [mul_inv, ← map_inv, Units.val_mul] at e
    rw [map_mul, map_mul, s.compat i j]
    refine (congrArg (_ * ·) e).trans ?_
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]
    rfl)
  refine ⟨v, fun j => ?_, fun w hw => TLinPf.eq_local M.U hc _ _ fun j => ?_⟩
  · rw [hv j, Units.inv_mul_cancel_right]
  · rw [hv j, hw j, Units.mul_inv_cancel_right]

def pullSec {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (ψ : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = ψ k)
    (le : ∀ j, LB.wchart L ψ j ≤ h ⁻¹ᵁ LB.wchart L φ j) (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb L ψ ε) where
  f := fun j => (Y'.presheaf.map (homOfLE (le j)).op).hom ((h.app _).hom (s.f j))
  compat := fun (j j' : K → L.ι) => Geo.Tor.fn_ext fun y hy => by
    have v : ∀ j : K → L.ι, y ∈ LB.wchart L ψ j →
        Geo.Tor.gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (le j)).op).hom ((h.app _).hom (s.f j))) =
        Geo.Tor.gs (𝟙 Y' ≫ h) y (LB.wchart L φ j) (s.f j) := fun j hj =>
      (Geo.Tor.gs_res _ y _ hj _).trans (Geo.Tor.gs_pull _ h y _ (le j hj) _)
    refine ((Geo.Tor.gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_
      ((Geo.Tor.gs_mul (𝟙 Y') y _ hy _ _).trans
      (congrArg₂ (· * ·) ((Geo.Tor.gs_unit (𝟙 Y') y _ hy _).trans
        (congrArg Units.val (Geo.Tor.gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2)))
        ((Geo.Tor.gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
    rw [Geo.Tor.sec_trans s (𝟙 Y' ≫ h) y (le j hy.1) (le j' hy.2)]
    simp only [Geo.Tor.trF, Category.assoc, e]

theorem powFrame_isGen {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S}
    (z : T ⟶ A)
    (e : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
    (he : e.IsGen) (k : ℤ) : (powFrame A L z e k).IsGen := by
  intro i j
  have h := congrArg (· ^ k) (he i j)
  simp only [mul_zpow, ← map_zpow] at h
  refine h.trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem evValSt : ∀ S : Scheme.{0}, EvValSt (S := S) := by
  intro S P N T z e he s
  exact existsUnique_sec_eq_mul_gen _ (TLinPf.linComb_cover P.L P.isLB _ _)
    (pullSec P.L (fun _ : Fin 1 => (snd T P.A).left) (fun _ => (N : ℤ)) (ptSecT P.A z).left
      (fun _ => z.left) (fun _ => by rw [← Over.comp_left, ptSecT, lift_snd])
      (val_le P.A P.L z) s)
    (powFrame P.A P.L z e N) (powFrame_isGen P.A P.L z e he N)

end GlobalTheory.EvVal
end
end
