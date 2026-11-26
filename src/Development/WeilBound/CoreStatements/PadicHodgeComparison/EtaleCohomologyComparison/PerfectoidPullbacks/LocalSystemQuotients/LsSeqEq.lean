module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientReductionBijectiveOfFlat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFundamentalDomainDiff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelMorphismCoverCompat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittCoordQuotientPullBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfFlatTower

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatWittTowerLevel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatWittTowerLevel
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FlatLevel

theorem exists_trivial_of_smul_eq_zero {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Flat A M]
    (f : A) (y : M) (h : f • y = 0) :
    ∃ (n : ℕ) (u : Fin n → A) (v : Fin n → M), y = ∑ j, u j • v j ∧ ∀ j, f * u j = 0 := by
  classical
  have h' : ∑ i : Unit, (fun _ : Unit => f) i • (fun _ : Unit => y) i = 0 := by simpa using h
  obtain ⟨n, a, z, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero h'
  refine ⟨n, fun j => a () j, z, ?_, fun j => ?_⟩
  · simpa using hx ()
  · simpa using ha j

theorem exists_mul_of_flat {W B : Type} [CommRing W] [CommRing B] {t : W} (ht : t ∈ nonZeroDivisors W)
    {a b m : ℕ} (h : a + b = m) (c : W ⧸ Ideal.span {t ^ m} →+* B) (hc : c.Flat) (y : B)
    (hy : c (Ideal.Quotient.mk _ (t ^ b)) * y = 0) : ∃ z, c (Ideal.Quotient.mk _ (t ^ a)) * z = y := by
  let _ := c.toAlgebra
  have : Module.Flat (W ⧸ Ideal.span {t ^ m}) B := hc
  have hb : Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ b) • y = 0 := by
    rw [Algebra.smul_def]
    exact hy
  obtain ⟨n, u, v, hyv, hu⟩ := exists_trivial_of_smul_eq_zero (A := W ⧸ Ideal.span {t ^ m}) (M := B) _ y hb
  have key : ∀ j, ∃ s : W, u j = Ideal.Quotient.mk (Ideal.span {t ^ m}) (t ^ a * s) := by
    intro j
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (u j)
    have h1 := hu j
    rw [← hw, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨s, hs⟩ := h1
    refine ⟨s, ?_⟩
    rw [← hw]
    congr 1
    have hb' : t ^ b ∈ nonZeroDivisors W := pow_mem ht b
    have h2 : (w - t ^ a * s) * t ^ b = 0 := by
      rw [← h, pow_add] at hs
      linear_combination (-1 : W) * hs
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hb').mp h2)
  choose s hs using key
  refine ⟨∑ j, c (Ideal.Quotient.mk _ (s j)) * v j, ?_⟩
  rw [hyv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, hs j, ← mul_assoc, ← map_mul, ← map_mul]
  rfl

theorem natCast_mem_nonZeroDivisors (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] :
    (l : WittVector l k) ∈ nonZeroDivisors (WittVector l k) := by
  exact mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)

set_option backward.isDefEq.respectTransparency false in
theorem flatL_Kt : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (m : ℕ), FlatL l m (Kt l F ρ m) := by
  intro l _ k _ _ _ O _ F ρ m
  show FlatL l m (CrystallineSemistableComparison.CH.cx (CrystallineSemistableComparison.CH.modF (CrystallineSemistableComparison.Pb.LsG.sW l F ρ m).A))
  rw [CrystallineSemistableComparison.Pb.LsG.modF_sW]
  intro i
  refine ⟨fun x => ?_, fun a b hab x hx => ?_⟩
  · funext s
    have h0 : Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m}) ((l : WittVector l k) ^ m) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    change ((s.obj (Fin.last i)).obj.i (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})
      ((l : WittVector l k) ^ m))) * (show (s.obj (Fin.last i)).obj.B from x s) = 0
    rw [h0, map_zero, zero_mul]
  · have key : ∀ s : ComposableArrows (fl l F ρ m).FullSubcategory i,
        ∃ z : ((fl l F ρ m).ι ⋙ Wc.OM l F ρ m).obj (s.obj (Fin.last i)),
          (l : WittVector l k) ^ a • z = x s := by
      intro s
      have hs : (s.obj (Fin.last i)).obj.i.Flat := (s.obj (Fin.last i)).property
      have h0 : (l : WittVector l k) ^ b • x s = 0 := congrFun hx s
      obtain ⟨z, hz⟩ := exists_mul_of_flat (natCast_mem_nonZeroDivisors l k) hab
        (s.obj (Fin.last i)).obj.i hs (x s) h0
      exact ⟨z, hz⟩
    choose z hz using key
    rw [CrystallineSemistableComparison.Ls.lpow, LinearMap.mem_range]
    exact ⟨z, funext fun s => hz s⟩

end GlobalTheory.CompanionTheory.FlatLevel

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatWittTowerLevelStatement
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_witt_tower_level : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (m : ℕ), FlatL l m (Kt l F ρ m) := by
  first | exact @GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt | exact GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt | (intros; apply GlobalTheory.CompanionTheory.FlatLevel.flatL_Kt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullEqOfNatTrans
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullEqOfNatTrans
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison
open GlobalTheory.CatH (face toLast)

universe w w' v u v' u'

namespace GlobalTheory.CompanionTheory.CatPrism

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}

def cyl {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) : Fin 2 × C' ⥤ C := Functor.uncurry.obj (ComposableArrows.mk₁ α)

theorem cyl_top {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) {T T' : C'} (φ : T ⟶ T') :
    G₂.map φ = (cyl α).map ((𝟙 (Fin.last 1), φ) : (Fin.last 1, T) ⟶ (Fin.last 1, T')) := by
  simp [cyl]

theorem cyl_bot {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) {T T' : C'} (φ : T ⟶ T') :
    G₁.map φ = (cyl α).map ((𝟙 (0 : Fin 2), φ) : ((0 : Fin 2), T) ⟶ ((0 : Fin 2), T')) := by
  simp [cyl]

theorem cyl_step {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) (T : C') :
    α.app T = (cyl α).map ((homOfLE (Fin.zero_le _), 𝟙 T) : ((0 : Fin 2), T) ⟶ (Fin.last 1, T)) := by
  simp [cyl]

variable {n p : ℕ}

theorem map_map {X Y Z : C} (F : C ⥤ ModuleCat.{w} R) (φ : X ⟶ Y) (ψ : Y ⟶ Z) (x : F.obj X) :
    (F.map ψ).hom ((F.map φ).hom x) = (F.map (φ ≫ ψ)).hom x := by
  rw [F.map_comp]; rfl

def chain {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) {a : Fin (p + 1) → Fin 2} {t : Fin (p + 1) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) (s : ComposableArrows C' n) : ComposableArrows C p :=
  (ha.functor.prod' (ht.functor ⋙ s)) ⋙ cyl α

def up (s : ComposableArrows C' n) (b : Fin 2) (c : Fin (n + 1)) :
    (b, s.obj c) ⟶ (Fin.last 1, s.obj (Fin.last n)) :=
  (homOfLE (Fin.le_last b), s.map (homOfLE (Fin.le_last c)))

variable (m₂ : CH.Mor F F' σ) {G₁ : C' ⥤ C} (α : G₁ ⟶ m₂.G)

def val (s : ComposableArrows C' n) (f : CH.Cn F p) {a : Fin (p + 1) → Fin 2} {t : Fin (p + 1) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) : F'.obj (s.obj (Fin.last n)) :=
  m₂.τ _ ((F.map ((cyl α).map (up s (a (Fin.last p)) (t (Fin.last p))))).hom (f (chain α ha ht s)))

theorem val_congr (s : ComposableArrows C' n) (f : CH.Cn F p) {a a' : Fin (p + 1) → Fin 2} {t t' : Fin (p + 1) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) (ha' : Monotone a') (ht' : Monotone t') (h : a = a') (h' : t = t') :
    val m₂ α s f ha ht = val m₂ α s f ha' ht' := by
  subst h h'; rfl

theorem val_face (s : ComposableArrows C' (n + 1)) (f : CH.Cn F p) (j : Fin (n + 2)) {a : Fin (p + 1) → Fin 2}
    {t : Fin (p + 1) → Fin (n + 1)} (ha : Monotone a) (ht : Monotone t) :
    (F'.map (toLast j s)).hom (val m₂ α (face j s) f ha ht) =
      val m₂ α s f ha ((Fin.strictMono_succAbove j).monotone.comp ht) := by
  have e : (cyl α).map (up (face j s) (a (Fin.last p)) (t (Fin.last p))) ≫ m₂.G.map (toLast j s) =
      (cyl α).map (up s (a (Fin.last p)) (j.succAbove (t (Fin.last p)))) := by
    rw [cyl_top α, ← Functor.map_comp]
    congr 1
    refine Prod.ext (Subsingleton.elim _ _) ?_
    change s.map _ ≫ s.map _ = s.map _
    rw [← s.map_comp]; rfl
  unfold val
  rw [← m₂.nat]
  exact congrArg (m₂.τ _) ((map_map F _ _ _).trans
    (congrArg (fun q => (F.map q).hom (f (chain α ha ht (face j s)))) e))

theorem val_d (s : ComposableArrows C' n) (f : CH.Cn F p) {a : Fin (p + 2) → Fin 2} {t : Fin (p + 2) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) :
    val m₂ α s (CH.d F p f) ha ht = ∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) •
      val m₂ α s f (ha.comp (Fin.strictMono_succAbove k).monotone) (ht.comp (Fin.strictMono_succAbove k).monotone) := by
  have e : ∀ k : Fin (p + 2), toLast k (chain α ha ht s) ≫ (cyl α).map (up s (a (Fin.last (p + 1))) (t (Fin.last (p + 1)))) =
      (cyl α).map (up s (a (k.succAbove (Fin.last p))) (t (k.succAbove (Fin.last p)))) := by
    intro k
    change (cyl α).map _ ≫ _ = _
    rw [← Functor.map_comp]
    congr 1
    refine Prod.ext (Subsingleton.elim _ _) ?_
    change s.map _ ≫ s.map _ = s.map _
    rw [← s.map_comp]; rfl
  unfold val
  change m₂.τ _ ((F.map _).hom (∑ k : Fin (p + 2), (-1 : ℤ) ^ (k : ℕ) • (F.map (toLast k (chain α ha ht s))).hom (f (face k (chain α ha ht s))))) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, map_zsmul]
  exact congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • m₂.τ _ y) ((map_map F _ _ _).trans
    (congrArg (fun q => (F.map q).hom (f (face k (chain α ha ht s)))) (e k)))

section Combinatorics

theorem succAbove_val {m : ℕ} (p : Fin (m + 1)) (q : Fin m) :
    (p.succAbove q : ℕ) = if (q : ℕ) < p then (q : ℕ) else q + 1 := by
  unfold Fin.succAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

theorem predAbove_val {m : ℕ} (p : Fin m) (q : Fin (m + 1)) :
    (p.predAbove q : ℕ) = if (p : ℕ) < q then (q : ℕ) - 1 else q := by
  unfold Fin.predAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

theorem sign_of_odd (a b c e : ℕ) (h : Odd (a + b + c + e)) :
    (-1 : ℤ) ^ a * (-1) ^ b = -((-1) ^ c * (-1) ^ e) := by
  have h' : (-1 : ℤ) ^ (a + b + c + e) = -1 := h.neg_one_pow
  rw [pow_add, pow_add, pow_add] at h'
  rcases neg_one_pow_eq_or ℤ a with ha | ha <;> rcases neg_one_pow_eq_or ℤ b with hb | hb <;>
    rcases neg_one_pow_eq_or ℤ c with hc | hc <;> rcases neg_one_pow_eq_or ℤ e with he | he <;>
    simp_all

def skip {m : ℕ} (i : Fin (m + 1)) (l : Fin m) : Fin (m + 2) := i.castSucc.succAbove (i.succAbove l)

theorem skip_val {m : ℕ} (i : Fin (m + 1)) (l : Fin m) :
    (skip i l : ℕ) = if (l : ℕ) < i then (l : ℕ) else l + 2 := by
  unfold skip
  simp only [succAbove_val, Fin.val_castSucc]
  split_ifs <;> omega

theorem prism_tele {A : Type*} [AddCommGroup A] (m : ℕ) (X : Fin (m + 1) → Fin (m + 2) → A)
    (h1 : ∀ i : Fin m, X i.succ i.succ.castSucc = X i.castSucc i.castSucc.succ) :
    ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • X i k =
      X 0 0 - X (Fin.last m) (Fin.last (m + 1)) +
        ∑ i : Fin (m + 1), ∑ l : Fin m, (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (skip i l : ℕ) • X i (skip i l) := by
  have hi : ∀ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ k : Fin (m + 2), (-1 : ℤ) ^ (k : ℕ) • X i k =
      (X i i.castSucc - X i i.succ) +
        ∑ l : Fin m, (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (skip i l : ℕ) • X i (skip i l) := by
    intro i
    rw [Fin.sum_univ_succAbove _ i.castSucc, Fin.sum_univ_succAbove _ i, Fin.succAbove_castSucc_self]
    have e1 : (-1 : ℤ) ^ (i : ℕ) * (-1 : ℤ) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]; simp
    simp only [smul_add, Finset.smul_sum, smul_smul, Fin.val_castSucc, Fin.val_succ, pow_succ, e1]
    have e2 : (-1 : ℤ) ^ (i : ℕ) * ((-1 : ℤ) ^ (i : ℕ) * (-1)) = -1 := by
      rw [← mul_assoc, e1]; simp
    rw [e2, one_smul, neg_smul, one_smul, sub_eq_add_neg, add_assoc]
    rfl
  simp only [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  rw [Fin.sum_univ_succ (fun i : Fin (m + 1) => X i i.castSucc), Fin.sum_univ_castSucc (fun i : Fin (m + 1) => X i i.succ)]
  simp only [h1]
  simp only [Fin.castSucc_zero, Fin.succ_last]
  abel

theorem prism_cancel {A : Type*} [AddCommGroup A] (n : ℕ) (X : Fin (n + 2) → Fin (n + 1) → A)
    (Y : Fin (n + 2) → Fin (n + 1) → A) (h : ∀ i l, X i l = Y (i.succAbove l) (l.predAbove i)) :
    ∑ i : Fin (n + 2), ∑ l : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (skip i l : ℕ) • X i l +
      ∑ j : Fin (n + 2), ∑ l : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • (-1 : ℤ) ^ (l : ℕ) • Y j l = 0 := by
  have hinv : Function.Involutive (fun p : Fin (n + 2) × Fin (n + 1) => (p.1.succAbove p.2, p.2.predAbove p.1)) := by
    rintro ⟨i, l⟩
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type',
    ← Equiv.sum_comp hinv.toPerm (fun p : Fin (n + 2) × Fin (n + 1) => (-1 : ℤ) ^ (p.1 : ℕ) • (-1 : ℤ) ^ (p.2 : ℕ) • Y p.1 p.2),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero ?_
  rintro ⟨i, l⟩ _
  simp only [Function.Involutive.coe_toPerm, smul_smul]
  rw [h, sign_of_odd (i : ℕ) (skip i l : ℕ) (i.succAbove l : ℕ) (l.predAbove i : ℕ), neg_smul, neg_add_cancel]
  rw [Nat.odd_iff, skip_val, succAbove_val, predAbove_val]
  split_ifs <;> omega

end Combinatorics

section Prism

def pa {m : ℕ} (i : Fin (m + 1)) (t : Fin (m + 2)) : Fin 2 := if (i : ℕ) < t then Fin.last 1 else 0

theorem pa_mono {m : ℕ} (i : Fin (m + 1)) : Monotone (pa i) := by
  intro x y h
  have h' : (x : ℕ) ≤ y := h
  unfold pa
  split_ifs with h1 h2
  · exact le_rfl
  · omega
  · exact Fin.zero_le _
  · exact le_rfl

theorem pt_mono {m : ℕ} (i : Fin (m + 1)) : Monotone i.predAbove := Fin.predAbove_right_monotone i

theorem sa_mono {m : ℕ} (k : Fin (m + 1)) : Monotone k.succAbove := (Fin.strictMono_succAbove k).monotone

theorem pa_diag {m : ℕ} (i : Fin m) : pa i.succ ∘ i.succ.castSucc.succAbove = pa i.castSucc ∘ i.castSucc.succ.succAbove := by
  funext x
  simp only [Function.comp, pa, succAbove_val, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem pt_diag {m : ℕ} (i : Fin m) : i.succ.predAbove ∘ i.succ.castSucc.succAbove = i.castSucc.predAbove ∘ i.castSucc.succ.succAbove := by
  funext x
  apply Fin.ext
  simp only [Function.comp, predAbove_val, succAbove_val, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> omega

theorem pa_first {m : ℕ} : pa (0 : Fin (m + 1)) ∘ (0 : Fin (m + 2)).succAbove = fun _ => Fin.last 1 := by
  funext x
  simp only [Function.comp, pa, succAbove_val, Fin.val_zero]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem pt_first {m : ℕ} : (0 : Fin (m + 1)).predAbove ∘ (0 : Fin (m + 2)).succAbove = id := by
  funext x
  apply Fin.ext
  simp only [Function.comp, predAbove_val, succAbove_val, Fin.val_zero, id]
  split_ifs <;> omega

theorem prism_last_comp_succAbove_zero {m : ℕ} : pa (Fin.last m) ∘ (Fin.last (m + 1)).succAbove = fun _ => 0 := by
  funext x
  have := x.2
  simp only [Function.comp, pa, succAbove_val, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem predAbove_last_comp_succAbove_id {m : ℕ} : (Fin.last m).predAbove ∘ (Fin.last (m + 1)).succAbove = id := by
  funext x
  have := x.2
  apply Fin.ext
  simp only [Function.comp, predAbove_val, succAbove_val, Fin.val_last, id]
  split_ifs <;> omega

theorem pa_skip {m : ℕ} (i : Fin (m + 2)) (l : Fin (m + 1)) : pa i ∘ (skip i l).succAbove = pa (l.predAbove i) := by
  funext x
  simp only [Function.comp, pa, succAbove_val, predAbove_val, skip_val]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem pt_skip {m : ℕ} (i : Fin (m + 2)) (l : Fin (m + 1)) :
    i.predAbove ∘ (skip i l).succAbove = (i.succAbove l).succAbove ∘ (l.predAbove i).predAbove := by
  funext x
  apply Fin.ext
  simp only [Function.comp, succAbove_val, predAbove_val, skip_val]
  split_ifs <;> omega

end Prism

theorem cochain_congr (f : CH.Cn F p) {c c' : ComposableArrows C p} (h : c = c') {X : C}
    (φ : c.obj (Fin.last p) ⟶ X) (φ' : c'.obj (Fin.last p) ⟶ X) (hφ : φ = eqToHom (by rw [h]) ≫ φ') :
    (F.map φ).hom (f c) = (F.map φ').hom (f c') := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at hφ
  rw [hφ]

theorem chain_top {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) (s : ComposableArrows C' n) :
    chain α (monotone_const : Monotone fun _ : Fin (n + 1) => Fin.last 1) monotone_id s = s ⋙ G₂ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun x y g => ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Eq.trans ?_ (cyl_top α (s.map g)).symm
  change (cyl α).map (X := (Fin.last 1, s.obj x)) (Y := (Fin.last 1, s.obj y)) (_, s.map _) = _
  congr 1

theorem chain_bot {G₁ G₂ : C' ⥤ C} (α : G₁ ⟶ G₂) (s : ComposableArrows C' n) :
    chain α (monotone_const : Monotone fun _ : Fin (n + 1) => (0 : Fin 2)) monotone_id s = s ⋙ G₁ := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun x y g => ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Eq.trans ?_ (cyl_bot α (s.map g)).symm
  change (cyl α).map (X := ((0 : Fin 2), s.obj x)) (Y := ((0 : Fin 2), s.obj y)) (_, s.map _) = _
  congr 1

theorem up_top (s : ComposableArrows C' n) : up s (Fin.last 1) (Fin.last n) = 𝟙 _ :=
  Prod.ext (Subsingleton.elim _ _) ((congrArg s.map (Subsingleton.elim _ _)).trans (s.map_id _))

theorem up_bot (s : ComposableArrows C' n) :
    up s 0 (Fin.last n) = (homOfLE (Fin.zero_le _), 𝟙 (s.obj (Fin.last n))) :=
  Prod.ext (Subsingleton.elim _ _) ((congrArg s.map (Subsingleton.elim _ _)).trans (s.map_id _))

theorem val_top (s : ComposableArrows C' n) (f : CH.Cn F n) :
    val m₂ α s f (monotone_const : Monotone fun _ : Fin (n + 1) => Fin.last 1) monotone_id = m₂.pullC n f s := by
  refine congrArg (m₂.τ _) ((cochain_congr f (chain_top α s) _ (𝟙 _) ?_).trans ?_)
  · refine Eq.trans ?_ (Category.comp_id _).symm
    refine Eq.trans ?_ (eqToHom_refl _ rfl).symm
    change (cyl α).map (up s (Fin.last 1) (Fin.last n)) = 𝟙 _
    rw [up_top, (cyl α).map_id]
  · rw [F.map_id]; rfl

theorem val_bot (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x)
    (s : ComposableArrows C' n) (f : CH.Cn F n) :
    val m₂ α s f (monotone_const : Monotone fun _ : Fin (n + 1) => (0 : Fin 2)) monotone_id = m₁.pullC n f s := by
  refine Eq.trans (congrArg (m₂.τ _) (cochain_congr f (chain_bot α s) _ (α.app _) ?_)) (hτ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ α.app _) (eqToHom_refl _ rfl)).symm
  refine Eq.trans ?_ (Category.id_comp _).symm
  change (cyl α).map (up s 0 (Fin.last n)) = _
  rw [up_bot, cyl_step α]
  rfl

def htpy (n : ℕ) (f : CH.Cn F (n + 1)) : CH.Cn F' n := fun s =>
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • val m₂ α s f (pa_mono i) (pt_mono i)

theorem val_zero (s : ComposableArrows C' n) {a : Fin (p + 1) → Fin 2} {t : Fin (p + 1) → Fin (n + 1)}
    (ha : Monotone a) (ht : Monotone t) : val m₂ α s (0 : CH.Cn F p) ha ht = 0 :=
  (congrArg (m₂.τ _) (map_zero _)).trans (map_zero _)

theorem htpy_zero (n : ℕ) : htpy m₂ α n (0 : CH.Cn F (n + 1)) = 0 := by
  funext s
  exact Finset.sum_eq_zero fun i _ => by rw [val_zero, smul_zero]

def xv (s : ComposableArrows C' n) (f : CH.Cn F n) (i : Fin (n + 1)) (k : Fin (n + 2)) : F'.obj (s.obj (Fin.last n)) :=
  val m₂ α s f ((pa_mono i).comp (sa_mono k)) ((pt_mono i).comp (sa_mono k))

theorem hd_eq (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x)
    (s : ComposableArrows C' n) (f : CH.Cn F n) :
    htpy m₂ α n (CH.d F n f) s = m₂.pullC n f s - m₁.pullC n f s +
      ∑ i : Fin (n + 1), ∑ l : Fin n, (-1 : ℤ) ^ (i : ℕ) • (-1 : ℤ) ^ (skip i l : ℕ) • xv m₂ α s f i (skip i l) := by
  have h0 : htpy m₂ α n (CH.d F n f) s = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • xv m₂ α s f i k :=
    Finset.sum_congr rfl fun i _ => congrArg _ (val_d m₂ α s f _ _)
  rw [h0, prism_tele n (xv m₂ α s f) fun i => val_congr m₂ α s f _ _ _ _ (pa_diag i) (pt_diag i)]
  congr 2
  · exact (val_congr m₂ α s f _ _ monotone_const monotone_id pa_first pt_first).trans (val_top m₂ α s f)
  · exact (val_congr m₂ α s f _ _ monotone_const monotone_id prism_last_comp_succAbove_zero predAbove_last_comp_succAbove_id).trans (val_bot m₂ m₁ α hτ s f)

theorem dh_eq (s : ComposableArrows C' (n + 1)) (f : CH.Cn F (n + 1)) :
    CH.d F' n (htpy m₂ α n f) s = ∑ j : Fin (n + 2), ∑ l : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • (-1 : ℤ) ^ (l : ℕ) •
      val m₂ α s f (pa_mono l) ((sa_mono j).comp (pt_mono l)) := by
  change ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • (F'.map (toLast j s)).hom
    (∑ l : Fin (n + 1), (-1 : ℤ) ^ (l : ℕ) • val m₂ α (face j s) f (pa_mono l) (pt_mono l)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, val_face, Finset.smul_sum]

theorem htpy_spec (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x)
    (f : CH.Cn F (n + 1)) :
    htpy m₂ α (n + 1) (CH.d F (n + 1) f) + CH.d F' n (htpy m₂ α n f) = m₂.pullC (n + 1) f - m₁.pullC (n + 1) f := by
  funext s
  change htpy m₂ α (n + 1) (CH.d F (n + 1) f) s + CH.d F' n (htpy m₂ α n f) s = m₂.pullC (n + 1) f s - m₁.pullC (n + 1) f s
  rw [hd_eq m₂ m₁ α hτ, dh_eq]
  exact (add_assoc _ _ _).trans ((congrArg _ (prism_cancel n (fun i l => xv m₂ α s f i (skip i l))
    (fun j l => val m₂ α s f (pa_mono l) ((sa_mono j).comp (pt_mono l)))
    (fun i l => val_congr m₂ α s f _ _ _ _ (pa_skip i l) (pt_skip i l)))).trans (add_zero _))

theorem htpy_spec_zero (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x)
    (f : CH.Cn F 0) : htpy m₂ α 0 (CH.d F 0 f) = m₂.pullC 0 f - m₁.pullC 0 f := by
  funext s
  rw [hd_eq m₂ m₁ α hτ]
  simp

theorem pull_eq_of_natTrans (m₁ : CH.Mor F F' σ) (α : m₁.G ⟶ m₂.G)
    (hτ : ∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x) (j : ℕ) :
    m₁.pull j = m₂.pull j := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (m₁.hom.mapZ j z) = Submodule.Quotient.mk (m₂.hom.mapZ j z)
  rw [Submodule.Quotient.eq]
  change m₁.pullC j z.1 - m₂.pullC j z.1 ∈ (CH.cx F').B j
  have hz : CH.d F j z.1 = 0 := z.2
  cases j with
  | zero =>
    have h := htpy_spec_zero m₂ m₁ α hτ z.1
    rw [hz, htpy_zero] at h
    have h' : m₁.pullC 0 z.1 - m₂.pullC 0 z.1 = 0 := by
      rw [← neg_sub, ← h, neg_zero]
    rw [h']
    exact Submodule.zero_mem _
  | succ n =>
    have h := htpy_spec m₂ m₁ α hτ z.1
    rw [hz, htpy_zero, zero_add] at h
    refine ⟨-htpy m₂ α n z.1, ?_⟩
    change CH.d F' n (-htpy m₂ α n z.1) = _
    rw [map_neg, h, neg_sub]

theorem pull_eq_target : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) (m₁ m₂ : CH.Mor F F' (RingHom.id R)) (α : m₁.G ⟶ m₂.G), (∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x) → ∀ j, m₁.pull j = m₂.pull j :=
  fun _ _ _ _ _ _ _ _ m₁ m₂ α h j => pull_eq_of_natTrans m₂ m₁ α h j

end GlobalTheory.CompanionTheory.CatPrism

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullEqOfNatTransStatement
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_eq_of_nat_trans : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) (m₁ m₂ : CH.Mor F F' (RingHom.id R)) (α : m₁.G ⟶ m₂.G), (∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x) → ∀ j, m₁.pull j = m₂.pull j := by
  first | exact @GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | exact GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | (intros; apply GlobalTheory.CompanionTheory.CatPrism.pull_eq_target <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsosStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LseqOfLevelIsos
open CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerSeq

theorem lseq_transport : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W)
    (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)),
    (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) →
    LSeq l S S' → Nonempty (LSeq l T T') := by
  intro W _ l S S' T T' e e' h h' L
  let E : ∀ n, S.M n ≃ₗ[W] T.M n := fun n => LinearEquiv.ofBijective (e.f n) (h n)
  let E' : ∀ n, S'.M n ≃ₗ[W] T'.M n := fun n => LinearEquiv.ofBijective (e'.f n) (h' n)
  have hc : ∀ n y, T.r n (E (n + 1) y) = E n (S.r n y) := fun n y => e.comm n y
  have hc' : ∀ n y, T'.r n (E' (n + 1) y) = E' n (S'.r n y) := fun n y => e'.comm n y
  have hr : ∀ n x, (E n).symm (T.r n x) = S.r n ((E (n + 1)).symm x) := by
    intro n x
    apply (E n).injective
    rw [LinearEquiv.apply_symm_apply, ← hc, LinearEquiv.apply_symm_apply]
  refine ⟨{
    ρ := fun c b => (E b).toLinearMap ∘ₗ L.ρ c b ∘ₗ (E c).symm.toLinearMap
    ν := fun a c => (E c).toLinearMap ∘ₗ L.ν a c ∘ₗ (E a).symm.toLinearMap
    δ := fun b a => (E' a).toLinearMap ∘ₗ L.δ b a ∘ₗ (E b).symm.toLinearMap
    kill := ?_, ρ_self := ?_, ρ_succ := ?_, ν_ρ := ?_, ν_r := ?_, ex₁ := ?_, δ_r := ?_, ex₂ := ?_ }⟩
  · intro n x
    apply (E n).symm.injective
    rw [map_smul, L.kill, map_zero]
  · intro c x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_self, LinearEquiv.apply_symm_apply]
  · intro c b hb x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [L.ρ_succ c b hb, hr]
  · intro a c ha x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [L.ν_ρ a c ha, map_smul, LinearEquiv.apply_symm_apply]
  · intro a c ha y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc, L.ν_r a c ha, hr]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.ρ c b ((E c).symm x) = 0 := by
      apply (E b).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₁ a b c hcab _ h0
    refine ⟨E a y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]
  · intro b a x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hc', L.δ_r]
  · intro a b c hcab x hx
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hx
    have h0 : L.δ b a ((E b).symm x) = 0 := by
      apply (E' a).injective
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := L.ex₂ a b c hcab _ h0
    refine ⟨E c y, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hy, LinearEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.TowerSeq
end

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lseq_of_level_isos : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' T T' : Sys.{1} W) (e : Sys.Hom S T (RingHom.id W)) (e' : Sys.Hom S' T' (RingHom.id W)), (∀ n, Function.Bijective (e.f n)) → (∀ n, Function.Bijective (e'.f n)) → LSeq l S S' → Nonempty (LSeq l T T') := by
  first | exact @GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | exact GlobalTheory.CompanionTheory.TowerSeq.lseq_transport | (intros; apply GlobalTheory.CompanionTheory.TowerSeq.lseq_transport <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoZeroSub
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.BijCov
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.BijOfSub
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

variable {R : Type} [CommRing R] {D D' : Type 1} [Category.{0} D] [Category.{0} D'] {Θ : PDF R D} {Θ' : PDF R D'}
  {P : ObjectProperty D} {P' : ObjectProperty D'}

def rA (Θ : PDF R D) {P Q : ObjectProperty D} (h : Q ≤ P) :
    CH.Mor (CH.modF (Θ.res P.ι).A) (CH.modF (Θ.res Q.ι).A) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

def rQ (Θ : PDF R D) {P Q : ObjectProperty D} (h : Q ≤ P) (c : R) :
    CH.Mor (sq (IdF.top (Θ.res P.ι).A) (IdF.span (Θ.res P.ι).A c)) (sq (IdF.top (Θ.res Q.ι).A) (IdF.span (Θ.res Q.ι).A c))
      (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem bij_of_sub {c : R} (m : QMor (Θ.res P.ι) (Θ'.res P'.ι) (IdF.span _ c)) (Q : ObjectProperty D) (Q' : ObjectProperty D')
    (hQ : Q ≤ P) (hQ' : Q' ≤ P') (hG : ∀ T : Q'.FullSubcategory, Q (m.G.obj ⟨T.obj, hQ' _ T.property⟩).obj) (j : ℕ)
    (z0 : Function.Bijective ((rA Θ hQ).pull j)) (zq : Function.Bijective ((rQ Θ' hQ' c).pull j))
    (g : Function.Bijective (((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl).pull j)) :
    Function.Bijective ((m.o (IdF.span _ c) fun _ => le_rfl).pull j) := by
  refine (Function.Bijective.of_comp_iff' zq _).1 ?_
  have e : ⇑((rQ Θ' hQ' c).pull j) ∘ ⇑((m.o (IdF.span _ c) fun _ => le_rfl).pull j) =
      ⇑(((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl).pull j) ∘ ⇑((rA Θ hQ).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (m.o (IdF.span _ c) fun _ => le_rfl) (rQ Θ' hQ' c) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (rA Θ hQ)
        ((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl) j x).1))
    rfl
  rw [e]
  exact g.comp z0

end CrystallineSemistableComparison.Pb.SubquotientResolution
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.LsQ

section Q

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k)


set_option maxHeartbeats 4000000 in
theorem bij_cov (U : Cov q) {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    Function.Bijective (((mq (F := B.schFn q) (ρ := ρ) hn).o (IdF.span _ ((l : WittVector l k) ^ n))
      (fun _ => le_rfl)).pull j) := by
  have hUs : sSup (Set.range U.U) = ⊤ := by
    rw [sSup_range]
    exact U.cover
  have g := GlobalTheory.T.witt_level_morphism_cover_compat q ρ U n ((l : WittVector l k) ^ n) (mq (F := B.schFn q) (ρ := ρ) hn) (hGq q ρ hn)
    (fun S hS j => by
      obtain ⟨α, hα⟩ := hS
      obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S, U.U α) ≤ U.U α) (U.inter S ⟨α, hα⟩)
      exact GlobalTheory.T.witt_coord_quotient_pull_bijective q ρ hn c' j) j
  have z0 := GlobalTheory.T.witt_site_restrict_bijective q ρ n (Set.range U.U) hUs j
  have zq := GlobalTheory.T.witt_site_quotient_restrict_bijective q ρ (n + 1) (Set.range U.U) ((l : WittVector l k) ^ n) hUs j
  exact bij_of_sub (mq (F := B.schFn q) (ρ := ρ) hn) (stF q ρ n (Set.range U.U)) (stF q ρ (n + 1) (Set.range U.U)) (fun _ h => h.1)
    (fun _ h => h.1) (hGq q ρ hn _) j z0 zq g

end Q


set_option maxHeartbeats 1000000 in
theorem bij : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K), M.Sm →
    ∀ (n : ℕ) (hn : n ≠ 0) (j : ℕ), Function.Bijective (((mq (F := B.schFn M.p) (ρ := r.ρ) hn).o
      (IdF.span _ ((l : WittVector l r.k) ^ n)) (fun _ => le_rfl)).pull j) := by
  intro l _ K r M hM n hn j
  have : IsProper M.p := GlobalTheory.CommonModel.isProper_of_isProjOver hM.1.1
  obtain ⟨U⟩ := (cov_ex M.p).1 hM.2
  exact bij_cov M.p r.ρ U hn j

end CrystallineSemistableComparison.Pb.SubquotientResolution

end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.LsQ

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG

section Gen

variable {R : Type} [CommRing R]

theorem mapH_comp {K L P : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (ψ : Cx.Hom L P (RingHom.id R)) (j : ℕ)
    (x : K.H j) : (φ.comp ψ).mapH j x = ψ.mapH j (φ.mapH j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem mapH_eq_self {K : Cx.{1} R} (φ : Cx.Hom K K (RingHom.id R)) (h : ∀ i x, φ.f i x = x) (j : ℕ) (x : K.H j) :
    φ.mapH j x = x := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h j z))

def hinv {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) :
    Cx.Hom L K (RingHom.id R) where
  f i := (LinearEquiv.ofBijective (φ.f i) (h i)).symm.toLinearMap
  comm i y := (h (i + 1)).1 (by
    have e : ∀ i y, φ.f i ((LinearEquiv.ofBijective (φ.f i) (h i)).symm y) = y := fun i y =>
      (LinearEquiv.ofBijective (φ.f i) (h i)).apply_symm_apply y
    change φ.f (i + 1) (K.d i ((LinearEquiv.ofBijective (φ.f i) (h i)).symm y)) =
      φ.f (i + 1) ((LinearEquiv.ofBijective (φ.f (i + 1)) (h (i + 1))).symm (L.d i y))
    rw [← φ.comm, e, e])

theorem hinv_left {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) (i : ℕ)
    (x : K.X i) : (hinv φ h).f i (φ.f i x) = x := (LinearEquiv.ofBijective (φ.f i) (h i)).symm_apply_apply x

theorem hinv_right {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) (i : ℕ)
    (y : L.X i) : φ.f i ((hinv φ h).f i y) = y := (LinearEquiv.ofBijective (φ.f i) (h i)).apply_symm_apply y

theorem hinv_bij {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) (i : ℕ) :
    Function.Bijective ((hinv φ h).f i) := (LinearEquiv.ofBijective (φ.f i) (h i)).symm.bijective

theorem mapH_bij {K L : Cx.{1} R} (φ : Cx.Hom K L (RingHom.id R)) (h : ∀ i, Function.Bijective (φ.f i)) (j : ℕ) :
    Function.Bijective (φ.mapH j) := by
  refine ⟨Function.LeftInverse.injective (g := (hinv φ h).mapH j) fun x => ?_,
    Function.RightInverse.surjective (g := (hinv φ h).mapH j) fun y => ?_⟩
  · rw [← mapH_comp]; exact mapH_eq_self _ (hinv_left φ h) j x
  · rw [← mapH_comp]; exact mapH_eq_self _ (hinv_right φ h) j y

theorem pull_comp {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} {F'' : C'' ⥤ ModuleCat.{0} R}
    (m : CH.Mor F F' (RingHom.id R)) (m' : CH.Mor F' F'' (RingHom.id R)) (j : ℕ) (x : CH.H F j) :
    (m.comp m').pull j x = m'.pull j (m.pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

def zh (K L : Cx.{1} R) : Cx.Hom K L (RingHom.id R) := ⟨fun _ => 0, fun _ _ => by simp⟩

theorem quo_zero_sub (l : ℕ) (K : Cx.{1} R) (j : ℕ) : Subsingleton ((quo l K 0).H j) := by
  have hX : Subsingleton ((quo l K 0).X j) := by
    refine Submodule.Quotient.subsingleton_iff.2 ?_
    rw [eq_top_iff]
    intro x _
    exact ⟨x, by simp⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Subsingleton.elim a b]

end Gen

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {F : B.Fn O} {ρ : O →+* k}

theorem Kt_zero_sub (j : ℕ) : Subsingleton ((Kt l F ρ 0).H j) := by
  have hW : Subsingleton (Wc.Wm l k 0) := by
    refine Ideal.Quotient.subsingleton_iff.2 ?_
    rw [pow_zero, Ideal.span_singleton_one]
  have hT : ∀ T : (fl l F ρ 0).FullSubcategory, Subsingleton T.obj.B := fun T =>
    subsingleton_of_zero_eq_one (by rw [← map_zero T.obj.i, Subsingleton.elim (0 : Wc.Wm l k 0) 1, map_one])
  have hX : Subsingleton ((Kt l F ρ 0).X j) :=
    ⟨fun f g => funext fun s => @Subsingleton.elim _ (hT (s.obj (Fin.last j))) (f s) (g s)⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have : a = b := Subsingleton.elim a b
  subst this
  rfl

section Pos

variable {n : ℕ} (hn : n ≠ 0)


variable (F ρ) in
def psiP : Cx.Hom (Kt l F ρ n) (quo l (Kt l F ρ (n + 1)) n) (RingHom.id _) :=
  ((mq hn).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).hom.comp
    (hinv (cmpq (sW l F ρ (n + 1)).A l n) fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l F ρ (n + 1)).A l n i)

theorem cmpq_psiP (j : ℕ) (y : (Kt l F ρ n).H j) :
    (cmpq (sW l F ρ (n + 1)).A l n).mapH j ((psiP F ρ hn).mapH j y) =
      ((mq hn).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).pull j y := by
  rw [psiP, mapH_comp, ← mapH_comp]
  exact mapH_eq_self _ (fun i x =>
    hinv_right (cmpq (sW l F ρ (n + 1)).A l n) (fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l F ρ (n + 1)).A l n i) i x) j _

theorem cmpq_prj (j : ℕ) (z : (Kt l F ρ (n + 1)).H j) :
    (cmpq (sW l F ρ (n + 1)).A l n).mapH j ((prj l (Kt l F ρ (n + 1)) n).mapH j z) =
      (qM (sW l F ρ (n + 1)).A l n).pull j z := by
  rw [← mapH_comp]
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

def qαN : ((qM (sW l F ρ (n + 1)).A l n).G ⋙ (fl l F ρ (n + 1)).ι) ⟶
    ((qG hn ⋙ (fl l F ρ n).ι) ⋙ (Wc.redM l F ρ n).functor) where
  app T := qα hn T.obj
  naturality _ _ f := (qα_nat hn f.hom).symm

theorem psiP_compat (j : ℕ) (x : (Wc.HS l F ρ j).M (n + 1)) :
    (psiP F ρ hn).mapH j (resF l F ρ n j ((Wc.HS l F ρ j).r n x)) =
      (prj l (Kt l F ρ (n + 1)) n).mapH j (resF l F ρ (n + 1) j x) := by
  apply (mapH_bij _ (fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l F ρ (n + 1)).A l n i) j).1
  rw [cmpq_psiP, cmpq_prj]
  have key := GlobalTheory.T.pull_eq_of_nat_trans _ _ _ _ _
    ((CH.Mor.restrict (Wc.OM l F ρ (n + 1)) (fl l F ρ (n + 1)).ι).comp (qM (sW l F ρ (n + 1)).A l n))
    ((Wc.redMor l F ρ n).comp ((CH.Mor.restrict (Wc.OM l F ρ n) (fl l F ρ n).ι).comp
      ((mq hn).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl))))
    (qαN hn) (fun _ _ => rfl) j
  have h1 := congrArg (fun g => g x) key
  simp only [pull_comp] at h1
  exact h1.symm

end Pos

theorem seqflat0_pf : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K),
    M.Sm → ∃ (ψ : ∀ n, Cx.Hom (Kt l (B.schFn M.p) r.ρ n) (quo l (Kt l (B.schFn M.p) r.ρ (n + 1)) n) (RingHom.id _))
      (_ : ∀ n j, Function.Bijective ((ψ n).mapH j)), ∀ n j x,
      (ψ n).mapH j (resF l (B.schFn M.p) r.ρ n j ((Wc.HS l (B.schFn M.p) r.ρ j).r n x)) =
        (prj l (Kt l (B.schFn M.p) r.ρ (n + 1)) n).mapH j (resF l (B.schFn M.p) r.ρ (n + 1) j x) := by
  intro l _ K r M hM
  refine ⟨fun n => if hn : n = 0 then zh _ _ else psiP (B.schFn M.p) r.ρ hn, fun n j => ?_, fun n j x => ?_⟩
  · by_cases hn : n = 0
    · subst hn
      have := Kt_zero_sub (F := B.schFn M.p) (ρ := r.ρ) j
      have := quo_zero_sub l (Kt l (B.schFn M.p) r.ρ 1) j
      exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    · dsimp only
      rw [dite_eq_right hn]
      have e : ∀ y, (psiP (B.schFn M.p) r.ρ hn).mapH j y =
          (hinv (cmpq (sW l (B.schFn M.p) r.ρ (n + 1)).A l n)
            fun i => GlobalTheory.T.compare_quotient_bijective _ _ (sW l (B.schFn M.p) r.ρ (n + 1)).A l n i).mapH j
          (((mq hn).o (IdF.span _ ((l : WittVector l r.k) ^ n)) (fun _ => le_rfl)).pull j y) := fun y =>
        mapH_comp _ _ j y
      rw [show ⇑((psiP (B.schFn M.p) r.ρ hn).mapH j) = _ from funext e]
      exact (mapH_bij _ (hinv_bij _ _) j).comp (SubquotientResolution.bij r M hM n hn j)
  · by_cases hn : n = 0
    · subst hn
      have := quo_zero_sub l (Kt l (B.schFn M.p) r.ρ 1) j
      exact Subsingleton.elim _ _
    · dsimp only
      rw [dite_eq_right hn]
      exact psiP_compat hn j x

end CrystallineSemistableComparison.Pb.LsQ

end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.LsG

open CrystallineSemistableComparison.Ls

theorem seq_flat {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K)
    (hM : M.Sm) : ∃ (ψ : ∀ n, Cx.Hom (Kt l (B.schFn M.p) r.ρ n) (quo l (Kt l (B.schFn M.p) r.ρ (n + 1)) n) (RingHom.id _))
      (_ : ∀ n j, Function.Bijective ((ψ n).mapH j)),
      (∀ m b (h : b ≤ m) j, Function.Bijective ((qred l (ψ m) h).mapH j)) ∧
      ∀ n j x, (ψ n).mapH j (resF l (B.schFn M.p) r.ρ n j ((Wc.HS l (B.schFn M.p) r.ρ j).r n x)) =
        (prj l (Kt l (B.schFn M.p) r.ρ (n + 1)) n).mapH j (resF l (B.schFn M.p) r.ρ (n + 1) j x) := by
  obtain ⟨ψ, hψ, hc⟩ := LsQ.seqflat0_pf r M hM
  have hfl : ∀ c, FlatL l c (Kt l (B.schFn M.p) r.ρ c) := fun c => GlobalTheory.T.flat_witt_tower_level l r.k _ (B.schFn M.p) r.ρ c
  exact ⟨ψ, hψ, fun m b h j => GlobalTheory.T.quotient_reduction_bijective_of_flat _ l _ _ m (ψ m) (hfl m) (hfl (m + 1)) (hψ m) b h j, hc⟩

theorem ls_seq {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (M : Model l K)
    (hM : M.Sm) (j : ℕ) :
    Nonempty (CrystallineSemistableComparison.Tw.LSeq l (Wc.HS l (B.schFn M.p) r.ρ j) (Wc.HS l (B.schFn M.p) r.ρ (j + 1))) := by
  obtain ⟨ψ, hψ, hq, hc⟩ := seq_flat r M hM
  have hf := GlobalTheory.T.smooth_model_restriction_bijective r M hM
  have hfl : ∀ c, FlatL l c (Kt l (B.schFn M.p) r.ρ c) := fun c => GlobalTheory.T.flat_witt_tower_level l r.k _ (B.schFn M.p) r.ρ c
  have fwd : ∀ i n x, (tsys l (Kt l (B.schFn M.p) r.ρ) ψ hψ i).r n (resF l (B.schFn M.p) r.ρ (n + 1) i x) =
      resF l (B.schFn M.p) r.ρ n i ((Wc.HS l (B.schFn M.p) r.ρ i).r n x) := by
    intro i n x
    change (LinearEquiv.ofBijective _ (hψ n i)).symm ((prj l _ n).mapH i (resF l (B.schFn M.p) r.ρ (n + 1) i x)) = _
    rw [← hc n i x]
    exact (LinearEquiv.ofBijective _ (hψ n i)).symm_apply_apply _
  let E : ∀ i n, (Wc.HS l (B.schFn M.p) r.ρ i).M n ≃ₗ[WittVector l r.k] (Kt l (B.schFn M.p) r.ρ n).H i :=
    fun i n => LinearEquiv.ofBijective _ (hf n i)
  let e : ∀ i, Sys.Hom (tsys l (Kt l (B.schFn M.p) r.ρ) ψ hψ i) (Wc.HS l (B.schFn M.p) r.ρ i) (RingHom.id _) := fun i =>
    { f := fun n => (E i n).symm.toLinearMap
      comm := fun n y => by
        apply (E i n).injective
        change E i n ((Wc.HS l (B.schFn M.p) r.ρ i).r n ((E i (n + 1)).symm y)) = E i n ((E i n).symm _)
        rw [LinearEquiv.apply_symm_apply]
        have h1 := fwd i n ((E i (n + 1)).symm y)
        have h2 : resF l (B.schFn M.p) r.ρ (n + 1) i ((E i (n + 1)).symm y) = y := (E i (n + 1)).apply_symm_apply y
        exact h1.symm.trans (congrArg _ h2) }
  exact GlobalTheory.T.lseq_of_level_isos _ l _ _ _ _ (e j) (e (j + 1)) (fun n => (E j n).symm.bijective) (fun n => (E (j + 1) n).symm.bijective)
    (GlobalTheory.T.lseq_of_flat_tower _ l _ ψ hψ hfl hq j).some

end CrystallineSemistableComparison.Pb.LsG

end
