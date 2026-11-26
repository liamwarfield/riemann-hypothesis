module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameDerivationCompat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvProd
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedQuotientInjectiveMap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedQuotientInjectiveMap
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

theorem idx_self_eq {d : ℕ} (I : Idx d d) : I.1 = id := by
  have hs : Function.Surjective I.1 := Finite.injective_iff_surjective.1 I.2.injective
  exact (StrictMono.range_inj I.2 strictMono_id).1 (by rw [hs.range_eq, Set.range_id])

theorem sum_idx_self {M : Type*} [AddCommMonoid M] {d : ℕ} [Fintype (Idx d d)] (g : Idx d d → M) :
    ∑ I, g I = g ⟨id, strictMono_id⟩ := by
  letI : Unique (Idx d d) :=
    { default := ⟨id, strictMono_id⟩, uniq := fun I => Subtype.ext (idx_self_eq I) }
  exact Fintype.sum_unique g

section Form
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d j : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (I : Fin j → Fin d) (u : ComposableArrows C j)

theorem form_add_fun (x x' : Φ.A.obj E.D) : E.form σ I (x + x') u = E.form σ I x u + E.form σ I x' u := by
  simp only [Frame.form, map_add (f := _), mul_add]

theorem form_sub_fun (x x' : Φ.A.obj E.D) : E.form σ I (x - x') u = E.form σ I x u - E.form σ I x' u := by
  simp only [Frame.form, map_sub, mul_sub]

theorem form_alg_mul (a : R) (x : Φ.A.obj E.D) :
    E.form σ I (algebraMap R _ a * x) u = a • E.form σ I x u := by
  simp only [Frame.form, map_mul, AlgHom.commutes, Algebra.smul_def]
  ring

end Form

theorem coef_map : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (r : ℤ), r = d → d + 1 ≤ s →
    letI := (strV q W).toAlgebra
    ∃ φ : HQ (KS q s {W}) r (r + 1) d →ₗ[K] Γ(X, W), Function.Injective φ ∧ ∀ (y : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c → φ c = y := by
  intro K _ _ X q W d t s E ε hL σ r hr hs
  letI := (strV q W).toAlgebra
  obtain ⟨hE, hU⟩ := GlobalTheory.T.local_graded_class_representative q t s E ε hL σ d r hr hs
  have ex : ∀ c : HQ (KS q s {W}) r (r + 1) d, ∃ y : Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c := by
    intro c
    obtain ⟨y, hy⟩ := hE c
    refine ⟨y ⟨id, strictMono_id⟩, ?_⟩
    have e : (fun u => ∑ I : Idx d d, E.form σ I.1 (ε (y I)) u) = E.form σ id (ε (y ⟨id, strictMono_id⟩)) :=
      funext fun u => sum_idx_self (fun I : Idx d d => E.form σ I.1 (ε (y I)) u)
    rwa [e] at hy
  have z0 : ∀ y : Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) 0 → y = 0 := by
    intro y h
    have e : (fun u => ∑ I : Idx d d, E.form σ I.1 (ε ((fun _ => y : Idx d d → Γ(X, W)) I)) u) = E.form σ id (ε y) :=
      funext fun u => sum_idx_self (fun I : Idx d d => E.form σ I.1 (ε y) u)
    exact congrFun (hU (fun _ => y) (by rwa [e])) ⟨id, strictMono_id⟩
  have uniq : ∀ (y y' : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c →
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y')) c → y = y' := by
    intro y y' c h h'
    have h2 := rep_add h (rep_smul (-1 : K) h')
    have e : (fun u => E.form σ id (ε y) u + (-1 : K) • E.form σ id (ε y') u) = E.form σ id (ε (y - y')) := by
      funext u
      rw [map_sub, form_sub_fun, neg_one_smul, sub_eq_add_neg]
    rw [e, neg_one_smul, add_neg_cancel] at h2
    exact sub_eq_zero.1 (z0 _ h2)
  choose φ hφ using ex
  refine ⟨{ toFun := φ, map_add' := ?_, map_smul' := ?_ }, ?_, fun y c h => uniq _ _ c (hφ c) h⟩
  · intro c c'
    refine uniq _ _ (c + c') (hφ _) ?_
    have h2 := rep_add (hφ c) (hφ c')
    have e : (fun u => E.form σ id (ε (φ c)) u + E.form σ id (ε (φ c')) u) = E.form σ id (ε (φ c + φ c')) := by
      funext u
      rw [map_add (f := _), form_add_fun]
    rwa [e] at h2
  · intro a c
    refine uniq _ _ (a • c) (hφ _) ?_
    have h2 := rep_smul a (hφ c)
    have e : (fun u => a • E.form σ id (ε (φ c)) u) = E.form σ id (ε (a • φ c)) := by
      funext u
      have e1 : a • φ c = strV q W a * φ c := Algebra.smul_def a (φ c)
      rw [e1, map_mul, hL.2.2.1 a, form_alg_mul]
    rwa [e] at h2
  · intro c c' h
    have h' : φ c = φ c' := h
    have h2 := hφ c'
    rw [← h'] at h2
    exact rep_unique (hφ c) h2

end GlobalTheory.CompanionTheory.ConeLocal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedQuotientInjectiveMapStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_graded_quotient_injective_map : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (r : ℤ), r = d → d + 1 ≤ s →
    letI := (strV q W).toAlgebra
    ∃ φ : HQ (KS q s {W}) r (r + 1) d →ₗ[K] Γ(X, W), Function.Injective φ ∧ ∀ (y : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c → φ c = y := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.coef_map | exact GlobalTheory.CompanionTheory.ConeLocal.coef_map | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.coef_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAbove
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAbove
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal.SnocPerm

theorem eq_succAbove_of_snoc_eq_perm {n : ℕ} (I : Fin n → Fin (n + 1)) (k : Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 1))) (hI : StrictMono I)
    (h : Fin.snoc (α := fun _ => Fin (n + 1)) I k = ⇑π) : I = k.succAbove := by
  have hcast : ∀ i : Fin n, π i.castSucc = I i := fun i => by
    rw [← h]; simp
  have hlast : π (Fin.last n) = k := by
    rw [← h]; simp
  have hrange : Set.range I = Set.range k.succAbove := by
    rw [Fin.range_succAbove]
    ext y
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩ hy
      rw [← hcast i, ← hlast] at hy
      exact (Fin.castSucc_lt_last i).ne (π.injective hy)
    · intro hy
      obtain ⟨x, rfl⟩ := π.surjective y
      have hx : x ≠ Fin.last n := fun hx => hy (by rw [hx, hlast])
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hx
      exact ⟨i, (hcast i).symm⟩
  exact (StrictMono.range_inj hI (Fin.strictMono_succAbove k)).1 hrange

end GlobalTheory.CompanionTheory.ConeLocal.SnocPerm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAboveStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictMono_snoc_perm_eq_succAbove : ∀ {n : ℕ} (I : Fin n → Fin (n + 1)) (k : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 1))), StrictMono I →
    Fin.snoc (α := fun _ => Fin (n + 1)) I k = ⇑π → I = k.succAbove := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm | exact GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.SnocPerm.eq_succAbove_of_snoc_eq_perm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentative
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal


open GlobalTheory.CompanionTheory.CocProd in
theorem d_eq_of_rep {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {n : ℕ}
    (f g : CH.Cn (CH.modF A) n) {c : CH.H (sq a b) n}
    (hf : CrystallineSemistableComparison.Pb.Rep a b (fun u => f u) c) (hg : CrystallineSemistableComparison.Pb.Rep a b (fun u => g u) c) :
    ∃ e : CH.Cn (CH.modF A) n, (∀ s, e s ∈ b.S _) ∧ CH.d _ n f = CH.d _ n g + CH.d _ n e := by
  obtain ⟨f', hf', rfl, hv⟩ := hf
  obtain ⟨g', hg', hc, hv'⟩ := hg
  have hB : f' - g' ∈ (CH.cx (sq a b)).B n := by
    have := (Submodule.Quotient.eq _).1 hc
    exact this
  cases n with
  | zero =>
    have h0 : f' - g' = 0 := hB
    refine ⟨f - g, fun s => ?_, ?_⟩
    · have e1 : (show sqM a b _ from f' s) = (show sqM a b _ from g' s) := congrFun (sub_eq_zero.1 h0) s
      have e2 := (hv s).symm.trans ((congrArg Subtype.val e1).trans (hv' s))
      have e3 : ∀ x y : A.obj (s.obj (Fin.last 0)), Ideal.Quotient.mk (b.S _) x = Ideal.Quotient.mk (b.S _) y → x - y ∈ b.S _ :=
        fun x y h => Ideal.Quotient.eq.1 h
      exact e3 _ _ e2
    · rw [map_sub]; abel
  | succ m =>
    obtain ⟨h', hh⟩ := hB
    have hl : ∀ s, ∃ t ∈ a.S _, Ideal.Quotient.mk (b.S _) t = (show sqM a b _ from h' s).1 := fun s =>
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from h' s).2
    choose l hl1 hl2 using hl
    let l' : CH.Cn (CH.modF A) m := fun s => l s
    refine ⟨f - g - CH.d _ m l', fun s => ?_, ?_⟩
    · have e0 := d_val h' (fun s => l s) (fun s => (hl2 s).symm) s
      have e1 : (show sqM a b _ from CH.d (sq a b) m h' s) =
          (show sqM a b _ from f' s) - (show sqM a b _ from g' s) := congrFun hh s
      rw [e1] at e0
      have e3 : ∀ x y z : A.obj (s.obj (Fin.last (m + 1))), Ideal.Quotient.mk (b.S _) x - Ideal.Quotient.mk (b.S _) y =
          Ideal.Quotient.mk (b.S _) z → x - y - z ∈ b.S _ := fun x y z h => by
        rw [← map_sub] at h
        exact Ideal.Quotient.eq.1 h
      refine e3 _ _ _ ?_
      rw [← hv, ← hv']
      exact e0
    · rw [map_sub, map_sub, CH.d_d]; abel

section Form
open GlobalTheory.CompanionTheory.CocProd
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)

def headP {j : ℕ} (I : Fin j → Fin d) (s : ComposableArrows C (j + 1)) : Φ.A.obj (s.obj (Fin.last (j + 1))) :=
  ∏ k : Fin j, ga E σ (I k) s k.castSucc.castSucc k.succ.castSucc (by rw [Fin.le_def]; simp)

theorem alt_sum_form {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
      (-1) ^ j * (headP E σ I s * ((Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x -
        (Φ.A.map (σ _ ≫ toLast (Fin.last (j + 1)) s)).hom x)) := by
  classical
  set u : Fin j → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun k =>
    ga E σ (I k) s k.castSucc.castSucc k.succ.castSucc (by rw [Fin.le_def]; simp) with hu
  set v : Fin j → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun k =>
    ga E σ (I k) s k.succ.castSucc k.succ.succ (by rw [Fin.le_def]; simp) with hv
  set P : ℕ → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP
  set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    ∏ k : Fin j, ga E σ (I k) s (i.succAbove k.castSucc) (i.succAbove k.succ)
        ((Fin.strictMono_succAbove i).monotone (Fin.castSucc_lt_succ (i := k)).le) with hT
  set W : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    (Φ.A.map (toLast i s)).hom ((Φ.A.map (σ _)).hom x) with hW
  set Y := (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom x with hY
  have hT0 : T 0 = P 0 := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Nat.not_lt_zero, if_false]
    refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp
  have hTl : T (Fin.last (j + 1)) = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp
  have hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i := by
    intro i
    have hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)
      simp only [Nat.lt_add_one, if_true] at this
      exact this.symm
    have hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)
      simp only [lt_irrefl, if_false] at this
      exact this.symm
    have hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => ga E σ (I k) s (i.succ.castSucc.succAbove k.castSucc)
        (i.succ.castSucc.succAbove k.succ) ((Fin.strictMono_succAbove _).monotone (Fin.castSucc_lt_succ (i := k)).le)) (Finset.mem_univ i)
      refine this.symm.trans ?_
      congr 1
      · rw [hu, hv]
        dsimp only
        rw [← ga_add]
        refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp [sa_val] <;> (try split_ifs) <;> simp_all <;> omega
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
        split_ifs with h
        · refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp [sa_val] <;> (try split_ifs) <;> simp_all <;> omega
        · refine ga_congr E σ _ s _ _ ?_ ?_ <;> simp [sa_val] <;> (try split_ifs) <;> simp_all <;> omega
    have hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) =
        ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
      have : (k : ℕ) < i + 1 ↔ (k : ℕ) < i := by omega
      simp only [this]
    rw [hTa, hPa, hPb, hE]
    ring
  have hWY : ∀ i : Fin (j + 2), i ≠ Fin.last (j + 1) → W i = Y := by
    intro i hi
    have hi' : i.succAbove (Fin.last j) = Fin.last (j + 1) := by
      have h1 : (i : ℕ) ≠ j + 1 := fun h => hi (Fin.ext h)
      have h2 := i.2
      apply Fin.ext
      rw [sa_val]
      simp only [Fin.val_last]
      split_ifs <;> omega
    calc W i = (Φ.A.map (σ _ ≫ toLast i s)).hom x := map_map _ _ _
      _ = Y := by rw [show σ _ ≫ toLast i s = σ (s.obj (Fin.last (j + 1))) from sec_last E σ s _ hi']
  have hPj : headP E σ I s = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    rfl
  have hWl : (Φ.A.map (σ _ ≫ toLast (Fin.last (j + 1)) s)).hom x = W (Fin.last (j + 1)) := (map_map _ _ _).symm
  rw [hWl, hPj]
  have hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) =
      (-1) ^ (i : ℕ) * (T i * W i) := by
    intro i
    rw [face_form, zsmul_eq_mul]
    push_cast
    rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have h0 : T (Fin.castSucc 0) = P 0 := hT0
  have hne0 : Fin.castSucc (0 : Fin (j + 1)) ≠ Fin.last (j + 1) := (Fin.castSucc_lt_last _).ne
  have hint : ∑ i : Fin j, (-1) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * (T i.succ.castSucc * W i.succ.castSucc) =
      (∑ m ∈ Finset.range j, (-1) ^ (m + 1) * (P (m + 1) + P m)) * Y := by
    rw [Finset.sum_mul, ← Fin.sum_univ_eq_sum_range (fun m => (-1) ^ (m + 1) * (P (m + 1) + P m) * Y) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hTi, hWY _ (Fin.castSucc_lt_last _).ne]
    simp only [Fin.val_castSucc, Fin.val_succ]
    ring
  rw [hint, h0, hWY _ hne0, hTl]
  simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]
  linear_combination Y * tele P j

theorem form_snoc {j : ℕ} (I : Fin j → Fin d) (k : Fin d) (z : Φ.A.obj E.D) (s : ComposableArrows C (j + 1)) :
    E.form σ (Fin.snoc (α := fun _ => Fin d) I k) z s =
      headP E σ I s * (ga E σ k s ((Fin.last (j + 1)).succAbove (Fin.last j)) (Fin.last (j + 1)) (Fin.le_last _) *
        (Φ.A.map (σ (s.obj (Fin.last (j + 1))))).hom z) := by
  unfold Frame.form headP
  rw [Fin.prod_univ_castSucc, mul_assoc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    rw [Fin.snoc_castSucc (α := fun _ => Fin d)]
    exact ga_congr E σ _ s _ _ (by simp) (by simp)
  · congr 1
    rw [Fin.snoc_last (α := fun _ => Fin d)]
    refine ga_congr E σ _ s (Fin.castSucc_lt_succ (i := Fin.last j)).le _ ?_ ?_
    · simp [sa_val]
    · simp

theorem ga_last {j : ℕ} (k : Fin d) (s : ComposableArrows C (j + 1)) (q : Fin (j + 2)) (h : q ≤ Fin.last (j + 1)) :
    ga E σ k s q (Fin.last (j + 1)) h = E.τ k (σ (s.obj q) ≫ s.map (homOfLE h)) (σ (s.obj (Fin.last (j + 1)))) := by
  unfold ga
  have : (homOfLE (Fin.le_last (Fin.last (j + 1))) : Fin.last (j + 1) ⟶ Fin.last (j + 1)) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, s.map_id]
  simp
  rfl

theorem form_neg_pow {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (m : ℕ) (s : ComposableArrows C j) :
    E.form σ I ((-1) ^ m * x) s = (-1) ^ m * E.form σ I x s := by
  unfold Frame.form
  rw [map_mul, map_pow, map_neg, map_one]
  ring

end Form

section Conn
open GlobalTheory.CompanionTheory.CocProd
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}

theorem d_form {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    {p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D} (hT : Taylor Fil E p) {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D)
    (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) -
      (-1) ^ j * ∑ k : Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) I k) (p k x) s ∈ (Fil ((j : ℤ) + 1 + 1)).S _ := by
  set q := (Fin.last (j + 1)).succAbove (Fin.last j) with hq
  set T := s.obj (Fin.last (j + 1)) with hTdef
  set v : E.D ⟶ T := σ (s.obj q) ≫ s.map (homOfLE (Fin.le_last q)) with hv
  have hvl : (σ _ ≫ toLast (Fin.last (j + 1)) s) = v := rfl
  set g : Fin d → Φ.A.obj T := fun k => ga E σ k s q (Fin.last (j + 1)) (Fin.le_last _) with hg
  have hgτ : ∀ k, g k = E.τ k v (σ T) := fun k => ga_last E σ k s q (Fin.le_last _)
  have hg1 : ∀ k, g k ∈ (Fil ((1 : ℕ) : ℤ)).S T := fun k => ga_mem E σ hF k s q _ _
  have hdiff : ∀ k, g k * ((Φ.A.map v).hom (p k x) - (Φ.A.map (σ T)).hom (p k x)) ∈ (Fil ((2 : ℕ) : ℤ)).S T := by
    intro k
    have h0 : p k x ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
      rw [hF.top _ (by norm_num)]; trivial
    have h1 := hc 0 v (σ T) h0
    have e1 : (((0 : ℕ) : ℤ) + 1) = ((1 : ℕ) : ℤ) := by norm_num
    rw [e1] at h1
    exact hF.mul 1 1 T (hg1 k) h1
  have hin : (Φ.A.map (σ T)).hom x - (Φ.A.map v).hom x - ∑ k, g k * (Φ.A.map (σ T)).hom (p k x) ∈ (Fil ((2 : ℕ) : ℤ)).S T := by
    have tay := hT T (σ T) v x
    have e2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := by norm_num
    rw [e2] at tay
    have e3 : (Φ.A.map (σ T)).hom x - (Φ.A.map v).hom x - ∑ k, g k * (Φ.A.map (σ T)).hom (p k x) =
        ((Φ.A.map (σ T)).hom x - (Φ.A.map v).hom x - ∑ k, E.τ k v (σ T) * (Φ.A.map v).hom (p k x)) +
          ∑ k, g k * ((Φ.A.map v).hom (p k x) - (Φ.A.map (σ T)).hom (p k x)) := by
      simp only [hgτ, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e3]
    exact Ideal.add_mem _ tay (Ideal.sum_mem _ fun k _ => hdiff k)
  have hfin := prod_mem hF (fun k : Fin j => ga E σ (I k) s k.castSucc.castSucc k.succ.castSucc (by rw [Fin.le_def]; simp))
    (fun k => ga_mem E σ hF _ s _ _ _) hin
  have e4 : ((j + 2 : ℕ) : ℤ) = (j : ℤ) + 1 + 1 := by push_cast; ring
  rw [e4] at hfin
  have e5 : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I x (face i s)) -
      (-1) ^ j * ∑ k : Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) I k) (p k x) s =
      (-1) ^ j * (headP E σ I s * ((Φ.A.map (σ T)).hom x - (Φ.A.map v).hom x - ∑ k, g k * (Φ.A.map (σ T)).hom (p k x))) := by
    rw [alt_sum_form, hvl]
    simp only [form_snoc, ← Finset.mul_sum]
    ring
  rw [e5]
  exact Ideal.mul_mem_left _ _ hfin

theorem connecting_form {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (hT : Taylor Fil E p) (n : ℕ) (f : CH.Cn (CH.modF Φ.A) n) (y : Idx n d → Φ.A.obj E.D) (c : CH.H (gr Fil (n : ℤ)) n)
      (x : CH.H (gr Fil ((n : ℤ) + 1)) (n + 1))
      (hf : CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => f u) c)
      (hg : CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => ∑ I : Idx n d, E.form σ I.1 (y I) u) c)
      (hx : CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) (fun u => CH.d _ n f u) x) :
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1))
        (fun u => ∑ a : Idx n d × Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) a.1.1 a.2) ((-1) ^ n * p a.2 (y a.1)) u) x := by
  let g : CH.Cn (CH.modF Φ.A) n := fun u => (∑ I : Idx n d, E.form σ I.1 (y I) u : Φ.A.obj (u.obj (Fin.last n)))
  obtain ⟨e, he, hde⟩ := d_eq_of_rep f g hf hg
  have h0 : CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) (fun u => CH.d _ n (-e) u) 0 :=
    rep_d (-e) fun s => (Fil ((n : ℤ) + 1)).S _ |>.neg_mem (he s)
  have h1 := rep_add hx h0
  rw [add_zero] at h1
  refine rep_congr h1 fun s => ?_
  have e1 : CH.d _ n f s + CH.d _ n (-e) s = CH.d _ n g s := by
    rw [hde, map_neg]
    simp
  have e2 : ∀ (a b : Φ.A.obj (s.obj (Fin.last (n + 1)))), (CH.d _ n f s + CH.d _ n (-e) s : (CH.modF Φ.A).obj _) = a →
     a - b ∈ (Fil ((n : ℤ) + 1 + 1)).S _ → (show Φ.A.obj _ from CH.d _ n f s) + (show Φ.A.obj _ from CH.d _ n (-e) s) - b ∈ (Fil ((n : ℤ) + 1 + 1)).S _ := by
    intro a b h h'
    rw [← h] at h'
    exact h'
  refine e2 (∑ I : Idx n d, ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (E.form σ I.1 (y I) (face i s))) _ ?_ ?_
  · rw [e1]
    change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (∑ I : Idx n d, E.form σ I.1 (y I) (face i s)) = _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
  · rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have := d_form hF E σ hc hT I.1 (y I) s
    simpa only [form_neg_pow, Finset.mul_sum] using this

end Conn

end GlobalTheory.CompanionTheory.ConeLocal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorDifferentialRepresentativeStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_differential_representative : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D), Taylor Fil E p → ∀ (n : ℕ) (f : CH.Cn (CH.modF Φ.A) n) (y : Idx n d → Φ.A.obj E.D) (c : CH.H (gr Fil (n : ℤ)) n)
      (x : CH.H (gr Fil ((n : ℤ) + 1)) (n + 1)),
      CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => f u) c →
      CrystallineSemistableComparison.Pb.Rep (Fil (n : ℤ)) (Fil ((n : ℤ) + 1)) (fun u => ∑ I : Idx n d, E.form σ I.1 (y I) u) c →
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) (fun u => CH.d _ n f u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1))
        (fun u => ∑ a : Idx n d × Fin d, E.form σ (Fin.snoc (α := fun _ => Fin d) a.1.1 a.2) ((-1) ^ n * p a.2 (y a.1)) u) x := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.connecting_form | exact GlobalTheory.CompanionTheory.ConeLocal.connecting_form | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.connecting_form <;> assumption)
end
end

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

def I0 (m : ℕ) : Idx m m := ⟨id, strictMono_id⟩

theorem idx_eq {m : ℕ} (I : Idx m m) : I = I0 m := by
  refine Subtype.ext ((StrictMono.range_inj I.2 strictMono_id).1 ?_)
  have h : Function.Surjective I.1 := (Finite.injective_iff_surjective).1 I.2.injective
  rw [h.range_eq, Function.surjective_id.range_eq]

instance {m : ℕ} : Unique (Idx m m) := ⟨⟨I0 m⟩, idx_eq⟩

theorem sgn_det {B : Type} [CommRing B] {m : ℕ} (c : Fin m → Fin m → B) :
    ∑ J : Fin m → Fin m, sgn (I0 m) J • ∏ k, c k (J k) = (Matrix.of fun i k => c k i).det := by
  rw [Matrix.det_apply]
  simp only [sgn, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.sum_eq_single (⇑π)]
  · simp only [I0, Function.id_comp, if_true]
    rw [Units.smul_def]
    simp
  · intro J _ hJ
    simp [I0, hJ]
  · simp

theorem sgn_snoc {n : ℕ} (I : Idx n (n + 1)) (k : Fin (n + 1)) (h : I.1 ≠ k.succAbove) :
    sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) I.1 k) = 0 := by
  refine Finset.sum_eq_zero fun π _ => ?_
  rw [if_neg]
  intro e
  exact h (GlobalTheory.T.strictMono_snoc_perm_eq_succAbove I.1 k π I.2 e)

theorem inv_map {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) : Ring.inverse (e a) = e (Ring.inverse a) := by
  by_cases h : IsUnit a
  · obtain ⟨v, rfl⟩ := h
    have e1 : e (v : A) = ((Units.map e.toMonoidHom v : Bˣ) : B) := rfl
    rw [e1, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · have h' : ¬ IsUnit (e a) := fun hu => h ((MulEquiv.isUnit_map e).1 hu)
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', map_zero]

theorem inv_prod {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] (u : ι → A) (h : ∀ k, IsUnit (u k)) :
    Ring.inverse (∏ k, u k) = ∏ k, Ring.inverse (u k) := by
  choose v hv using h
  simp only [← hv]
  rw [← Units.coe_prod, Ring.inverse_unit, ← Finset.prod_inv_distrib, Units.coe_prod]
  simp only [Ring.inverse_unit]

theorem rep_one {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {m : ℕ} (E : Frame Φ m)
    (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (w : Idx m m → Φ.A.obj E.D) (cl : CH.H (gr Fil r) m)
    (h : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m m, E.form σ I.1 (w I) u) cl) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ id (w (I0 m))) cl := by
  refine rep_congr h fun u => ?_
  rw [Fintype.sum_unique]
  change E.form σ (I0 m).1 (w (I0 m)) u - _ ∈ _
  rw [show (I0 m).1 = id from rfl, sub_self]
  exact Ideal.zero_mem _

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (n s : ℕ), n + 1 < s → ∀ (V V' : X.Opens) (hVV : V ≤ V'), IsAffineOpen V' → ∀ (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∃ φ : HQ (KS q s {V}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1) →ₗ[K] Γ(X, V), Function.Injective φ ∧
      (∀ (g : Fin (n + 1) → Γ(X, V')), (∀ k, IsUnit (g k)) → ∀ ĝ : Fin (n + 1) → ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B, (∀ k T, Ideal.Quotient.mk T.obj.J (ĝ k T) = ev T.obj (ks_in q s V' _ T.property) (g k)) → ∀ x : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1),
        Rep (sFil (KS q s {V'}) ((n : ℤ) + 1)) (sFil (KS q s {V'}) ((n : ℤ) + 1 + 1))
          (cupListC (sP (KS q s {V'})).A fun k => dlogC (KS q s {V'}) s (ĝ k)) x →
        φ (resKS q s hVV _ _ _ x) = Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det ∨
        φ (resKS q s hVV _ _ _ x) = -(Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det)) ∧
      (∀ ω : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1),
        φ (resKS q s hVV _ _ _ ω) ∈ jacSpan hVV (RingHom.id _) (fun k => D k) id) ∧
      ∀ (f : CH.Cn (CH.modF (sP (KS q s {V'})).A) n), (∀ σ, f σ ∈ (sFil (KS q s {V'}) n).S _) →
        (∀ σ, CH.d _ n f σ ∈ (sFil (KS q s {V'}) ((n : ℤ) + 1)).S _) →
        ∀ x : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1),
        Rep (sFil (KS q s {V'}) ((n : ℤ) + 1)) (sFil (KS q s {V'}) ((n : ℤ) + 1 + 1)) (CH.d _ n f) x →
        ∃ η : Fin (n + 1) → Γ(X, V), (∀ k, η k ∈ jacSpan hVV (RingHom.id _) (fun k => D k) (Fin.succAbove k)) ∧
          φ (resKS q s hVV _ _ _ x) = ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k) := by
  intro K _ _ X q _ n s hs V V' hVV hV' c D hD
  obtain ⟨E, ε, hL⟩ := GlobalTheory.T.exists_local_frame_of_coords q c s (by omega)
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  have hT := GlobalTheory.T.taylor_of_local_frame q c s E ε hL D hD
  have hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨φ, hinj, hφ⟩ := GlobalTheory.T.top_graded_quotient_injective_map q c.t s E ε hL σ ((n : ℤ) + 1) hr (by omega)
  refine ⟨φ, hinj, ?_, ?_, ?_⟩
  · intro g hg ĝ hĝ x hx
    left
    have h1 := rep_res (ks_le q s hVV) _ _ hx
    choose h hh happ using fun k => GlobalTheory.T.local_frame_taylor_class_eq q s (by omega) hVV c.t E ε hL _ hT σ (g k) (hg k) (ĝ k) (hĝ k)
    let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k => resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s (ĝ k))
    let cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D := fun k i =>
      Ring.inverse (ε (rs hVV (g k))) * ε (D i (ε.symm (ε (rs hVV (g k)))))
    have h2 : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
        (fun u => (show (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) from cupListC (sP (KS q s {V})).A ℓ u) *
          ((sP (KS q s {V})).A.map (σ _)).hom 1) (resKS q s hVV _ _ _ x) := by
      refine rep_congr h1 fun u => ?_
      have e := congrFun (cup_resQ (ks_le q s hVV) (fun k => dlogC (KS q s {V'}) s (ĝ k))) u
      rw [map_one, mul_one]
      exact (sub_eq_zero.2 e) ▸ Ideal.zero_mem _
    have h3 := GlobalTheory.T.cup_list_representative_of_forms hF E σ hc (n + 1) ℓ cc h hh happ 1 _ hr _ h2
    have h4 := GlobalTheory.T.form_sum_representative_lift hF E σ hc (n + 1) _ hr (fun I => I) (fun I => 1 * ∏ k, cc k (I k)) _ h3
    have h5 := rep_one E σ _ (fun I => ∑ J, sgn I J • (1 * ∏ k, cc k (J k))) _ h4
    have hu : ∀ k, IsUnit (rs hVV (g k)) := fun k => (hg k).map (rs hVV)
    have e : ∑ J : Fin (n + 1) → Fin (n + 1), sgn (I0 (n + 1)) J • (1 * ∏ k, cc k (J k)) =
        ε (Ring.inverse (∏ k, rs hVV (g k)) * (Matrix.of fun k l => D k (rs hVV (g l))).det) := by
      simp only [one_mul]
      rw [sgn_det, inv_prod _ hu, ← Matrix.det_mul_row]
      have e1 := (ε : Γ(X, V) →+* (sP (KS q s {V})).A.obj E.D).map_det
        (Matrix.of fun k l => Ring.inverse (rs hVV (g l)) * D k (rs hVV (g l)))
      refine Eq.trans ?_ e1.symm
      congr 1
      ext i k
      simp [cc, inv_map]
    rw [e] at h5
    exact hφ _ _ h5
  · intro ω
    obtain ⟨y, hy⟩ := (GlobalTheory.T.local_graded_class_representative q c.t s E ε hL σ (n + 1) ((n : ℤ) + 1) hr (by omega)).1 (resKS q s hVV _ _ _ ω)
    have h1 := GlobalTheory.T.local_frame_derivation_compat q s hVV hV' c D hD E ε hL σ (n + 1) ((n : ℤ) + 1) hr (by omega) ω y hy (I0 _)
    have h2 := hφ (y (I0 _)) _ (rep_one E σ _ (fun I => ε (y I)) _ hy)
    rw [h2]
    exact h1
  · intro f hf hdf x hx
    obtain ⟨ξ, hξ⟩ := rep_exists (a := sFil (KS q s {V'}) (n : ℤ)) (b := sFil (KS q s {V'}) ((n : ℤ) + 1)) f hf hdf
    have h1 := rep_res (ks_le q s hVV) _ _ hξ
    have h2 := rep_res (ks_le q s hVV) _ _ hx
    obtain ⟨y, hy⟩ := (GlobalTheory.T.local_graded_class_representative q c.t s E ε hL σ n (n : ℤ) rfl (by omega)).1 (resKS q s hVV _ _ _ ξ)
    have hmem := GlobalTheory.T.local_frame_derivation_compat q s hVV hV' c D hD E ε hL σ n (n : ℤ) rfl (by omega) ξ y hy
    have h2' : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
        (fun u => CH.d _ n (resQ (ks_le q s hVV) f) u) (resKS q s hVV _ _ _ x) := by
      refine rep_congr h2 fun u => ?_
      have e := congrFun (d_resQ (ks_le q s hVV) f) u
      exact (sub_eq_zero.2 e.symm) ▸ Ideal.zero_mem _
    have h3 := GlobalTheory.T.taylor_differential_representative hF E σ hc _ hT n (resQ (ks_le q s hVV) f) (fun I => ε (y I)) (resKS q s hVV _ _ _ ξ) (resKS q s hVV _ _ _ x) h1 hy h2'
    have h4 := GlobalTheory.T.form_sum_representative_lift hF E σ hc (n + 1) _ hr (fun a : Idx n (n + 1) × Fin (n + 1) => Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2)
      (fun a => (-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) _ h3
    have h5 := rep_one E σ _ (fun I => ∑ a : Idx n (n + 1) × Fin (n + 1), sgn I (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1)))))) _ h4
    let Ik : Fin (n + 1) → Idx n (n + 1) := fun k => ⟨k.succAbove, Fin.strictMono_succAbove k⟩
    let sg : Fin (n + 1) → ℤ := fun k => sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) (Ik k).1 k)
    refine ⟨fun k => ((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k), fun k => ?_, ?_⟩
    · exact AddSubgroup.zsmul_mem _ (hmem (Ik k)) _
    · have e : ∑ a : Idx n (n + 1) × Fin (n + 1), sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) =
          ε (∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Fintype.sum_prod_type_right, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_eq_single (Ik k)]
        · have a1 : ((-1 : Γ(X, V)) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by rw [← mul_pow]; simp
          rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul, RingEquiv.symm_apply_apply]
          push_cast
          have a2 : (-1 : Γ(X, V)) ^ (k : ℕ) * (((-1) ^ (k : ℕ) * (-1) ^ n * (sg k : Γ(X, V))) * D k (y (Ik k))) =
              (sg k : Γ(X, V)) * ((-1) ^ n * D k (y (Ik k))) := by
            linear_combination ((-1) ^ n * (sg k : Γ(X, V)) * D k (y (Ik k))) * a1
          rw [a2, map_mul, map_mul, map_pow, map_neg, map_one, map_intCast]
        · intro I _ hI
          rw [sgn_snoc I k (fun h => hI (Subtype.ext h)), zero_smul]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [e] at h5
      exact hφ _ _ h5

end GlobalTheory.CompanionTheory.ConeLocal
end
end

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.LExact

open GlobalTheory.CompanionTheory.CupRep

section
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ) (V : X.Opens)
  {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
  (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D) (σ : ∀ T, E.D ⟶ T)

def lf (g : Γ(X, V)) (T : (KS q s {V}).FullSubcategory) : (sP (KS q s {V})).A.obj T :=
  liftV T.obj (ks_in q s V T.obj T.property) g

variable {q s V t E ε}

theorem lf_sub_mem (hL : IsLoc q s t E ε) (g : Γ(X, V)) (T : (KS q s {V}).FullSubcategory) (u : E.D ⟶ T) :
    lf q s V g T - ((sP (KS q s {V})).A.map u).hom (ε g) ∈ (sP (KS q s {V})).J.S T := by
  have a1 : Ideal.Quotient.mk T.obj.J (lf q s V g T) = ev T.obj (ks_in q s V T.obj T.property) g :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T.obj (ks_in q s V T.obj T.property) g))
  have a2 := hL.2.2.2.1 T u g
  exact Ideal.Quotient.eq.1 (a1.trans a2)

theorem addC_eq (hL : IsLoc q s t E ε) (k : Fin d) (u : ComposableArrows (KS q s {V}).FullSubcategory 1) :
    (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from addC (KS q s {V}) (lf q s V (t k)) u) -
      (∑ i, E.form σ ![i] (if k = i then 1 else 0) u +
        ((lf q s V (t k) (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))) -
          ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom
            (lf q s V (t k) (u.obj 0) - ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))))) = 0 := by
  have e1 : ∑ i, E.form σ ![i] (if k = i then (1 : (sP (KS q s {V})).A.obj E.D) else 0) u =
      E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) := by
    simp only [DlogApprox.form_one]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, map_one, mul_one]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), map_zero, mul_zero]
    · simp
  have e2 : E.a σ k (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) =
      ((sP (KS q s {V})).A.map (σ _)).hom (ε (t k)) -
      ((sP (KS q s {V})).A.map (σ _ ≫ u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (ε (t k)) :=
    hL.2.2.2.2 k _ _
  have e3 : ((sP (KS q s {V})).A.map (σ _ ≫ u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (ε (t k)) =
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (((sP (KS q s {V})).A.map (σ _)).hom (ε (t k))) := by
    rw [Functor.map_comp]; rfl
  rw [e1, e2, e3, map_sub]
  change (lf q s V (t k) (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (lf q s V (t k) (u.obj 0))) - _ = 0
  abel
end

section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)

theorem fc_zero {j : ℕ} (I : Fin j → Fin d) : fc E σ I 0 = 0 := by
  funext s
  change E.form σ I 0 s = 0
  unfold Frame.form
  rw [map_zero, mul_zero]

theorem sum_fc_delta (m : ℕ) (E : Frame Φ m) (σ : ∀ T : C, E.D ⟶ T) :
    ∑ I : Fin m → Fin m, fc E σ I (∏ k, if k = I k then (1 : Φ.A.obj E.D) else 0) = fc E σ id 1 := by
  rw [Finset.sum_eq_single id]
  · simp
  · intro I _ hI
    obtain ⟨k, hk⟩ : ∃ k, k ≠ I k := by
      by_contra hh
      push_neg at hh
      exact hI (funext fun k => (hh k).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk), fc_zero]
  · simp
end

section
variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {s : ℕ} {V : X.Opens}

theorem rep_xdt {n : ℕ} {t : Fin (n + 1) → Γ(X, V)} {E : Frame (sP (KS q s {V})) (n + 1)}
    {ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D} (hL : IsLoc q s t E ε) (σ : ∀ T, E.D ⟶ T) (w : Γ(X, V))
    (r : ℤ) (hr : r = ((n + 1 : ℕ) : ℤ)) (cl : HQ (KS q s {V}) r (r + 1) (n + 1))
    (h : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (E.form σ id (ε w)) cl) :
    CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (xdtC s V t w) cl := by
  subst hr
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  let ℓ : Fin (n + 1) → CH.Cn (CH.modF (sP (KS q s {V})).A) 1 := fun k => addC (KS q s {V}) (lf q s V (t k))
  let cc : Fin (n + 1) → Fin (n + 1) → (sP (KS q s {V})).A.obj E.D := fun k i => if k = i then 1 else 0
  let hh : Fin (n + 1) → ∀ T, (sP (KS q s {V})).A.obj T := fun k T =>
    lf q s V (t k) T - ((sP (KS q s {V})).A.map (σ T)).hom (ε (t k))
  have hJ : ∀ k T, hh k T ∈ (sP (KS q s {V})).J.S T := fun k T => lf_sub_mem hL _ T (σ T)
  have hh0 : ∀ k, h0 (hh k) ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 0 := fun k => mem_FC.2 fun u => by
    have := hJ k (u.obj (Fin.last 0))
    rw [← hF.one] at this
    rw [Nat.cast_one]
    exact this
  have he : ∀ k, ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hh k))) ∈
      FC (sFil (KS q s {V}) ((1 + 1 : ℕ) : ℤ)) 1 := fun k => mem_FC.2 fun u => by
    have e : vl (ℓ k - (∑ i, fc E σ ![i] (cc k i) + CH.d (CH.modF (sP (KS q s {V})).A) 0 (h0 (hh k)))) u =
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from ℓ k u) - (∑ i, E.form σ ![i] (cc k i) u +
          (hh k (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (hh k (u.obj 0)))) := by
      rw [← cech_d_h0_eval]
      change _ - (vl (∑ i, fc E σ ![i] (cc k i)) u + _) = _
      congr 2
      rw [vl, Finset.sum_apply]
      rfl
    rw [e]
    have e0 := addC_eq σ hL k u
    exact e0 ▸ Ideal.zero_mem _
  obtain ⟨g, hg, hn⟩ := near E σ hF hc (n + 1) ℓ cc (fun k => h0 (hh k)) hh0 he
  obtain ⟨H, hH, rfl⟩ := hg
  rw [show (∑ I : Fin (n + 1) → Fin (n + 1), fc E σ I (∏ k, cc k (I k))) = fc E σ id 1 from sum_fc_delta _ E σ] at hn
  have hcL : cupListC (sP (KS q s {V})).A ℓ ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) (n + 1) := by
    have h1 := FC_anti hF (r := ((n + 1 : ℕ) : ℤ)) (by push_cast; omega) hn
    have h2 : fc E σ id (1 : (sP (KS q s {V})).A.obj E.D) ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) (n + 1) := fc_mem E σ hF id 1
    have h3 := d_mem hH
    have := add_mem (add_mem h1 h3) h2
    rwa [sub_add_cancel, sub_add_cancel] at this
  let H' : CH.Cn (CH.modF (sP (KS q s {V})).A) n := fun u => (show (sP (KS q s {V})).A.obj (u.obj (Fin.last n)) from H u) * ((sP (KS q s {V})).A.map (σ _)).hom (ε w)
  have hH' : H' ∈ FC (sFil (KS q s {V}) ((n + 1 : ℕ) : ℤ)) n :=
    mem_FC.2 fun u => Ideal.mul_mem_right _ _ (mem_FC.1 hH u)
  have h1 := rep_add h (rep_d (b := sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)) H' (mem_FC.1 hH'))
  rw [add_zero] at h1
  refine rep_congr h1 fun u => ?_
  have e1 := mem_FC.1 hn u
  have e2 := d_mul E σ hF hc (ε w) hH u
  have e5 := form_mul E σ id (ε w) 1 u
  rw [mul_one] at e5
  let ψ := u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))))
  let T0 := u.obj (CH.front (Nat.zero_add (n + 1)) (Fin.last 0))
  have a1 : ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0 - ((sP (KS q s {V})).A.map (σ T0)).hom (ε w)) ∈
      (sP (KS q s {V})).J.S _ := (sP (KS q s {V})).J.map_mem ψ (lf_sub_mem hL w T0 (σ T0))
  have a2 := DlogApprox.const1 hF hc (σ T0 ≫ ψ) (σ (u.obj (Fin.last (n + 1)))) (ε w)
  have a3 : ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) - ((sP (KS q s {V})).A.map (σ (u.obj (Fin.last (n + 1))))).hom (ε w) ∈
      (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    have a4 := ((sP (KS q s {V})).J.S _).add_mem a1 a2
    have e3 : ((sP (KS q s {V})).A.map (σ T0 ≫ ψ)).hom (ε w) =
        ((sP (KS q s {V})).A.map ψ).hom (((sP (KS q s {V})).A.map (σ T0)).hom (ε w)) := by
      rw [Functor.map_comp]; rfl
    rw [e3, map_sub, sub_add_sub_cancel] at a4
    exact a4
  have ex : vl (xdtC (q := q) s V t w) u = ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) * vl (cupListC (sP (KS q s {V})).A ℓ) u :=
    congrArg (fun b : (sP (KS q s {V})).A.obj (u.obj (Fin.last (n + 1))) => ((sP (KS q s {V})).A.map ψ).hom (lf q s V w T0) * b)
      (CrystallineSemistableComparison.Auxff.term_id _ u _ _ _ (fun t => by simp [CH.back]))
  have e6 := hF.mul 1 (n + 1) _ a3 (mem_FC.1 hcL u)
  have e7 : ((1 + (n + 1) : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  have e8 : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e7] at e6
  rw [e8] at e1 e2
  have e9 := ((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).add_mem
    (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).add_mem
      (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem
        (Ideal.mul_mem_right (((sP (KS q s {V})).A.map (σ (u.obj (Fin.last (n + 1))))).hom (ε w)) _ e1))
      (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem e2))
    (((sFil (KS q s {V}) (((n + 1 : ℕ) : ℤ) + 1)).S _).neg_mem e6)
  change E.form σ id (ε w) u + vl (CH.d (CH.modF (sP (KS q s {V})).A) n H') u - vl (xdtC (q := q) s V t w) u ∈ _
  rw [ex, e5]
  convert e9 using 1
  change _ = -((vl (cupListC (sP (KS q s {V})).A ℓ) u - vl (fc E σ id 1) u - vl (CH.d (CH.modF (sP (KS q s {V})).A) n H) u) * _) +
    -(vl (CH.d (CH.modF (sP (KS q s {V})).A) n H) u * _ - vl (CH.d (CH.modF (sP (KS q s {V})).A) n H') u) + -(_ * _)
  ring
end

theorem main : CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → CrystallineSemistableComparison.Pb.KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] (s : ℕ), n + 1 < s → ∀ (V V' : X.Opens) (hVV : V ≤ V'), IsAffineOpen V' →
    ∀ (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (f : CH.Cn (CH.modF (sP (KS q s {V'})).A) n), (∀ σ, f σ ∈ (sFil (KS q s {V'}) n).S _) →
      (∀ σ, CH.d _ n f σ ∈ (sFil (KS q s {V'}) ((n : ℤ) + 1)).S _) →
      ∀ x : HQ (KS q s {V'}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1), Rep (sFil (KS q s {V'}) ((n : ℤ) + 1)) (sFil (KS q s {V'}) ((n : ℤ) + 1 + 1)) (CH.d _ n f) (x) →
      ∃ η : Fin (n + 1) → Γ(X, V), (∀ k, η k ∈ jacSpan hVV (RingHom.id _) (fun k => D k) (Fin.succAbove k)) ∧
        Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t (∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k))) (resKS q s hVV _ _ _ x) := by
  intro _ _ _ K _ _ X q n _ s hs V V' hVV hV' c D hD f hf hdf x hx
  haveI : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q
  obtain ⟨E, ε, hL⟩ := GlobalTheory.T.exists_local_frame_of_coords q c s (by omega)
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  have hc : E.GrConst (sFil (KS q s {V})) := hL.1
  have hT := GlobalTheory.T.taylor_of_local_frame q c s E ε hL D hD
  have hr : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨ξ, hξ⟩ := rep_exists (a := sFil (KS q s {V'}) (n : ℤ)) (b := sFil (KS q s {V'}) ((n : ℤ) + 1)) f hf hdf
  have h1 := rep_res (ks_le q s hVV) _ _ hξ
  have h2 := rep_res (ks_le q s hVV) _ _ hx
  obtain ⟨y, hy⟩ := (GlobalTheory.T.local_graded_class_representative q c.t s E ε hL σ n (n : ℤ) rfl (by omega)).1 (resKS q s hVV _ _ _ ξ)
  have hmem := GlobalTheory.T.local_frame_derivation_compat q s hVV hV' c D hD E ε hL σ n (n : ℤ) rfl (by omega) ξ y hy
  have h2' : CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1))
      (fun u => CH.d _ n (resQ (ks_le q s hVV) f) u) (resKS q s hVV _ _ _ x) := by
    refine rep_congr h2 fun u => ?_
    have e := congrFun (d_resQ (ks_le q s hVV) f) u
    exact (sub_eq_zero.2 e.symm) ▸ Ideal.zero_mem _
  have h3 := GlobalTheory.T.taylor_differential_representative hF E σ hc _ hT n (resQ (ks_le q s hVV) f) (fun I => ε (y I)) (resKS q s hVV _ _ _ ξ) (resKS q s hVV _ _ _ x) h1 hy h2'
  have h4 := GlobalTheory.T.form_sum_representative_lift hF E σ hc (n + 1) _ hr (fun a : Idx n (n + 1) × Fin (n + 1) => Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2)
    (fun a => (-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) _ h3
  have h5 := rep_one E σ _ (fun I => ∑ a : Idx n (n + 1) × Fin (n + 1), sgn I (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1)))))) _ h4
  let Ik : Fin (n + 1) → Idx n (n + 1) := fun k => ⟨k.succAbove, Fin.strictMono_succAbove k⟩
  let sg : Fin (n + 1) → ℤ := fun k => sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) (Ik k).1 k)
  refine ⟨fun k => ((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k), fun k => ?_, ?_⟩
  · exact AddSubgroup.zsmul_mem _ (hmem (Ik k)) _
  · have e : ∑ a : Idx n (n + 1) × Fin (n + 1), sgn (I0 (n + 1)) (Fin.snoc (α := fun _ => Fin (n + 1)) a.1.1 a.2) • ((-1) ^ n * ε (D a.2 (ε.symm (ε (y a.1))))) =
        ε (∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (((-1 : ℤ) ^ (k : ℕ) * (-1) ^ n * sg k) • y (Ik k))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fintype.sum_prod_type_right, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_eq_single (Ik k)]
      · have a1 : ((-1 : Γ(X, V)) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by rw [← mul_pow]; simp
        rw [map_zsmul, zsmul_eq_mul, zsmul_eq_mul, RingEquiv.symm_apply_apply]
        push_cast
        have a2 : (-1 : Γ(X, V)) ^ (k : ℕ) * (((-1) ^ (k : ℕ) * (-1) ^ n * (sg k : Γ(X, V))) * D k (y (Ik k))) =
            (sg k : Γ(X, V)) * ((-1) ^ n * D k (y (Ik k))) := by
          linear_combination ((-1) ^ n * (sg k : Γ(X, V)) * D k (y (Ik k))) * a1
        rw [a2, map_mul, map_mul, map_pow, map_neg, map_one, map_intCast]
      · intro I _ hI
        rw [sgn_snoc I k (fun h => hI (Subtype.ext h)), zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [e] at h5
    exact rep_xdt hL σ _ _ hr _ h5

end GlobalTheory.CompanionTheory.ConeLocal.LExact
