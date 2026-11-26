module

public import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally
public import Development.EtaleCohomology.KummerTheory.InjSlice

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsEtaleKummerChernClassCochainOfLineBundle (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) α 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (R := ZMod q) α 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (R := ZMod q) α 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def ExistsEtaleKummerChernClassCochain : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α

def EtaleKummerChernClassCochainIsCocycle : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, IsEtaleKummerChernClassCochainOfLineBundle q L α → δ 2 3 α = 0

def EvMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x

def ExistsNaturalEtaleKummerChernClassDegreeOneValue : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      a U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def ExistsNaturalEtaleKummerChernClassDegreeTwoValue : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      a U x = kumT q U v + kumT q U w - kumT q U (v * w)

noncomputable def vals {q : ℕ} {E : Spc} (a1 : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U)
    (a2 : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 2 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X s) U
  | 0, _, _, _, _ => 0
  | Nat.succ 0, s, h, U, x => (show (1 : ℤ) = s by omega) ▸ a1 U x
  | Nat.succ (Nat.succ 0), s, h, U, x => (show (0 : ℤ) = s by omega) ▸ a2 U x
  | Nat.succ (Nat.succ (Nat.succ _)), _, _, _, _ => 0

theorem vals_nat {q : ℕ} {E : Spc} (a1 : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U)
    (a2 : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a1 U x) = a1 V (x.res g))
    (h2 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a2 U x) = a2 V (x.res g)) :
    ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (vals a1 a2 p s h U x) = vals a1 a2 p s h V (x.res g) := by
  intro p
  match p with
  | 0 =>
    intro s h V U g x
    simp [vals]
  | Nat.succ 0 =>
    intro s h V U g x
    subst s
    exact h1 V U g x
  | Nat.succ (Nat.succ 0) =>
    intro s h V U g x
    subst s
    exact h2 V U g x
  | Nat.succ (Nat.succ (Nat.succ _)) =>
    intro s h V U g x
    simp [vals]

theorem exists_etale_kummer_chern_class_cochain_of_degree_values (hmk : EvMk) (h1 : ExistsNaturalEtaleKummerChernClassDegreeOneValue) (h2 : ExistsNaturalEtaleKummerChernClassDegreeTwoValue) : ExistsEtaleKummerChernClassCochain := by
  intro q _ E L hi
  obtain ⟨a1, n1, e1⟩ := h1 q L hi
  obtain ⟨a2, n2, e2⟩ := h2 q L hi
  obtain ⟨α, hα⟩ := hmk (ZMod q) (vals a1 a2) (vals_nat a1 a2 n1 n2)
  refine ⟨α, ?_, ?_, ?_⟩
  · intro U x; rw [hα]; rfl
  · intro U x v hv; rw [hα]; exact e1 U x v hv
  · intro U x v w hv hw; rw [hα]; exact e2 U x v w hv hw

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.exists_closed_etale_kummer_chern_class_cochain_of_values (hmk : EvMk) (h1 : ExistsNaturalEtaleKummerChernClassDegreeOneValue) (h2 : ExistsNaturalEtaleKummerChernClassDegreeTwoValue) (hd : EtaleKummerChernClassCochainIsCocycle) :
    LateralTheory.EtaleFoundations.first_chern_class_exists := by
  intro q _ E L hi
  obtain ⟨α, hα⟩ := exists_etale_kummer_chern_class_cochain_of_degree_values hmk h1 h2 q L hi
  exact ⟨Cocycle.mk α 3 (by norm_num) (hd q L hi α hα), hα⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibnizOfPairing
section -- merged from Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupLeibniz
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)), μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ → δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW

namespace LateralTheory.EtaleFoundations.AWLeib
variable {R : Type} [CommRing R]

theorem bd_map {E : Spc} {U : Scheme.{0}} {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    (f : ∀ p : ℕ, Sx E p U → G) (p : ℕ) (y : Sx E p U) : φ (bd f p y) = bd (fun q z => φ (f q z)) p y := by
  cases p with
  | zero => simp [bd]
  | succ p => simp [bd, map_sum, map_zsmul]

theorem ev_delta_bd {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ)
    (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (U : Scheme.{0}) (x : Sx E p U) :
    ev (R := R) (δ n m α) p t ht U x = Sec.map (I.d s t) (ev (R := R) α p s hs U x) +
      m.negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = t then ev (R := R) α q t hh U z else 0) p x := by
  have ev_eq {k : ℤ} (a : Cochain ((chains R).obj E) I k) (q : ℕ) (j : ℤ)
      (h : -(q : ℤ) + k = j) (y : Sx E q U) :
      ev (R := R) a q j h U y = Sec.map ((chainsXIso R E q).inv ≫ a.v _ _ h) (freeGen R _ U y) := rfl
  cases p with
  | zero =>
    rw [ev_eq, δ_v n m hm α _ _ ht s 1 (by omega) (by simp),
      (isZero_pos E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0]
    simp only [zero_comp, smul_zero, add_zero, bd]
    rfl
  | succ p =>
    have hp : -(p : ℤ) + n = t := by omega
    rw [ev_eq, δ_v n m hm α _ _ ht s (-(p : ℤ)) (by omega) (by omega),
      Preadditive.comp_add, Linear.comp_units_smul, reassoc_of% (chains_d (R := R) E p),
      Preadditive.sum_comp]
    refine (sec_map_add _ _ _).trans ?_
    congr 1
    rw [Units.smul_def, Units.smul_def, sec_map_zsmul, sec_map_sum]
    congr 1
    simp only [bd, dite_eq_left hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp, sec_map_zsmul, ev_eq]
    congr 1
    exact congrArg (Sec.map ((chainsXIso R E p).inv ≫ α.v (-(p : ℤ)) t hp)) (map_freeGen (E.δ i) U x)

theorem mul_congr {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w) (h' : s' + t' = w) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    μ.mul U s t w h (ev (R := R) α p s hs U y) (ev (R := R) β q t ht U z) =
      μ.mul U s' t' w h' (ev (R := R) α p s' hs' U y) (ev (R := R) β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

theorem leib' {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (s t w s' t' w' : ℤ) (h : s + t = w) (hs : s + 1 = s')
    (ht : t + 1 = t') (hw : w + 1 = w') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = μ.mul U s' t w' (by omega) (Sec.map (I.d s s') a) b +
      s.negOnePow • μ.mul U s t' w' (by omega) a (Sec.map (J.d t t') b) := by
  subst hs ht hw; exact μ.leibniz U s t w h a b

theorem mul_bd_left {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    μ.mul U s t w h (bd f p y) b = bd (fun q z => μ.mul U s t w h (f q z) b) p y :=
  bd_map (((μ.mul U s t w h).flip b).toAddMonoidHom) f p y

theorem mul_bd_right {I J K : Cx R} (μ : Pair I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    μ.mul U s t w h a (bd f p y) = bd (fun q z => μ.mul U s t w h a (f q z)) p y :=
  bd_map ((μ.mul U s t w h a).toAddMonoidHom) f p y

theorem secmap_sum {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {ι : Type*} (s : Finset ι) (f : ι → Sec F U) :
    Sec.map φ (∑ i ∈ s, f i) = ∑ i ∈ s, Sec.map φ (f i) := map_sum ((φ.hom.app (op U)).hom) f s

theorem secmap_zsmul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℤ) (a : Sec F U) :
    Sec.map φ (c • a) = c • Sec.map φ a := map_zsmul ((φ.hom.app (op U)).hom) c a

def Fm {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w hh (ev (R := R) α p _ rfl U y) (ev (R := R) β q _ rfl U z) else 0

theorem recombine {G : Type*} [AddCommGroup G] (X Y BF BF' BB BB' : G) (c s K c' P e1 e2 c2 e3 : ℤ) (hF : BF' = BF)
    (hB : BB' = BB) (h2 : c * s = e2 * c2) (h3 : K * c' = c * e1) (h4 : K * (c * P) = e2 * (c2 * e3)) :
    c • (X + s • Y) + K • (c' • BF + c • P • BB) = c • (X + e1 • BF') + e2 • c2 • (Y + e3 • BB') := by
  subst hF hB
  simp only [smul_add, smul_smul]
  rw [h2, h3, h4]
  abel

theorem sign_nat (p : ℕ) : ((-1 : ℤ) ^ p) = (((p : ℤ).negOnePow : ℤˣ) : ℤ) := by
  simp [Int.negOnePow_def]

end LateralTheory.EtaleFoundations.AWLeib


open LateralTheory.EtaleFoundations.AWLeib in
theorem LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibniz := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ hγ h1 h2
  have ev_ext (a b : Cochain ((chains R).obj E) K (k + 1))
      (h : ∀ p s hs U x, ev (R := R) a p s hs U x = ev (R := R) b p s hs U x) : a = b := by
    ext i j hij : 1
    by_cases hi : 0 < i
    · exact (isZero_pos E i hi).eq_of_src _ _
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ (fun U x => h p j hij U x)
  apply ev_ext
  intro N w hw U x
  have ev_add : ev (R := R) (γ₁ + n.negOnePow • γ₂) N w hw U x =
      ev (R := R) γ₁ N w hw U x + ev (R := R) (n.negOnePow • γ₂) N w hw U x := by
    unfold ev
    rw [Cochain.add_v, Preadditive.comp_add]
    rfl
  have ev_units_smul : ev (R := R) (n.negOnePow • γ₂) N w hw U x = n.negOnePow • ev (R := R) γ₂ N w hw U x := by
    change Sec.map ((chainsXIso R E N).inv ≫ (n.negOnePow • γ₂).v _ _ hw) (freeGen R _ U x) = _
    rw [Cochain.units_smul_v, Linear.comp_units_smul, Units.smul_def, sec_map_zsmul]
    rfl
  rw [ev_add, ev_units_smul, ev_delta_bd rfl γ N (-(N : ℤ) + k) w rfl hw U x, hγ N _ rfl U x, h1 N w hw U x,
    h2 N w hw U x]
  rw [bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) •
      Fm μ α β U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]
  swap
  · intro N' y hN
    rw [dite_eq_left (by omega), hγ N' w _ U y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Units.smul_def]
    unfold Fm
    rw [dite_eq_left (by omega)]
  rw [bd_aw (Fm μ α β U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ))
    (fun p => by congr 2; push_cast; ring) N x]
  rw [secmap_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Units.smul_def, secmap_zsmul, leib' μ U _ _ _ (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) w _ (by ring) (by ring) (by omega)]
  rw [ev_delta_bd rfl α p (-((p : ℕ) : ℤ) + n) _ rfl _ U, ev_delta_bd rfl β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl _ U]
  simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, Units.smul_def, mul_bd_left, mul_bd_right]
  refine recombine _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
  · refine bd_congr (fun q z hq => ?_) _
    rw [dite_eq_left (by omega)]
    unfold Fm
    rw [dite_eq_left (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine bd_congr (fun q z hq => ?_) _
    rw [dite_eq_left (by omega)]
    unfold Fm
    rw [dite_eq_left (by omega)]
    exact mul_congr μ U α β _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-((p : ℕ) : ℤ), by ring⟩
  · subst hk
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
  · subst hk
    rw [sign_nat]
    simp only [← Units.val_mul, ← Int.negOnePow_add]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨0, by ring⟩
end
end

section -- merged from Development.EtaleCohomology.TateTwists.CyclotomicPrimitiveRootProductIdentitiesOfAdjoin
open Polynomial Finset GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.PrimPf

noncomputable def μ (q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)

lemma hμ (q : ℕ) [NeZero q] : IsPrimitiveRoot (μ q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma aeval_cyc {n : ℕ} (hn : 0 < n) {ν : ℂ} (h : IsPrimitiveRoot ν n) :
    aeval ν (cyclotomic n ℤ) = 0 := by
  rw [cyclotomic_eq_minpoly h hn]; exact minpoly.aeval _ _

lemma hom_aeval {S T : Type} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (f : S →+* T) (x : S) (p : ℤ[X]) :
    f (aeval x p) = aeval (f x) p := by
  rw [aeval_def, aeval_def, hom_eval₂]; congr 1; exact RingHom.ext_int _ _

abbrev R (q : ℕ) := AdjoinRoot (cyclotomic q ℤ)

noncomputable abbrev θ (q : ℕ) : R q := AdjoinRoot.root (cyclotomic q ℤ)

noncomputable def φ (q : ℕ) [NeZero q] : R q →+* ℂ :=
  AdjoinRoot.lift (algebraMap ℤ ℂ) (μ q) (by rw [← aeval_def]; exact aeval_cyc (NeZero.pos q) (hμ q))

lemma φ_root (q : ℕ) [NeZero q] : φ q (θ q) = μ q := AdjoinRoot.lift_root _

lemma φ_inj (q : ℕ) [NeZero q] : Function.Injective (φ q) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [AdjoinRoot.mk_eq_zero]
  have h : aeval (μ q) p = 0 := by
    rw [φ, AdjoinRoot.lift_mk] at hx; rwa [aeval_def]
  rw [cyclotomic_eq_minpoly (hμ q) (NeZero.pos q)]
  exact minpoly.isIntegrallyClosed_dvd ((hμ q).isIntegral (NeZero.pos q)) h

noncomputable def ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : R q →+* A :=
  AdjoinRoot.lift (algebraMap ℤ A) ζ.1 (by rw [← aeval_def]; exact ζ.2.2)

lemma ψ_root {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ψ ζ (θ q) = ζ.1 :=
  AdjoinRoot.lift_root _

lemma θ_pow (q : ℕ) [NeZero q] : θ q ^ q = 1 :=
  φ_inj q (by rw [map_pow, φ_root, map_one, (hμ q).pow_eq_one])

lemma root_of_prim {q r a : ℕ} [NeZero q] (hr : 0 < r) (h : IsPrimitiveRoot (μ q ^ a) r) :
    aeval (θ q ^ a) (cyclotomic r ℤ) = 0 :=
  φ_inj q (by rw [hom_aeval (φ q), map_pow, φ_root, map_zero]; exact aeval_cyc hr h)

lemma image_range (q : ℕ) [NeZero q] :
    (range q).image (fun a => μ q ^ a) = nthRootsFinset q (1 : ℂ) := by
  ext x
  rw [mem_image, mem_nthRootsFinset (NeZero.pos q)]
  constructor
  · rintro ⟨a, -, rfl⟩; rw [← pow_mul, mul_comm, pow_mul, (hμ q).pow_eq_one, one_pow]
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx
    exact ⟨i, mem_range.2 hi, rfl⟩

lemma image_prim (q : ℕ) [NeZero q] :
    ((range q).filter (fun a => Nat.Coprime a q)).image (fun a => μ q ^ a) = primitiveRoots q ℂ := by
  ext x
  rw [mem_image, mem_primitiveRoots (NeZero.pos q)]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact (hμ q).pow_of_coprime a (mem_filter.1 ha).2
  · intro hx
    obtain ⟨i, hi, rfl⟩ := (hμ q).eq_pow_of_pow_eq_one hx.pow_eq_one
    exact ⟨i, mem_filter.2 ⟨mem_range.2 hi, ((hμ q).pow_iff_coprime (NeZero.pos q) i).1 hx⟩, rfl⟩

lemma inj_on (q : ℕ) [NeZero q] (s : Finset ℕ) (hs : s ⊆ range q) :
    Set.InjOn (fun a => μ q ^ a) s := by
  intro i hi j hj h
  exact (hμ q).pow_inj (mem_range.1 (hs hi)) (mem_range.1 (hs hj)) h

lemma C_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (μ q ^ a)) = (X ^ q - 1 : ℂ[X]) := by
  rw [X_pow_sub_one_eq_prod (NeZero.pos q) (hμ q), ← image_range,
    prod_image (inj_on q _ subset_rfl)]

lemma C_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (μ q ^ a)) = cyclotomic q ℂ := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (hμ q), ← image_prim,
    prod_image (inj_on q _ (filter_subset _ _))]

lemma mapφ_C_prod (q : ℕ) [NeZero q] (s : Finset ℕ) :
    (∏ a ∈ s, (X - C (θ q ^ a))).map (φ q) = ∏ a ∈ s, (X - C (μ q ^ a)) := by
  simp [Polynomial.map_prod, φ_root]

lemma R_prod_all (q : ℕ) [NeZero q] :
    ∏ a ∈ range q, (X - C (θ q ^ a)) = (X ^ q - 1 : (R q)[X]) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_all]; simp

lemma R_prod_prim (q : ℕ) [NeZero q] :
    ∏ a ∈ (range q).filter (fun a => Nat.Coprime a q), (X - C (θ q ^ a))
      = (cyclotomic q ℤ).map (algebraMap ℤ (R q)) := by
  apply Polynomial.map_injective _ (φ_inj q)
  rw [mapφ_C_prod, C_prod_prim, Polynomial.map_map, ← map_cyclotomic_int]
  congr 1; exact RingHom.ext_int _ _

lemma C_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (μ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : ℂ[X]) := by
  have h := C_prod_all (n + 1)
  rw [prod_range_succ', pow_zero, ← geom_sum_mul, C_1] at h
  have hne : (X - 1 : ℂ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℂ)
  exact mul_right_cancel₀ hne h

lemma R_prod_geom (n : ℕ) [NeZero (n + 1)] :
    ∏ i ∈ range n, (X - C (θ (n + 1) ^ (i + 1))) = ∑ i ∈ range (n + 1), (X ^ i : (R (n + 1))[X]) := by
  apply Polynomial.map_injective _ (φ_inj (n + 1))
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_prod, Polynomial.map_sum, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, map_pow, φ_root, Polynomial.map_pow]
  simpa using C_prod_geom n

lemma eval_prod_ψ {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) (f : ℕ → ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ f a))) = ∏ a ∈ s, (y - ζ.1 ^ f a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma eval_prod_ψ0 {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) (y : A) (s : Finset ℕ) :
    eval₂ (ψ ζ) y (∏ a ∈ s, (X - C (θ q ^ a))) = ∏ a ∈ s, (y - ζ.1 ^ a) := by
  simp [eval₂_finsetProd, eval₂_pow, ψ_root]

lemma unit_prod {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ∏ i ∈ range (q - 1), (1 - ζ.1 ^ (i + 1)) = (q : A) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos q)).symm⟩
  have h := congrArg (eval₂ (ψ ζ) 1) (R_prod_geom n)
  rw [eval_prod_ψ ζ 1 _ (fun i => i + 1)] at h
  simpa [eval₂_finsetSum] using h

theorem cyclotomic_primitive_root_product_identities_of_adjoin_root : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities := by
  intro q _ A _
  have hq1 : ∀ ζ : Prim q A, ζ.1 ^ q = 1 := fun ζ => by
    rw [← ψ_root, ← map_pow, θ_pow, map_one]
  have hu : ∀ ζ : Prim q A, IsUnit ζ.1 := fun ζ =>
    IsUnit.of_mul_eq_one (ζ.1 ^ (q - 1)) (by
      rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos q), hq1])
  have hmod : ∀ (ζ : Prim q A) (a : ℕ), ζ.1 ^ a = ζ.1 ^ (a % q) := fun ζ a => by
    conv_lhs => rw [← Nat.mod_add_div a q, pow_add, pow_mul, hq1, one_pow, mul_one]
  have hlt : ∀ (ζ : Prim q A) (c d : ℕ), c < d → d < q → IsUnit (ζ.1 ^ c - ζ.1 ^ d) := by
    intro ζ c d hcd hd
    obtain ⟨i, rfl⟩ : ∃ i, d = c + (i + 1) := ⟨d - c - 1, by omega⟩
    have e : ζ.1 ^ c - ζ.1 ^ (c + (i + 1)) = ζ.1 ^ c * (1 - ζ.1 ^ (i + 1)) := by ring
    rw [e]
    refine ((hu ζ).pow c).mul (isUnit_of_dvd_unit ?_ ζ.2.1)
    have hd := dvd_prod_of_mem (fun j => 1 - ζ.1 ^ (j + 1)) (mem_range.2 (show i < q - 1 by omega))
    rw [unit_prod ζ] at hd
    exact hd
  refine ⟨hq1, ?_, ?_, ?_, ?_, ?_⟩
  · intro ζ a ha
    refine ⟨⟨ζ.1 ^ a, ζ.2.1, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim (NeZero.pos q) ((hμ q).pow_of_coprime a ha), map_zero]
  · intro ζ a b hab
    rw [hmod ζ a, hmod ζ b]
    have hne : a % q ≠ b % q := hab
    have ha := Nat.mod_lt a (NeZero.pos q)
    have hb := Nat.mod_lt b (NeZero.pos q)
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt ζ _ _ h hb
    · have := (hlt ζ _ _ h ha).neg
      rwa [neg_sub] at this
  · intro ζ x hx
    have h := congrArg (eval₂ (ψ ζ) x) (R_prod_all q)
    rw [eval_prod_ψ0] at h
    simpa [hx] using h
  · intro ζ ξ
    have h := congrArg (eval₂ (ψ ζ) ξ.1) (R_prod_prim q)
    rw [eval_prod_ψ0, eval₂_map] at h
    rw [h]
    have e : (ψ ζ).comp (algebraMap ℤ (R q)) = algebraMap ℤ A := RingHom.ext_int _ _
    rw [e, ← aeval_def]; exact ξ.2.2
  · intro r hr ζ
    have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr (NeZero.pos q)
    have hur : IsUnit (r : A) := by
      obtain ⟨k, hk⟩ := hr
      have := ζ.2.1
      rw [hk, Nat.cast_mul] at this
      exact isUnit_of_mul_isUnit_left this
    refine ⟨⟨ζ.1 ^ (q / r), hur, ?_⟩, rfl⟩
    rw [← ψ_root, ← map_pow, ← hom_aeval (ψ ζ),
      root_of_prim hr0 ((hμ q).pow (NeZero.pos q) (Nat.div_mul_cancel hr).symm), map_zero]

end LateralTheory.EtaleFoundations.PrimPf
end

section -- merged from Development.EtaleCohomology.TateTwists.TwLocPfR
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwLocPf

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := congrArg (fun f => f.hom x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  exact h.symm

theorem twGen_res (q : ℕ) (i : ℤ) (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  refine (ofRings_sec_res (twF q i) g _).trans ?_
  unfold twGen
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]

def TwSecLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
  Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)

def TwTors : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ),
  c • twGen i ζ = 0 → q ∣ c

theorem TwLoc_of (h1 : TwSecLoc) (h2 : TwTors) : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc := by
  intro q _ i
  exact ⟨fun U ζ y => h1 q i U ζ y, fun U _ ζ c hc => h2 q i U ζ c hc, fun V U g ζ => twGen_res q i V U g ζ⟩

end LateralTheory.EtaleFoundations.TwLocPf
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainCupAssocOfCupSpecAndAlexanderWhitney
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def t_cup_spec0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧
    ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def t_aw_assoc0 : Prop :=
  ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M')
    (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w)
      (h3 : t + u = tu) (h4 : s + tu = w) a b c,
      ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
    ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w)
      (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
      (ab : Cochain ((chains R).obj E) M nm) (bc : Cochain ((chains R).obj E) M' mk)
      (x y : Cochain ((chains R).obj E) L w),
      μ.IsAW h1 α β ab → ν.IsAW h2 ab γ x → μ'.IsAW h3 β γ bc → ν'.IsAW h4 α bc y → x = y

theorem etale_cochain_cup_assoc_of_cup_spec_and_alexander_whitney_assoc (hs : t_cup_spec0) (ha : t_aw_assoc0) : EtaleCochainCupAssociativeOfPairing := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 a b c
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨ab, hab⟩ := (hs R μ (E := E) h1).1 α β
  rw [(hs R μ (E := E) h1).2 α β ab hab]
  obtain ⟨x, hx⟩ := (hs R ν (E := E) h2).1 ab γ
  rw [(hs R ν (E := E) h2).2 ab γ x hx]
  obtain ⟨bc, hbc⟩ := (hs R μ' (E := E) h3).1 β γ
  rw [(hs R μ' (E := E) h3).2 β γ bc hbc]
  obtain ⟨y, hy⟩ := (hs R ν' (E := E) h4).1 α bc
  rw [(hs R ν' (E := E) h4).2 α bc y hy]
  congr 1
  exact Subtype.ext (ha R μ ν μ' ν' hass E h1 h2 h3 h4 α.1 β.1 γ.1 ab.1 bc.1 x.1 y.1 hab hx hbc hy)

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationGeneratorMapOfSectio
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TwMulGenMap

def twSec : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ

theorem nsmul_congr {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n m : ℕ)
    (h : (n : ZMod q) = m) (x : M) : n • x = m • x := by
  have hn : (n : ULift.{1} (ZMod q)) = ULift.up (n : ZMod q) := by ext; simp
  have hm : (m : ULift.{1} (ZMod q)) = ULift.up (m : ZMod q) := by ext; simp
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), hn, hm, h]

theorem val_mul {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) (i j k : ℤ) (hk : i + j = k) :
    ((((a ^ i : (ZMod q)ˣ) : ZMod q).val * ((a ^ j : (ZMod q)ˣ) : ZMod q).val : ℕ) : ZMod q) =
      ((((a ^ k : (ZMod q)ˣ) : ZMod q).val : ℕ) : ZMod q) := by
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul,
    ← zpow_add, hk]

theorem sec_map_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ)
    (x : Sec F U) : Sec.map φ (n • x) = n • Sec.map φ x := map_nsmul _ _ _

open LateralTheory.EtaleFoundations.TwMulPf in
theorem genMap_of (h : twSec) : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists := by
  intro q _ i j k T μ _ hk
  let π : (sgl T).X 0 ⟶ T := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).hom
  have hπ : π ≫ sglι T = 𝟙 _ := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 T).hom_inv_id
  let e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec T U := fun U ζ =>
    Sec.map π (μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)))
  have hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    simp only [e]
    rw [sec_res_map, μ.nat, sec_res_map, sec_res_map, (h q i).2.2.2.1, (h q j).2.2.2.1]
  have hrel : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ k : (ZMod q)ˣ) : ZMod q).val • e U ζ := by
    intro U ζ ξ a hξ
    simp only [e]
    rw [(h q i).2.2.2.2.1 U ζ ξ a hξ, (h q j).2.2.2.2.1 U ζ ξ a hξ]
    rw [sec_map_nsmul, sec_map_nsmul, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul,
      sec_map_nsmul, mul_comm, nsmul_congr _ _ (val_mul a i j k hk)]
  obtain ⟨φ, hφ, -⟩ := (h q k).2.2.2.2.2 T e hnat hrel
  refine ⟨φ, fun U ζ => ?_⟩
  rw [hφ U ζ]
  simp only [e]
  rw [sec_map_comp, hπ, sec_map_id]

end LateralTheory.EtaleFoundations.TwMulGenMap

theorem LateralTheory.EtaleFoundations.etale_tate_twist_multiplication_generator_map_of_section_description (h : LateralTheory.EtaleFoundations.TwMulGenMap.twSec) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists :=
  LateralTheory.EtaleFoundations.TwMulGenMap.genMap_of h
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafInjectiveResolutionPropertiesOfMathlib
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ResBasicPf

variable {R : Type} [CommRing R]

noncomputable def descH {F G : Shv R} (φ : F ⟶ G) :
    InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) φ :=
  ⟨InjectiveResolution.desc φ (injectiveResolution G) (injectiveResolution F),
    HomologicalComplex.congr_hom (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F)) 0⟩

lemma resMap_eq {F G : Shv R} (φ : F ⟶ G) : resMap R φ = (descH φ).hom' := rfl

lemma resι_eq (F : Shv R) : resι R F =
    (injectiveResolution F).ι.f 0 ≫ ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := by
  simp [resι, InjectiveResolution.ι'_f_zero]
  rfl

lemma kinj (F : Shv R) : (res R F).IsKInjective :=
  isKInjective_of_injective (injectiveResolution F).cochainComplex 0

lemma inj (F : Shv R) (n : ℤ) : Injective ((res R F).X n) :=
  inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))

lemma ge (F : Shv R) : (res R F).IsStrictlyGE 0 :=
  inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)

lemma qis (F : Shv R) : QuasiIso (resAug F) :=
  inferInstanceAs (QuasiIso (injectiveResolution F).ι')

lemma mono (F : Shv R) : Mono (resι R F) := by
  have h0 : Mono ((injectiveResolution F).ι.f 0) := inferInstance
  have h2 : Mono ((injectiveResolution F).cochainComplexXIso 0 0 rfl).inv := inferInstance
  rw [resι_eq]; exact @mono_comp _ _ _ _ _ _ h0 _ h2

lemma dzero (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  rw [resι_eq]
  change _ ≫ (injectiveResolution F).cochainComplex.d 0 1 = 0
  rw [InjectiveResolution.cochainComplex_d _ 0 1 0 1 rfl rfl]
  erw [Category.assoc, Iso.inv_hom_id_assoc, InjectiveResolution.ι_f_zero_comp_complex_d_assoc, zero_comp]
  rfl

lemma aug_nat {F G : Shv R} (φ : F ⟶ G) :
    resAug F ≫ resMap R φ = (CochainComplex.singleFunctor (Shv R) 0).map φ ≫ resAug G := by
  rw [resMap_eq]; exact InjectiveResolution.Hom.ι'_comp_hom' _

lemma ι_nat {F G : Shv R} (φ : F ⟶ G) : resι R F ≫ (resMap R φ).f 0 = φ ≫ resι R G := by
  have h := congrArg (fun f => sglι F ≫ HomologicalComplex.Hom.f f 0) (aug_nat φ)
  simp only [HomologicalComplex.comp_f] at h
  change resι R F ≫ _ = _ at h
  rw [h]
  simp [sglι, resι, resAug, CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self]

end LateralTheory.EtaleFoundations.ResBasicPf

open LateralTheory.EtaleFoundations.ResBasicPf in
theorem LateralTheory.EtaleFoundations.etaleSheaf_injectiveResolution_properties_of_mathlib : LateralTheory.EtaleFoundations.EtaleInjectiveResolutionBasicProperties := by
  intro R _ F
  exact ⟨kinj F, inj F, ge F, qis F, rfl, mono F, dzero F, fun G φ => ⟨aug_nat φ, ι_nat φ⟩⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafShortComplexExactIffLocalLiftsHolds
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExactIffPf

variable {R : Type} [CommRing R]

theorem inj_of_mono {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (Sec.map φ (U := U)) := by
  have : Mono φ.hom := inferInstance
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem ker_sec {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) (b : Sec F U) (hb : Sec.map φ b = 0) :
    ∃ k : Sec (kernel φ) U, Sec.map (kernel.ι φ) k = b := by
  let E := sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙
    (evaluation _ _).obj (op U)
  have hl : IsLimit (Fork.ofι (E.map (kernel.ι φ))
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]) :
      Fork (E.map φ) 0) := isLimitOfHasKernelOfPreservesLimit E φ
  let M := LinearMap.ker (φ.hom.app (op U)).hom
  let s : ModuleCat.of (ULift.{1} R) M ⟶ E.obj F := ModuleCat.ofHom M.subtype
  have hs : s ≫ E.map φ = s ≫ 0 := by
    ext x
    simp [s, E]
  obtain ⟨l, hl'⟩ := Fork.IsLimit.lift' hl s hs
  refine ⟨l.hom ⟨b, hb⟩, ?_⟩
  have := congrArg (fun m => m.hom (⟨b, hb⟩ : M)) hl'
  simpa [s, E] using this

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 →
    Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  rw [S.exact_iff_epi_kernel_lift, ← Sheaf.isLocallySurjective_iff_epi' (φ := kernel.lift S.g S.f S.zero)]
  set φ := kernel.lift S.g S.f S.zero with hφ
  have hfac : ∀ V (a : Sec S.X₁ V), Sec.map (kernel.ι S.g) (Sec.map φ a) = Sec.map S.f a := by
    intro V a
    show ((φ ≫ kernel.ι S.g).hom.app (op V)).hom a = _
    rw [hφ, kernel.lift_ι]
  have hnat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (k : Sec (kernel S.g) U),
      Sec.map (kernel.ι S.g) (Sec.res g k) = Sec.res g (Sec.map (kernel.ι S.g) k) := by
    intro V U g k
    have := congrArg (fun m => m.hom k) ((kernel.ι S.g).hom.naturality g.op)
    simp [Sec.map, Sec.res] at this ⊢
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := ker_sec S.g U b hb
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} φ.hom k, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← hfac]
    rw [show Sec.map φ t = Sec.res g k from ht, hnat]
  · intro h
    constructor
    intro U k
    obtain ⟨T, hT, hTk⟩ := h U (Sec.map (kernel.ι S.g) k) (by
      show ((kernel.ι S.g ≫ S.g).hom.app (op U)).hom k = 0
      rw [kernel.condition]; rfl)
    refine Scheme.etaleTopology.superset_covering ?_ hT
    intro V g hg
    obtain ⟨a, ha⟩ := hTk V g hg
    refine ⟨a, ?_⟩
    apply inj_of_mono (kernel.ι S.g) V
    change Sec.map (kernel.ι S.g) (Sec.map φ a) = Sec.map (kernel.ι S.g) (Sec.res g k)
    rw [hfac, hnat, ha]

end LateralTheory.EtaleFoundations.ExactIffPf

theorem LateralTheory.EtaleFoundations.etale_sheaf_short_complex_exact_iff_local_lifts_holds : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts := by
  intro R _ S
  exact LateralTheory.EtaleFoundations.ExactIffPf.exact_iff S
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTateTwistMultiplicationTensorExistsOfComple
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TensExPf
open LateralTheory.EtaleFoundations.TwMulPf
open scoped TensorProduct DirectSum

variable {R : Type} [CommRing R]

theorem sec_map_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  rfl

theorem sec_zero_of_isZero {Z : Shv R} (hZ : IsZero Z) {U : Scheme.{0}} (y : Sec Z U) : y = 0 := by
  have h : Sec.map (𝟙 Z) y = Sec.map 0 y := by rw [hZ.eq_of_src (𝟙 Z) 0]
  rw [sec_map_id, sec_map_zero] at h
  exact h

theorem isZero_sglX (F : Shv R) {w : ℤ} (hw : w ≠ 0) : IsZero ((sgl F).X w) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hw

theorem sgl_d (F : Shv R) (a : ℤ) : (sgl F).d a (a + 1) = 0 := by
  by_cases ha : a = 0
  · exact (isZero_sglX F (by omega)).eq_of_tgt _ _
  · exact (isZero_sglX F ha).eq_of_src _ _

def eIso (K : Cx R) (w : ℤ) (h : w = 0) : K.X w ≅ (sgl (K.X 0)).X w :=
  K.XIsoOfEq h ≪≫ (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 (K.X 0) w h).symm

def e (K : Cx R) (w : ℤ) : K.X w ⟶ (sgl (K.X 0)).X w :=
  if h : w = 0 then (eIso K w h).hom else 0

theorem e_pos (K : Cx R) {w : ℤ} (h : w = 0) : e K w = (eIso K w h).hom := dif_pos h

def μ {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) : Pair (sgl A) (sgl B) (sgl (K.X 0)) where
  mul U s t w h := (τ.mul U s t w h).compr₂ (secL (e K w) U)
  nat g s t w h a b := by
    change Sec.res g (Sec.map (e K w) _) = Sec.map (e K w) _
    rw [sec_res_map, τ.nat]
  leibniz U s t w h a b := by
    change Sec.map ((sgl (K.X 0)).d w (w + 1)) _ =
      Sec.map (e K (w + 1)) (τ.mul U (s + 1) t (w + 1) _ (Sec.map ((sgl A).d s (s + 1)) a) b) +
        s.negOnePow • Sec.map (e K (w + 1)) (τ.mul U s (t + 1) (w + 1) _ a (Sec.map ((sgl B).d t (t + 1)) b))
    simp only [sgl_d, sec_map_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

theorem μ_lift {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) (U : Scheme.{0}) (w : ℤ)
    (x : Tens (sgl A) (sgl B) U w) : (μ τ).lift U w x = Sec.map (e K w) (τ.lift U w x) := by
  classical
  change _ = secL (e K w) U (τ.lift U w x)
  rw [← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp [Pair.lift, μ]

theorem tens_summand_zero {A B : Shv R} {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) {U : Scheme.{0}}
    (z : Sec ((sgl A).X a) U ⊗[ULift.{1} R] Sec ((sgl B).X b) U) : z = 0 := by
  refine TensorProduct.induction_on (motive := fun z => z = 0) z rfl (fun u v => ?_) (fun x y hx hy => by rw [hx, hy, add_zero])
  rcases hab with h | h
  · rw [sec_zero_of_isZero (isZero_sglX A h) u, TensorProduct.zero_tmul]
  · rw [sec_zero_of_isZero (isZero_sglX B h) v, TensorProduct.tmul_zero]

theorem tens_zero {A B : Shv R} {U : Scheme.{0}} {w : ℤ} (hw : w ≠ 0) (x : Tens (sgl A) (sgl B) U w) : x = 0 := by
  refine DirectSum.ext fun p => ?_
  rw [DirectSum.zero_apply]
  refine tens_summand_zero ?_ _
  have := p.2
  by_contra hc
  push Not at hc
  omega

theorem μ_isTensor {A B : Shv R} {K : Cx R} (τ : Pair (sgl A) (sgl B) K) (hτ : τ.IsTensor) :
    (μ τ).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · by_cases hw : w = 0
    · refine loc_mono (hτ.1 U w (Sec.map (eIso K w hw).inv y)) fun V g ⟨x, hx⟩ => ⟨x, ?_⟩
      rw [μ_lift, hx, ← sec_res_map, e_pos K hw, sec_map_comp, Iso.inv_hom_id, sec_map_id]
    · refine ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨0, ?_⟩⟩
      rw [map_zero]
      exact (sec_zero_of_isZero (isZero_sglX _ hw) _).symm
  · by_cases hw : w = 0
    · refine hτ.2 U w x ?_
      rw [μ_lift, e_pos K hw] at hx
      have := congrArg (Sec.map (eIso K w hw).inv) hx
      rw [sec_map_comp, Iso.hom_inv_id, sec_map_id] at this
      rw [this]
      exact map_zero _
    · obtain rfl := tens_zero hw x
      exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => map_zero _⟩

end LateralTheory.EtaleFoundations.TensExPf

open LateralTheory.EtaleFoundations.TensExPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_multiplication_tensor_exists_of_complex_tensor_exists
    (hex : ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor) :
    LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists := by
  intro q _ i j
  obtain ⟨K, τ, hτ⟩ := hex (ZMod q) (sgl (tw q i)) (sgl (tw q j))
  exact ⟨K.X 0, μ τ, μ_isTensor τ hτ⟩
end
end
