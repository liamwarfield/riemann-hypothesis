module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLiftingOfSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivGaussianExponentialAtZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalSectionsCompatibleSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackTwistIsoDifference
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackTwistIsoDifference
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem lbIso_pull_quot_of_consecutive_pw : ∀ {X Y : Scheme.{0}} (b : Y ⟶ X) (A C : LB X) (N : LB Y) (n : ℤ), A.IsLB → C.IsLB → N.IsLB → LBIso (A.pull b) (pw N n) → LBIso (C.pull b) (pw N (n + 1)) → LBIso N ((tw C A (-1)).pull b) := by
  intro X Y b A C N n hA hC hN h1 h2
  have hAb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hA b
  have hCb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hC b
  have hT := GlobalTheory.AbLaw.isLB_tw hC hA (-1)
  have hTb := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hT b
  rw [← GlobalTheory.CechPic.cls_eq_iff hN hTb, GlobalTheory.CechPic.cls_pull hT b hTb]
  have e1 := (GlobalTheory.CechPic.cls_eq_iff hAb (GlobalTheory.AbLaw.isLB_pw hN n)).2 h1
  have e2 := (GlobalTheory.CechPic.cls_eq_iff hCb (GlobalTheory.AbLaw.isLB_pw hN (n + 1))).2 h2
  rw [GlobalTheory.CechPic.cls_pull hA b hAb, GlobalTheory.EffBound.cls_pw hN n] at e1
  rw [GlobalTheory.CechPic.cls_pull hC b hCb, GlobalTheory.EffBound.cls_pw hN (n + 1)] at e2
  have hT' : GlobalTheory.CechPic.cls (GlobalTheory.AbLaw.tw C A (-1)) hT
      = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
    show GlobalTheory.CechPic.cls (C.div (GlobalTheory.AbLaw.pw A (-(-1)))) hT = _
    rw [GlobalTheory.CechPic.cls_div hC (GlobalTheory.AbLaw.isLB_pw hA _) hT, GlobalTheory.EffBound.cls_pw hA]
    simp
  rw [hT', map_sub, e1, e2, add_smul, one_smul, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.FormalAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackTwistIsoDifferenceStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_twist_iso_difference : ∀ {X Y : Scheme.{0}} (b : Y ⟶ X) (A C : LB X) (N : LB Y) (n : ℤ), A.IsLB → C.IsLB → N.IsLB → LBIso (A.pull b) (pw N n) → LBIso (C.pull b) (pw N (n + 1)) → LBIso N ((tw C A (-1)).pull b) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw | exact GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.lbIso_pull_quot_of_consecutive_pw <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBundleRootFromRelations
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBundleRootFromRelations
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

abbrev wordSet {k : ℕ} {τ : Type} (w : Fin k → τ) : Multiset τ := Finset.univ.val.map w

theorem wordSet_update_add {k : ℕ} {τ : Type} (f : Fin k → τ) (l : Fin k) (a : τ) :
    wordSet (Function.update f l a) + {f l} = wordSet f + {a} := by
  have key : ∀ g : Fin k → τ, wordSet g = g l ::ₘ ((Finset.univ.erase l).val.map g) := by
    intro g
    rw [← Multiset.map_cons, Finset.erase_val, Multiset.cons_erase (Finset.mem_univ_val l)]
  have e : (Finset.univ.erase l).val.map (Function.update f l a) = (Finset.univ.erase l).val.map f :=
    Multiset.map_congr rfl fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase (show x ∈ Finset.univ.erase l from hx)) _ _
  rw [key, key f, Function.update_self, e, ← Multiset.singleton_add, ← Multiset.singleton_add (f l)]
  abel

theorem wordSet_update_rel {k : ℕ} {τ : Type} (f g : Fin k → τ) (l l' : Fin k) (a : τ) (h : f l = g l') :
    wordSet f + wordSet (Function.update g l' a) = wordSet (Function.update f l a) + wordSet g := by
  refine add_right_cancel (b := ({f l} : Multiset τ)) ?_
  have e₁ := wordSet_update_add f l a
  have e₂ := wordSet_update_add g l' a
  rw [← h] at e₂
  calc wordSet f + wordSet (Function.update g l' a) + {f l}
      = wordSet f + (wordSet (Function.update g l' a) + {f l}) := by abel
    _ = wordSet f + (wordSet g + {a}) := by rw [e₂]
    _ = (wordSet f + {a}) + wordSet g := by abel
    _ = (wordSet (Function.update f l a) + {f l}) + wordSet g := by rw [e₁]
    _ = _ := by abel

section Ring

variable {B τ : Type} [CommRing B] {k : ℕ} {x : (Fin k → τ) → B}

theorem mul_word_update
    (hrel : ∀ w₁ w₂ w₃ w₄ : Fin k → τ, wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄ →
      x w₁ * x w₂ = x w₃ * x w₄)
    {i j : τ} {l₀ : Fin k} {r : B} (hu : IsUnit (x fun _ => i))
    (hr : r * x (fun _ => i) = x (Function.update (fun _ => i) l₀ j))
    (w : Fin k → τ) (l : Fin k) (hw : w l = i) : r * x w = x (Function.update w l j) := by
  refine hu.mul_right_cancel ?_
  have := hrel _ _ _ _ (wordSet_update_rel w (fun _ => i) l l₀ j hw)
  rw [← hr] at this
  rw [← this]
  ring

theorem pow_mul_word_const
    (hrel : ∀ w₁ w₂ w₃ w₄ : Fin k → τ, wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄ →
      x w₁ * x w₂ = x w₃ * x w₄)
    {i j : τ} {l₀ : Fin k} {r : B} (hu : IsUnit (x fun _ => i))
    (hr : r * x (fun _ => i) = x (Function.update (fun _ => i) l₀ j)) :
    r ^ k * x (fun _ => i) = x fun _ => j := by
  have key : ∀ n, n ≤ k → r ^ n * x (fun _ => i) = x (fun l => if l.val < n then j else i) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hlt : n < k := hn
      have := mul_word_update hrel hu hr (fun l => if l.val < n then j else i) ⟨n, hlt⟩ (by simp)
      rw [pow_succ', mul_assoc, ih hlt.le, this]
      congr 1
      funext l
      by_cases h : l = ⟨n, hlt⟩
      · subst h; simp
      · have : l.val ≠ n := fun e => h (Fin.ext e)
        rw [Function.update_of_ne h]
        by_cases h' : l.val < n
        · simp [h', Nat.lt_succ_of_lt h']
        · have : ¬ l.val < n + 1 := by omega
          simp [h', this]
  rw [key k le_rfl]
  congr 1
  funext l
  simp [l.isLt]

end Ring

theorem prod_update_mul {M τ : Type} [CommMonoid M] {k : ℕ} (φ : τ → M) (f : Fin k → τ) (l : Fin k) (a : τ) :
    (∏ m, φ (Function.update f l a m)) * φ (f l) = (∏ m, φ (f m)) * φ a := by
  have key : ∀ w : Fin k → τ, ∏ l, φ (w l) = ((wordSet w).map φ).prod := by
    intro w
    rw [Multiset.map_map]
    rfl
  have := congrArg (fun s => (s.map φ).prod) (wordSet_update_add f l a)
  simpa [Multiset.map_add (f := _), Multiset.prod_add, key] using this

section Root

variable {X : Scheme.{0}} {Q : LB X} {k : ℕ} (hk : 1 ≤ k) {τ : Type} (u : (Fin k → τ) → LB.Sec Q)

def oneLetter (i j : τ) : Fin k → τ := Function.update (fun _ => i) ⟨0, hk⟩ j

def VeroneseRel : Prop :=
  ∀ w₁ w₂ w₃ w₄ : Fin k → τ, wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄ →
    ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c

def rootChart (i : τ) : X.Opens := nonzeroLocus (u fun _ => i)

def rootRatio (i j : τ) : Γ(X, rootChart u i) := secRatio (u fun _ => i) (u (oneLetter hk i j))

variable {u}

theorem VeroneseRel.resG (h : VeroneseRel u) {W : X.Opens} {c : Q.ι} (hc : W ≤ Q.U c)
    (w₁ w₂ w₃ w₄ : Fin k → τ) (hw : wordSet w₁ + wordSet w₂ = wordSet w₃ + wordSet w₄) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₁).f c) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₂).f c) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₃).f c) * ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hc ((u w₄).f c) := by
  rw [← map_mul, ← map_mul, h _ _ _ _ hw c]

variable (u)

theorem rootRatio_chart {W : X.Opens} {i : τ} (j : τ) {c : Q.ι} (hi : W ≤ rootChart u i) (hc : W ≤ Q.U c) :
    resG X hi (rootRatio hk u i j) * resG X hc ((u fun _ => i).f c) =
      resG X hc ((u (oneLetter hk i j)).f c) :=
  (secRatio_on _ _ c hi hc).symm

theorem rootRatio_self (i : τ) : rootRatio hk u i i = 1 := by
  have : oneLetter hk i i = fun _ => i := Function.update_eq_self (⟨0, hk⟩ : Fin k) (fun _ : Fin k => i)
  rw [rootRatio, this]
  exact secRatio_self _

variable {u}

theorem rootRatio_mul (h : VeroneseRel u) {W : X.Opens} {i j : τ} (l : τ) (hi : W ≤ rootChart u i)
    (hj : W ≤ rootChart u j) :
    resG X hi (rootRatio hk u i j) * resG X hj (rootRatio hk u j l) = resG X hi (rootRatio hk u i l) := by
  refine ext_charts (u fun _ => i) hi fun c => ?_
  have hc : W ⊓ Q.U c ≤ Q.U c := inf_le_right
  have hi' : W ⊓ Q.U c ≤ rootChart u i := inf_le_left.trans hi
  have hj' : W ⊓ Q.U c ≤ rootChart u j := inf_le_left.trans hj
  have ui : IsUnit (resG X hc ((u fun _ => i).f c)) := isUnit_resG_sec _ c hi' hc
  have uj : IsUnit (resG X hc ((u fun _ => j).f c)) := isUnit_resG_sec _ c hj' hc
  refine ui.mul_right_cancel ?_
  rw [map_mul, resG_resG, resG_resG, resG_resG]
  have e3 := mul_word_update (x := fun w => resG X hc ((u w).f c)) (h.resG hc) (i := j) (j := l)
    (l₀ := ⟨0, hk⟩) uj (rootRatio_chart hk u l hj' hc) (oneLetter hk i j) ⟨0, hk⟩
    (by simp [oneLetter])
  have e4 : Function.update (oneLetter hk i j) ⟨0, hk⟩ l = oneLetter hk i l :=
    Function.update_idem _ _ _
  rw [e4] at e3
  rw [rootRatio_chart hk u l hi' hc, mul_right_comm, rootRatio_chart hk u j hi' hc, mul_comm]
  exact e3

theorem rootRatio_pow (h : VeroneseRel u) {W : X.Opens} {i : τ} (j : τ) {c : Q.ι}
    (hi : W ≤ rootChart u i) (hc : W ≤ Q.U c) :
    resG X hi (rootRatio hk u i j) ^ k * resG X hc ((u fun _ => i).f c) =
      resG X hc ((u fun _ => j).f c) :=
  pow_mul_word_const (x := fun w => resG X hc ((u w).f c)) (h.resG hc) (l₀ := ⟨0, hk⟩)
    (isUnit_resG_sec _ c hi hc) (rootRatio_chart hk u j hi hc)

def rootG (h : VeroneseRel u) (i j : τ) : Γ(X, rootChart u i ⊓ rootChart u j)ˣ where
  val := resG X inf_le_left (rootRatio hk u i j)
  inv := resG X inf_le_right (rootRatio hk u j i)
  val_inv := by
    rw [rootRatio_mul hk h i inf_le_left inf_le_right, rootRatio_self, map_one]
  inv_val := by
    rw [rootRatio_mul hk h j inf_le_right inf_le_left, rootRatio_self, map_one]

def rootLB (h : VeroneseRel u) : LB X := ⟨τ, rootChart u, rootG hk h⟩

theorem rootG_self (h : VeroneseRel u) (i : τ) :
    res (le_inf le_rfl le_rfl : rootChart u i ≤ rootChart u i ⊓ rootChart u i) (rootG hk h i i) = 1 :=
  Units.ext (by
    change resG X _ (resG X _ (rootRatio hk u i i)) = 1
    rw [rootRatio_self, map_one, map_one])

theorem rootG_cocycle (h : VeroneseRel u) (i j l : τ) :
    res (inf_le_left : rootChart u i ⊓ rootChart u j ⊓ rootChart u l ≤ rootChart u i ⊓ rootChart u j)
        (rootG hk h i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        rootChart u i ⊓ rootChart u j ⊓ rootChart u l ≤ rootChart u j ⊓ rootChart u l) (rootG hk h j l) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        rootChart u i ⊓ rootChart u j ⊓ rootChart u l ≤ rootChart u i ⊓ rootChart u l) (rootG hk h i l) :=
  Units.ext (by
    change resG X _ (resG X _ (rootRatio hk u i j)) * resG X _ (resG X _ (rootRatio hk u j l)) =
      resG X _ (resG X _ (rootRatio hk u i l))
    simp only [resG_resG]
    exact rootRatio_mul hk h l _ _)

theorem rootLB_isLB (h : VeroneseRel u) (hc : ⨆ i : τ, nonzeroLocus (u fun _ => i) = ⊤) :
    (rootLB hk h).IsLB := {
  cover := hc
  g_self := rootG_self hk h
  cocycle := rootG_cocycle hk h }

def rootIso (h : VeroneseRel u) : LB.Iso (pw (rootLB hk h) (k : ℤ)) Q where
  s p := (isUnit_resG_sec (u fun _ => (show τ from p.2)) p.1 inf_le_right inf_le_left).unit

theorem rootIso_isGen (h : VeroneseRel u) : (rootIso hk h).IsGen := by
  rintro ⟨c, i⟩ ⟨c', i'⟩
  let A := pw (rootLB hk h) (k : ℤ)
  have hp : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ Q.U c := inf_le_left.trans inf_le_left
  have hq : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ A.U i := inf_le_left.trans inf_le_right
  have hp' : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ Q.U c' := inf_le_right.trans inf_le_left
  have hq' : Q.U c ⊓ A.U i ⊓ (Q.U c' ⊓ A.U i') ≤ A.U i' := inf_le_right.trans inf_le_right
  have key : res (le_inf hp hq) (@id (Γ(X, Q.U c ⊓ A.U i)ˣ) ((rootIso hk h).s (c, i))) *
      res (le_inf hq hq') (A.g i i') = res (le_inf hp hp') (Q.g c c') *
        res (le_inf hp' hq') (@id (Γ(X, Q.U c' ⊓ A.U i')ˣ) ((rootIso hk h).s (c', i'))) := by
    refine Units.ext ?_
    have eg : resG X (le_inf hq hq') (A.g i i').val =
        resG X (show _ ≤ rootChart u (show τ from i) from hq) (rootRatio hk u i i') ^ k := by
      have : A.g i i' = (rootG hk h i i') ^ k := by
        change (rootG hk h i i') ^ (k : ℤ) = _
        exact zpow_natCast _ _
      rw [this, Units.val_pow_eq_pow_val]
      exact (map_pow (resG X (le_inf hq hq')) _ k).trans (congrArg (· ^ k) (resG_resG _ _ _))
    change resG X (le_inf hp hq) (resG X inf_le_left ((u fun _ => (show τ from i)).f c)) *
        resG X (le_inf hq hq') (A.g i i').val =
      resG X (le_inf hp hp') (Q.g c c').val *
        resG X (le_inf hp' hq') (resG X inf_le_left ((u fun _ => (show τ from i')).f c'))
    rw [resG_resG, resG_resG, ← sec_compat _ c c' hp hp', eg, mul_comm]
    exact rootRatio_pow hk h _ _ _
  change res (le_inf hp hq) (@id (Γ(X, Q.U c ⊓ A.U i)ˣ) ((rootIso hk h).s (c, i))) =
    res (le_inf hp hp') (Q.g c c') * (res (le_inf hq hq') (A.g i i'))⁻¹ *
      res (le_inf hp' hq') (@id (Γ(X, Q.U c' ⊓ A.U i')ˣ) ((rootIso hk h).s (c', i')))
  rw [mul_right_comm, ← key, mul_inv_cancel_right]

section Pull

variable {Y : Scheme.{0}} (b : Y ⟶ X) {L : LB Y} {d D : ℤ} (hD : d * k = D)
  (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D))

include hk in
theorem preimage_rootChart_le (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) (i : τ) :
    b ⁻¹ᵁ rootChart u i ≤ nonzeroLocus (a i) :=
  (nonzeroLocus_secPull _ _).ge.trans
    (((hm _).nonzeroLocus_eq (LB.isLB_pull hQ b) (isLB_pw hL D)).le.trans
      (nonzeroLocus_secMono_const hD a i hk).le)

theorem appLE_rootRatio_chart {W : Y.Opens} {i : τ} (j : τ) {c : Q.ι} (hi : W ≤ b ⁻¹ᵁ rootChart u i)
    (hc : W ≤ b ⁻¹ᵁ Q.U c) :
    (b.appLE _ W hi).hom (rootRatio hk u i j) * (b.appLE _ W hc).hom ((u fun _ => i).f c) =
      (b.appLE _ W hc).hom ((u (oneLetter hk i j)).f c) := by
  have hW : W ≤ b ⁻¹ᵁ (rootChart u i ⊓ Q.U c) := le_inf hi hc
  have e := congrArg (b.appLE (rootChart u i ⊓ Q.U c) W hW).hom
    (rootRatio_chart hk u j (inf_le_left : rootChart u i ⊓ Q.U c ≤ _) inf_le_right)
  rwa [map_mul, appLE_resG, appLE_resG, appLE_resG] at e

theorem appLE_rootRatio_mul (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) {W : Y.Opens} {i : τ} (j : τ)
    (hi : W ≤ b ⁻¹ᵁ rootChart u i) (p : L.ι) (hp : W ≤ L.U p) :
    (b.appLE _ W hi).hom (rootRatio hk u i j) * resG Y hp (chartFn (a i) p) =
      resG Y hp (chartFn (a j) p) := by
  have hnz : W ≤ nonzeroLocus (secPull (u fun _ => i) b) := hi.trans (nonzeroLocus_secPull _ _).ge
  refine ext_charts (secPull (u fun _ => i) b) hnz fun c' => ?_
  have hc' : W ⊓ (Q.pull b).U c' ≤ (Q.pull b).U c' := inf_le_right
  have hp' : W ⊓ (Q.pull b).U c' ≤ L.U p := inf_le_left.trans hp
  have hi' : W ⊓ (Q.pull b).U c' ≤ b ⁻¹ᵁ rootChart u i := inf_le_left.trans hi
  have hcb : W ⊓ (Q.pull b).U c' ≤ b ⁻¹ᵁ Q.U (c' ⟨⟩) := hc'.trans (pull_U Q b c').le
  let α : τ → Γ(Y, W ⊓ (Q.pull b).U c') := fun i => resG Y hp' (chartFn (a i) p)
  let β : (Fin k → τ) → Γ(Y, W ⊓ (Q.pull b).U c') :=
    fun w => (b.appLE (Q.U (c' ⟨⟩)) _ hcb).hom ((u w).f (c' ⟨⟩))
  let ρ : Γ(Y, W ⊓ (Q.pull b).U c') := (b.appLE _ _ hi').hom (rootRatio hk u i j)
  let t : Γ(Y, W ⊓ (Q.pull b).U c') := resG Y (le_inf hp' hc' : _ ≤ (pw L D).U p ⊓ (Q.pull b).U c')
    (@id (Γ(Y, (pw L D).U p ⊓ (Q.pull b).U c')ˣ) (θ.s (p, c'))).val
  have S : ∀ w, ∏ l, α (w l) = t * β w := fun w => by
    have e : resG Y (le_inf hp' hc' : _ ≤ (pw L D).U p ⊓ (Q.pull b).U c')
        (resG Y inf_le_left (∏ l, chartFn (a (w l)) p)) =
        resG Y (le_inf hp' hc' : _ ≤ (pw L D).U p ⊓ (Q.pull b).U c')
          ((@id (Γ(Y, (pw L D).U p ⊓ (Q.pull b).U c')ˣ) (θ.s (p, c'))).val *
            resG Y inf_le_right ((secPull (u w) b).f c')) :=
      congrArg _ (hm w (p, c'))
    rw [map_mul, resG_resG, resG_resG] at e
    refine (map_prod (resG Y hp') _ _).symm.trans (e.trans (congrArg (t * ·) ?_))
    exact (resG_resG _ _ _).trans rfl
  have hρ : ρ * β (fun _ => i) = β (oneLetter hk i j) := appLE_rootRatio_chart hk b j hi' hcb
  have e1 := prod_update_mul α (fun _ : Fin k => i) ⟨0, hk⟩ j
  have hP := S fun _ => i
  have uα : IsUnit (α i) := isUnit_resG_sec (a i) p
    (hi'.trans (preimage_rootChart_le hk b hD a θ hQ hL hm i)) hp'
  have uP : IsUnit (∏ _l : Fin k, α i) := by
    rw [Finset.prod_const]
    exact uα.pow _
  rw [map_mul, resG_appLE, resG_resG, resG_resG]
  change ρ * α i = α j
  refine uP.mul_left_cancel ?_
  calc (∏ _l : Fin k, α i) * (ρ * α i) = t * (ρ * β fun _ => i) * α i := by
        rw [hP]; ring
    _ = (∏ l, α (oneLetter hk i j l)) * α i := by rw [hρ, S]
    _ = _ := e1

def rootPullIso (h : VeroneseRel u) (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) :
    LB.Iso ((rootLB hk h).pull b) (pw L d) where
  s p := (isUnit_resG_sec (a (p.2 ⟨⟩)) p.1
    (inf_le_right.trans ((pull_U (rootLB hk h) b p.2).le.trans
      (preimage_rootChart_le hk b hD a θ hQ hL hm _))) inf_le_left).unit

theorem rootPullIso_isGen (h : VeroneseRel u) (hQ : Q.IsLB) (hL : L.IsLB)
    (hm : ∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) :
    (rootPullIso hk b hD a θ h hQ hL hm).IsGen := by
  rintro ⟨l, i⟩ ⟨l', i'⟩
  let P := (rootLB hk h).pull b
  let M := pw L d
  have hp : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ M.U l := inf_le_left.trans inf_le_left
  have hq : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ P.U i := inf_le_left.trans inf_le_right
  have hp' : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ M.U l' := inf_le_right.trans inf_le_left
  have hq' : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ P.U i' := inf_le_right.trans inf_le_right
  have hi : M.U l ⊓ P.U i ⊓ (M.U l' ⊓ P.U i') ≤ b ⁻¹ᵁ rootChart u (i ⟨⟩) :=
    hq.trans (pull_U (rootLB hk h) b i).le
  have key : res (le_inf hp hq)
        (@id (Γ(Y, M.U l ⊓ P.U i)ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l, i))) *
      res (le_inf hq hq') (P.g i i') = res (le_inf hp hp') (M.g l l') *
        res (le_inf hp' hq')
          (@id (Γ(Y, M.U l' ⊓ P.U i')ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l', i'))) := by
    refine Units.ext ?_
    have eg : resG Y (le_inf hq hq') (P.g i i').val =
        (b.appLE _ _ hi).hom (rootRatio hk u (i ⟨⟩) (i' ⟨⟩)) := by
      have e := congrArg (fun v => resG Y (le_inf hq hq') (Units.val v)) (pull_g (rootLB hk h) b i i')
      refine e.trans ?_
      change resG Y _ (resG Y _ ((b.app _).hom (resG X inf_le_left (rootRatio hk u (i ⟨⟩) (i' ⟨⟩))))) = _
      refine (resG_resG _ _ _).trans ?_
      refine (congrArg (resG Y _) (app_resG b _ _)).trans ?_
      refine (resG_resG _ _ _).trans ?_
      rfl
    change resG Y (le_inf hp hq) (resG Y inf_le_left ((a (i ⟨⟩)).f l)) *
        resG Y (le_inf hq hq') (P.g i i').val =
      resG Y (le_inf hp hp') (M.g l l').val *
        resG Y (le_inf hp' hq') (resG Y inf_le_left ((a (i' ⟨⟩)).f l'))
    rw [resG_resG, resG_resG, ← sec_compat _ l l' hp hp', eg, mul_comm]
    exact appLE_rootRatio_mul hk b hD a θ hQ hL hm _ hi l hp
  change res (le_inf hp hq)
      (@id (Γ(Y, M.U l ⊓ P.U i)ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l, i))) =
    res (le_inf hp hp') (M.g l l') * (res (le_inf hq hq') (P.g i i'))⁻¹ *
      res (le_inf hp' hq')
        (@id (Γ(Y, M.U l' ⊓ P.U i')ˣ) ((rootPullIso hk b hD a θ h hQ hL hm).s (l', i')))
  rw [mul_right_comm, ← key, mul_inv_cancel_right]

end Pull

end Root

theorem exists_root_of_veronese : ∀ (X : Scheme.{0}) (Q : LB X), Q.IsLB → ∀ (k : ℕ), 1 ≤ k → ∀ (τ : Type) (u : (Fin k → τ) → LB.Sec Q), (∀ w₁ w₂ w₃ w₄ : Fin k → τ, (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c) → (⨆ i : τ, nonzeroLocus (u (fun _ => i)) = ⊤) → ∃ (A : LB X) (ω : LB.Iso (pw A (k : ℤ)) Q), A.IsLB ∧ ω.IsGen ∧ ∀ (Y : Scheme.{0}) (b : Y ⟶ X) (L : LB Y) (d D : ℤ) (hD : d * k = D) (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D)), L.IsLB → θ.IsGen → (∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) → LBIso (A.pull b) (pw L d) := by
  intro X Q hQ k hk τ u hrel hcov
  have h : VeroneseRel u := hrel
  exact ⟨rootLB hk h, rootIso hk h, rootLB_isLB hk h hcov, rootIso_isGen hk h,
    fun Y b L d D hD a θ hL _ hm => ⟨rootPullIso hk b hD a θ h hQ hL hm,
      rootPullIso_isGen hk b hD a θ h hQ hL hm⟩⟩

end GlobalTheory.CompanionTheory.FormalAlg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBundleRootFromRelationsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_root_from_relations : ∀ (X : Scheme.{0}) (Q : LB X), Q.IsLB → ∀ (k : ℕ), 1 ≤ k → ∀ (τ : Type) (u : (Fin k → τ) → LB.Sec Q), (∀ w₁ w₂ w₃ w₄ : Fin k → τ, (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c) → (⨆ i : τ, nonzeroLocus (u (fun _ => i)) = ⊤) → ∃ (A : LB X) (ω : LB.Iso (pw A (k : ℤ)) Q), A.IsLB ∧ ω.IsGen ∧ ∀ (Y : Scheme.{0}) (b : Y ⟶ X) (L : LB Y) (d D : ℤ) (hD : d * k = D) (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D)), L.IsLB → θ.IsGen → (∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) → LBIso (A.pull b) (pw L d) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese | exact GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleTwistDifference
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleTwistDifference
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

variable {X : Scheme.{0}}

theorem res_res_units {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (resG_resG h₁ h₂ _)

theorem mul_chart_cancel {S : Type} [CommRing S] (u G k' k u' a : S) (h : u = G * k' * u') (h' : k' * k = 1) :
    u * (k * a) = G * (u' * a) := by
  subst h
  linear_combination (G * u' * a) * h'

theorem eq_of_resG_near {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ y ∈ U, ∃ (W : X.Opens) (_ : y ∈ W) (hW : W ≤ U), resG X hW a = resG X hW b) : a = b :=
  ext_germ fun y hy => by
    obtain ⟨W, hyW, hW, e⟩ := h y hy
    rw [← germ_resG hW y hyW a, ← germ_resG hW y hyW b, e]

theorem iso_sec_chart {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) (p p' : B.ι) (q q' : A.ι)
    {W : X.Opens} (h₁ : W ≤ B.U p) (h₁' : W ≤ B.U p') (h₂ : W ≤ A.U q) (h₂' : W ≤ A.U q') :
    resG X (le_inf h₁ h₂) (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) * resG X h₂ (a.f q) =
      resG X (le_inf h₁ h₁') (B.g p p' : Γ(X, B.U p ⊓ B.U p')) *
        (resG X (le_inf h₁' h₂') (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q')) : Γ(X, B.U p' ⊓ A.U q')) *
          resG X h₂' (a.f q')) := by
  have hW : W ≤ (LB.div B A).U (p, q) ⊓ (LB.div B A).U (p', q') :=
    le_inf (le_inf h₁ h₂) (le_inf h₁' h₂')
  have e := congrArg (res hW) (hw (p, q) (p', q'))
  have e₂ : res hW ((LB.div B A).g (p, q) (p', q')) =
      res (le_inf h₁ h₁') (B.g p p') * (res (le_inf h₂ h₂') (A.g q q'))⁻¹ := by
    exact (map_mul (res hW) _ _).trans (congrArg₂ (· * ·) (res_res_units _ _ _)
      ((map_inv (res hW) _).trans (congrArg (·⁻¹) (res_res_units _ _ _))))
  rw [map_mul, e₂, res_res_units, res_res_units] at e
  have e₃ := congrArg (fun u : Γ(X, W)ˣ => (u : Γ(X, W))) e
  simp only [Units.val_mul] at e₃
  rw [sec_compat a q q' h₂ h₂']
  have e₄ : ((res (le_inf h₂ h₂') (A.g q q'))⁻¹ : Γ(X, W)ˣ).val * resG X (le_inf h₂ h₂') (A.g q q' : Γ(X, A.U q ⊓ A.U q')) = 1 :=
    Units.inv_mul (res (le_inf h₂ h₂') (A.g q q'))
  exact mul_chart_cancel _ _ _ _ _ _ e₃ e₄

theorem exists_secMaps {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) :
    ∃ b : B.Sec, SecMaps w a b := by
  have hself : ∀ (p : B.ι) {W : X.Opens} (h : W ≤ B.U p),
      resG X (le_inf h h) (B.g p p : Γ(X, B.U p ⊓ B.U p)) = 1 := by
    intro p W h
    have e := congrArg (fun u : Γ(X, B.U p)ˣ => resG X h (u : Γ(X, B.U p))) (hB.g_self p)
    simp only [val_res, resG_resG, Units.val_one, map_one] at e
    exact e
  have glue : ∀ p : B.ι, ∃ b : Γ(X, B.U p), ∀ q : A.ι, resG X (inf_le_left : B.U p ⊓ A.U q ≤ B.U p) b =
      (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q) := by
    intro p
    obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun q : A.ι => B.U p ⊓ A.U q) (B.U p)
      (fun _ => homOfLE inf_le_left)
      (fun y hy => by
        obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, hq⟩)
      (fun q => (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q))
      (fun q q' => by
        have h₁ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ B.U p := inf_le_left.trans inf_le_left
        have h₂ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
        have h₃ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
        have k := iso_sec_chart hw a p p q q' h₁ h₁ h₂ h₃
        rw [hself p h₁, one_mul] at k
        change resG X inf_le_left _ = resG X inf_le_right _
        rw [map_mul, map_mul]
        repeat rw [resG_resG]
        exact k)
    exact ⟨b, hb⟩
  choose b hb using glue
  refine ⟨⟨b, fun p p' => ?_⟩, fun r => hb r.1 r.2⟩
  refine eq_of_resG_near fun y hy => ?_
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
  have h₀ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p ⊓ B.U p' := inf_le_left
  have h₁ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p := inf_le_left.trans inf_le_left
  have h₁' : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p' := inf_le_left.trans inf_le_right
  have h₂ : B.U p ⊓ B.U p' ⊓ A.U q ≤ A.U q := inf_le_right
  refine ⟨B.U p ⊓ B.U p' ⊓ A.U q, ⟨hy, hq⟩, h₀, ?_⟩
  have e₁ := congrArg (resG X (le_inf h₁ h₂)) (hb p q)
  have e₂ := congrArg (resG X (le_inf h₁' h₂)) (hb p' q)
  rw [map_mul, resG_resG, resG_resG] at e₁ e₂
  have k := iso_sec_chart hw a p p' q q h₁ h₁' h₂ h₂
  change resG X h₀ (resG X inf_le_left (b p)) = resG X h₀ ((B.g p p' : Γ(X, B.U p ⊓ B.U p')) * resG X inf_le_right (b p'))
  rw [map_mul, resG_resG, resG_resG]
  exact e₁.trans (k.trans (congrArg _ e₂.symm))

theorem relAmple_tw_of_roots : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (m : ℕ) (ζ : Fin (m + 1) → LB.Sec Q), Q.IsLB → VeryAmpleBy X.hom Q ζ → ∀ (A C : LB X.left) (n : ℕ), 1 ≤ n → A.IsLB → C.IsLB → LBIso (pw A ((n + 1 : ℕ) : ℤ)) Q → LBIso (pw C (n : ℤ)) Q → RelAmple X (tw C A (-1)) := by
  intro R _ X Q m ζ hQ hva A C n hn hA hC hAQ hCQ
  have hM : (tw C A (-1)).IsLB := isLB_tw hC hA _
  have hD : 1 ≤ n * (n + 1) := Nat.mul_pos hn (Nat.succ_pos n)
  have hP := isLB_pw hM ((n * (n + 1) : ℕ) : ℤ)
  have hcls : GlobalTheory.CechPic.cls _ hP = GlobalTheory.CechPic.cls Q hQ := by
    have hc : GlobalTheory.CechPic.cls _ hM = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
      refine (GlobalTheory.CechPic.cls_div hC (isLB_pw hA _) hM).trans ?_
      rw [GlobalTheory.AmpleStabFinite.cls_pw hA]
      simp
    have e₁ : ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hA _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hAQ)
    have e₂ : (n : ℤ) • GlobalTheory.CechPic.cls C hC = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hC _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hCQ)
    rw [GlobalTheory.AmpleStabFinite.cls_pw hM, hc, smul_sub]
    have f₁ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls C hC = ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₂, smul_smul]; congr 1 <;> (push_cast; ring)
    have f₂ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = (n : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₁, smul_smul]; congr 1 <;> (push_cast; ring)
    rw [f₁, f₂, ← sub_smul]
    simp
  obtain ⟨w, hw⟩ : LBIso Q (pw (tw C A (-1)) ((n * (n + 1) : ℕ) : ℤ)) := (GlobalTheory.CechPic.cls_eq_iff hQ hP).1 hcls.symm
  choose t ht using fun i => exists_secMaps hQ hP hw (ζ i)
  obtain ⟨hs, hci⟩ := (veryAmpleBy_iff X.hom ζ).1 hva
  have ht' := iSup_nonzeroLocus_of_secMaps hs hQ hP ht
  refine GlobalTheory.Unif.relAmple_of_veryAmpleBy hM hD t ((veryAmpleBy_iff X.hom t).2 ⟨ht', ?_⟩)
  rw [toProj_eq_of_secMaps hs ht' ht]
  exact hci

end GlobalTheory.CompanionTheory.FormalAlg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativelyAmpleTwistDifferenceStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatively_ample_twist_difference : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (m : ℕ) (ζ : Fin (m + 1) → LB.Sec Q), Q.IsLB → VeryAmpleBy X.hom Q ζ → ∀ (A C : LB X.left) (n : ℕ), 1 ≤ n → A.IsLB → C.IsLB → LBIso (pw A ((n + 1 : ℕ) : ℤ)) Q → LBIso (pw C (n : ℤ)) Q → RelAmple X (tw C A (-1)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.relAmple_tw_of_roots | exact GlobalTheory.CompanionTheory.FormalAlg.relAmple_tw_of_roots | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.relAmple_tw_of_roots <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleTensorPowerSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleTensorPowerSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem mem_basicOpen_prod {X : Scheme.{0}} {U : X.Opens} {ι : Type} (s : Finset ι) (g : ι → Γ(X, U)) {y : X}
    (hy : y ∈ U) : y ∈ X.basicOpen (∏ l ∈ s, g l) ↔ ∀ l ∈ s, y ∈ X.basicOpen (g l) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Scheme.basicOpen_one, Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    exact hy
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Scheme.basicOpen_mul, Finset.forall_mem_insert, ← ih]
    rfl

theorem mem_nonzeroLocus_secMono {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D)
    (a : τ → LB.Sec (pw L d)) (w : Fin k → τ) (hk : 1 ≤ k) (y : X) :
    y ∈ nonzeroLocus (secMono h a w) ↔ ∀ l, y ∈ nonzeroLocus (a (w l)) := by
  constructor
  · intro hy l
    obtain ⟨c, hc⟩ := exists_chart_of_mem_nonzeroLocus hy
    have h1 := (mem_nonzeroLocus_iff_basicOpen (secMono h a w) hc).1 hy
    exact (mem_nonzeroLocus_iff_basicOpen (a (w l)) hc).2
      ((mem_basicOpen_prod Finset.univ (fun l => chartFn (a (w l)) c) hc).1 h1 l (Finset.mem_univ l))
  · intro hy
    obtain ⟨c, hc⟩ := exists_chart_of_mem_nonzeroLocus (hy ⟨0, hk⟩)
    refine (mem_nonzeroLocus_iff_basicOpen (secMono h a w) hc).2 ?_
    exact (mem_basicOpen_prod Finset.univ (fun l => chartFn (a (w l)) c) hc).2 fun l _ =>
      (mem_nonzeroLocus_iff_basicOpen (a (w l)) hc).1 (hy l)

theorem prod_update_eq_mul {B τ : Type} [CommMonoid B] {k : ℕ} (φ : τ → B) (w : Fin k → τ) (l : Fin k) (c : τ)
    (ρ : B) (h : φ c = ρ * φ (w l)) :
    ∏ l', φ (Function.update w l c l') = ρ * ∏ l', φ (w l') := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase Finset.univ (fun l' => φ (w l')) (Finset.mem_univ l), Function.update_self, h, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun l' hl' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl')]

theorem secRatio_secMono_update {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D)
    (a : τ → LB.Sec (pw L d)) (w : Fin k → τ) (l : Fin k) (c : τ)
    (hl : nonzeroLocus (secMono h a w) ≤ nonzeroLocus (a (w l))) :
    secRatio (secMono h a w) (secMono h a (Function.update w l c)) = resG X hl (secRatio (a (w l)) (a c)) := by
  refine (eq_secRatio _ _ fun κ => ?_).symm
  have key := secRatio_on (a (w l)) (a c) κ
    (W := nonzeroLocus (secMono h a w) ⊓ (pw L D).U κ) (inf_le_left.trans hl) inf_le_right
  have := prod_update_eq_mul (fun t => resG X (inf_le_right : nonzeroLocus (secMono h a w) ⊓ (pw L D).U κ ≤ L.U κ)
    (chartFn (a t) κ)) w l c _ key
  change resG X _ (∏ l', chartFn (a (Function.update w l c l')) κ) = _ * resG X _ (∏ l', chartFn (a (w l')) κ)
  rw [map_prod, map_prod, resG_resG]
  exact this

theorem mem_of_basicOpen {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (F : Γ(X, U))
    (hV : V = X.basicOpen F) (hle : V ≤ U) (S : Subring Γ(X, V)) (h1 : ∀ x, resG X hle x ∈ S)
    (g : Γ(X, V)) (hg : g ∈ S) (hgF : g * resG X hle F = 1) (z : Γ(X, V)) : z ∈ S := by
  subst hV
  have := hU.isLocalization_basicOpen F
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers F) z
  have hx' : z * resG X hle F ^ n = resG X hle x := by
    have e : ∀ t, algebraMap Γ(X, U) Γ(X, X.basicOpen F) t = resG X hle t := fun _ => rfl
    simpa only [e, map_pow] using hx
  have : z = resG X hle x * g ^ n := by
    rw [← hx', mul_assoc, ← mul_pow, mul_comm (resG X hle F), hgF, one_pow, mul_one]
  rw [this]
  exact S.mul_mem (h1 x) (S.pow_mem hg n)

theorem veryAmpleBy_secMono : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (d D : ℤ) (k : ℕ) (h : d * k = D) (p : ℕ) (a : Fin (p + 1) → LB.Sec (pw L d)), L.IsLB → 1 ≤ k → VeryAmpleBy f (pw L d) a → ∀ (m : ℕ) (e : Fin (m + 1) ≃ (Fin k → Fin (p + 1))), VeryAmpleBy f (pw L D) (fun j => secMono h a (e j)) := by
  intro R _ X f L d D k h p a hL hk hva m e
  obtain ⟨hcov, hch⟩ := hva
  refine ⟨?_, fun j => ?_⟩
  · refine top_unique ?_
    rw [← hcov]
    refine iSup_le fun i => ?_
    rw [← nonzeroLocus_secMono_const h a i hk]
    refine le_trans ?_ (le_iSup _ (e.symm fun _ => i))
    simp only [Equiv.apply_symm_apply, le_refl]
  · beta_reduce
    let w : Fin k → Fin (p + 1) := e j
    let l₀ : Fin k := ⟨0, hk⟩
    obtain ⟨hU, r, hr, hsurj⟩ := hch (w l₀)
    obtain rfl : r = fun t => secRatio (a (w l₀)) (a t) := funext fun t => eq_secRatio _ _ (hr t)
    have hN : ∀ l, nonzeroLocus (secMono h a w) ≤ nonzeroLocus (a (w l)) := fun l y hy =>
      (mem_nonzeroLocus_secMono h a w hk y).1 hy l
    have hV : nonzeroLocus (secMono h a w) = X.basicOpen (∏ l, secRatio (a (w l₀)) (a (w l))) := by
      ext y
      constructor
      · intro hy
        refine (mem_basicOpen_prod Finset.univ _ (hN l₀ hy)).2 fun l _ => ?_
        rw [basicOpen_secRatio]
        exact ⟨hN l₀ hy, hN l hy⟩
      · intro hy
        have hy₀ := X.basicOpen_le _ hy
        refine (mem_nonzeroLocus_secMono h a w hk y).2 fun l => ?_
        have := (mem_basicOpen_prod Finset.univ _ hy₀).1 hy l (Finset.mem_univ l)
        rw [basicOpen_secRatio] at this
        exact this.2
    refine ⟨hV ▸ hU.basicOpen _, fun t => secRatio (secMono h a w) (secMono h a (e t)),
      fun t κ => secRatio_spec _ _ κ, fun z => ?_⟩
    let S := (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (secMono h a w)))
      fun t => secRatio (secMono h a w) (secMono h a (e t))).range
    have hρ : ∀ v, secRatio (secMono h a w) (secMono h a v) ∈ S := fun v =>
      ⟨MvPolynomial.X (e.symm v), by simp⟩
    have hC : ∀ c : R, cst f (nonzeroLocus (secMono h a w)) c ∈ S := fun c =>
      ⟨MvPolynomial.C c, by simp⟩
    have h1 : ∀ x, resG X (hN l₀) x ∈ S := fun x => by
      obtain ⟨P, rfl⟩ := hsurj x
      induction P using MvPolynomial.induction_on with
      | C c =>
        rw [MvPolynomial.eval₂Hom_C]
        exact (rs_cst f (hN l₀) c).symm ▸ hC c
      | add P Q hP hQ =>
        rw [map_add (f := _), map_add (f := _)]
        exact S.add_mem hP hQ
      | mul_X P t hP =>
        rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']
        refine S.mul_mem hP ?_
        rw [← secRatio_secMono_update h a w l₀ t (hN l₀)]
        exact hρ _
    obtain ⟨P, hP⟩ : z ∈ S := mem_of_basicOpen hU _ hV (hN l₀) S h1
      (∏ l, secRatio (secMono h a w) (secMono h a (Function.update w l (w l₀))))
      (S.prod_mem fun l _ => hρ _) (by
        rw [map_prod, ← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun l _ => ?_
        rw [secRatio_secMono_update h a w l (w l₀) (hN l), mul_comm,
          secRatio_mul_secRatio _ _ _ (hN l₀) (hN l), secRatio_self, map_one]) z
    exact ⟨P, hP⟩

end GlobalTheory.CompanionTheory.FormalAlg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleTensorPowerSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.very_ample_tensor_power_sections : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (d D : ℤ) (k : ℕ) (h : d * k = D) (p : ℕ) (a : Fin (p + 1) → LB.Sec (pw L d)), L.IsLB → 1 ≤ k → VeryAmpleBy f (pw L d) a → ∀ (m : ℕ) (e : Fin (m + 1) ≃ (Fin k → Fin (p + 1))), VeryAmpleBy f (pw L D) (fun j => secMono h a (e j)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono | exact GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleUnionSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleUnionSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

namespace GlobalTheory.CompanionTheory.VeryAmpleUnion

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def ChartBy (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (a : LB.Sec H) {m : ℕ}
    (s : Fin (m + 1) → LB.Sec H) : Prop :=
  IsAffineOpen (nonzeroLocus a) ∧
    ∃ r : Fin (m + 1) → Γ(X, nonzeroLocus a),
      (∀ j k, rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus a ⊓ H.U k ≤ nonzeroLocus a) (r j) *
          rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (a.f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus a)) r)

theorem ChartBy.of_sub {f : X ⟶ Spec (CommRingCat.of R)} {H : LB X} {a : LB.Sec H} {m n : ℕ}
    {w : Fin (n + 1) → LB.Sec H} {z : Fin (m + 1) → LB.Sec H} (ι : Fin (n + 1) → Fin (m + 1))
    (hι : ∀ l, z (ι l) = w l) (h : ChartBy f H a w) : ChartBy f H a z := by
  obtain ⟨ha, r, hr, hs⟩ := h
  refine ⟨ha, fun j => secRatio a (z j), fun j k => secRatio_spec a (z j) k, fun g => ?_⟩
  obtain ⟨p, rfl⟩ := hs g
  refine ⟨MvPolynomial.rename ι p, ?_⟩
  have hrr : (fun j => secRatio a (z j)) ∘ ι = r := by
    funext l
    refine (eq_secRatio a (z (ι l)) ?_).symm
    intro k
    rw [hι l]
    exact hr l k
  simp only [MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_rename, hrr]

theorem veryAmpleBy_union : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X), H.IsLB → ∀ (m₁ m₂ m : ℕ) (x : Fin (m₁ + 1) → LB.Sec H) (y : Fin (m₂ + 1) → LB.Sec H) (e : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1)), VeryAmpleBy f H x → VeryAmpleBy f H y → VeryAmpleBy f H (fun j => Sum.elim x y (e j)) := by
  intro R _ X f H _ m₁ m₂ m x y e hx hy
  have key : ∀ (z : Fin (m + 1) → LB.Sec H), (∀ j, z j = Sum.elim x y (e j)) →
      (⨆ j, nonzeroLocus (z j) = ⊤) ∧ ∀ j, ChartBy f H (z j) z := by
    intro z hz
    have hl : ∀ i, z (e.symm (Sum.inl i)) = x i := fun i => by simp [hz]
    have hr : ∀ i, z (e.symm (Sum.inr i)) = y i := fun i => by simp [hz]
    refine ⟨eq_top_iff.2 ?_, fun j => ?_⟩
    · rw [← hx.1]
      exact iSup_le fun i => le_iSup_of_le (e.symm (Sum.inl i)) (by rw [hl])
    · rcases he : e j with i | i
      · have hj : z j = x i := by rw [hz, he]; rfl
        rw [hj]
        exact ChartBy.of_sub (fun l => e.symm (Sum.inl l)) hl (hx.2 i)
      · have hj : z j = y i := by rw [hz, he]; rfl
        rw [hj]
        exact ChartBy.of_sub (fun l => e.symm (Sum.inr l)) hr (hy.2 i)
  exact key _ fun _ => rfl

end GlobalTheory.CompanionTheory.VeryAmpleUnion
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleUnionSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.very_ample_union_sections : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X), H.IsLB → ∀ (m₁ m₂ m : ℕ) (x : Fin (m₁ + 1) → LB.Sec H) (y : Fin (m₂ + 1) → LB.Sec H) (e : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1)), VeryAmpleBy f H x → VeryAmpleBy f H y → VeryAmpleBy f H (fun j => Sum.elim x y (e j)) := by
  first | exact @GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union | exact GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union | (intros; apply GlobalTheory.CompanionTheory.VeryAmpleUnion.veryAmpleBy_union <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalAlgebraisationSchemes
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
open GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

theorem exists_compatible {R : Type} [CommRing R] (I : Ideal R) {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {N : ∀ e, LB (Y e).left}
    {v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))} {D : ℤ}
    (step : ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D),
      SecMaps (pullPow (v e) D) σ (secPull σ' (β e)))
    {τ : Type} (a₀ : τ → LB.Sec (pw (N 0) D)) :
    ∃ a : ∀ e, τ → LB.Sec (pw (N e) D), a 0 = a₀ ∧
      ∀ e i, SecMaps (pullPow (v e) D) (a e i) (secPull (a (e + 1) i) (β e)) := by
  choose L hL using step
  exact ⟨fun e i => Nat.rec (motive := fun e => LB.Sec (pw (N e) D)) (a₀ i) (fun e x => L e x) e,
    rfl, fun e i => hL e _⟩

theorem tower_sections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (n p q : ℕ) (a : ∀ e, Fin (p + 1) → LB.Sec (pw (N e) (n : ℤ))) (c : ∀ e, Fin (q + 1) → LB.Sec (pw (N e) ((n : ℤ) + 1))), 1 ≤ n ∧ VeryAmpleBy (Y 0).hom (pw (N 0) (n : ℤ)) (a 0) ∧ VeryAmpleBy (Y 0).hom (pw (N 0) ((n : ℤ) + 1)) (c 0) ∧ (∀ e i, SecMaps (pullPow (v e) (n : ℤ)) (a e i) (secPull (a (e + 1) i) (β e))) ∧ (∀ e i, SecMaps (pullPow (v e) ((n : ℤ) + 1)) (c e i) (secPull (c (e + 1) i) (β e))) := by
  intro R _ _ I Y β hβ hP N v hN hA
  obtain ⟨d, hd, m₁, s, m₂, s', hs, hs'⟩ := GlobalTheory.T.relatively_ample_consecutive_very_ample (R ⧸ I ^ (0 + 1)) (Y 0) (N 0) (hN 0).1 hA
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.T.formal_line_bundle_very_ample_system R I Y β hβ hP N v hN d hd m₁ s hs
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.T.formal_line_bundle_very_ample_system R I Y β hβ hP N v hN (d + 1) (by omega) m₂ s' hs'
  set k := max t₁ t₂ with hk
  set t := 1 + (d + 1) * k with ht
  set t' := 1 + d * k with ht'
  have hkt : k ≤ t := by nlinarith
  have hkt' : k ≤ t' := by nlinarith
  have h1 : t₁ ≤ t := (le_max_left _ _).trans hkt
  have h2 : t₂ ≤ t' := (le_max_right _ _).trans hkt'
  have e₁ : ((d * t : ℕ) : ℤ) = (d : ℤ) * (t : ℕ) := by push_cast; ring
  have e₂ : ((d * t : ℕ) : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) * (t' : ℕ) := by
    simp only [ht, ht']; push_cast; ring
  have hc₁ : 0 < Fintype.card (Fin t → Fin (m₁ + 1)) := Fintype.card_pos
  have hc₂ : 0 < Fintype.card (Fin t' → Fin (m₂ + 1)) := Fintype.card_pos
  obtain ⟨p, hp⟩ : ∃ p, Fintype.card (Fin t → Fin (m₁ + 1)) = p + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₁).symm⟩
  obtain ⟨q, hq⟩ : ∃ q, Fintype.card (Fin t' → Fin (m₂ + 1)) = q + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc₂).symm⟩
  let E₁ : Fin (p + 1) ≃ (Fin t → Fin (m₁ + 1)) := (Fintype.equivFinOfCardEq hp).symm
  let E₂ : Fin (q + 1) ≃ (Fin t' → Fin (m₂ + 1)) := (Fintype.equivFinOfCardEq hq).symm
  have ht1 : 1 ≤ t := by omega
  have ht1' : 1 ≤ t' := by omega
  have va := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ t e₁.symm m₁ s (hN 0).1 ht1 hs p E₁
  have vc := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ t' e₂.symm m₂ s' (hN 0).1 ht1' hs' q E₂
  obtain ⟨a, ha0, ha⟩ := exists_compatible I (v := v) (ht₁ t h1 _ e₁) (fun j => secMono e₁.symm s (E₁ j))
  obtain ⟨c, hc0, hc⟩ := exists_compatible I (v := v) (ht₂ t' h2 _ e₂) (fun j => secMono e₂.symm s' (E₂ j))
  refine ⟨d * t, p, q, a, c, Nat.mul_pos hd ht1, ?_, ?_, ha, hc⟩
  · rw [ha0]; exact va
  · rw [hc0]; exact vc

theorem schemes_of_closedProj : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro hGE R _ _ I hI Y β hβ hP N hN hv hA
  choose v hvg using hv
  have hNv : ∀ e, (N e).IsLB ∧ (v e).IsGen := fun e => ⟨hN e, hvg e⟩
  obtain ⟨n, p, q, a, c, hn, ha0, hc0, hca, hcc⟩ := tower_sections R I Y β hβ hP N v hNv hA
  set D : ℤ := (n : ℤ) * ((n + 1 : ℕ) : ℤ) with hD
  have h1 : (n : ℤ) * ((n + 1 : ℕ) : ℤ) = D := rfl
  have h2 : ((n : ℤ) + 1) * ((n : ℕ) : ℤ) = D := by rw [hD]; push_cast; ring
  have hcard : ∀ (k r : ℕ), ∃ m, Fintype.card (Fin k → Fin (r + 1)) = m + 1 := fun k r =>
    ⟨_, (Nat.succ_pred_eq_of_pos (Fintype.card_pos (α := Fin k → Fin (r + 1)))).symm⟩
  obtain ⟨m₁, hm₁⟩ := hcard (n + 1) p
  obtain ⟨m₂, hm₂⟩ := hcard n q
  let E₁ : Fin (m₁ + 1) ≃ (Fin (n + 1) → Fin (p + 1)) := (Fintype.equivFinOfCardEq hm₁).symm
  let E₂ : Fin (m₂ + 1) ≃ (Fin n → Fin (q + 1)) := (Fintype.equivFinOfCardEq hm₂).symm
  let m := m₁ + 1 + m₂
  let E : Fin (m + 1) ≃ Fin (m₁ + 1) ⊕ Fin (m₂ + 1) :=
    (finCongr (by omega)).trans finSumFinEquiv.symm
  let z : ∀ e, Fin (m + 1) → LB.Sec (pw (N e) D) := fun e j =>
    Sum.elim (fun i => secMono h1 (a e) (E₁ i)) (fun i => secMono h2 (c e) (E₂ i)) (E j)
  have hz1 : ∀ e w, z e (E.symm (Sum.inl (E₁.symm w))) = secMono h1 (a e) w := fun e w => by
    simp [z]
  have hz2 : ∀ e w, z e (E.symm (Sum.inr (E₂.symm w))) = secMono h2 (c e) w := fun e w => by
    simp [z]
  have hva : VeryAmpleBy (Y 0).hom (pw (N 0) D) (z 0) := by
    have x1 := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ (n + 1) h1 p (a 0) (hN 0) (by omega) ha0 m₁ E₁
    have x2 := GlobalTheory.T.very_ample_tensor_power_sections _ (Y 0).hom (N 0) _ _ n h2 q (c 0) (hN 0) hn hc0 m₂ E₂
    exact GlobalTheory.T.very_ample_union_sections _ (Y 0).hom _ (isLB_pw (hN 0) D) m₁ m₂ m _ _ E x1 x2
  have hzc : ∀ e j, SecMaps (pullPow (v e) D) (z e j) (secPull (z (e + 1) j) (β e)) := fun e j => by
    simp only [z]
    rcases E j with i | i
    · exact secMaps_secMono (v e) h1 (a e) (a (e + 1)) (hca e) _
    · exact secMaps_secMono (v e) h2 (c e) (c (e + 1)) (hcc e) _
  obtain ⟨X, Q, ζ, b, ω, hQ, hX, hXa, hb, hbc, hω, hωz, hquad, hcov⟩ :=
    GlobalTheory.T.formal_sections_compatible_system hGE R I hI Y β hβ (fun e => pw (N e) D) (fun e => pullPow (v e) D)
      (fun e => ⟨isLB_pw (hN e) D, pullPow_isGen _ _ (hvg e)⟩) m z hzc hva
  let ia : (Fin (n + 1) → Fin (p + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inl (E₁.symm w))
  let ic : (Fin n → Fin (q + 1)) → Fin (m + 1) := fun w => E.symm (Sum.inr (E₂.symm w))
  have hA' : ⨆ i : Fin (p + 1), nonzeroLocus (ζ (ia fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (p + 1) => ia fun _ => i) (by
      rw [iSup_range, ← ha0.1]
      refine iSup_congr fun i => ?_
      rw [hz1, nonzeroLocus_secMono_const h1 _ _ (by omega)])
    rwa [iSup_range] at this
  have hC' : ⨆ i : Fin (q + 1), nonzeroLocus (ζ (ic fun _ => i)) = ⊤ := by
    have := hcov (Set.range fun i : Fin (q + 1) => ic fun _ => i) (by
      rw [iSup_range, ← hc0.1]
      refine iSup_congr fun i => ?_
      rw [hz2, nonzeroLocus_secMono_const h2 _ _ hn])
    rwa [iSup_range] at this
  obtain ⟨A, ωA, hAL, hωA, hAc⟩ := GlobalTheory.T.line_bundle_root_from_relations X.left Q hQ (n + 1) (by omega) (Fin (p + 1)) (fun w => ζ (ia w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ia, hz1]; exact secMono_mul h1 (a e) w₁ w₂ w₃ w₄ hw c'') c') hA'
  obtain ⟨C, ωC, hCL, hωC, hCc⟩ := GlobalTheory.T.line_bundle_root_from_relations X.left Q hQ n hn (Fin (q + 1)) (fun w => ζ (ic w))
    (fun w₁ w₂ w₃ w₄ hw c' => hquad _ _ _ _ (fun e c'' => by
      simp only [ic, hz2]; exact secMono_mul h2 (c e) w₁ w₂ w₃ w₄ hw c'') c') hC'
  refine ⟨X, tw C A (-1), b, hX, isLB_tw hCL hAL _,
    GlobalTheory.T.relatively_ample_twist_difference R X Q m ζ hQ hXa A C n hn hAL hCL ⟨ωA, hωA⟩ ⟨ωC, hωC⟩, hb, hbc, fun e => ?_⟩
  refine GlobalTheory.T.pullback_twist_iso_difference (b e) A C (N e) n hAL hCL (hN e) ?_ ?_
  · refine hAc _ (b e) (N e) n D h1 (a e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ia w)
    simp only [ia, hz1] at this
    exact this
  · refine hCc _ (b e) (N e) ((n : ℤ) + 1) D h2 (c e) (ω e) (hN e) (hω e) fun w => ?_
    have := hωz e (ic w)
    simp only [ic, hz2] at this
    exact this

end GlobalTheory.CompanionTheory.FormalAlg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalAlgebraisationSchemesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_algebraisation_schemes : GEClosedProj → GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj | exact GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.schemes_of_closedProj <;> assumption)
end
