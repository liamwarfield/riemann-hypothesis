module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module

noncomputable section

namespace GlobalTheory.PstRank

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

def sigSt (g : ↥(GK K)) : Bst P ⊗[ℚ_[l]] V →ₗ[ℚ_[l]] Bst P ⊗[ℚ_[l]] V :=
  TensorProduct.map (actSt P (g : GQ l)).toLinearMap ((ρ g).restrictScalars ℚ_[l])

theorem sigSt_smul (g : ↥(GK K)) (b : Bst P) (w : Bst P ⊗[ℚ_[l]] V) :
    sigSt P ρ g (b • w) = actSt P (g : GQ l) b • sigSt P ρ g w := by
  induction w using TensorProduct.inductionOn with
  | tmul c v => simp [sigSt, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem sigSt_comm (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Bst P) :
    sigSt P ρ g (TensorProduct.comm ℚ_[l] V (Bst P) y) =
      TensorProduct.comm ℚ_[l] V (Bst P) (stRep P ρ g y) := by
  induction y using TensorProduct.inductionOn with
  | tmul v b => simp [sigSt]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem comm_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : V ⊗[ℚ_[l]] Bst P) :
    TensorProduct.comm ℚ_[l] V (Bst P) (mulV P LL V c y) = c • TensorProduct.comm ℚ_[l] V (Bst P) y := by
  induction y using TensorProduct.inductionOn with
  | tmul v b => simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

def toB : DpstUr P ρ →ₗ[↥(MaximalUnramifiedExtension l)] Bst P ⊗[ℚ_[l]] V where
  toFun x := TensorProduct.comm ℚ_[l] V (Bst P) (((toUr P ρ).symm x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P)
  map_add' x y := by simp
  map_smul' c x := comm_mulV P c _

theorem toB_injective : Function.Injective (toB P ρ) := fun x y h =>
  (toUr P ρ).symm.injective (Subtype.ext ((TensorProduct.comm ℚ_[l] V (Bst P)).injective h))

end GlobalTheory.PstRank

namespace GlobalTheory.PstRank

theorem rank_DpstUr_le : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l), IsDomain (Bst P) → (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 → (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) → ∀ {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] (ρ : Representation LL ↥(GK K) V), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
  intro l _ P hdom hreg K LL _ _ V _ _ _ _ _ ρ
  refine rank_le fun s hs => ?_
  choose F hF using fun i : ↥s => (mem_Dpst P ρ).mp ((toUr P ρ).symm (i : DpstUr P ρ)).2
  have hFd := fun i : ↥s => (F i).2
  let K' : FinExt l := supExt K ⟨⨆ i, (F i).1, inferInstance⟩
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hFK' : ∀ i, (F i).1 ≤ K'.1 := fun i => (le_iSup (fun i => (F i).1) i).trans le_sup_right
  let v : ↥s → Bst P ⊗[ℚ_[l]] V := fun i => toB P ρ (i : DpstUr P ρ)
  have hv : ∀ (g : ↥(GK K')) i, sigSt P ρ ⟨g, GK_le hKK' g.2⟩ (v i) = v i := by
    intro g i
    change sigSt P ρ _ (TensorProduct.comm ℚ_[l] V (Bst P) _) = _
    rw [sigSt_comm, hF i ⟨g, GK_le hKK' g.2⟩ (GK_le (hFK' i) g.2)]
    rfl
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) v := hs.map' (toB P ρ) (LinearMap.ker_eq_bot.mpr (toB_injective P ρ))
  have hB : LinearIndepOn (Bst P) v ((Finset.univ : Finset ↥s) : Set ↥s) :=
    GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P) (G := ↥(GK K'))
      (fun g b => actSt P (g : GQ l) b)
      (fun g => (sigSt P ρ ⟨g, GK_le hKK' g.2⟩).toAddMonoidHom)
      (fun g b w => sigSt_smul P ρ _ b w)
      (fun b b' hb h => by
        obtain ⟨c, -, hc⟩ := hreg K' b b' hb h
        exact ⟨c, hc⟩)
      v hv Finset.univ (hli.linearIndepOn _)
  have hB' : LinearIndependent (Bst P) v := by
    rw [← linearIndepOn_univ_iff]; rw [Finset.coe_univ] at hB; exact hB
  simpa using LinearIndependent.fintype_card_le_finrank hB'

end GlobalTheory.PstRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentationStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dpst_unramified_le_dim_representation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l), IsDomain (Bst P) → (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 → (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) → ∀ {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] (ρ : Representation LL ↥(GK K) V), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
  first | exact @GlobalTheory.PstRank.rank_DpstUr_le | exact GlobalTheory.PstRank.rank_DpstUr_le | (intros; apply GlobalTheory.PstRank.rank_DpstUr_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.CongLevel

section Ext

variable {k : Type} [CommRing k] {n : ℕ} (c : ℕ)

def resX : (Fin (n + c) → k) →ₗ[k] (Fin n → k) := LinearMap.funLeft k k (Fin.castAdd c)

theorem inX_apply (x : Fin n → k) (l : Fin (n + c)) :
    Loc.inX k n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  unfold Loc.inX
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

theorem resX_inX (x : Fin n → k) : resX c (Loc.inX k n c x) = x := by
  funext i
  show Loc.inX k n c x (Fin.castAdd c i) = _
  rw [inX_apply, dite_eq_left (by simp)]
  rfl

theorem resX_eN (i : ℕ) : resX c (Loc.eN k (n + c) (n + i)) = 0 := by
  funext l
  show Loc.eN k (n + c) (n + i) (Fin.castAdd c l) = 0
  have := l.2
  unfold Loc.eN
  rw [if_neg]
  simp only [Fin.val_castAdd]
  omega

theorem inX_mem_Ufl (i : ℕ) (x : Fin n → k) : Loc.inX k n c x ∈ Loc.Ufl k n c i := by
  intro l hl
  rw [inX_apply, dite_eq_right]
  intro h
  exact hl (show l.1 < n + i by omega)

def extL (a : (Fin n → k) →ₗ[k] (Fin n → k)) : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.id + Loc.inX k n c ∘ₗ (a - LinearMap.id) ∘ₗ resX c

theorem extL_apply (a : (Fin n → k) →ₗ[k] (Fin n → k)) (v : Fin (n + c) → k) :
    extL c a v = v + Loc.inX k n c (a (resX c v) - resX c v) := rfl

theorem extL_extL (a b : (Fin n → k) →ₗ[k] (Fin n → k)) (hab : ∀ x, a (b x) = x) (v : Fin (n + c) → k) :
    extL c a (extL c b v) = v := by
  have h : resX c (extL c b v) = b (resX c v) := by
    rw [extL_apply, map_add (f := _), resX_inX]; abel
  rw [extL_apply c a, h, hab, extL_apply, map_sub, map_sub]
  abel

def extE (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k) :=
  LinearEquiv.ofLinear (extL c κ.toLinearMap) (extL c κ.symm.toLinearMap)
    (LinearMap.ext fun v => extL_extL c _ _ (fun x => κ.apply_symm_apply x) v)
    (LinearMap.ext fun v => extL_extL c _ _ (fun x => κ.symm_apply_apply x) v)

theorem extE_apply (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) (v : Fin (n + c) → k) :
    extE c κ v = v + Loc.inX k n c (κ (resX c v) - resX c v) := rfl

theorem extE_inv (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) : (extE c κ)⁻¹ = extE c κ⁻¹ :=
  LinearEquiv.ext fun _ => rfl

theorem extE_R1cond (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) : Loc.R1cond k n c (extE c κ) := by
  have h : ∀ i, extE c κ (Loc.eN k (n + c) (n + i)) = Loc.eN k (n + c) (n + i) := by
    intro i
    rw [extE_apply, resX_eN]
    simp
  refine ⟨fun i v hv => ?_, h 0, fun i => ?_⟩
  · rw [extE_apply]
    exact add_mem hv (inX_mem_Ufl c i _)
  · rw [h, sub_self]
    exact zero_mem _

theorem extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) : extE c κ ∈ Loc.R1 k n c :=
  ⟨extE_R1cond c κ, by rw [extE_inv]; exact extE_R1cond c _⟩

theorem extE_inX (κ : (Fin n → k) ≃ₗ[k] (Fin n → k)) (x : Fin n → k) :
    extE c κ (Loc.inX k n c x) = Loc.inX k n c (κ x) := by
  rw [extE_apply, resX_inX, map_sub]
  abel

end Ext

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem mem_sclLat (N : ℕ) (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ LocE.sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * x l) := by
  unfold LocE.sclLat stdAt
  rw [Submodule.mem_comap, mem_localization_standardLattice]
  rfl

omit [StarRing E] in
theorem intAt_nat (m : ℕ) : IntAt P (m : E) := by
  simpa using IntAt.coe P (m : 𝓞 E)

theorem sclLat_le (hq : (q : E) ≠ 0) (N : ℕ) (e : ℕ → ℤ) (p : ℕ → Prop) [DecidablePred p] :
    LocE.sclLat P q N (fun l => e l + if p l then 1 else 0) ≤ LocE.sclLat P q N e := by
  intro x hx
  rw [mem_sclLat] at hx ⊢
  intro l
  have h := hx l
  by_cases hp : p l.1
  · rw [if_pos hp] at h
    have h2 := (intAt_nat P q).mul h
    convert h2 using 1
    rw [zpow_add₀ hq, zpow_one]
    have := zpow_ne_zero (e l.1) hq
    field_simp
  · rw [if_neg hp, add_zero] at h
    exact h

theorem smul_mem_sclLat (hq : (q : E) ≠ 0) (N : ℕ) (e : ℕ → ℤ) (p : ℕ → Prop) [DecidablePred p]
    (x : Sp E N) (hx : (q : E)⁻¹ • x ∈ LocE.sclLat P q N e) :
    x ∈ LocE.sclLat P q N (fun l => e l + if p l then 1 else 0) := by
  rw [mem_sclLat] at hx ⊢
  intro l
  have h := hx l
  rw [Pi.smul_apply, smul_eq_mul] at h
  have := zpow_ne_zero (e l.1) hq
  by_cases hp : p l.1
  · rw [if_pos hp]
    convert h using 1
    rw [zpow_add₀ hq, zpow_one]
    field_simp
  · rw [if_neg hp, add_zero]
    have h2 := (intAt_nat P q).mul h
    convert h2 using 1
    field_simp

theorem bvec_mem (hq : (q : E) ≠ 0) (N : ℕ) (e : ℕ → ℤ) (f : ℕ) :
    ((q : E) ^ e f) • Loc.eN E N f ∈ LocE.sclLat P q N e := by
  rw [mem_sclLat]
  intro l
  rw [Pi.smul_apply, smul_eq_mul]
  unfold Loc.eN
  split_ifs with h
  · rw [h, mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq)]
    simpa using intAt_nat P 1
  · simpa using intAt_nat P 0

theorem mem_flagU {N : ℕ} (L : Submodule (𝓞 E) (Sp E N)) (M : ℕ → Submodule (𝓞 E) (Sp E N)) (e : ℕ → Sp E N)
    (r : ℕ) (st : Set ℕ) (hM : ∀ s, M s ≤ L) (hM' : ∀ s x, (q : E)⁻¹ • x ∈ L → x ∈ M s) (he : ∀ s, e s ∈ L)
    (g : Sp E N ≃ₗ[E] Sp E N) (hg : g ∈ stabL E N L) (hc : ∀ x ∈ L, (q : E)⁻¹ • (g x - x) ∈ L) :
    g ∈ LocE.flagU M e r st := by
  have hs : ∀ s, g ∈ stabL E N (M s) := by
    intro s x
    constructor
    · intro hx
      have h1 := hM' s _ (hc x ((hg x).1 (hM s hx)))
      have := sub_mem hx h1
      rwa [sub_sub_cancel] at this
    · intro hx
      have h1 := hM' s _ (hc x (hM s hx))
      have := add_mem h1 hx
      rwa [sub_add_cancel] at this
  exact ⟨fun s _ => hs s, fun s _ => ⟨hs s, hM' s _ (hc _ (he s))⟩⟩

theorem inX_mem_lamY {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (x : Sp E n) (hx : x ∈ stdAt E n P) :
    Loc.inX E n c x ∈ LocE.lamY P q n c ex := by
  unfold LocE.lamY
  rw [mem_sclLat]
  intro l
  rw [inX_apply]
  split_ifs with h
  · unfold LocE.scE
    rw [if_pos h, zpow_zero, inv_one, one_mul]
    exact (mem_localization_standardLattice P x).1 hx _
  · simpa using intAt_nat P 0

theorem resX_mem {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (v : Sp E (n + c)) (hv : v ∈ LocE.lamY P q n c ex) :
    resX c v ∈ stdAt E n P := by
  unfold LocE.lamY at hv
  rw [mem_sclLat] at hv
  refine (mem_localization_standardLattice P _).2 fun i => ?_
  have h := hv (Fin.castAdd c i)
  unfold LocE.scE at h
  rw [if_pos (by simp), zpow_zero, inv_one, one_mul] at h
  exact h

theorem extE_maps {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P)
    (v : Sp E (n + c)) (hv : v ∈ LocE.lamY P q n c ex) : extE c κ v ∈ LocE.lamY P q n c ex := by
  rw [extE_apply]
  have h := resX_mem P q c ex v hv
  exact add_mem hv (inX_mem_lamY P q c ex _ (sub_mem ((hκ _).2 h) h))

theorem extE_stab {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P) :
    extE c κ ∈ stabL E (n + c) (LocE.lamY P q n c ex) := by
  intro v
  refine ⟨fun hv => ?_, extE_maps P q c ex κ hκ v⟩
  have h := extE_maps P q c ex κ⁻¹ (inv_mem hκ) _ hv
  rw [← extE_inv] at h
  rwa [show (extE c κ)⁻¹ (extE c κ v) = v from LinearEquiv.symm_apply_apply _ v] at h

theorem extE_cong {n : ℕ} (c : ℕ) (ex : ℕ → ℕ) (hd : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (q : E)))
    (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P) (hr : ∀ x ∈ stdAt E n P, redV P (κ x) = redV P x)
    (v : Sp E (n + c)) (hv : v ∈ LocE.lamY P q n c ex) :
    (q : E)⁻¹ • (extE c κ v - v) ∈ LocE.lamY P q n c ex := by
  rw [extE_apply, add_sub_cancel_left, ← map_smul]
  have h := resX_mem P q c ex v hv
  refine inX_mem_lamY P q c ex _ ((mem_localization_standardLattice P _).2 fun i => ?_)
  have h1 := (mem_localization_standardLattice P _).1 (sub_mem ((hκ _).2 h) h) i
  have h2 := (mem_localization_standardLattice P _).1 h i
  have h3 : redP P (κ (resX c v) i) = redP P (resX c v i) := congrFun (hr _ h) i
  have h4 := reduction_add h1 h2
  rw [Pi.sub_apply, sub_add_cancel, h3] at h4
  have h5 := hd _ h1 (by rw [Pi.sub_apply]; exact (add_eq_right.1 h4.symm))
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← div_eq_mul_inv]
  exact h5

omit [StarRing E] in
theorem conj_cong {N : ℕ} (L : Submodule (𝓞 E) (Sp E N)) (g h : Sp E N ≃ₗ[E] Sp E N) (hh : h ∈ stabL E N L)
    (hc : ∀ x ∈ L, (q : E)⁻¹ • (g x - x) ∈ L) : ∀ x ∈ L, (q : E)⁻¹ • ((h⁻¹ * g * h) x - x) ∈ L := by
  intro x hx
  refine (hh _).1 ?_
  rw [map_smul, map_sub, show h ((h⁻¹ * g * h) x) = g (h x) from LinearEquiv.apply_symm_apply _ _]
  exact hc _ ((hh x).2 hx)

end Lat

theorem cong_mem_prCat : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs → (∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E))) → ∀ h : AutY X R j, h ∈ stabL X.E _ (lamYat (Pr := Pr) j w) → ∀ κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j), κ ∈ GLint X.E (R.N j) w → (∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) → κ ∈ prCat (Pr := Pr) sharp j w h := by
  intro X Pr R sharp j w hw hd h hh κ hκ hr
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  unfold lamYat at hh
  rw [if_pos hw] at hh
  refine ⟨extE _ κ, ⟨extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ κ, ?_⟩, extE_inX _ κ⟩
  have e : (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) = h⁻¹ * extE (cOf R j) κ * h := by simp
  show (MulAut.conj h⁻¹).toMonoidHom (extE (cOf R j) κ) ∈ Jat (Pr := Pr) sharp j w
  rw [e]
  have hs := mul_mem (mul_mem (inv_mem hh) (extE_stab w (qOf w) (cOf R j) (fun i => i + 1) κ hκ)) hh
  have hc := conj_cong (qOf w) _ _ h hh (extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr)
  unfold Jat
  rw [if_pos hw]
  split_ifs
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _
  · refine ⟨hs, mem_flagU (qOf w) _ _ _ _ _ (fun s => ?_) (fun s x hx => ?_) (fun s => ?_) _ hs hc⟩
    · exact sclLat_le w _ hq _ _ _
    · exact smul_mem_sclLat w _ hq _ _ _ x hx
    · exact bvec_mem w _ hq _ _ _

end GlobalTheory.CongLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedMuPartInBaseChange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.MuBlock

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem frobEig_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (f : ℝ → ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) ∧
    A.frobEig (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) =
      (L.map fun k => (A.frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((f k : ℝ) : ℂ))).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons k L ih =>
    have hk := (A.unr_tw a (f k)).2 ha
    refine ⟨(A.unr_sum _ _).2 ⟨hk, ih.1⟩, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [A.frobEig_sum _ _ hk ih.1, A.frobEig_tw a _ ha, ih.2]

theorem frobEig_spehLoc (p : Part A.CG) (w : PlE H) (h : A.unr (A.locG p.π w)) :
    A.unr (spehLoc N A p w) ∧ A.frobEig (spehLoc N A p w) =
      ((List.range p.d).map fun k => (A.frobEig (A.locG p.π w)).map
        (· * ((normV w : ℕ) : ℂ) ^ (((((p.d : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum :=
  frobEig_foldr N A _ h (fun k : ℝ => ((p.d : ℝ) - 1) / 2 - k) _

theorem frobEig_isoLoc (Pa : List (Part A.CG)) (w : PlE H) (h : ∀ p ∈ Pa, A.unr (A.locG p.π w)) :
    A.unr (isoLoc N A Pa w) ∧ A.frobEig (isoLoc N A Pa w) =
      (Pa.map fun p => ((List.range p.d).map fun k => (A.frobEig (A.locG p.π w)).map
        (· * ((normV w : ℕ) : ℂ) ^ (((((p.d : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum := by
  induction Pa with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons p Pa ih =>
    have ih' := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := frobEig_spehLoc N A p w (h p (List.mem_cons_self ..))
    refine ⟨(A.unr_sum _ _).2 ⟨hp.1, ih'.1⟩, ?_⟩
    change A.frobEig (A.lpSum (spehLoc N A p w) (isoLoc N A Pa w)) = _
    rw [A.frobEig_sum _ _ hp.1 ih'.1, hp.2, ih'.2]
    simp only [List.map_cons, List.sum_cons]

theorem frobEig_eq_single {w : PlE H} (a : A.LP w) (hu : A.unr a) (hd : A.lpDim a = 1) :
    ∃ c, A.frobEig a = {c} :=
  Multiset.card_eq_one.1 (by rw [A.frobEig_card a hu, hd])

theorem absNorm_eq_normV (w : PlE H) : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem exists_split_not_mem (hC : ∀ Sg : Set (PlE H), Sg.Finite →
    closure {σ : G H.E N.Om | ∃ w ∉ Sg, IsSplitPl H w ∧ ∃ B : ValuationSubring N.Om,
      IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ} = Set.univ)
    (S : Set (PlE H)) (hS : S.Finite) : ∃ w ∉ S, IsSplitPl H w := by
  by_contra hn
  push_neg at hn
  have h := hC S hS
  have he : {σ : G H.E N.Om | ∃ w ∉ S, IsSplitPl H w ∧ ∃ B : ValuationSubring N.Om,
      IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ} = ∅ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨w, hw, hs, -⟩
    exact hn w hw hs
  rw [he, closure_empty] at h
  exact Set.empty_ne_univ h

end GlobalTheory.MuBlock

namespace GlobalTheory.MuBlock

end GlobalTheory.MuBlock

namespace GlobalTheory.MuBlock

end GlobalTheory.MuBlock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.TypePrimeUnif

theorem _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq {X : _root_.Formalism.L2.Col.Fields} (hX : X.Ok) {Pr : _root_.Formalism.L2.Col.Primes X}
    (hP : Pr.Ok) (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E))
    (hv : P ∈ Pr.vG i) : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 := by
  classical
  refine ⟨hP.g_mem hv, fun hsq => ?_⟩
  have hdiv : ∀ Q ∈ Pr.vG i, X.conjO (Pr.piG i) ∈ Q.asIdeal := fun Q hQ =>
    _root_.Formalism.L2.Col.decoFin_mem_of_mem_divs (show Q ∈ _root_.Formalism.L2.Col.divs (X.conjO (Pr.piG i)) from hQ)
  have hg1 : 1 < Pr.g i := (hP.g_prime i).one_lt
  have hN : Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)}) = Pr.g i ^ X.f := by
    have h1 : Ideal.absNorm (Ideal.span {Pr.piG i}) * Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)})
        = Pr.g i ^ (2 * X.f) := by
      rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, X.absNorm_nat, hX.rankQ]
    rw [X.absNorm_conjO, ← sq, pow_mul'] at h1
    rw [X.absNorm_conjO]
    exact Nat.pow_left_injective two_ne_zero h1
  have hπP : Pr.piG i ∉ P.asIdeal := fun h => by
    obtain ⟨a, b, hab⟩ := hP.piG_cop i
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left a h) (P.asIdeal.mul_mem_left b (hdiv P hv))
  have hcop : IsCoprime (P.asIdeal ^ 2) (Ideal.span {Pr.piG i}) := by
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := P.isMaximal.eq_of_le h le_sup_left
    exact hπP (by rw [heq]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hP2 : P.asIdeal ^ 2 ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    have h : P.asIdeal ^ 2 ∣ Ideal.span {Pr.piG i} * Ideal.span {X.conjO (Pr.piG i)} := by
      rw [Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, Ideal.dvd_span_singleton]
      exact hsq
    first
      | exact hcop.dvd_of_dvd_mul_left h
      | exact hcop.dvd_of_dvd_mul_right h
  let e : HeightOneSpectrum (𝓞 X.E) → ℕ := fun Q => if Q = P then 2 else 1
  have hall : ∏ Q ∈ Pr.vG i, Q.asIdeal ^ e Q ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    apply Finset.prod_dvd_of_coprime
    · intro Q _ Q' _ hne
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal
        (fun h => hne (HeightOneSpectrum.ext h))
    · intro Q hQ
      by_cases h : Q = P
      · subst h
        simpa [e] using hP2
      · simpa [e, h, Ideal.dvd_span_singleton] using hdiv Q hQ
  have hnorm := map_dvd Ideal.absNorm hall
  rw [map_prod, hN] at hnorm
  have hcount : ∏ Q ∈ Pr.vG i, Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ (X.f + 1) := by
    rw [Finset.prod_congr rfl (fun Q hQ => show Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ e Q by
      rw [map_pow, hP.vG_norm i Q hQ]), Finset.prod_pow_eq_pow_sum]
    congr 1
    have he : ∀ Q, e Q = 1 + if Q = P then 1 else 0 := fun Q => by
      by_cases h : Q = P <;> simp [e, h]
    simp only [he, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.sum_ite_eq', hv, if_true, hP.vG_card i]
  rw [hcount] at hnorm
  have := (Nat.pow_dvd_pow_iff_le_right hg1).mp hnorm
  omega

theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (g : 𝓞 E)
    (h1 : g ∈ w.asIdeal) (h2 : g ∉ w.asIdeal ^ 2) (a : E) (ha : _root_.Formalism.L2.Col.IntAt w a) (h0 : _root_.Formalism.L2.Col.redP w a = 0) :
    _root_.Formalism.L2.Col.IntAt w (a / algebraMap (𝓞 E) E g) := by
  haveI := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have key : ∃ c r, ∃ s ∉ w.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk w.asIdeal s * c = Ideal.Quotient.mk w.asIdeal r := by
    obtain ⟨r, s, hs, hsr⟩ := ha
    have hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact ⟨(Ideal.Quotient.mk w.asIdeal s)⁻¹ * Ideal.Quotient.mk w.asIdeal r, r, s, hs, hsr,
      mul_inv_cancel_left₀ hs0 _⟩
  unfold _root_.Formalism.L2.Col.redP at h0
  rw [dite_eq_left key] at h0
  have hspec := key.choose_spec
  rw [h0] at hspec
  obtain ⟨r, s, hs, hsr, hc⟩ := hspec
  rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc
  obtain ⟨J, hJ⟩ := (Ideal.dvd_span_singleton (I := w.asIdeal) (x := g)).mpr h1
  have hJw : ¬ J ≤ w.asIdeal := fun hle => h2 (by
    rw [sq]
    exact Ideal.mul_mono_right hle (hJ ▸ Ideal.mem_span_singleton_self g))
  obtain ⟨t, htJ, htw⟩ := Set.not_subset.mp hJw
  have hrt : r * t ∈ Ideal.span {g} := hJ ▸ Ideal.mul_mem_mul hc htJ
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hrt
  have hg0 : algebraMap (𝓞 E) E g ≠ 0 := by
    intro h
    apply h2
    rw [(IsFractionRing.injective (𝓞 E) E) (h.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨x, s * t, fun hst => (w.isPrime.mem_or_mem hst).elim hs htw, ?_⟩
  have hxE : algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g =
      algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E t := by
    rw [← map_mul, ← map_mul, hx]
  have hmain : algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a =
      algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g := by
    linear_combination algebraMap (𝓞 E) E t * hsr - hxE
  calc algebraMap (𝓞 E) E (s * t) * (a / algebraMap (𝓞 E) E g)
      = algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a / algebraMap (𝓞 E) E g := by
        rw [map_mul]; ring
    _ = algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g / algebraMap (𝓞 E) E g := by rw [hmain]
    _ = algebraMap (𝓞 E) E x := mul_div_cancel_right₀ _ hg0

theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_qOf : ∀ (X : _root_.Formalism.L2.Col.Fields) (Pr : _root_.Formalism.L2.Col.Primes X), X.Ok → Pr.Ok →
    ∀ w ∈ Pr.vGs, ∀ a : X.E, _root_.Formalism.L2.Col.IntAt w a →
    _root_.Formalism.L2.Col.redP w a = 0 → _root_.Formalism.L2.Col.IntAt w (a / (_root_.Formalism.L2.Col.qOf w : X.E)) := by
  classical
  intro X Pr hX hP w hw a ha h0
  have hw' : w ∈ Pr.vG 0 ∪ Pr.vG 1 := hw
  obtain ⟨i, hv⟩ : ∃ i, w ∈ Pr.vG i := by
    rcases Finset.mem_union.mp hw' with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hq : (_root_.Formalism.L2.Col.qOf w : X.E) = algebraMap (𝓞 X.E) X.E ((Pr.g i : ℕ) : 𝓞 X.E) := by
    unfold _root_.Formalism.L2.Col.qOf
    rw [map_natCast, hP.vG_norm i w hv]
  have hgw := _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hP i w hv
  rw [hq]
  exact _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq w _ hgw.1 hgw.2 a ha h0

end GlobalTheory.TypePrimeUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDivLatticeQuotient
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

theorem exists_mem_one_sub_loc_dvd {R : Type} [CommRing R] [IsDedekindDomain R] (S : Finset (HeightOneSpectrum R))
    (I : Ideal R) (hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal) (c : R) [Finite (R ⧸ Ideal.span {c})] :
    ∃ s ∈ I, ∃ t r : R, (∀ P ∈ S, t ∉ P.asIdeal) ∧ t * (1 - s) = c * r := by
  have h1 : I ⊔ (⨅ P ∈ S, P.asIdeal) = ⊤ := by
    refine Ideal.sup_iInf_eq_top fun P hP => ?_
    obtain ⟨s, hs, hsP⟩ := hI P hP
    by_contra hne
    have := P.isMaximal.eq_of_le hne le_sup_right
    exact hsP (this ▸ (le_sup_left : I ≤ I ⊔ P.asIdeal) hs)
  have h2 : (1 : R) ∈ I ⊔ (⨅ P ∈ S, P.asIdeal) := h1 ▸ Submodule.mem_top
  obtain ⟨s0, hs0, π, hπ, hsum⟩ := Submodule.mem_sup.1 h2
  have hπ' : ∀ P ∈ S, π ∈ P.asIdeal := by
    intro P hP
    exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hπ P) hP
  have key : ∃ i j : ℕ, i < j ∧ Ideal.Quotient.mk (Ideal.span {c}) (π ^ i) = Ideal.Quotient.mk (Ideal.span {c}) (π ^ j) := by
    obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun i : ℕ => Ideal.Quotient.mk (Ideal.span {c}) (π ^ i))
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact ⟨i, j, h', h⟩
    · exact ⟨j, i, h', h.symm⟩
  obtain ⟨i, j, hij, h⟩ := key
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨1 - π ^ i, ?_, 1 - π ^ (d + 1), r, ?_, ?_⟩
  · have : (1 - π) ∣ 1 - π ^ i := by simpa using sub_dvd_pow_sub_pow (1 : R) π i
    obtain ⟨u, hu⟩ := this
    have hs : 1 - π = s0 := by rw [← hsum]; ring
    rw [hu, hs]
    exact I.mul_mem_right _ hs0
  · intro P hP hmem
    have : π ^ (d + 1) ∈ P.asIdeal := P.asIdeal.pow_mem_of_mem (hπ' P hP) _ (Nat.succ_pos d)
    have h1 : (1 : R) ∈ P.asIdeal := by simpa using P.asIdeal.add_mem hmem this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · rw [← hr]; ring

theorem finite_divLat_quot_mulLat_homAt :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (cA cB : ℕ), Submodule.IsFullLattice E N → Submodule.IsLattice E N' → 0 < cA → 0 < cB → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) := by
  intro E _ _ _ a b S N N' cA cB hN hN' hA hB
  classical
  obtain ⟨G, hG⟩ := hN.fg
  have hA' : (cA : E) ≠ 0 := by exact_mod_cast hA.ne'
  have hB' : (cB : E) ≠ 0 := by exact_mod_cast hB.ne'
  have memD : ∀ x : HomE E a b, x ∈ divLat cA (homAt S N N') ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, (cA : 𝓞 E) • x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  have memM : ∀ x : HomE E a b, x ∈ mulLat cB (homAt S N N') ↔
      ∃ h ∈ homAt S N N', (cB : 𝓞 E) • h = x := fun x => Iff.rfl
  have memH : ∀ x : HomE E a b, x ∈ homAt S N N' ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  let ev : HomE E a b →ₗ[𝓞 E] (G → Sp E b) :=
    { toFun := fun x g => (cA : 𝓞 E) • x g
      map_add' := by intro x y; funext g; simp
      map_smul' := by intro r x; funext g; simp [smul_comm r] }
  have ev_inj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hsp : Submodule.span E (G : Set (Sp E a)) = ⊤ := by
      rw [← hN.span_eq_top, ← hG, Submodule.span_span_of_tower]
    refine LinearMap.ext_on hsp fun g hg => ?_
    have := congrFun hx ⟨g, hg⟩
    have h2 : (cA : E) • x g = 0 := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact this
    simpa [hA'] using (smul_eq_zero.1 h2).resolve_left hA'
  let T : Submodule (𝓞 E) (G → Sp E b) := Submodule.pi Set.univ fun _ => N'
  have hT : T.FG := Submodule.fg_pi fun _ => hN'.fg
  let Z : Submodule (𝓞 E) (HomE E a b) := T.comap ev
  have memZ : ∀ x : HomE E a b, x ∈ Z ↔ ∀ g : G, (cA : 𝓞 E) • x g ∈ N' := fun x =>
    ⟨fun h g => h g trivial, fun h g _ => h g⟩
  have hZ : Z.FG := by
    have : Module.Finite (𝓞 E) T := Module.Finite.iff_fg.2 hT
    have : Module.Finite (𝓞 E) Z := Module.Finite.of_injective (ev.restrict (p := Z) (q := T) fun x hx => hx) (by
      intro x y hxy
      exact Subtype.ext (ev_inj (congrArg Subtype.val hxy)))
    exact Module.Finite.iff_fg.1 this
  have hZD : Z ≤ divLat cA (homAt S N N') := by
    intro x hx
    rw [memD]
    intro P hP y hy
    obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
    have : ∀ w ∈ N, (cA : 𝓞 E) • x w ∈ N' := by
      intro w hw
      rw [← hG] at hw
      induction hw using Submodule.span_induction with
      | mem g hg => exact (memZ x).1 hx ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => rw [map_add (f := _), smul_add]; exact N'.add_mem hu hv
      | smul r u _ hu => rw [LinearMap.map_smul_of_tower, smul_comm]; exact N'.smul_mem r hu
    refine (mem_locP P N' _).2 ⟨s, hs, ?_⟩
    have h := this _ hsy
    rwa [LinearMap.map_smul_of_tower, smul_comm] at h
  have : Module.Finite (𝓞 E) Z := Module.Finite.iff_fg.2 hZ
  have hc : ((cB : 𝓞 E) * cA) ≠ 0 := by
    have : cB * cA ≠ 0 := by positivity
    exact_mod_cast this
  have : Finite (𝓞 E ⧸ Ideal.span {(cB : 𝓞 E) * cA}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hc)
  have hsurj : Function.Surjective
      (((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let I : Ideal (𝓞 E) := Z.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
    have hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal := by
      intro P hP
      have h1 : ∀ g : G, ∃ s ∉ P.asIdeal, s • (cA : 𝓞 E) • x g ∈ N' := fun g =>
        (mem_locP P N' _).1 ((memD x).1 hx P hP g (le_locP P N (hG ▸ Submodule.subset_span g.2)))
      choose f hf hf' using h1
      refine ⟨∏ g, f g, ?_, ?_⟩
      · show (∏ g, f g) • x ∈ Z
        rw [memZ]
        intro g
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), LinearMap.smul_apply, smul_comm, mul_smul]
        exact N'.smul_mem _ (hf' g)
      · intro h
        have := P.isPrime
        obtain ⟨g, _, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
        exact hf g hg
    obtain ⟨s, hs, t, r, ht, htr⟩ := exists_mem_one_sub_loc_dvd S I hI ((cB : 𝓞 E) * cA)
    refine ⟨⟨s • x, hs⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show x - s • x ∈ mulLat cB (homAt S N N')
    have hBinv : ∀ {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] (w : W),
        (cB : 𝓞 E) • (cB : E)⁻¹ • w = w := by
      intro W _ _ _ w
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hB', one_smul]
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x - s • x), ?_, hBinv _⟩
    rw [memH]
    intro P hP y hy
    obtain ⟨u, hu, huy⟩ := (mem_locP P N' _).1 ((memD x).1 hx P hP y hy)
    refine (mem_locP P N' _).2 ⟨u * t, fun h => (P.isPrime.mem_or_mem h).elim hu (ht P hP), ?_⟩
    have e1 : t • ((cB : E)⁻¹ • (x - s • x)) y = r • (cA : 𝓞 E) • x y := by
      have e2 : (x - s • x) y = (1 - s) • x y := by simp [sub_smul]
      rw [LinearMap.smul_apply, smul_comm, e2, smul_smul t, htr, mul_assoc, mul_smul, smul_comm, hBinv, mul_comm, mul_smul]
    rw [mul_smul, e1, smul_comm]
    exact N'.smul_mem r huy
  have := Module.Finite.of_surjective _ hsurj
  have : Module.Finite ℤ (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
    Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion _ ?_
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨⟨((cB * cA : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
  rw [Submonoid.mk_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  show ((cB * cA : ℕ) : 𝓞 E) • x ∈ mulLat cB (homAt S N N')
  rw [memM]
  exact ⟨(cA : 𝓞 E) • x, hx, by rw [smul_smul, Nat.cast_mul]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtNatCast
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.GO.ChRoot

section Loc

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_natCast (k : ℕ) : IntAt P (k : E) := by simpa using IntAt.coe P (k : 𝓞 E)

theorem intAt_zero' : IntAt P (0 : E) := by simpa using intAt_natCast (P := P) 0

theorem intAt_one' : IntAt P (1 : E) := by simpa using intAt_natCast (P := P) 1

theorem qOf_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

variable [StarRing E]

theorem mem_stdAt' {n : ℕ} {x : Sp E n} : x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

theorem mem_lamY_zero {q n c : ℕ} {x : Sp E (n + c)} : x ∈ LocE.lamY P q n c 0 ↔ x ∈ stdAt E (n + c) P := by
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt', mem_stdAt']
  refine forall_congr' fun i => ?_
  simp [LocE.scE]

theorem eN_mem {N i : ℕ} : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt']
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one'
  · exact intAt_zero'

theorem intAt_n1Arg {n c : ℕ} (a : E) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (h : ∀ x ∈ stdAt E (n + c) P, a • r x ∈ stdAt E (n + c) P) : IntAt P (a * Loc.n1Arg r) := by
  unfold Loc.n1Arg
  rw [Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt'.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero'

omit [StarRing E] in
theorem unitV_root {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) (h : LocE.unitV χ a ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ LocE.unitV χ a ^ k = 1 := by
  unfold LocE.unitV at h ⊢
  split_ifs at h ⊢ with hu
  · have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
    refine ⟨Nat.card (𝓞 E ⧸ P.asIdeal)ˣ, Nat.card_pos, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  · exact absurd rfl h

end Loc

theorem psi_root {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) (x : X.E)
    (hx : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * x)) : c.psi P x ^ (qOf P.1 ^ c.D P) = 1 := by
  have key : ∀ k : ℕ, c.psi P ((k : X.E) * x) = c.psi P x ^ k := by
    intro k
    induction k with
    | zero => simpa using hc.psi_int P 0 intAt_zero'
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ hx, ih, pow_succ]
      rw [mul_left_comm]
      exact (intAt_natCast k).mul hx
  rw [← key]
  exact hc.psi_int P _ (by simpa using hx)

theorem lam_root {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j)
    (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (hP : P.1 ∉ Pr.vGs) (g : (L.levQ j b P).H) :
    ∃ k : ℕ, 0 < k ∧ (L.levQ j b P).lam g ^ k = 1 := by
  classical
  have hg := Subgroup.mem_subgroupOf.1 ((hL.grpQ j b P).le g.2)
  obtain ⟨r, hr, hrg⟩ := hg
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  obtain ⟨h, hh⟩ : ∃ h, h = L.h j b P' := ⟨_, rfl⟩
  have hχ : (((L.levQ j b P).lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P' (L.h j b P') r := hL.chrQ j b P g r hr hrg
  replace hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h := hh ▸ hr
  rw [← hh] at hχ
  have hb := hL.boundQ j b P' hP
  have hD := hL.depthQ' P' hP
  have hm := hL.hm
  simp only [lamYat, show P'.1 ∉ Pr.vGs from hP, if_false, mem_lamY_zero] at hb
  have hκ := hr.2
  simp only [Jat, hP, if_false] at hκ
  have hκ' : ∀ x, (h⁻¹ * r * h) x ∈ stdAt X.E _ P.1 ↔ x ∈ stdAt X.E _ P.1 := by
    intro x
    exact hκ.1 x
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ j * Loc.n1Arg r) := by
    refine intAt_n1Arg _ r fun x hx => ?_
    have h1 := (hb _ ((hκ' _).2 (hb x hx).1)).2
    have h2 : h ((h⁻¹ * r * h) (h⁻¹ x)) = r x := by
      change (h * (h⁻¹ * r * h) * h⁻¹) x = r x
      congr 1
      group
    rwa [← hh, h2] at h1
  have hint' : IntAt P'.1 ((qOf P'.1 : X.E) ^ cst.D P' * Loc.n1Arg r) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P' = d + j := ⟨cst.D P' - j, by omega⟩
    rw [hd, pow_add, mul_assoc, ← Nat.cast_pow]
    exact (intAt_natCast _).mul hint
  have h1 := psi_root hL.cst_ok P' _ hint'
  simp only [chiInv, lamRow, show P'.1 ∉ Pr.vGs from hP, if_false, LocE.lamQB] at hχ
  have hne := ((L.levQ j b P).lam g).ne_zero
  rw [hχ] at hne
  obtain ⟨k, hk, h2⟩ := unitV_root _ _ (fun h0 => right_ne_zero_of_mul hne (inv_eq_zero.2 h0))
  refine ⟨qOf P'.1 ^ cst.D P' * k, Nat.mul_pos (pow_pos (qOf_pos _) _) hk, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hχ, mul_pow, inv_pow, inv_pow, pow_mul, h1, one_pow, mul_comm _ k, pow_mul, h2, one_pow]
  simp

end GlobalTheory.GO.ChRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatumStatement
open Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitEx_every_datum : ∀ D : D7, Formalism.L2.SplitEx D := by
  first | exact @GlobalTheory.SplitConjPlace.splitEx_all | exact GlobalTheory.SplitConjPlace.splitEx_all | (intros; apply GlobalTheory.SplitConjPlace.splitEx_all <;> assumption)
end
