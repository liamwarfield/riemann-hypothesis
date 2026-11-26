module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransportSymm
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.GlobBc

universe w w'

theorem tens_transport {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f) : Tens R f₁ := by
  obtain ⟨g, hg⟩ := hT
  let c : (∀ i, N i ⊗[R] M₁ i) ≃+ (∀ i, N i ⊗[R] M i) :=
    AddEquiv.piCongrRight fun i => (TensorProduct.congr (LinearEquiv.refl R (N i)) (e i).symm).toAddEquiv
  refine ⟨c.trans (g.trans e'), fun i n x => ?_⟩
  have hc : c (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ (e i).symm x) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [c]
    · simp [c, Pi.single_eq_of_ne hk]
  simp only [AddEquiv.trans_apply]
  rw [hc, hg, h, LinearEquiv.apply_symm_apply]

theorem tens_transport_symm {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f₁) : Tens R f :=
  tens_transport (fun i => (e i).symm) e'.symm
    (fun i n x => by rw [AddEquiv.symm_apply_eq, h, LinearEquiv.apply_symm_apply]) hT

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))

def thM : SMor (thP (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))) (thP (nlFun γ 0 X q (κA O I)))
    (algebraMap O A) where
  G := ((nmO γ q).mor 0).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

theorem leC {c : A} {i : ℕ} (hc : c ∈ pdP γ i) (r : ℤ) :
    (thM γ q).LeC c (thFil _ (r - i)) (thFil _ r) := by
  intro T x hx
  have h1 : T.i c ∈ pdP T.δ i := dividedPowerFiltration_map T.compat i hc
  have h2 : x ∈ pdP T.δ (r - i).toNat := hx
  have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ _ _ (Ideal.mul_mem_mul h1 h2)
  exact T.pdPow_anti (by omega) h3

end

abbrev rq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    CH.Mor (sq (sFil Q r) (sFil Q r')) (sq (sFil Q' r) (sFil Q' r')) (RingHom.id _) :=
  (incl h).sq (incl_fil h r) (incl_fil h r')

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) {m : ℕ} (S : GrSplit O γ m)

theorem leS (𝒱 : Set X.Opens) (i : Fin m) (n : S.N i) (r : ℤ) :
    (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r) :=
  fun T x hx => leC γ q (S.mem i n) r T.obj x hx

abbrev mC (𝒱 : Set X.Opens) (r r' : ℤ) (i : Fin m) (n : S.N i) :=
  (smO γ q l s 𝒱).sqC (S.ν i n) (leS γ q l s S 𝒱 i n r) (leS γ q l s S 𝒱 i n r')

def BcAt (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) : Prop :=
  Tens O (N := S.N) (M := fun i => HQ (TO q l s 𝒱) (r - i) (r' - i) j) (M' := HQ (TS γ q l s 𝒱) r r' j)
    fun i n x => (mC γ q l s S 𝒱 r r' i n).pull j x

variable {γ q l s}

theorem st_top {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {p : ℕ} {κ : O →+* R ⧸ J}
    (Q : ObjectProperty (Thick (nlFun δ p X q κ))) (𝒱 : Set X.Opens) : St Q 𝒱 ≤ St Q {⊤} := by
  rintro T ⟨h, V, -, -⟩
  exact ⟨h, ⊤, rfl, fun _ _ => trivial⟩

theorem comm_top (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) (i : Fin m) (n : S.N i) (x) :
    (rq (st_top (TF l s) 𝒱) r r').pull j ((mC γ q l s S {⊤} r r' i n).pull j x) =
    (mC γ q l s S 𝒱 r r' i n).pull j ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j x) := by
  refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (mC γ q l s S {⊤} r r' i n) (rq (st_top (TF l s) 𝒱) r r') j x).1).symm.trans
    (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (rq (st_top (TF l s) 𝒱) (r - i) (r' - i)) (mC γ q l s S 𝒱 r r' i n) j x).1))
  refine CrystallineSemistableComparison.P.prism (σ := algebraMap O A) ((mC γ q l s S {⊤} r r' i n).comp (rq (st_top (TF l s) 𝒱) r r'))
    ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).comp (mC γ q l s S 𝒱 r r' i n)) (𝟙 _) (fun T y => ?_) j x
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  first
    | rfl
    | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)

theorem used_TF {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} (l s : ℕ) :
    Used (TF l s : ObjectProperty (Thick (nlFun δ 0 X q κ))) :=
  Or.inl ⟨rfl, l, s, rfl⟩

theorem bcAt_iff (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ) (j : ℕ) :
    BcAt γ q l s S {⊤} r r' j ↔ BcAt γ q l s S 𝒱 r r' j := by
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup 𝒱 := fun W hW => by rw [h𝒱]; exact le_top
  have bO := (GlobalTheory.T.cech_refinement_cohomology_bijective (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk (⊥ : Ideal O)) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  have bA := (GlobalTheory.T.cech_refinement_cohomology_bijective (γ := γ) (p := 0) (q := q) (κ := κA O I) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  let eO : ∀ i : Fin m, HQ (TO q l s {⊤}) (r - i) (r' - i) j ≃ₗ[O] HQ (TO q l s 𝒱) (r - i) (r' - i) j := fun i =>
    LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j) (bO _ _)
  let eA : HQ (TS γ q l s {⊤}) r r' j ≃+ HQ (TS γ q l s 𝒱) r r' j :=
    (LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) r r').pull j) (bA _ _)).toAddEquiv
  have hcomm : ∀ i n x, eA ((mC γ q l s S {⊤} r r' i n).pull j x) = (mC γ q l s S 𝒱 r r' i n).pull j (eO i x) :=
    fun i n x => comm_top S 𝒱 r r' j i n x
  exact ⟨tens_transport eO eA hcomm, tens_transport_symm eO eA hcomm⟩

end

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {m : ℕ} (S : GrSplit O γ m)

abbrev thO (q : X ⟶ Spec (CommRingCat.of O)) (r r' : ℤ) :
    Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) ⥤ ModuleCat.{0} O :=
  sq (thFil _ r) (thFil _ r')

abbrev thS (r r' : ℤ) : Thick (nlFun γ 0 X q (κA O I)) ⥤ ModuleCat.{0} A :=
  sq (thFil _ r) (thFil _ r')

abbrev tM (r r' : ℤ) (i : Fin m) (n : S.N i) : CH.Mor (thO q (r - i) (r' - i)) (thS γ q r r') (algebraMap O A) :=
  (thM γ q).sqC (S.ν i n) (leC γ q (S.mem i n) r) (leC γ q (S.mem i n) r')

theorem tM_add (r r' : ℤ) (i : Fin m) (n n' : S.N i) (T) (x) :
    (tM γ q S r r' i (n + n')).τ T x = (tM γ q S r r' i n).τ T x + (tM γ q S r r' i n').τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (n + n')) * z' = algebraMap A B (S.ν i n) * z' + algebraMap A B (S.ν i n') * z' := by
    rw [map_add (f := _), map_add (f := _), add_mul]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

theorem tM_smul (r r' : ℤ) (i : Fin m) (c : O) (n : S.N i) (T) (x) :
    (tM γ q S r r' i (c • n)).τ T x = algebraMap O A c • (tM γ q S r r' i n).τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (c • n)) * z' = algebraMap O A c • (algebraMap A B (S.ν i n) * z') := by
    rw [map_smul, Algebra.smul_def c, map_mul, mul_assoc, Algebra.smul_def (algebraMap O A c)]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

end

theorem main : KH.GlobBcSt → BcOn True → BcOn False := by
  intro hG hT O A _ _ _ I γ l s m hO hA S X q 𝒱 hc r r' hrr hr's ha hb j
  obtain ⟨U, h𝒱⟩ : Nonempty (Cov q) ∧ sSup 𝒱 = ⊤ := by
    rcases hc with ⟨h, -⟩ | ⟨-, h⟩
    · exact h.elim
    · exact h
  obtain ⟨U⟩ := U
  have hU : sSup (Set.range U.U) = ⊤ := by rw [sSup_range]; exact U.cover
  have hmem : ∀ (𝒲 : Set X.Opens) (T), St (TF l s) 𝒲 T → St (TF l s) 𝒲 ((((nmO γ q).mor 0).functor).obj T) :=
    fun 𝒲 T h => nmO_mem γ q l s 𝒲 T h
  have key : ∀ j, BcAt γ q l s S (Set.range U.U) r r' j := fun j =>
    hG (O := O) (R := O) (I := ⊥) (γ := dividedPowersBot O) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥)
      (O' := O) (R' := A) (I' := I) (γ' := γ) (p' := 0) (X' := X) (q' := q) (κ' := κA O I)
      (Λ := O) (Λ' := A) (σ := algebraMap O A) ((nmO γ q).mor 0).functor S.N
      (fun i => thO q (r - i) (r' - i)) (thS γ q r r')
      (fun i n T => (tM γ q S r r' i n).τ T) (fun i n {T T'} φ x => (tM γ q S r r' i n).nat φ x)
      (fun i n n' T x => tM_add γ q S r r' i n n' T x) (fun i c n T x => tM_smul γ q S r r' i c n T x)
      (TF l s) (TF l s) U.U U.U (fun α T h => hmem _ T h) (fun S' T h => hmem _ T h) (fun T h => hmem _ T h)
      (fun S' hS' j => by
        obtain ⟨α, hα⟩ := hS'
        obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S', U.U α) ≤ U.U α) (U.inter S' ⟨α, hα⟩)
        exact hT γ l s m hO hA S q {⨅ α ∈ S', U.U α} (Or.inl ⟨trivial, _, _, rfl, ⟨c'⟩⟩) r r' hrr hr's
          (fun i n => leS γ q l s S _ i n r) (fun i n => leS γ q l s S _ i n r') j) j
  exact (bcAt_iff S 𝒱 h𝒱 r r' j).1 ((bcAt_iff S (Set.range U.U) hU r r' j).2 (key j))

end GlobalTheory.CompanionTheory.GlobBc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParity
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame.SignWord

variable {n : ℕ}

def sg (b : Bool) : ℤ := cond b 1 (-1)

theorem step_sign (a b c e : Bool) (k : ℕ) (h : Xor (a = b) (c = e)) :
    sg c * sg a * (-1 : ℤ) ^ k = sg e * sg b * (-1 : ℤ) ^ (k + 1) := by
  cases a <;> cases b <;> cases c <;> cases e <;> simp_all [Xor, sg, pow_succ]

theorem sign_left (b : Bool) (k : ℕ) (h : sg b * sg true * (-1 : ℤ) ^ k = 1) :
    b = true ↔ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

theorem sign_right (b : Bool) (k : ℕ) (h : sg b * sg false * (-1 : ℤ) ^ k = 1) :
    b = true ↔ ¬ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

theorem sum_neg_one_pow (n : ℕ) : ∑ p ∈ range (2 * n + 1), (-1 : ℤ) ^ p = 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    have h : (-1 : ℤ) ^ (2 * k + 1) = -1 := (odd_two_mul_add_one k).neg_one_pow
    have h' : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1 := by rw [pow_succ, h]; norm_num
    rw [h, h']; norm_num

theorem above_lt_of_lt (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) {r : ℝ}
    (x : Fin (n + 1) ⊕ Fin n) (h : r < Sum.elim d d' x) :
    above d d' (Sum.elim d d' x) < above d d' r := by
  unfold above
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨x, ?_, ?_⟩
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact h.trans hz
  · simpa using h
  · simp

theorem above_lt_card (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (x : Fin (n + 1) ⊕ Fin n) :
    above d d' (Sum.elim d d' x) < 2 * n + 1 := by
  have h : above d d' (Sum.elim d d' x) < (univ : Finset (Fin (n + 1) ⊕ Fin n)).card := by
    unfold above
    apply Finset.card_lt_card
    exact Finset.filter_ssubset.2 ⟨x, mem_univ _, by simp⟩
  have h2 : (univ : Finset (Fin (n + 1) ⊕ Fin n)).card = 2 * n + 1 := by
    simp [Finset.card_univ, Fintype.card_sum]; ring
  omega

theorem above_injective (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    Function.Injective fun x => above d d' (Sum.elim d d' x) := by
  intro x y hxy
  simp only at hxy
  rcases lt_trichotomy (Sum.elim d d' x) (Sum.elim d d' y) with h | h | h
  · have := above_lt_of_lt d d' y h
    omega
  · exact hv h
  · have := above_lt_of_lt d d' x h
    omega

theorem above_image (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    (univ : Finset (Fin (n + 1) ⊕ Fin n)).image (fun x => above d d' (Sum.elim d d' x)) =
      range (2 * n + 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨x, -, rfl⟩ := mem_image.1 hp
    exact mem_range.2 (above_lt_card d d' x)
  · rw [Finset.card_image_of_injective _ (above_injective d d' hv)]
    simp [Finset.card_univ, Fintype.card_sum]
    omega

theorem sum_above (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    ∑ x : Fin (n + 1) ⊕ Fin n, (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = 1 := by
  have h := sum_neg_one_pow n
  rw [← above_image d d' hv,
    Finset.sum_image (fun x _ y _ h => above_injective d d' hv h)] at h
  exact h

theorem sum_signs (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1))
    (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e) :
    ∑ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft = 1 := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i, sg (ε i) = ∑ a, sg (ε' a) + 1 := by
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    have h0 : sg (ε (e (Sum.inr ()))) = 1 := by
      have : ε (e (Sum.inr ())) = true := hf.1
      simp [this, sg]
    simp [hf.2, h0]
  have hl : sg true = 1 := rfl
  have hr : sg false = -1 := rfl
  simp [hl, hr, h1]

theorem step_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') (x y : Fin (n + 1) ⊕ Fin n)
    (hxy : above d d' (Sum.elim d d' y) = above d d' (Sum.elim d d' x) + 1) :
    sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
      sg (Sum.elim ε ε' y) * sg y.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' y) := by
  have hlt : Sum.elim d d' y < Sum.elim d d' x := by
    rcases lt_trichotomy (Sum.elim d d' y) (Sum.elim d d' x) with h | h | h
    · exact h
    · rw [h] at hxy; omega
    · have := above_lt_of_lt d d' y h
      omega
  have hno : ∀ z, ¬ (Sum.elim d d' y < Sum.elim d d' z ∧ Sum.elim d d' z < Sum.elim d d' x) := by
    rintro z ⟨h1, h2⟩
    have a1 := above_lt_of_lt d d' z h1
    have a2 := above_lt_of_lt d d' x h2
    omega
  have hstep := hw x y hlt hno
  rw [hxy]
  exact step_sign _ _ _ _ _ hstep

theorem const_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    ∃ T : ℤ, ∀ x : Fin (n + 1) ⊕ Fin n,
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = T := by
  have him := above_image d d' hv
  have hsurj : ∀ p < 2 * n + 1, ∃ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p := by
    intro p hp
    have : p ∈ (univ : Finset (Fin (n + 1) ⊕ Fin n)).image
        (fun x => above d d' (Sum.elim d d' x)) := by
      rw [him]; exact mem_range.2 hp
    obtain ⟨x, -, hx⟩ := mem_image.1 this
    exact ⟨x, hx⟩
  obtain ⟨x0, hx0⟩ := hsurj 0 (by omega)
  refine ⟨sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0), ?_⟩
  have key : ∀ p : ℕ, ∀ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p →
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
        sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0) := by
    intro p
    induction p with
    | zero =>
      intro x hx
      have : x = x0 := above_injective d d' hv (by simp only [hx, hx0])
      rw [this]
    | succ k ih =>
      intro x hx
      have hk : k < 2 * n + 1 := by
        have := above_lt_card d d' x
        omega
      obtain ⟨y, hy⟩ := hsurj k hk
      rw [← ih y hy]
      exact (step_letters ε d ε' d' hv hw y x (by rw [hx, hy])).symm
  exact fun x => key _ x rfl

theorem heSign (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e)
    (hv : Function.Injective (Sum.elim d d')) (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧
      ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  obtain ⟨T, hT⟩ := const_letters ε d ε' d' hv hw
  have hsum : T = 1 := by
    have h1 : ∀ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft =
        T * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) := by
      intro x
      rw [← hT x]
      have hp : ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) *
          ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) = 1 := by
        rw [← mul_pow]; simp
      rw [mul_assoc, hp, mul_one]
    have h2 := sum_signs ε ε' e hf
    simp_rw [h1] at h2
    rw [← Finset.mul_sum, sum_above d d' hv] at h2
    simpa using h2
  subst hsum
  refine ⟨fun i => sign_left _ _ (by simpa using hT (Sum.inl i)),
    fun j => sign_right _ _ (by simpa using hT (Sum.inr j))⟩

end GlobalTheory.CompanionTheory.RgHeFrame.SignWord
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParityStatement
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interlacing_signature_parity : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), PositivityTheory.UnitaryDecomposition.Fits ε ε' e → Function.Injective (Sum.elim d d') → PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d' → (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧ ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | exact GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign <;> assumption)
end
end
