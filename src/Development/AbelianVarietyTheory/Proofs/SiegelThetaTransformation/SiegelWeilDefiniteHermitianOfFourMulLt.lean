module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsGoodSplitPrimeCmField
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TwistedSiegelWeilDifferenceBounded
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeckeRelationAdmissibleFamilyPointwise

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilFormulaDegreeSucc
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumNb
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumNb
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace NbAvg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def nbIn (M : ℕ) (P : Ideal (𝓞 E)) (A B : Lt E n) : Set (Lt E n) :=
  {X | X ∈ Nb M P A ∧ ∃ h ∈ DH E n M, Moves h B X}

def carry (M : ℕ) (P : Ideal (𝓞 E)) (A B : Lt E n) : Set (Matrix (Fin n) (Fin n) E) :=
  {h | h ∈ DH E n M ∧ ∃ X ∈ Nb M P A, Moves h B X}

theorem moves_unique {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) {B X Y : Lt E n}
    (h1 : Moves h B X) (h2 : Moves h B Y) : X = Y := by
  have hu' : h * ccT h = 1 := mul_eq_one_comm.1 hu
  ext w
  have hw : h *ᵥ (ccT h *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]
  have key := (h1 (ccT h *ᵥ w)).symm.trans (h2 (ccT h *ᵥ w))
  rwa [hw] at key

private theorem one_mem_UJset' {M : ℕ} : (1 : Matrix (Fin n) (Fin n) E) ∈ DH E n M := by
  refine ⟨?_, 1, one_pos, Nat.coprime_one_left _, 0, fun k i => ?_, by simp⟩
  · have h1 : ccT (1 : Matrix (Fin n) (Fin n) E) = 1 := by
      unfold ccT
      rw [Matrix.map_one _ (by simp [cc]) (by simp [cc]), Matrix.transpose_one]
    rw [h1, mul_one]
  · rw [Matrix.zero_apply]
    exact isIntegral_zero

private theorem eq_one_of_mem_DH_zero {h : Matrix (Fin n) (Fin n) E} (hh : h ∈ DH E n 0) : h = 1 := by
  obtain ⟨-, s, -, hs, y, -, e⟩ := hh
  rw [(Nat.coprime_zero_right _).1 hs] at e
  simpa [sub_eq_zero] using e

private theorem eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq {M : ℕ} {g : Matrix (Fin n) (Fin n) E} (hg : g ∈ DH E n M) :
    ccT g ∈ DH E n M ∧ ∀ h ∈ DH E n M, g * h ∈ DH E n M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · obtain rfl := eq_one_of_mem_DH_zero hg
    refine ⟨?_, fun h hh => by rw [one_mul]; exact hh⟩
    have hc := hg.1
    rw [mul_one] at hc
    rw [hc]
    exact hg
  · exact (finite_cls_and_stab E n M hM).2.2.2.1.2 g hg

theorem transporter_eq {M : ℕ} {g : Matrix (Fin n) (Fin n) E} (hg : g ∈ DH E n M) {B X : Lt E n}
    (m : Moves g B X) :
    {h ∈ DH E n M | Moves h B X} = (fun h => g * h) '' {h ∈ DH E n M | Moves h B B} := by
  have hgg : g * ccT g = 1 := mul_eq_one_comm.1 hg.1
  ext h
  constructor
  · rintro ⟨hh, mh⟩
    refine ⟨ccT g * h, ⟨(eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hg).1).2 h hh, fun v => ?_⟩, ?_⟩
    · rw [mh v, m ((ccT g * h) *ᵥ v), Matrix.mulVec_mulVec, ← mul_assoc, hgg, one_mul]
    · show g * (ccT g * h) = h
      rw [← mul_assoc, hgg, one_mul]
  · rintro ⟨k, ⟨hk, mk⟩, rfl⟩
    refine ⟨(eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hg).2 k hk, fun v => ?_⟩
    show v ∈ B ↔ (g * k) *ᵥ v ∈ X
    rw [mk v, m (k *ᵥ v), Matrix.mulVec_mulVec]

theorem mul_inj {g : Matrix (Fin n) (Fin n) E} (hu : ccT g * g = 1) :
    Function.Injective fun h : Matrix (Fin n) (Fin n) E => g * h := by
  intro a b hab
  have key := congrArg (fun x => ccT g * x) hab
  simpa only [← mul_assoc, hu, one_mul] using key

theorem ncard_carry {M : ℕ} {P : Ideal (𝓞 E)} {A B : Lt E n} (hN : (Nb M P A).Finite)
    (hB : {h ∈ DH E n M | Moves h B B}.Finite) :
    (carry M P A B).ncard = (nbIn M P A B).ncard * {h ∈ DH E n M | Moves h B B}.ncard := by
  classical
  have memC : ∀ h, h ∈ carry M P A B ↔ h ∈ DH E n M ∧ ∃ X ∈ Nb M P A, Moves h B X :=
    fun _ => Iff.rfl
  have memN : ∀ X, X ∈ nbIn M P A B ↔ X ∈ Nb M P A ∧ ∃ h ∈ DH E n M, Moves h B X :=
    fun _ => Iff.rfl
  have hex : ∀ X ∈ nbIn M P A B, ∃ g ∈ DH E n M, Moves g B X := fun X hX => ((memN X).1 hX).2
  choose! g hg hgm using hex
  have hmv : ∀ X ∈ nbIn M P A B, ∀ k, Moves k B B → Moves (g X * k) B X := by
    intro X hX k mk v
    rw [mk v, hgm X hX (k *ᵥ v), Matrix.mulVec_mulVec]
  let F : Lt E n × Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E := fun p => g p.1 * p.2
  have himg : F '' (nbIn M P A B ×ˢ {h ∈ DH E n M | Moves h B B}) = carry M P A B := by
    ext h
    constructor
    · rintro ⟨⟨X, k⟩, ⟨hX, hk, mk⟩, rfl⟩
      exact (memC _).2 ⟨(eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq (hg X hX)).2 k hk, X, ((memN X).1 hX).1, hmv X hX k mk⟩
    · intro hh
      obtain ⟨hh, X, hXN, mh⟩ := (memC h).1 hh
      have hX : X ∈ nbIn M P A B := (memN X).2 ⟨hXN, h, hh, mh⟩
      obtain ⟨k, hk, rfl⟩ :=
        (Set.ext_iff.1 (transporter_eq (hg X hX) (hgm X hX)) h).1 ⟨hh, mh⟩
      exact ⟨(X, k), ⟨hX, hk⟩, rfl⟩
  have hinj : Set.InjOn F (nbIn M P A B ×ˢ {h ∈ DH E n M | Moves h B B}) := by
    rintro ⟨X, k⟩ ⟨hX, hk, mk⟩ ⟨Y, k'⟩ ⟨hY, hk', mk'⟩ e
    have e' : g X * k = g Y * k' := e
    have m1 := hmv X hX k mk
    have m2 := hmv Y hY k' mk'
    rw [e'] at m1
    have hXY : X = Y := moves_unique ((eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq (hg Y hY)).2 k' hk').1 m1 m2
    subst hXY
    exact Prod.ext rfl (mul_inj (hg X hX).1 e')
  rw [← himg, hinj.ncard_image, Set.ncard_prod]

theorem ccT_mem_carry {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P)
    {A B : Lt E n} (hA : A ∈ Vset E n M) (hB : B ∈ Vset E n M) {h : Matrix (Fin n) (Fin n) E}
    (hh : h ∈ carry M P A B) : ccT h ∈ carry M (conjI P) B A := by
  obtain ⟨hh, X, hXN, mh⟩ := hh
  have hh' : h * ccT h = 1 := mul_eq_one_comm.1 hh.1
  have hc : ccT h ∈ DH E n M := (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hh).1
  obtain ⟨Y, -, mY⟩ := (finite_cls_and_stab E n M hM).2.2.2.2 (ccT h) hc A hA
  have hX : X ∈ Vset E n M := hXN.1
  obtain ⟨hgc, -, hnb⟩ := neighbours E n M q P hM hP
  have hAX : A ∈ Nb M (conjI P) X := ((hnb A hA).2.2.1 X hX).1 hXN
  have hequiv := ((neighbours E n M q (conjI P) hM hgc).2.2 X hX).2.2.2.2.2
  have hmXB : Moves (ccT h) X B := Nbr.move_inv hh' mh
  show ccT h ∈ DH E n M ∧ ∃ Y ∈ Nb M (conjI P) B, Moves (ccT h) A Y
  exact ⟨hc, Y, (hequiv (ccT h) hc B hB hmXB A Y mY).1 hAX, mY⟩

theorem ncard_carry_symm {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P)
    {A B : Lt E n} (hA : A ∈ Vset E n M) (hB : B ∈ Vset E n M) :
    (carry M (conjI P) B A).ncard = (carry M P A B).ncard := by
  have hcc : ∀ k : Matrix (Fin n) (Fin n) E, ccT (ccT k) = k := by
    intro k
    ext i j
    simp [ccT, Nbr.cc_cc]
  have hgc : GoodPrime M q (conjI P) := Nbr.good_conj hP
  have himg : (ccT : Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E) '' carry M P A B =
      carry M (conjI P) B A := by
    ext k
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ccT_mem_carry hM hP hA hB hh
    · intro hk
      refine ⟨ccT k, ?_, hcc k⟩
      have key := ccT_mem_carry hM hgc hB hA hk
      rwa [Nbr.conjI_conjI] at key
  rw [← himg, Set.ncard_image_of_injective _ (Function.LeftInverse.injective hcc)]

theorem wt_mul_nbIn {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P)
    {A B : Lt E n} (hA : A ∈ Vset E n M) (hB : B ∈ Vset E n M) :
    (wt M A : ℂ) * (nbIn M P A B).ncard = (wt M B : ℂ) * (nbIn M (conjI P) B A).ncard := by
  obtain ⟨-, -, hstab, -, -⟩ := finite_cls_and_stab E n M hM
  obtain ⟨hgc, -, hnb⟩ := neighbours E n M q P hM hP
  have hnb' := (neighbours E n M q (conjI P) hM hgc).2.2
  have h1 := ncard_carry (P := P) (A := A) (B := B) (hnb A hA).1 (hstab B hB).1
  have h2 := ncard_carry (P := conjI P) (A := B) (B := A) (hnb' B hB).1 (hstab A hA).1
  have h3 := ncard_carry_symm hM hP hA hB
  have key : (nbIn M P A B).ncard * {h ∈ DH E n M | Moves h B B}.ncard =
      (nbIn M (conjI P) B A).ncard * {h ∈ DH E n M | Moves h A A}.ncard := by
    rw [← h1, ← h2, h3]
  have hne : ∀ Λ ∈ Vset E n M, (({h ∈ DH E n M | Moves h Λ Λ}.ncard : ℕ) : ℂ) ≠ 0 := by
    intro Λ hΛ h0
    have hw := (hstab Λ hΛ).2
    norm_cast at h0
    simp only [wt, h0] at hw
    simp at hw
  simp only [wt]
  push_cast
  rw [inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff (hne A hA) (hne B hB)]
  exact_mod_cast key

private theorem exists_moves_of_cls_eq {M : ℕ} {a b : Vset E n M}
    (e : (Quot.mk _ a : Cls E n M) = Quot.mk _ b) : ∃ h ∈ DH E n M, Moves h a.1 b.1 := by
  have hq := Quot.eqvGen_exact e
  clear e
  induction hq with
  | rel x y hxy => exact hxy
  | refl x => exact ⟨1, one_mem_UJset', fun v => by rw [Matrix.one_mulVec]⟩
  | symm x y _ ih =>
    obtain ⟨h, hh, m⟩ := ih
    exact ⟨ccT h, (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hh).1, Nbr.move_inv (mul_eq_one_comm.1 hh.1) m⟩
  | trans x y z _ _ ih1 ih2 =>
    obtain ⟨h, hh, m⟩ := ih1
    obtain ⟨k, hk, m'⟩ := ih2
    exact ⟨k * h, (eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq hk).2 h hh, fun v => by rw [m v, m' (h *ᵥ v), Matrix.mulVec_mulVec]⟩

theorem sum_nb {M : ℕ} [Fintype (Cls E n M)] {P : Ideal (𝓞 E)} {A : Lt E n}
    (hN : (Nb M P A).Finite) {f : Lt E n → ℂ} (hf : IsClassFn M f) :
    ∑ᶠ X ∈ Nb M P A, f X =
      ∑ c : Cls E n M, ((nbIn M P A (Quot.out c).1).ncard : ℂ) * f (Quot.out c).1 := by
  classical
  rcases isEmpty_or_nonempty (Cls E n M) with hE | hE
  · have h0 : Nb M P A = ∅ := by
      ext X
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hX => hE.false (Quot.mk _ ⟨X, hX.1⟩)
    simp [h0]
  let cl : Lt E n → Cls E n M := fun X =>
    if hX : X ∈ Vset E n M then Quot.mk _ ⟨X, hX⟩ else hE.some
  have hcl : ∀ X (hX : X ∈ Vset E n M), cl X = Quot.mk _ ⟨X, hX⟩ := fun X hX => dif_pos hX
  rw [finsum_mem_eq_finite_toFinset_sum _ hN,
    ← Finset.sum_fiberwise_of_maps_to (s := hN.toFinset) (t := Finset.univ) (g := cl)
      (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hset : ((hN.toFinset.filter fun X => cl X = c : Finset (Lt E n)) : Set (Lt E n)) =
      nbIn M P A (Quot.out c).1 := by
    ext X
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, nbIn]
    constructor
    · rintro ⟨hX, hc⟩
      exact ⟨hX, exists_moves_of_cls_eq ((Quot.out_eq c).trans ((hcl X hX.1).symm.trans hc).symm)⟩
    · rintro ⟨hX, h, hh, m⟩
      refine ⟨hX, ?_⟩
      rw [hcl X hX.1]
      exact (Quot.sound (⟨h, hh, m⟩ : ∃ h ∈ DH E n M, Moves h (Quot.out c).1 X)).symm.trans
        (Quot.out_eq c)
  have hval : ∀ X ∈ hN.toFinset.filter (fun X => cl X = c), f X = f (Quot.out c).1 := by
    intro X hX
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hX
    obtain ⟨h, hh, m⟩ := exists_moves_of_cls_eq ((Quot.out_eq c).trans ((hcl X hX.1.1).symm.trans hX.2).symm)
    exact hf h hh _ (Quot.out c).2 X hX.1.1 m
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_coe_finset, hset]

end NbAvg


open NbAvg in
theorem classSum_nb :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → ∀ f : Lt E n → ℂ, (∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' → f Λ' = f Λ) → ((q : ℂ) - 1) * classSum M (fun Λ => ∑ᶠ Λ' ∈ Nb M P Λ, f Λ') = ((q : ℂ) ^ n - 1) * classSum M f := by
  intro E _ _ _ n M q P hM hP f hf
  obtain ⟨hcls, -, -, -, -⟩ := finite_cls_and_stab E n M hM
  let _ : Fintype (Cls E n M) := Fintype.ofFinite _
  obtain ⟨hgc, -, hnb⟩ := neighbours E n M q P hM hP
  have hnb' := (neighbours E n M q (conjI P) hM hgc).2.2
  have hf' : IsClassFn M f := hf
  have hone : IsClassFn M (fun _ : Lt E n => (1 : ℂ)) := fun _ _ _ _ _ _ _ => rfl
  have hcount : ∀ d : Cls E n M, ((q : ℂ) - 1) *
      ∑ c : Cls E n M, ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ) =
      (q : ℂ) ^ n - 1 := by
    intro d
    obtain ⟨hfin, hcnt, -⟩ := hnb' _ (Quot.out d).2
    have hs := NbAvg.sum_nb hfin hone
    simp only [mul_one] at hs
    have h1 : ∑ᶠ X ∈ Nb M (conjI P) (Quot.out d).1, (1 : ℂ) =
        ((Nb M (conjI P) (Quot.out d).1).ncard : ℂ) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, nsmul_eq_mul, mul_one,
        Set.ncard_eq_toFinset_card _ hfin]
    rw [h1] at hs
    rw [← hs]
    have hq1 : 1 ≤ q := hP.1.one_lt.le
    have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ hP.1.pos
    have hc := congrArg (fun x : ℕ => (x : ℂ)) hcnt
    simp only [Nat.cast_mul, Nat.cast_sub hq1, Nat.cast_sub hqn, Nat.cast_pow, Nat.cast_one] at hc
    linear_combination hc
  have hsum : ∀ c : Cls E n M, ∑ᶠ X ∈ Nb M P (Quot.out c).1, f X =
      ∑ d : Cls E n M, ((nbIn M P (Quot.out c).1 (Quot.out d).1).ncard : ℂ) * f (Quot.out d).1 :=
    fun c => NbAvg.sum_nb (hnb _ (Quot.out c).2).1 hf'
  simp only [classSum, finsum_eq_sum_of_fintype, hsum]
  calc _ = ∑ c : Cls E n M, ∑ d : Cls E n M, ((q : ℂ) - 1) * ((wt M (Quot.out d).1 : ℂ) *
        ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ)) * f (Quot.out d).1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← wt_mul_nbIn hM hP (Quot.out c).2 (Quot.out d).2]
        ring
    _ = ∑ d : Cls E n M, ∑ c : Cls E n M, ((q : ℂ) - 1) * ((wt M (Quot.out d).1 : ℂ) *
        ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ)) * f (Quot.out d).1 :=
        Finset.sum_comm
    _ = ∑ d : Cls E n M, ((wt M (Quot.out d).1 : ℂ) * f (Quot.out d).1) * (((q : ℂ) - 1) *
        ∑ c : Cls E n M, ((nbIn M (conjI P) (Quot.out d).1 (Quot.out c).1).ncard : ℂ)) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ((q : ℂ) ^ n - 1) * ∑ d : Cls E n M, (wt M (Quot.out d).1 : ℂ) * f (Quot.out d).1 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hcount d]
        ring

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumNbStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_sum_nb_eq_of_moves_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → ∀ f : Lt E n → ℂ, (∀ h ∈ DH E n M, ∀ Λ ∈ Vset E n M, ∀ Λ' ∈ Vset E n M, Moves h Λ Λ' → f Λ' = f Λ) → ((q : ℂ) - 1) * classSum M (fun Λ => ∑ᶠ Λ' ∈ Nb M P Λ, f Λ') = ((q : ℂ) ^ n - 1) * classSum M f := by
  first | exact @GlobalTheory.SW.classSum_nb | exact GlobalTheory.SW.classSum_nb | (intros; apply GlobalTheory.SW.classSum_nb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilFormulaDegreeSucc
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem isSB_of_adm (hΨ : IsType Ψ) (hn : Even n) {M R : ℕ} {φ : Fam E n N} (h : admitted M R φ)
    {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) : IsSB (φ Λ) := by
  obtain ⟨R', C, -, H⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn 1 R one_pos h.pos.2
  refine (H M Λ hΛ 1 Base.one_mem_UU (fun i j => ?_) (φ Λ) ⟨h.supp Λ hΛ, h.per Λ hΛ⟩).1
  by_cases e : i = j
  · subst e; simpa using isIntegral_one
  · simpa [Matrix.one_apply, e] using isIntegral_zero

theorem swd_sum (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M : ℕ} (hM : 0 < M)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) {ι : Type} (s : Finset ι) (ψ : ι → Fam E n N)
    (h : ∀ i, ∀ Λ ∈ Vset E n M, IsSB (ψ i Λ)) :
    (∀ Λ ∈ Vset E n M, IsSB ((∑ i ∈ s, ψ i) Λ)) ∧
      swd Ψ M (∑ i ∈ s, ψ i) Z 0 0 = ∑ i ∈ s, swd Ψ M (ψ i) Z 0 0 := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ _ => isSB_zero, ?_⟩
    have := (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M 0 hM (fun _ _ => isSB_zero) Z hZ).2.2.2.1 0
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih.2]
    exact ⟨fun Λ hΛ => (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (h a Λ hΛ) (ih.1 Λ hΛ)).1,
      (GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M (ψ a) hM (h a) Z hZ).2.2.1 _ ih.1⟩

theorem classSum_sum {M : ℕ} (hM : 0 < M) {ι : Type} (s : Finset ι) (f : ι → Lt E n → ℂ) :
    classSum M (fun Λ => ∑ i ∈ s, f i Λ) = ∑ i ∈ s, classSum M (f i) := by
  have := (finite_cls_and_stab E n M hM).1
  have := Fintype.ofFinite (Cls E n M)
  simp only [classSum, finsum_eq_sum_of_fintype, Finset.mul_sum]
  exact Finset.sum_comm

theorem exists_enum {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P) :
    ∃ (B : ℕ) (e : Fin B → Lt E n → Lt E n), ∀ Λ ∈ Vset E n M, (∀ j, e j Λ ∈ Vset E n M) ∧
      ∀ g : Lt E n → ℂ, ∑ᶠ Λ' ∈ Nb M P Λ, g Λ' = ∑ j, g (e j Λ) := by
  have H := (neighbours E n M q P hM hP).2.2
  have hq : 0 < q - 1 := Nat.sub_pos_of_lt hP.1.one_lt
  have key : ∀ Λ : Lt E n, ∃ e : Fin ((q ^ n - 1) / (q - 1)) → Lt E n, Λ ∈ Vset E n M →
      (∀ j, e j ∈ Vset E n M) ∧ ∀ g : Lt E n → ℂ, ∑ᶠ Λ' ∈ Nb M P Λ, g Λ' = ∑ j, g (e j) := by
    intro Λ
    by_cases hΛ : Λ ∈ Vset E n M
    · obtain ⟨hf, hc, -⟩ := H Λ hΛ
      have hc' : hf.toFinset.card = (q ^ n - 1) / (q - 1) := by
        rw [← hc, Nat.mul_div_cancel _ hq, Set.ncard_eq_toFinset_card _ hf]
      let σ := (Finset.equivFinOfCardEq hc').symm
      refine ⟨fun j => (σ j).1, fun _ => ⟨fun j => (hf.mem_toFinset.1 (σ j).2).1, fun g => ?_⟩⟩
      rw [finsum_mem_eq_finite_toFinset_sum _ hf, ← Finset.sum_coe_sort, ← σ.sum_comp]
    · exact ⟨fun _ => Λ, fun h => (hΛ h).elim⟩
  choose e he using key
  exact ⟨_, fun j Λ => e Λ j, he⟩

theorem swd_nb (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M R q : ℕ} {P : Ideal (𝓞 E)}
    {ψ : Fam E n N} (h : admitted M R ψ) (hP : GoodPrime M q P) {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) :
    (∀ Λ ∈ Vset E n M, IsSB fun x => ∑ᶠ Λ' ∈ Nb M P Λ, ψ Λ' x) ∧
      ((q : ℂ) - 1) * swd Ψ M (fun Λ x => ∑ᶠ Λ' ∈ Nb M P Λ, ψ Λ' x) Z 0 0 =
        ((q : ℂ) ^ n - 1) * swd Ψ M ψ Z 0 0 := by
  have hM := h.pos.1
  obtain ⟨B, e, he⟩ := exists_enum (n := n) hM hP
  obtain ⟨h1, h2⟩ := swd_sum hΨ hn hN hM hZ Finset.univ (fun j Λ => ψ (e j Λ))
    (fun j Λ hΛ => isSB_of_adm hΨ hn h ((he Λ hΛ).1 j))
  have eq : ∀ Λ ∈ Vset E n M, (fun x => ∑ᶠ Λ' ∈ Nb M P Λ, ψ Λ' x) =
      (∑ j, fun Λ => ψ (e j Λ)) Λ := fun Λ hΛ => by
    funext x
    rw [(he Λ hΛ).2 fun Λ' => ψ Λ' x]
    simp only [Finset.sum_apply]
  refine ⟨fun Λ hΛ => (eq Λ hΛ) ▸ h1 Λ hΛ, ?_⟩
  rw [(GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M _ hM h1 Z hZ).2.2.2.2 _ eq, h2]
  have H := GlobalTheory.T.classSum_sum_nb_eq_of_moves_invariant E n M q P hM hP (fun Λ => thH Ψ (ψ Λ) Z 0 0 - eis Ψ (ψ Λ) Z 0 0) (by
    intro g hg Λ hΛ Λ' hΛ' m
    have e1 : (fun x : Matrix (Fin n) (Fin N) E => ψ Λ' (g * x)) = ψ Λ :=
      funext (h.equiv g hg Λ hΛ Λ' hΛ' m)
    have := (GlobalTheory.T.hermitianWeilAction_comm_positiveUnitaryGroup E Ψ hΨ n N hn g hg.1 (ψ Λ') (isSB_of_adm hΨ hn h hΛ')).2.2 Z hZ
    exact congrArg₂ (· - ·) (this.1.symm.trans (congrArg (thH Ψ · Z 0 0) e1))
      (this.2.symm.trans (congrArg (eis Ψ · Z 0 0) e1)))
  refine Eq.trans ?_ H
  congr 1
  unfold swd
  rw [← classSum_sum hM]
  exact Base.classSum_congr fun Λ hΛ =>
    ((he Λ hΛ).2 fun Λ => thH Ψ (ψ Λ) Z 0 0 - eis Ψ (ψ Λ) Z 0 0).symm


omit [NumberField E] [IsCMField E] in
theorem detIm_pos {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) : 0 < detIm Z :=
  Finset.prod_pos fun τ _ => (Complex.pos_iff.1 (hZ τ).det_pos).1

theorem imH_add (Z : CM Ψ N N) {β : Matrix (Fin N) (Fin N) E} (hβ : ccT β = β) (τ : Ψ) :
    imH (Z τ + β.map τ.1) = imH (Z τ) := by
  unfold imH
  rw [conjTranspose_add, ← Base.ccT_map, hβ]
  congr 1
  abel

theorem hecke_swd (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {M R q : ℕ} {P : Ideal (𝓞 E)}
    {φ : Fam E n N} (h : admitted M R φ) (hP : GoodPrime (R * M) q P) {𝔛 : Lt E N} (h1 : 𝔛.FG)
    (h2 : Agree (R * M) 𝔛 (stdL E N)) :
    ∃ (A : ℕ) (XA XB : Fin A → Lt E N) (β : Fin A → Fin (q ^ N) → Matrix (Fin N) (Fin N) E),
      A * (q - 1) = q ^ N - 1 ∧
      (∀ i, (XA i).FG ∧ Agree (R * M) (XA i) (stdL E N) ∧ gidx (XA i) = q * gidx 𝔛 ∧
        (XB i).FG ∧ Agree (R * M) (XB i) (stdL E N) ∧ q * gidx (XB i) = gidx 𝔛 ∧
        ∀ j, ccT (β i j) = β i j) ∧
      ∀ Z ∈ Hn Ψ N, ((q : ℂ) ^ N - 1) * ((q : ℂ) ^ n + (q : ℂ) ^ N) *
          swd Ψ M (twist R 𝔛 φ) Z 0 0 =
        ((q : ℂ) - 1) * ((q : ℂ) ^ n * ∑ i, swd Ψ M (twist R (XA i) φ) Z 0 0 +
          ∑ i, ∑ j, swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0) := by
  obtain ⟨A, XA, XB, β, hA, hX, hid⟩ := GlobalTheory.T.hecke_relation_admissibleFamily_pointwise E Ψ hΨ n N M R q P φ 𝔛 h h1 h2 hP
  refine ⟨A, XA, XB, β, hA, hX, fun Z hZ => ?_⟩
  have hM := h.pos.1
  have hP' : GoodPrime M q P := ⟨hP.1, Nat.Coprime.coprime_mul_left_right hP.2.1, hP.2.2⟩
  have adm : ∀ Y : Lt E N, Y.FG → Agree (R * M) Y (stdL E N) → ∃ R', admitted M R' (twist R Y φ) :=
    fun Y a b => (twist_admissible E n N M R φ Y h a b).2.2.2.2.1
  have sb : ∀ Y : Lt E N, Y.FG → Agree (R * M) Y (stdL E N) → ∀ Λ ∈ Vset E n M,
      IsSB (twist R Y φ Λ) := fun Y a b Λ hΛ => isSB_of_adm hΨ hn (adm Y a b).choose_spec hΛ
  have aut := fun (ψ : Fam E n N) hψ => GlobalTheory.T.siegelWeilDifference_automorphy_linearity E Ψ hΨ n N hn hN M ψ hM hψ Z hZ
  have sbs : ∀ (c : ℂ) (ψ : Fam E n N), (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) →
      ∀ Λ ∈ Vset E n M, IsSB ((c • ψ) Λ) := fun c ψ hψ Λ hΛ =>
    (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hψ Λ hΛ) (hψ Λ hΛ)).2.1 c
  have sba : ∀ (ψ ψ' : Fam E n N), (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) →
      (∀ Λ ∈ Vset E n M, IsSB (ψ' Λ)) → ∀ Λ ∈ Vset E n M, IsSB ((ψ + ψ') Λ) :=
    fun ψ ψ' hψ hψ' Λ hΛ => (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ (hψ Λ hΛ) (hψ' Λ hΛ)).1
  obtain ⟨a1, a2⟩ := swd_sum hΨ hn hN hM hZ Finset.univ (fun i => twist R (XA i) φ)
    fun i => sb _ (hX i).1 (hX i).2.1
  have sbB : ∀ i, ∀ Λ ∈ Vset E n M, IsSB (twist R (XB i) φ Λ) :=
    fun i => sb _ (hX i).2.2.2.1 (hX i).2.2.2.2.1
  have b := fun i => swd_sum hΨ hn hN hM hZ Finset.univ
    (fun j Λ x => chiH Ψ (β i j) x * twist R (XB i) φ Λ x) fun j Λ hΛ => by
      simpa using Parab.isSB_chiH hΨ ((hX i).2.2.2.2.2.2 j) 1 (sbB i Λ hΛ)
  obtain ⟨b1, b2⟩ := swd_sum hΨ hn hN hM hZ Finset.univ _ fun i => (b i).1
  obtain ⟨R', hR'⟩ := adm 𝔛 h1 h2
  obtain ⟨c1, c2⟩ := swd_nb hΨ hn hN hR' hP' hZ
  have d1 := sb 𝔛 h1 h2
  have hL := sba _ _ (sbs ((q : ℂ) ^ n) _ a1) b1
  have e := (aut _ (sbs ((q : ℂ) - 1) _ hL)).2.2.2.2
    ((((q : ℂ) - 1) * (q : ℂ) ^ N) • (fun Λ x => ∑ᶠ Λ' ∈ Nb M P Λ, twist R 𝔛 φ Λ' x) +
      ((q : ℂ) ^ (2 * N) - (q : ℂ) ^ n) • twist R 𝔛 φ) (fun Λ hΛ => by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      exact (hid Λ hΛ x).symm)
  rw [(aut _ (sbs _ _ c1)).2.2.1 _ (sbs _ _ d1), (aut _ c1).2.2.2.1, (aut _ d1).2.2.2.1,
    (aut _ hL).2.2.2.1, (aut _ (sbs _ _ a1)).2.2.1 _ b1, (aut _ a1).2.2.2.1, a2, b2] at e
  have f : ∀ i, swd Ψ M (∑ j, fun Λ x => chiH Ψ (β i j) x * twist R (XB i) φ Λ x) Z 0 0 =
      ∑ j, swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0 := fun i => by
    rw [(b i).2]
    exact Finset.sum_congr rfl fun j _ => (aut _ (sbB i)).2.1 _ ((hX i).2.2.2.2.2.2 j)
  simp only [f] at e
  rw [← e]
  linear_combination (-(q : ℂ) ^ N) * c2

theorem bound_step (hΨ : IsType Ψ) {k : ℕ} (hN0 : 0 < N) (hN : 4 * N < k + k) {M R q : ℕ}
    {P : Ideal (𝓞 E)} {φ : Fam E (k + k) N} (h : admitted M R φ) (hP : GoodPrime (R * M) q P) {S : ℝ}
    (hS : ∀ 𝔛 : Lt E N, 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → ∀ Z ∈ Hn Ψ N,
      gidx 𝔛 ^ k * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ k ≤ S)
    (𝔛 : Lt E N) (h1 : 𝔛.FG) (h2 : Agree (R * M) 𝔛 (stdL E N)) (Z : CM Ψ N N)
    (hZ : Z ∈ Hn Ψ N) :
    gidx 𝔛 ^ k * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ k ≤
      (q : ℝ) ^ k * (1 + (q : ℝ) ^ N) / ((q : ℝ) ^ (k + k) + (q : ℝ) ^ N) * S := by
  obtain ⟨A, XA, XB, β, hA, hX, hid⟩ := hecke_swd hΨ ⟨k, rfl⟩ hN h hP h1 h2
  have hq1 : 1 < q := hP.1.one_lt
  have hq : (1 : ℝ) < q := by exact_mod_cast hq1
  have hqN : (1 : ℝ) < (q : ℝ) ^ N := one_lt_pow₀ hq hN0.ne'
  have hA' : (A : ℝ) * ((q : ℝ) - 1) = (q : ℝ) ^ N - 1 := by
    have := congrArg (Nat.cast : ℕ → ℝ) hA
    rwa [Nat.cast_mul, Nat.cast_sub hq1.le, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)),
      Nat.cast_pow, Nat.cast_one] at this
  have hg : 0 < gidx 𝔛 := (twist_admissible E _ N M R φ 𝔛 h h1 h2).2.2.2.1
  have hd := detIm_pos hZ
  set w : ℝ := gidx 𝔛 ^ k * detIm Z ^ k with hw
  have hw0 : 0 < w := by positivity
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hAi : ∀ i, (q : ℝ) ^ k * (w * ‖swd Ψ M (twist R (XA i) φ) Z 0 0‖) ≤ S := fun i => by
    have := hS _ (hX i).1 (hX i).2.1 Z hZ
    rw [(hX i).2.2.1, mul_pow] at this
    exact le_of_eq_of_le (by rw [hw]; ring) this
  have hBi : ∀ i j, w * ‖swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖ ≤
      (q : ℝ) ^ k * S := fun i j => by
    have hi := imH_add Z ((hX i).2.2.2.2.2.2 j)
    have := hS _ (hX i).2.2.2.1 (hX i).2.2.2.2.1 (fun τ => Z τ + (β i j).map τ.1)
      (fun τ => by simp only [hi]; exact hZ τ)
    have e : detIm (fun τ : Ψ => Z τ + (β i j).map τ.1) = detIm Z := by simp only [detIm, hi]
    rw [e] at this
    refine le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left this hqk.le)
    rw [hw, ← (hX i).2.2.2.2.2.1, mul_pow]; ring
  have hn := congrArg norm (hid Z hZ)
  have n1 : ‖((q : ℂ) ^ N - 1) * ((q : ℂ) ^ (k + k) + (q : ℂ) ^ N)‖ =
      ((q : ℝ) ^ N - 1) * ((q : ℝ) ^ (k + k) + (q : ℝ) ^ N) := by
    rw [← Real.norm_of_nonneg (r := ((q : ℝ) ^ N - 1) * ((q : ℝ) ^ (k + k) + (q : ℝ) ^ N))
      (mul_nonneg (by linarith) (by positivity)), ← Complex.norm_real]
    push_cast; rfl
  have n2 : ‖(q : ℂ) - 1‖ = (q : ℝ) - 1 := by
    rw [← Real.norm_of_nonneg (r := (q : ℝ) - 1) (by linarith), ← Complex.norm_real]
    push_cast; rfl
  rw [norm_mul, n1, norm_mul, n2] at hn
  have hle : w * ‖(q : ℂ) ^ (k + k) * ∑ i, swd Ψ M (twist R (XA i) φ) Z 0 0 +
      ∑ i, ∑ j, swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖ ≤
      A * ((q : ℝ) ^ k * (1 + (q : ℝ) ^ N) * S) := by
    calc _ ≤ w * ((q : ℝ) ^ (k + k) * ∑ i, ‖swd Ψ M (twist R (XA i) φ) Z 0 0‖ +
          ∑ i, ∑ j, ‖swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖) := by
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hw0.le
          · rw [norm_mul, norm_pow, Complex.norm_natCast]
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
          · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ = (∑ i, (q : ℝ) ^ k * ((q : ℝ) ^ k * (w * ‖swd Ψ M (twist R (XA i) φ) Z 0 0‖))) +
          ∑ i, ∑ j, w * ‖swd Ψ M (twist R (XB i) φ) (fun τ => Z τ + (β i j).map τ.1) 0 0‖ := by
          simp only [← Finset.mul_sum]; ring
      _ ≤ (∑ _i : Fin A, (q : ℝ) ^ k * S) + ∑ _i : Fin A, ∑ _j : Fin (q ^ N), (q : ℝ) ^ k * S :=
          add_le_add (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hAi i) hqk.le)
            (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hBi i j)
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  refine le_of_mul_le_mul_left ?_ (sub_pos.2 hqN)
  have := mul_le_mul_of_nonneg_left hle (sub_pos.2 hq).le
  rw [mul_left_comm, ← hn, ← mul_assoc ((q : ℝ) - 1), mul_comm ((q : ℝ) - 1), hA'] at this
  exact le_of_eq_of_le (by rw [hw]; ring) this

end GlobalTheory.SW.Step


open GlobalTheory.SW.Step in
theorem GlobalTheory.SW.swAt_succ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → SWAt Ψ n (N + 1) := by
  intro E _ _ _ Ψ hΨ n N hn hN hSW M R φ h Z hZ
  obtain ⟨C, hC⟩ := GlobalTheory.T.twisted_siegelWeil_difference_bounded E Ψ hΨ n N hn hN hSW M R φ h
  obtain ⟨k, rfl⟩ := hn
  have ek : ((k + k : ℕ) : ℝ) / 2 = (k : ℝ) := by push_cast; ring
  simp only [ek, Real.rpow_natCast] at hC
  obtain ⟨q, P, hP⟩ := GlobalTheory.T.exists_good_split_prime_cmField E (R * M) (Nat.mul_pos h.pos.2 h.pos.1)
  have hq : (1 : ℝ) < q := by exact_mod_cast hP.1.one_lt
  set θ : ℝ := (q : ℝ) ^ k * (1 + (q : ℝ) ^ (N + 1)) / ((q : ℝ) ^ (k + k) + (q : ℝ) ^ (N + 1))
    with hθ
  have θ0 : 0 ≤ θ := by positivity
  have θ1 : θ < 1 := by
    rw [hθ, div_lt_one (by positivity), pow_add _ k k]
    have a : (q : ℝ) ^ (N + 1) < (q : ℝ) ^ k := pow_lt_pow_right₀ hq (by omega)
    have b : (1 : ℝ) < (q : ℝ) ^ k := one_lt_pow₀ hq (by omega)
    nlinarith [mul_pos (sub_pos.2 a) (sub_pos.2 b)]
  have key : ∀ m : ℕ, ∀ 𝔛 : Lt E (N + 1), 𝔛.FG → Agree (R * M) 𝔛 (stdL E (N + 1)) →
      ∀ Z ∈ Hn Ψ (N + 1),
      gidx 𝔛 ^ k * ‖swd Ψ M (twist R 𝔛 φ) Z 0 0‖ * detIm Z ^ k ≤ θ ^ m * C := by
    intro m
    induction m with
    | zero => simpa using hC
    | succ m ih =>
      intro 𝔛 h1 h2 Z hZ
      rw [pow_succ', mul_assoc θ]
      exact bound_step hΨ N.succ_pos hN h hP ih 𝔛 h1 h2 Z hZ
  have s1 : (stdL E (N + 1)).FG := Submodule.fg_span (Set.finite_range _)
  have s2 : Agree (R * M) (stdL E (N + 1)) (stdL E (N + 1)) :=
    ⟨1, one_pos, Nat.coprime_one_left _, by simp, by simp⟩
  have lim : Tendsto (fun m : ℕ => θ ^ m * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one θ0 θ1).mul_const C
  have le0 := ge_of_tendsto' lim fun m => key m _ s1 s2 Z hZ
  rw [Base.gidx_stdL, one_pow, one_mul] at le0
  have z : ‖swd Ψ M (twist R (stdL E (N + 1)) φ) Z 0 0‖ ≤ 0 :=
    nonpos_of_mul_nonpos_left le0 (pow_pos (detIm_pos hZ) k)
  rw [← norm_le_zero_iff.1 z]
  exact Base.classSum_congr fun Λ hΛ => by
    rw [(twist_admissible E _ _ M R φ _ h s1 s2).2.1 Λ hΛ]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilFormulaDegreeSuccStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_formula_degree_succ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → SWAt Ψ n (N + 1) := by
  first | exact @GlobalTheory.SW.swAt_succ | exact GlobalTheory.SW.swAt_succ | (intros; apply GlobalTheory.SW.swAt_succ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDefiniteHermitianOfFourMulLt
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem siegel_weil_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  intro E _ _ _ Ψ hΨ n N hn
  induction N with
  | zero =>
    intro _ M R φ _ Z _
    rw [Base.swd_zero, Base.swDiff_deg_zero]
  | succ N ih =>
    intro h
    exact GlobalTheory.T.siegelWeil_formula_degree_succ E Ψ hΨ n N hn h (ih (by omega))

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDefiniteHermitianOfFourMulLtStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_definiteHermitian_of_four_mul_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → SWAt Ψ n N := by
  first | exact @GlobalTheory.SW.siegel_weil_definite | exact GlobalTheory.SW.siegel_weil_definite | (intros; apply GlobalTheory.SW.siegel_weil_definite <;> assumption)
end
