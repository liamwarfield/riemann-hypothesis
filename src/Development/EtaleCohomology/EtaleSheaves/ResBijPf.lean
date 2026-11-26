module

public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
public import Development.EtaleCohomology.EtaleSheaves.SHTensorPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.ResBijPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ResBijPf

def TwSec : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ

theorem res_comp' {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res (g ≫ h) x = Sec.res g (Sec.res h x) := by
  simp [Sec.res]

theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ n x

theorem sep' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (y z : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g y = Sec.res g z) : y = z := by
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem sec_empty {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} [IsEmpty U] (y z : Sec F U) : y = z :=
  sep' ⊥ (Scheme.bot_mem_grothendieckTopology U) y z (fun _ _ h => h.elim)

variable {q : ℕ} {i : ℤ}

theorem smul_mod {U : Scheme.{0}} (G : Sec (tw q i) U) (a : ℕ) : a • G = (a % q) • G := by
  have hq : q • G = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
    have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
      ext; simp
    rw [this, zero_smul]
  conv_lhs => rw [← Nat.mod_add_div a q]
  rw [add_smul, mul_comm, mul_smul, hq, smul_zero, add_zero]

theorem smul_eq_of_cast {U : Scheme.{0}} (G : Sec (tw q i) U) {a b : ℕ} (h : (a : ZMod q) = b) : a • G = b • G := by
  rw [smul_mod G a, smul_mod G b, (ZMod.natCast_eq_natCast_iff' a b q).1 h]

theorem cast_of_smul_eq (hT : TwSec) [NeZero q] {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) {a b : ℕ}
    (h : a • twGen i ζ = b • twGen i ζ) : (a : ZMod q) = b := by
  rw [ZMod.natCast_eq_natCast_iff']
  rw [smul_mod _ a, smul_mod _ b] at h
  have ha := Nat.mod_lt a (NeZero.pos q)
  have hb := Nat.mod_lt b (NeZero.pos q)
  have key : ∀ x y : ℕ, x < q → y < q → x ≤ y → x • twGen i ζ = y • twGen i ζ → x = y := by
    intro x y hx hy hxy he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    rw [add_smul] at he
    have hd : d • twGen i ζ = 0 := by
      have := congrArg (fun t => t - x • twGen i ζ) he
      simpa using this.symm
    have := (hT q i).2.2.1 U ζ d hd
    have : d = 0 := Nat.eq_zero_of_dvd_of_lt this (by omega)
    omega
  rcases le_total (a % q) (b % q) with hab | hab
  · exact key _ _ ha hb hab h
  · exact (key _ _ hb ha hab h.symm).symm

end LateralTheory.E.ResBijPf

namespace LateralTheory.E.ResBijPf
variable {q : ℕ} {i : ℤ}

theorem surj (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤))
    (s : Sec (tw q i) U) : ∃ k : ℕ, s = k • twGen i ζ := by
  obtain ⟨S, hS, hSP⟩ := (hT q i).2.1 U ζ s
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have hcov := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀
  have hgen : ∀ {V : Scheme.{0}} (g : V ⟶ U) (n : ℕ),
      n • twGen i (ζ.map g.appTop.hom) = Sec.res g (n • twGen i ζ) := by
    intro V g n
    rw [res_nsmul', (hT q i).2.2.2.1]
  have hc : ∀ j, ∃ c : ℕ, Sec.res (𝒰.f j) s = Sec.res (𝒰.f j) (c • twGen i ζ) := by
    intro j
    obtain ⟨c, hc⟩ := hSP _ _ (hle _ (𝒰.f j) (Presieve.ofArrows.mk j))
    exact ⟨c, hc.trans (hgen _ _)⟩
  choose c hc using hc
  have compat : ∀ j j' (x : 𝒰.X j) (x' : 𝒰.X j'), 𝒰.f j x = 𝒰.f j' x' → (c j : ZMod q) = c j' := by
    intro j j' x x' hx
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x x' hx
    have : Nonempty ↑(pullback (𝒰.f j) (𝒰.f j') : Scheme.{0}) := ⟨z⟩
    have e1 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s =
        Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j • twGen i ζ) := by
      rw [res_comp', hc j, ← res_comp']
    have e2 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s =
        Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j' • twGen i ζ) := by
      rw [pullback.condition, res_comp', hc j', ← res_comp']
    rw [← hgen] at e1 e2
    exact cast_of_smul_eq hT _ (e1.symm.trans e2)
  have hopen : ∀ j, IsOpen (Set.range (𝒰.f j)) := by
    intro j
    have := hcov.2 j
    exact (𝒰.f j).isOpenMap.isOpen_range
  obtain ⟨x0⟩ := (inferInstance : Nonempty U)
  obtain ⟨j0, y0, hy0⟩ := hcov.1 x0
  have claim : ∀ j (y : 𝒰.X j), (c j : ZMod q) = c j0 := by
    intro j y
    by_contra hne
    have hpc := (isPreconnected_univ (α := U))
      (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) = c j0), Set.range (𝒰.f j))
      (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) ≠ c j0), Set.range (𝒰.f j))
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j)
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j)
      (by
        intro x _
        obtain ⟨j', y', hy'⟩ := hcov.1 x
        by_cases h : (c j' : ZMod q) = c j0
        · exact Or.inl (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩)
        · exact Or.inr (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩))
      ⟨x0, trivial, Set.mem_iUnion₂.2 ⟨j0, rfl, y0, hy0⟩⟩
      ⟨𝒰.f j y, trivial, Set.mem_iUnion₂.2 ⟨j, hne, y, rfl⟩⟩
    obtain ⟨x, -, hA, hB⟩ := hpc
    obtain ⟨j1, h1, y1, hy1⟩ := Set.mem_iUnion₂.1 hA
    obtain ⟨j2, h2, y2, hy2⟩ := Set.mem_iUnion₂.1 hB
    exact h2 ((compat j2 j1 y2 y1 (hy2.trans hy1.symm)).trans h1)
  refine ⟨c j0, sep' _ (Scheme.Cover.mem_grothendieckTopology 𝒰) _ _ ?_⟩
  rintro V g ⟨W, h, g', hg', rfl⟩
  cases hg' with
  | mk j =>
    rw [res_comp', res_comp', hc j]
    congr 1
    rcases isEmpty_or_nonempty (𝒰.X j) with he | ⟨⟨y⟩⟩
    · exact sec_empty _ _
    · rw [smul_eq_of_cast _ (claim j y)]

theorem gen_bij (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤)) :
    Function.Bijective (fun k : ZMod q => k.val • twGen i ζ) := by
  refine ⟨fun k k' h => ?_, fun s => ?_⟩
  · have := cast_of_smul_eq hT ζ h
    simpa using this
  · obtain ⟨n, rfl⟩ := surj (i := i) hT ζ s
    refine ⟨(n : ZMod q), smul_eq_of_cast _ ?_⟩
    simp

theorem ResBij_of (hT : TwSec) : LateralTheory.E.HZeroPf.ResBij := by
  intro q i Y X f hY hX ⟨ζ⟩
  have : NeZero q := ⟨fun h0 => by
    subst h0
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    have h := ζ.2.1
    simp only [Nat.cast_zero, isUnit_zero_iff] at h
    exact zero_ne_one h⟩
  have h1 := gen_bij (i := i) hT ζ
  have h2 := gen_bij (i := i) hT (ζ.map f.appTop.hom)
  have e : (Sec.res (F := tw q i) f) ∘ (fun k : ZMod q => k.val • twGen i ζ) =
      fun k : ZMod q => k.val • twGen i (ζ.map f.appTop.hom) := by
    funext k
    simp only [Function.comp]
    rw [res_nsmul', (hT q i).2.2.2.1]
  exact (Function.Bijective.of_comp_iff _ h1).1 (by rw [e]; exact h2)

end LateralTheory.E.ResBijPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.TwFBijPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.TwFBijPf

theorem aeval_res {C : Type} [CommRing C] [IsLocalRing C] (q : ℕ) (x : C) :
    aeval (residue C x) (cyclotomic q ℤ) = residue C (aeval x (cyclotomic q ℤ)) :=
  by
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂]; congr 1

theorem isRoot_iff {K : Type} [CommRing K] (q : ℕ) (x : K) :
    IsRoot (cyclotomic q K) x ↔ aeval x (cyclotomic q ℤ) = 0 := by
  rw [← map_cyclotomic_int, IsRoot, Polynomial.eval_map, aeval_def, algebraMap_int_eq]

theorem res_prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot (residue C ζ) q := by
  haveI : NeZero ((q : ℕ) : ResidueField C) := ⟨by
    have := hq.map (residue C); rw [map_natCast] at this; exact this.ne_zero⟩
  rw [← isRoot_cyclotomic_iff, isRoot_iff]
  exact (aeval_res q ζ).trans (by rw [h, map_zero])

theorem pow_q {C : Type} [CommRing C] {q : ℕ} {ζ : C} (h : aeval ζ (cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ζ) hg
  simp [h] at this
  exact sub_eq_zero.1 this

theorem prim {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {ζ : C}
    (h : aeval ζ (cyclotomic q ℤ) = 0) : IsPrimitiveRoot ζ q := by
  refine ⟨pow_q h, fun l hl => (res_prim hq h).dvd_of_pow_eq_one l ?_⟩
  rw [← map_pow, hl, map_one]

theorem uniq {C : Type} [CommRing C] [IsLocalRing C] {n : ℕ} (hn : IsUnit (n : C)) {x y : C} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hr : residue C x = residue C y) : x = y := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have key := (Commute.all x y).geom_sum₂_mul n
  rw [hx, hy, sub_self] at key
  have hS : IsUnit (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← residue_ne_zero_iff_isUnit, map_sum]
    have : ∀ i ∈ Finset.range n, residue C (x ^ i * y ^ (n - 1 - i)) = residue C x ^ (n - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, ← hr, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 : IsUnit (residue C (n : C)) := hn.map _
    have h2 : IsUnit (residue C x) := (show IsUnit x from ⟨⟨x, x ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx],
      by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), hx]⟩, rfl⟩).map _
    rw [map_natCast] at h1
    exact (h1.mul (h2.pow _)).ne_zero
  have := hS.mul_right_eq_zero.1 key
  exact sub_eq_zero.1 this

theorem pow_rep {C : Type} [CommRing C] [IsLocalRing C] {q : ℕ} [NeZero q] (hq : IsUnit (q : C)) {η ξ : C}
    (hη : aeval η (cyclotomic q ℤ) = 0) (hξ : aeval ξ (cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = η ^ (a : ZMod q).val := by
  obtain ⟨i, hi, he⟩ := (res_prim hq hη).eq_pow_of_pow_eq_one (ξ := residue C ξ) (by rw [← map_pow, pow_q hξ, map_one])
  have hηi : η ^ i = ξ := uniq hq (by rw [← pow_mul, mul_comm, pow_mul, pow_q hη, one_pow]) (pow_q hξ) (by rw [map_pow, he])
  have hc : i.Coprime q := ((prim hq hη).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hηi ▸ prim hq hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hηi]

theorem pow_inj {C : Type} [CommRing C] {q : ℕ} [NeZero q] {η : C} (hη : IsPrimitiveRoot η q) {a b : (ZMod q)ˣ}
    (h : η ^ (a : ZMod q).val = η ^ (b : ZMod q).val) : a = b :=
  Units.ext (ZMod.val_injective q (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

theorem exists_root {A : Type} [CommRing A] {q : ℕ} [NeZero q] (hq : IsUnit (q : A)) (hA : SH A) :
    ∃ ζ : A, aeval ζ (cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hS⟩ := hA
  haveI : NeZero ((q : ℕ) : ResidueField A) := ⟨by
    have := hq.map (residue A); rw [map_natCast] at this; exact this.ne_zero⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (cyclotomic q (ResidueField A))
    (ne_of_gt (degree_cyclotomic_pos q _ (Nat.pos_of_ne_zero (NeZero.ne q)))) (separable_cyclotomic q _)
  obtain ⟨a0, rfl⟩ := residue_surjective x
  have hd : IsUnit ((cyclotomic q A).derivative.eval a0) := by
    rw [← residue_ne_zero_iff_isUnit]
    have := (separable_cyclotomic q (ResidueField A)).aeval_derivative_ne_zero (x := residue A a0) (by
      rw [aeval_def, Algebra.algebraMap_self, eval₂_id]; exact hx)
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← map_cyclotomic q (residue A), derivative_map,
      Polynomial.eval_map, Polynomial.eval₂_hom] at this
    exact this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (cyclotomic q A) (cyclotomic.monic q A) a0 (by
    rw [← residue_eq_zero_iff, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, map_cyclotomic]; exact hx) hd
  exact ⟨a, (isRoot_iff q a).1 ha⟩

section Gen
variable {q : ℕ} [NeZero q] (i : ℤ) {C : Type} [CommRing C] [IsLocalRing C]

theorem pmod {η : C} (hη : IsPrimitiveRoot η q) (n : ℕ) : η ^ (n % q) = η ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hη.pow_eq_one, one_pow, mul_one]

def ex (η ξ : Prim q C) : (ZMod q)ˣ := Classical.choose (pow_rep η.2.1 η.2.2 ξ.2.2)

theorem ex_spec (η ξ : Prim q C) : ξ.1 = η.1 ^ (ex η ξ : ZMod q).val := Classical.choose_spec (pow_rep η.2.1 η.2.2 ξ.2.2)

theorem ex_pow (η ξ ζ : Prim q C) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : ex η ξ = ex η ζ * a := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, h, ex_spec η ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, pmod hη]

theorem ex_self (η : Prim q C) : ex η η = 1 := by
  have hη := prim η.2.1 η.2.2
  apply pow_inj hη
  rw [← ex_spec, Units.val_one, ZMod.val_one_eq_one_mod, pmod hη, pow_one]

def psi (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ => ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)))

theorem rel_le (η : Prim q C) : twRel q i C ≤ LinearMap.ker (psi i η) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, psi, Finsupp.linearCombination_single, ex_pow η ξ ζ a h,
    mul_zpow, Units.val_mul]
  apply ULift.ext
  simp [mul_comm]

def Psi (η : Prim q C) : ((Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  (twRel q i C).liftQ (psi i η) (rel_le i η)

def gen (η : Prim q C) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C := Submodule.Quotient.mk (Finsupp.single η 1)

theorem Psi_gen (η : Prim q C) : Psi i η (gen i η) = 1 := by
  simp [Psi, gen, psi, Finsupp.linearCombination_single, ex_self]
  rfl

theorem decomp (η : Prim q C) (z : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) : z = Psi i η z • gen i η := by
  induction z using Submodule.Quotient.induction_on with
  | H x =>
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [Submodule.Quotient.mk_add, map_add (f := _), add_smul, ← hx, ← hy]
  | single ξ c =>
    have hrel : Finsupp.single ξ (1 : ULift.{1} (ZMod q)) - Finsupp.single η (ULift.up (((ex η η * ex η ξ) ^ i : (ZMod q)ˣ) : ZMod q))
        ∈ twRel q i C := by
      refine Submodule.subset_span ⟨η, ξ, ex η ξ, ex_spec η ξ, ?_⟩
      rw [ex_self, one_mul]
    rw [ex_self, one_mul] at hrel
    have h1 : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q C →₀ ULift.{1} (ZMod q)) ⧸ twRel q i C) =
        ULift.up (((ex η ξ ^ i : (ZMod q)ˣ) : ZMod q)) • gen i η := by
      rw [gen, ← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
      exact (Submodule.Quotient.eq _).2 hrel
    have h2 : (Finsupp.single ξ c : Prim q C →₀ ULift.{1} (ZMod q)) = c • Finsupp.single ξ 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h2, Submodule.Quotient.mk_smul, h1, smul_smul]
    congr 1
    rw [map_smul, Psi_gen, smul_eq_mul, mul_one]

end Gen

theorem bij_ty {q : ℕ} [NeZero q] (i : ℤ) {X Y : Type} [CommRing X] [CommRing Y] [IsLocalRing X] [IsLocalRing Y]
    (g : X →+* Y) (ζ : Prim q X) :
    Function.Bijective (Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)) := by
  set F := Submodule.mapQ (twRel q i X) (twRel q i Y) (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
      (Prim.map g)) (twRel_le q i g)
  have hF : ∀ z, F z = Psi i ζ z • gen i (Prim.map g ζ) := by
    intro z
    conv_lhs => rw [decomp i ζ z]
    rw [map_smul]
    congr 1
    simp only [F, gen, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  have hP : ∀ z, Psi i (Prim.map g ζ) (F z) = Psi i ζ z := by
    intro z
    rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
  refine ⟨fun z1 z2 h => ?_, fun w => ⟨Psi i (Prim.map g ζ) w • gen i ζ, ?_⟩⟩
  · rw [decomp i ζ z1, decomp i ζ z2, ← hP z1, ← hP z2, h]
  · rw [hF, map_smul, Psi_gen, smul_eq_mul, mul_one]
    exact (decomp i _ w).symm

theorem bij_gen {q : ℕ} [NeZero q] (i : ℤ) {X Y : CommRingCat.{0}} [IsLocalRing X] [IsLocalRing Y] (g : X ⟶ Y)
    (ζ : Prim q X) : Function.Bijective ((twF q i).map g).hom :=
  bij_ty i g.hom ζ

theorem TwFBij_of : LateralTheory.E.SHEqvPf.TwFBij := by
  intro q _ i A B f hq hA hB
  obtain ⟨hHA, hSA⟩ := hA
  obtain ⟨hHB, -⟩ := hB
  have hloc : ∀ (R : CommRingCat.{0}), IsLocalRing R → IsLocalRing Γ(Spec R, ⊤) := by
    intro R _
    let e := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    haveI : Nontrivial Γ(Spec R, ⊤) := e.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  haveI := hloc A inferInstance
  haveI := hloc B inferInstance
  obtain ⟨ζ, hζ⟩ := exists_root hq ⟨hHA, hSA⟩
  exact bij_gen i _ (Prim.map (Scheme.ΓSpecIso A).inv.hom ⟨ζ, hq, hζ⟩)

end LateralTheory.E.TwFBijPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocTensorPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.LocTensorPf

theorem isLocalRing_of_maximal_over_and_power_in_range (Z X B : Type) [CommRing Z] [CommRing X] [CommRing B] [IsLocalRing X] [IsLocalRing B] [Nontrivial Z]
    (u : X →+* Z) (v : B →+* Z)
    (hM : ∀ M : Ideal Z, M.IsMaximal → IsLocalRing.maximalIdeal X ≤ M.comap u ∧ IsLocalRing.maximalIdeal B ≤ M.comap v)
    (hF : ∀ z : Z, ∃ N : ℕ, 0 < N ∧ ∃ y : X,
      z ^ N - u y ∈ Ideal.map u (IsLocalRing.maximalIdeal X) ⊔ Ideal.map v (IsLocalRing.maximalIdeal B)) :
    IsLocalRing Z := by
  have hJ : ∀ M : Ideal Z, M.IsMaximal →
      Ideal.map u (IsLocalRing.maximalIdeal X) ⊔ Ideal.map v (IsLocalRing.maximalIdeal B) ≤ M := by
    intro M hMm
    obtain ⟨h1, h2⟩ := hM M hMm
    exact sup_le (Ideal.map_le_iff_le_comap.mpr h1) (Ideal.map_le_iff_le_comap.mpr h2)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨N, hN, y, hy⟩ := hF z
  by_cases hyu : IsUnit y
  · left
    by_contra hz
    obtain ⟨M, hMm, hzM⟩ := Ideal.exists_le_maximal (Ideal.span {z}) (by
      rwa [Ne, Ideal.span_singleton_eq_top])
    have hzM' : z ∈ M := hzM (Ideal.mem_span_singleton_self z)
    have h1 : z ^ N - u y ∈ M := hJ M hMm hy
    have h2 : z ^ N ∈ M := M.pow_mem_of_mem hzM' N hN
    have h3 : u y ∈ M := by
      have := M.sub_mem h2 h1; simpa using this
    exact hMm.ne_top (M.eq_top_of_isUnit_mem h3 (hyu.map u))
  · right
    by_contra hz
    obtain ⟨M, hMm, hzM⟩ := Ideal.exists_le_maximal (Ideal.span {1 - z}) (by
      rwa [Ne, Ideal.span_singleton_eq_top])
    have hzM' : 1 - z ∈ M := hzM (Ideal.mem_span_singleton_self _)
    have hyM : u y ∈ M := by
      have : y ∈ IsLocalRing.maximalIdeal X := hyu
      exact (hM M hMm).1 this
    have h2 : z ^ N ∈ M := by
      have := M.add_mem (hJ M hMm hy) hyM; simpa using this
    have hz' : z ∈ M := hMm.isPrime.mem_of_pow_mem N h2
    exact hMm.ne_top ((Ideal.eq_top_iff_one M).mpr (by simpa using M.add_mem hzM' hz'))

open IsLocalRing in
theorem maxOver {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z) (hp : IsPushout x b u v)
    [IsLocalRing A] [IsLocalRing X] [IsLocalRing B] (hx : IsLocalHom x.hom) (hb : b.hom.IsIntegral)
    (M : Ideal Z) (hM : M.IsMaximal) :
    maximalIdeal X ≤ M.comap u.hom ∧ maximalIdeal B ≤ M.comap v.hom := by
  have hu : u.hom.IsIntegral := LateralTheory.E.SHTensorPf.intPush hp hb
  have hX : (M.comap u.hom).IsMaximal := by
    let _ := u.hom.toAlgebra
    have : Algebra.IsIntegral X Z := ⟨hu⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal u.hom hu M
  have hXe : M.comap u.hom = maximalIdeal X := IsLocalRing.eq_maximalIdeal hX
  have hw : u.hom.comp x.hom = v.hom.comp b.hom := by
    have := congrArg CommRingCat.Hom.hom hp.w; simpa using this
  have hA : ((M.comap v.hom).comap b.hom) = maximalIdeal A := by
    rw [Ideal.comap_comap, ← hw, ← Ideal.comap_comap, hXe]
    ext a
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff x.hom a)
  have hB : (M.comap v.hom).IsMaximal := by
    let _ := b.hom.toAlgebra
    have : Algebra.IsIntegral A B := ⟨hb⟩
    have : (M.comap v.hom).IsPrime := Ideal.comap_isPrime v.hom M
    have hA' : ((M.comap v.hom).comap (algebraMap A B)).IsMaximal := by
      change ((M.comap v.hom).comap b.hom).IsMaximal
      rw [hA]; exact IsLocalRing.maximalIdeal.isMaximal A
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap b.hom hb (M.comap v.hom) hA'
  exact ⟨hXe.symm.le, (IsLocalRing.eq_maximalIdeal hB).symm.le⟩

open IsLocalRing in
theorem locHom_of_int {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (b : A →+* B)
    (hb : b.IsIntegral) : IsLocalHom b := by
  have hm : ((maximalIdeal B).comap b).IsMaximal := by
    let _ := b.toAlgebra
    have : Algebra.IsIntegral A B := ⟨hb⟩
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal b hb (maximalIdeal B)
  have he := IsLocalRing.eq_maximalIdeal hm
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have : a ∈ (maximalIdeal B).comap b := by rw [he]; exact hna
  exact (IsLocalRing.mem_maximalIdeal _).mp this ha

open IsLocalRing in
theorem resInt {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (b : A →+* B)
    (hb : b.IsIntegral) [IsLocalHom b] : (ResidueField.map b).IsIntegral := by
  intro y
  obtain ⟨y0, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨p, hpm, hp⟩ := hb y0
  have hc : (ResidueField.map b).comp (residue A) = (residue B).comp b := by
    ext a; simp [ResidueField.map_residue]
  refine ⟨p.map (residue A), hpm.map _, ?_⟩
  rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hp, map_zero]

open IsLocalRing in
theorem nontriv {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z) (hp : IsPushout x b u v)
    [IsLocalRing A] [IsLocalRing X] [IsLocalRing B] (hx : IsLocalHom x.hom) (hb : b.hom.IsIntegral) : Nontrivial Z := by
  have : IsLocalHom b.hom := locHom_of_int b.hom hb
  let K := AlgebraicClosure (ResidueField X)
  let e : ResidueField A →+* K := (algebraMap (ResidueField X) K).comp (ResidueField.map x.hom)
  let _ : Algebra (ResidueField A) K := e.toAlgebra
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map b.hom).toAlgebra
  have : Algebra.IsIntegral (ResidueField A) (ResidueField B) := ⟨resInt b.hom hb⟩
  have : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := inferInstance
  let l : ResidueField B →ₐ[ResidueField A] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f : X →+* K := (algebraMap (ResidueField X) K).comp (residue X)
  let g : B →+* K := l.toRingHom.comp (residue B)
  have hw : x ≫ CommRingCat.ofHom f = b ≫ CommRingCat.ofHom g := by
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, f, g]
    rw [← ResidueField.map_residue x.hom, ← ResidueField.map_residue b.hom]
    have := l.commutes (residue A a)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show (ResidueField.map b.hom) (residue A a) = algebraMap (ResidueField A) (ResidueField B) (residue A a) from rfl, this]
    rfl
  let d : Z ⟶ CommRingCat.of K := hp.desc (CommRingCat.ofHom f) (CommRingCat.ofHom g) hw
  exact d.hom.domain_nontrivial

theorem frobAdd {R : Type} [CommRing R] (q n : ℕ) (hq : q = 1 ∨ (q.Prime ∧ (q : R) = 0)) (a b : R) :
    (a + b) ^ (q ^ n) = a ^ (q ^ n) + b ^ (q ^ n) := by
  rcases hq with rfl | ⟨hpr, h0⟩
  · simp
  · rcases subsingleton_or_nontrivial R with hs | hs
    · exact Subsingleton.elim _ _
    · have : Fact q.Prime := ⟨hpr⟩
      have : CharP R q := (CharP.charP_iff_prime_eq_zero hpr).mpr h0
      exact add_pow_char_pow a b q n

theorem gen {A X B Z : CommRingCat.{0}} {x : A ⟶ X} {b : A ⟶ B} {u : X ⟶ Z} {v : B ⟶ Z} (hp : IsPushout x b u v)
    (z : Z) : z ∈ Subring.closure (Set.range u.hom ∪ Set.range v.hom) := by
  set T := Subring.closure (Set.range u.hom ∪ Set.range v.hom)
  let u' : X ⟶ CommRingCat.of T := CommRingCat.ofHom (u.hom.codRestrict T
    (fun y => Subring.subset_closure (Or.inl ⟨y, rfl⟩)))
  let v' : B ⟶ CommRingCat.of T := CommRingCat.ofHom (v.hom.codRestrict T
    (fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)))
  let ι : CommRingCat.of T ⟶ Z := CommRingCat.ofHom T.subtype
  have hw : x ≫ u' = b ≫ v' := by
    ext a
    have := congrArg (fun f => f.hom a) hp.w
    simpa [u', v'] using this
  let s := hp.desc u' v' hw
  have hs : s ≫ ι = 𝟙 Z := by
    apply hp.hom_ext
    · rw [← Category.assoc, hp.inl_desc]; ext y; rfl
    · rw [← Category.assoc, hp.inr_desc]; ext y; rfl
  have : z = ι.hom (s.hom z) := by
    have := congrArg (fun f => f.hom z) hs; simpa using this.symm
  rw [this]; exact (s.hom z).2

open IsLocalRing in
theorem frob {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z) (hp : IsPushout x b u v)
    [IsLocalRing A] [IsLocalRing X] [IsLocalRing B] [IsSepClosed (ResidueField A)]
    (hx : IsLocalHom x.hom) (hb : b.hom.IsIntegral) (z : Z) : ∃ N : ℕ, 0 < N ∧ ∃ y : X,
      z ^ N - u.hom y ∈ Ideal.map u.hom (maximalIdeal X) ⊔ Ideal.map v.hom (maximalIdeal B) := by
  have : IsLocalHom b.hom := locHom_of_int b.hom hb
  set J := Ideal.map u.hom (maximalIdeal X) ⊔ Ideal.map v.hom (maximalIdeal B) with hJ
  have hw : u.hom.comp x.hom = v.hom.comp b.hom := by
    have := congrArg CommRingCat.Hom.hom hp.w; simpa using this
  have hwa : ∀ a, u.hom (x.hom a) = v.hom (b.hom a) := fun a => by
    have := congrArg (fun f => f a) hw; simpa using this
  have huJ : ∀ y ∈ maximalIdeal X, u.hom y ∈ J := fun y hy =>
    Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hy)
  have hvJ : ∀ y ∈ maximalIdeal B, v.hom y ∈ J := fun y hy =>
    Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hy)
  set q := ringExpChar (ResidueField A) with hqdef
  have hexp : ExpChar (ResidueField A) q := ringExpChar.expChar _
  have key : ∀ r : ℕ, ExpChar (ResidueField A) r → r = 1 ∨ (r.Prime ∧ ((r : ℕ) : Z ⧸ J) = 0) := by
    intro q hexp
    rcases hexp with _ | ⟨hpr⟩
    · left; rfl
    · right; refine ⟨hpr, ?_⟩
      have h1 : ((q : A)) ∈ maximalIdeal A := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ q
      have h2 : x.hom (q : A) ∈ maximalIdeal X := map_nonunit x.hom _ h1
      have h3 := huJ _ h2
      rw [map_natCast, map_natCast] at h3
      rw [← map_natCast (Ideal.Quotient.mk J)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have hq := key q hexp
  have hq1 : 0 < q := by rcases hq with h | ⟨h, _⟩; · omega
                         · exact h.pos
  let mk := Ideal.Quotient.mk J
  let P : Z → Prop := fun z => ∃ n : ℕ, ∃ y : X, mk (z ^ (q ^ n)) = mk (u.hom y)
  have lift : ∀ z n k y, mk (z ^ (q ^ n)) = mk (u.hom y) → mk (z ^ (q ^ (n + k))) = mk (u.hom (y ^ (q ^ k))) := by
    intro z n k y h
    rw [pow_add, pow_mul, map_pow, h, ← map_pow, ← map_pow]
  have hadd : ∀ z w, P z → P w → P (z + w) := by
    rintro z w ⟨n, y, hy⟩ ⟨m, y', hy'⟩
    refine ⟨n + m, y ^ (q ^ m) + y' ^ (q ^ n), ?_⟩
    rw [map_pow, map_add (f := _), frobAdd q _ hq, ← map_pow, ← map_pow, lift z n m y hy, add_comm n m,
      lift w m n y' hy', map_add, map_add]
  have hmul : ∀ z w, P z → P w → P (z * w) := by
    rintro z w ⟨n, y, hy⟩ ⟨m, y', hy'⟩
    refine ⟨n + m, y ^ (q ^ m) * y' ^ (q ^ n), ?_⟩
    rw [mul_pow, map_mul, lift z n m y hy, add_comm n m, lift w m n y' hy', map_mul, map_mul]
  have hu : ∀ y, P (u.hom y) := fun y => ⟨0, y, by simp⟩
  have hv : ∀ y, P (v.hom y) := by
    intro y
    let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map b.hom).toAlgebra
    have : Algebra.IsIntegral (ResidueField A) (ResidueField B) := ⟨resInt b.hom hb⟩
    have : Algebra.IsAlgebraic (ResidueField A) (ResidueField B) := inferInstance
    have : IsPurelyInseparable (ResidueField A) (ResidueField B) :=
      Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem (ResidueField A) q (residue B y)
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨n, x.hom a, ?_⟩
    have h1 : y ^ (q ^ n) - b.hom a ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ← hc]
      change ResidueField.map b.hom (residue A a) - _ = 0
      rw [ResidueField.map_residue, sub_self]
    have h2 := hvJ _ h1
    rw [map_sub, map_pow, ← hwa] at h2
    exact Ideal.Quotient.eq.mpr h2
  have hz : P z := by
    have hg := gen hp z
    induction hg using Subring.closure_induction with
    | mem w hw' => rcases hw' with ⟨y, rfl⟩ | ⟨y, rfl⟩; exacts [hu y, hv y]
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add _ _ _ _ h1 h2 => exact hadd _ _ h1 h2
    | neg w _ h =>
      have : -w = u.hom (-1) * w := by simp
      rw [this]; exact hmul _ _ (hu _) h
    | mul _ _ _ _ h1 h2 => exact hmul _ _ h1 h2
  obtain ⟨n, y, hy⟩ := hz
  exact ⟨q ^ n, pow_pos hq1 n, y, Ideal.Quotient.eq.mp hy⟩

theorem LocTensor_of : LateralTheory.E.SHTensorPf.LocTensor := by
  intro A X B Z x b u v hp hA hX hx hb hB
  obtain ⟨hAh, hAs⟩ := hA
  obtain ⟨hXh, _⟩ := hX
  have := nontriv x b u v hp hx hb
  exact isLocalRing_of_maximal_over_and_power_in_range Z X B u.hom v.hom (fun M hM => maxOver x b u v hp hx hb M hM) (frob x b u v hp hx hb)

end LateralTheory.E.LocTensorPf
end
end
