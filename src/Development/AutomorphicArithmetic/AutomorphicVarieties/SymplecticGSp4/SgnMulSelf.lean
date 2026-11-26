module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem wt_add' (i k j : Fin 4) : wt i j = wt i k + wt k j := by
  simp only [wt, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

private theorem wt_self' (i : Fin 4) : wt i i = 0 := by
  simp [wt]

variable {R : Type} [CommRing R]

private theorem wv_add' (t : Rˣ × Rˣ) (a b : ℤ × ℤ) : wv t (a + b) = wv t a * wv t b := by
  simp only [wv, Prod.fst_add, Prod.snd_add, zpow_add]
  rw [mul_mul_mul_comm]

private theorem wv_zero' (t : Rˣ × Rˣ) : wv t 0 = 1 := by simp [wv]

private theorem adj_mul' (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn] <;> ring

private theorem adj_adj' (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn]

private theorem adj_smul' (a : R) (X : M4 R) : adj (a • X) = a • adj X := by
  ext i j
  simp only [adj_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_smul_comm]

private theorem adj_one' : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Matrix.one_apply]

private theorem tconj_apply' (t : Rˣ × Rˣ) (X : M4 R) (i j : Fin 4) : tconj t X i j = (wv t (wt i j) : R) * X i j := rfl

private theorem tconj_unit' (t : Rˣ × Rˣ) : ∃ u : (M4 R)ˣ, ∀ X, tconj t X = u * X * (u⁻¹ : (M4 R)ˣ) := by
  let d : Fin 4 → Rˣ := fun i => wv t (lamW i, muW i)
  have key : ∀ i j, wv t (wt i j) = d i * (d j)⁻¹ := by
    intro i j
    rw [eq_mul_inv_iff_mul_eq, ← wv_add']
    congr 1
    simp [wt]
  let u : (M4 R)ˣ := ⟨Matrix.diagonal fun i => (d i : R), Matrix.diagonal fun i => ((d i)⁻¹ : Rˣ),
    by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one], by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]⟩
  refine ⟨u, fun X => ?_⟩
  ext i j
  simp only [u, Units.inv_mk, tconj_apply', key, Units.val_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.grp :
    ∀ (R : Type) [CommRing R], (∀ X Y : M4 R, adj (X * Y) = adj Y * adj X) ∧ (∀ X : M4 R, adj (adj X) = X) ∧ (∀ X Y : M4 R, adj (X + Y) = adj X + adj Y) ∧ (∀ (a : R) (X : M4 R), adj (a • X) = a • adj X) ∧ adj (1 : M4 R) = 1 ∧ (∀ (R' : Type) [CommRing R'] (f : R →+* R') (X : M4 R), adj (X.map f) = (adj X).map f) ∧ (∀ (ν : R) (g g' : M4 R), IsGSp ν g → g * g' = 1 → adj g = ν • g') ∧ (∀ (ν ν' : R) (g g' : M4 R), IsGSp ν g → IsGSp ν' g' → IsGSp (ν * ν') (g * g')) ∧ (∀ (t : Rˣ × Rˣ) (X Y : M4 R), tconj t (X * Y) = tconj t X * tconj t Y) ∧ (∀ t : Rˣ × Rˣ, tconj t (1 : M4 R) = 1) ∧ (∀ (t : Rˣ × Rˣ) (X : M4 R), adj (tconj t X) = tconj t (adj X)) ∧ (∀ (t : Rˣ × Rˣ) (X : M4 R), (tconj t X).trace = X.trace) ∧ (∀ t : Rˣ × Rˣ, ∃ u : (M4 R)ˣ, ∀ X, tconj t X = u * X * (u⁻¹ : (M4 R)ˣ)) := by
  intro R _
  refine ⟨adj_mul', adj_adj', ?_, adj_smul', adj_one', ?_, ?_, ?_, ?_, ?_, ?_, ?_, tconj_unit'⟩
  · intro X Y
    ext i j
    simp [adj_apply]
  · intro R' _ f X
    ext i j
    simp [adj_apply, Matrix.map_apply]
  · intro ν g g' hg h
    have hg' : adj g * g = ν • 1 := hg
    calc adj g = adj g * (g * g') := by rw [h, mul_one]
      _ = adj g * g * g' := (mul_assoc _ _ _).symm
      _ = ν • g' := by rw [hg', smul_mul_assoc, one_mul]
  · intro ν ν' g g' hg hg'
    have h1 : adj g * g = ν • 1 := hg
    have h2 : adj g' * g' = ν' • 1 := hg'
    show adj (g * g') * (g * g') = (ν * ν') • 1
    rw [adj_mul', mul_assoc, ← mul_assoc (adj g), h1, smul_mul_assoc, one_mul, mul_smul_comm, h2,
      smul_smul]
  · intro t X Y
    ext i j
    simp only [tconj_apply', Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [wt_add' i k j, wv_add', Units.val_mul]
    ring
  · intro t
    ext i j
    rw [tconj_apply', Matrix.one_apply]
    split_ifs with h
    · subst h
      simp [wt_self', wv_zero']
    · simp
  · intro t X
    ext i j
    simp only [adj_apply, tconj_apply']
    rw [wt_rev, mul_smul_comm]
  · intro t X
    simp [Matrix.trace, tconj_apply', wt_self', wv_zero']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.GradeZeroInterpolatingElement

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def w4 (i : Fin 4) : ℤ × ℤ := (lamW i, muW i)

theorem w4_sub_w4_eq_wt (i j : Fin 4) : w4 i - w4 j = wt i j := rfl

def J4 (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

def form (O : Type) [CommRing O] : FormData O w4 where
  J := J4 O
  unit := IsUnit.of_mul_eq_one (-J4 O) (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J4, Matrix.mul_apply, Fin.sum_univ_four])
  sym := Or.inr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J4])
  κ := Unit
  blk _ := ()
  σ := id
  invol _ := rfl
  hblk _ _ _ := rfl
  c := (1, 1)
  hw a b h := by
    fin_cases a <;> fin_cases b <;> simp [J4] at h <;> decide

namespace Raw

variable (D : Raw Ω c)

theorem residueChar_mem_levelPrimes : l ∈ D.T := Finset.mem_insert_self _ _

theorem mem_T {p : ℕ} (hp : p ∈ D.Sb) : p ∈ D.T := Finset.mem_insert_of_mem hp

def LocEqs {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) R) : Prop :=
  D.eqL (ρ ⟨l, D.residueChar_mem_levelPrimes⟩).hom ∧ ∀ p (hp : p ∈ D.Sb), D.eqP p (ρ ⟨p, D.mem_T hp⟩).hom

def SP : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | ∃ p ∈ D.S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}

abbrev Gam : Type := GS Ω D.SP

def frame : Frame D.Gam where
  T := D.T
  v0 := ⟨l, D.residueChar_mem_levelPrimes⟩
  Gv v := D.Gp v
  φ v := locHom D.SP (D.pl v)
  hφ v := continuous_locHom D.SP (D.pl v)
  Q := (D.S \ D.T : Finset ℕ)
  Gq q := D.Gp q
  ψ q := locHom D.SP (D.pl q)
  hψ q := continuous_locHom D.SP (D.pl q)
  N q := (D.Ip q ⊓ D.rbar.ker).subgroupOf (D.Gp q)

def Nums : Prop :=
  ∀ (rb : D.Gam →* M4 (ResidueField c.O)), rb.comp (toGS Ω D.SP) = D.rbar → ∀ (h : (form c.O).Normalises rb) (j : ℤ × ℤ),
    Module.Finite (ResidueField c.O) (D.frame.Ob (FormData.adRep h j)) ∧
    Module.finrank (ResidueField c.O) (D.frame.Ob (FormData.adRep h j)) =
      Module.finrank (ResidueField c.O) (D.frame.H1c (FormData.adRep h j)) +
        (if j = 0 then 2 else if j = wPs ∨ j = -wPs then 1 else 0) ∧
    (j ≠ 0 → j ≠ wPs → j ≠ -wPs → Module.finrank (ResidueField c.O) (D.frame.H1c (FormData.adRep h j)) = 0)

end Raw

structure LocBase (D : Raw Ω c) where
  B : Type
  [cB : CommRing B]
  [aB : Algebra c.O B]
  [coB : IsCO c.O B]
  W : WPres c.O (ℤ × ℤ) B
  wt_mem : ∀ i, W.wt i ∈ wts
  org : W.HasOrigin
  ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) B
  eqs : D.LocEqs ρ
  univ : ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ' : ∀ v : D.T, Lift c.O (D.rbarAt v) R), D.LocEqs ρ' →
    ∃! f : B →ₐ[c.O] R, ∀ v, (ρ v).map f = ρ' v
  hom : ∀ (v : D.T) g i j, (ρ v).hom g i j ∈ W.part (wt i j)
  at0 : ∀ (v : D.T) (g : D.Gp v) i j, W.origin org ((ρ v).hom g i j) = D.r0 g i j
  smooth : SmoothPt W.gr ((W.origin org).comp W.A.val) fun j => dimL j + D.Sb.card * dimP j

attribute [instance] LocBase.cB LocBase.aB LocBase.coB

end UpperTheory.V.GradeZeroInterpolatingElement

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.IrrIff
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleIffStable
theorem UpperTheory.Reformulated.B.StableSubmoduleBotOrTopOfSpanEqTop.irrIff_stable :
    ∀ {H K : Type} [inst : Group H] [inst_1 : Field K] {n : ℕ}
    (r : H →* Matrix (Fin n) (Fin n) K),
    Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) = ⊤ →
      ∀ (W : Submodule K (Fin n → K)),
        (∀ (g : H), ∀ v ∈ W, ((r : H → Matrix (Fin n) (Fin n) K) g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro H K _ _ n r hspan W hW
  have hall : ∀ (A : Matrix (Fin n) (Fin n) K), ∀ v ∈ W, A.mulVec v ∈ W := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hW g v hv
    | zero => rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h := hall (Matrix.of fun a b => if b = i then w a / v i else 0) v hv
    have e : (Matrix.of fun a b => if b = i then w a / v i else 0 :
        Matrix (Fin n) (Fin n) K).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [e] at h
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem irrIff_stable {H K : Type} [Group H] [Field K] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) K)
    (h : Submodule.span K (Set.range r) = ⊤) (W : Submodule K (Fin n → K))
    (hW : ∀ g, ∀ v ∈ W, (r g).mulVec v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  _root_.UpperTheory.Reformulated.B.StableSubmoduleBotOrTopOfSpanEqTop.irrIff_stable r h W hW

theorem UpperTheory.V.GradeZeroInterpolatingElement.irrIff :
    ∀ {H : Type} [Group H] (K : Type) [Field K] [IsAlgClosed K], (∀ r : H →* M4 K, Irr r ↔ Af.IsIrr r.toHomUnits) ∧ ∀ r r' : H →* M4 K, IsConj4 r r' ↔ Af.RepIso r.toHomUnits r'.toHomUnits := by
  intro H _ K _ _
  refine ⟨fun r => ⟨fun h => ?_, fun h => ?_⟩, fun r r' => ⟨?_, ?_⟩⟩
  · exact ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => irrIff_stable r h W hW⟩
  · exact KStar.Schema.span_eq_top_of_irreducible r fun N hN => h.2.2 N le_top hN
  · rintro ⟨u, hu⟩
    exact ⟨u, fun s => Units.ext (hu s)⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, fun s => congrArg Units.val (hu s)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_mul {H : Type} [Group H] {K : Type} [Field K] (r : H →* M4 K) {x y : M4 K}
    (hx : x ∈ Submodule.span K (Set.range r)) (hy : y ∈ Submodule.span K (Set.range r)) :
    x * y ∈ Submodule.span K (Set.range r) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, rfl⟩ := ha
      obtain ⟨h, rfl⟩ := hb
      exact Submodule.subset_span ⟨g * h, map_mul r g h⟩
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add b c _ _ hb hc => rw [add_mul]; exact add_mem hb hc
  | smul c b _ hb => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hb

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_top {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (S : Submodule K (Matrix n n K)) (h : ∀ i j, Matrix.single i j (1 : K) ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Matrix.matrix_eq_sum_single x]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have := S.smul_mem (x i j) (h i j)
  simpa [Matrix.smul_single] using this

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_iff {H : Type} [Group H] {K : Type} [Field K] (r : H →* M4 K)
    (he : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) (i j : Fin 4) :
    Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r) := by
  constructor
  · rintro ⟨g, hg⟩
    have h1 := geAlg_mul r (geAlg_mul r (he i) (Submodule.subset_span ⟨g, rfl⟩)) (he j)
    have h2 := Submodule.smul_mem _ (r g i j)⁻¹ h1
    rw [Matrix.single_mul_mul_single, Matrix.smul_single] at h2
    simpa [hg] using h2
  · intro h
    by_contra hn
    have hz : ∀ g, r g i j = 0 := fun g => by
      by_contra h'
      exact hn ⟨g, h'⟩
    have key : ∀ x ∈ Submodule.span K (Set.range r), x i j = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem a ha => obtain ⟨g, rfl⟩ := ha; exact hz g
      | zero => rfl
      | add b c _ _ hb hc => simp [hb, hc]
      | smul c b _ hb => simp [hb]
    simpa using key _ h

theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg :
    ∀ {H : Type} [Group H] (K : Type) [Field K] (r : H →* M4 K) (ν : H → K), (∀ g, IsGSp (ν g) (r g)) → (∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) → (∀ i j, Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r)) ∧ (∀ i, Ge r i i) ∧ (∀ i j k, Ge r i j → Ge r j k → Ge r i k) ∧ (∀ i j, Ge r i j → Ge r j.rev i.rev) ∧ (Irr r ↔ ∀ i j, Ge r i j) ∧ (Ge r 0 2 → Ge r 2 0 → (∀ g, IsBlock (r g)) → Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) = ⊤) := by
  intro H _ K _ r ν hν he
  have hiff := geAlg_iff r he
  refine ⟨hiff, fun i => (hiff i i).2 (he i), ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk
    have := geAlg_mul r ((hiff i j).1 hij) ((hiff j k).1 hjk)
    rw [Matrix.single_mul_single_same, mul_one] at this
    exact (hiff i k).2 this
  · rintro i j ⟨g, hg⟩
    refine ⟨g⁻¹, fun h0 => hg ?_⟩
    have h1 : adj (r g) = ν g • r g⁻¹ := by
      have h2 : adj (r g) * r g * r g⁻¹ = ν g • (1 : M4 K) * r g⁻¹ := by rw [hν g]
      rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one, smul_mul_assoc, one_mul] at h2
    have h3 := congrFun (congrFun h1 j.rev) i.rev
    rw [adj_apply, Fin.rev_rev, Fin.rev_rev, Matrix.smul_apply, h0, smul_zero] at h3
    have h4 : ∀ a b : Fin 4, sgn a * sgn b = 1 ∨ sgn a * sgn b = -1 := by decide
    rcases h4 j.rev i.rev with h | h <;> rw [h] at h3 <;> simpa using h3
  · constructor
    · intro h i j
      rw [hiff, h]
      trivial
    · intro h
      exact geAlg_top _ fun i j => (hiff i j).1 (h i j)
  · intro h02 h20 _
    let f : M4 K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
      { toFun := fun x => x.submatrix ixA ixA
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hm : ∀ x ∈ Submodule.span K (Set.range r),
        f x ∈ Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) := by
      intro x hx
      have := Submodule.mem_map_of_mem (f := f) hx
      rwa [Submodule.map_span, ← Set.range_comp] at this
    have hs : ∀ a b : Fin 2, f (Matrix.single (ixA a) (ixA b) (1 : K)) = Matrix.single a b 1 := by
      intro a b
      ext c d
      have hinj : ∀ a b : Fin 2, ixA a = ixA b ↔ a = b := by decide
      show Matrix.single (ixA a) (ixA b) (1 : K) (ixA c) (ixA d) = _
      simp only [Matrix.single_apply, hinj]
    refine geAlg_top _ fun a b => ?_
    rw [← hs]
    apply hm
    fin_cases a <;> fin_cases b
    · exact he 0
    · exact (hiff 0 2).1 h02
    · exact (hiff 2 0).1 h20
    · exact he 2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem part_indep {O X R : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R]
    (W : WPres O X R) : iSupIndep W.part := by
  have h := (W.A.val.toLinearMap.iSupIndep_map Subtype.val_injective
    (gr_internal O X R W).submodule_iSupIndep)
  convert h using 1
  funext j
  rw [WPres.gr, Submodule.map_comap_eq, eq_comm, inf_eq_right]
  intro x hx
  exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩

private theorem part_gen {O X R : Type} [CommRing O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [CommRing R] [Algebra O R] (W : WPres O X R) :
    Algebra.adjoin O ((W.part 0 : Set R) ∪ Set.range W.z) = W.A := by
  have h := congrArg (Subalgebra.map W.A.val) (gr_gen O R X W)
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val] at h
  rw [← h]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    constructor
    · intro hx
      exact ⟨⟨x, W.part_le_A hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · ext x
    simp [WPres.zA, WPres.z]

private theorem quot_pres {O X R S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing S] [Algebra O S] [IsCO O S] (W : WPres O X R) (org : W.HasOrigin) (π : R →ₐ[O] S)
    (surj : Function.Surjective π) {κ : Type} [Finite κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i))
    (ker : RingHom.ker π = Ideal.span (Set.range g)) :
    ∃ WS : WPres O X S, (∀ w, WS.part w = (W.part w).map π.toLinearMap) ∧ ∀ i, WS.z i ∈ maximalIdeal S := by
  have hz : ∀ i, W.z i ∈ maximalIdeal R := by
    intro i
    let ψ : R →+* ResidueField O := (IsLocalRing.residue O).comp (W.origin org).toRingHom
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨algebraMap O R a, by simp [ψ]⟩
    have heq : RingHom.ker ψ = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
    rw [← heq, RingHom.mem_ker]
    simp [ψ, WPres.z, WPres.origin_π]
  have hhom : IsHomog O W.wt (RingHom.ker (π.comp W.π)) := by
    have h := (homog_span O R X W κ (fun i => ⟨g i, W.part_le_A (hg i)⟩) c
      (fun i => Submodule.mem_comap.mpr (hg i))).1
    convert h using 1
    ext f
    rw [RingHom.mem_ker, Ideal.mem_comap]
    show π (W.π f) = 0 ↔ W.π f ∈ Ideal.span (Set.range g)
    rw [← ker, RingHom.mem_ker]
  refine ⟨W.quot π surj hhom, ?_, ?_⟩
  · intro w
    exact Submodule.map_comp W.π.toLinearMap π.toLinearMap (wtPart O W.wt w)
  · intro i
    show π (W.z i) ∈ maximalIdeal S
    rw [← res_eq_zero_iff O S, res_map, res_eq_zero_iff]
    exact hz i

theorem UpperTheory.V.GradeZeroInterpolatingElement.sInternal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, iSupIndep M.sPart ∧ (∃ s : Finset M.S, (∀ x ∈ s, ∃ w, x ∈ M.sPart w) ∧ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ s) = M.SS) ∧ ∃ WS : WPres c.O (ℤ × ℤ) M.S, (∀ w, WS.part w = M.sPart w) ∧ ∀ i, WS.z i ∈ maximalIdeal M.S := by
  intro Ω _ _ _ l _ c D _ M
  classical
  let g : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → M.R := Sum.elim M.F (Sum.elim M.E M.Z)
  let cw : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → ℤ × ℤ :=
    Sum.elim (fun _ => -wPs) (Sum.elim (fun _ => wPs) (fun _ => 0))
  have hg : ∀ i, g i ∈ M.W.part (cw i) := by
    rintro (i | i | i)
    · exact M.hF i
    · exact M.hE i
    · exact (M.hZ i).1
  have hker : RingHom.ker M.π = Ideal.span (Set.range g) := by
    rw [M.ker]
    simp only [g, Set.Sum.elim_range, Set.union_assoc]
  obtain ⟨WS, hpart, hzm⟩ := quot_pres M.W M.org M.π M.surj g cw hg hker
  have hp : WS.part = M.sPart := funext hpart
  have hA : WS.A = M.SS := by
    unfold WPres.A Model.SS
    congr
  haveI := WS.fin
  refine ⟨by rw [← hp]; exact part_indep WS, ⟨Finset.univ.image WS.z, ?_, ?_⟩, WS, hpart, hzm⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨WS.wt i, by rw [← hp]; exact WS.z_mem i⟩
  · rw [← hA, ← part_gen WS, ← hp]
    congr 2
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WcompMulHomog
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem wcomp_mul_homog (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
    {w : X} {e : MvPowerSeries σ O} (he : e ∈ wtPart O wt w) (G : MvPowerSeries σ O) (j : X) :
    wcomp O wt j (G * e) = wcomp O wt (j - w) G * e := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add (f := _), h2, add_sub_cancel_right]
    · rw [he _ h2, mul_zero, mul_zero]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = w
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      apply h
      rw [← hp', map_add (f := _), h1, h2, sub_add_cancel]
    · rw [he _ h2, mul_zero]

private theorem span_coeffs {O R X κ N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    (W : WPres O X R) [Fintype κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i)) (u : N → X)
    (B : Submodule O R) (hB : ∀ n i, W.part (u n - c i) ≤ B) (x : R) (hx' : x ∈ ⨆ n, W.part (u n))
    (hx : x ∈ Ideal.span (Set.range g)) : ∃ a : κ → R, (∀ i, a i ∈ B) ∧ x = ∑ i, a i * g i := by
  classical
  have hg' : ∀ i, ∃ e ∈ wtPart O W.wt (c i), W.π e = g i := fun i => hg i
  choose e he heg using hg'
  have hl : ∃ f, W.π f = x ∧ ∃ s : Finset X, (∀ j ∈ s, ∃ n, u n = j) ∧
      ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0 := by
    refine Submodule.iSup_induction (fun n => W.part (u n))
      (motive := fun z : R => ∃ f, W.π f = z ∧ ∃ s : Finset X, (∀ j ∈ s, ∃ n, u n = j) ∧
        ∀ n, Finsupp.weight W.wt n ∉ s → coeff n f = 0) hx' ?_ ?_ ?_
    · rintro i _ ⟨f, hf, rfl⟩
      exact ⟨f, rfl, {u i}, fun j hj => ⟨i, (Finset.mem_singleton.1 hj).symm⟩,
        fun n hn => hf n (by simpa using hn)⟩
    · exact ⟨0, map_zero _, ∅, by simp, fun n _ => map_zero _⟩
    · rintro a b ⟨f, hf, s, ht, hs⟩ ⟨f', hf', s', ht', hs'⟩
      refine ⟨f + f', by rw [map_add (f := _), hf, hf'], s ∪ s', fun j hj => ?_, fun n hn => ?_⟩
      · rcases Finset.mem_union.1 hj with h | h
        · exact ht j h
        · exact ht' j h
      · rw [Finset.mem_union, not_or] at hn
        rw [map_add (f := _), hs n hn.1, hs' n hn.2, add_zero]
  obtain ⟨f, hf, s, ht, hs⟩ := hl
  have hsum : f = ∑ j ∈ s, wcomp O W.wt j f := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · exact hs n h
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hx
  choose G hG using fun i => W.surj (a i)
  have h1 : f - ∑ i, G i * e i ∈ RingHom.ker W.π := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, hf, ← ha, map_sum]
    simp [hG, heg]
  have key : ∀ j, W.π (wcomp O W.wt j f) = ∑ i, W.π (wcomp O W.wt (j - c i) (G i)) * g i := by
    intro j
    have h2 := W.homog _ h1 j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wcomp_mul_homog O W.wt (he i), map_mul, heg]
  refine ⟨fun i => ∑ j ∈ s, W.π (wcomp O W.wt (j - c i) (G i)), fun i => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j hj => ?_
    obtain ⟨n, rfl⟩ := ht j hj
    exact hB n i ⟨_, wcomp_mem O W.wt _ _, rfl⟩
  · rw [← hf]
    conv_lhs => rw [hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [key, Finset.sum_mul]
    exact Finset.sum_comm

end SlopeTestRemainingChoices

theorem UpperTheory.V.GradeZeroInterpolatingElement.kerA :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, (∀ f : M.A, M.toSS f = 0 ↔ f ∈ M.eqns.ideal) ∧ (∀ n (x : M.SS), x.1 ∈ M.sPart (0, n) → ∃ f ∈ M.gr n, M.toSS f = x) ∧ ∀ n, ∀ f ∈ M.gr n, (M.toSS f).1 ∈ M.sPart (0, n) := by
  intro Ω _ _ _ l _ c D _ M
  refine ⟨fun f => ⟨fun hf => ?_, fun hf => ?_⟩, ?_, ?_⟩
  · have h0 : (f : M.R) ∈ RingHom.ker M.π := congrArg Subtype.val hf
    rw [M.ker, ← Set.Sum.elim_range, ← Set.Sum.elim_range] at h0
    obtain ⟨a, ha, hfa⟩ := span_coeffs M.W (Sum.elim (Sum.elim M.F M.E) M.Z)
      (fun i => ((0 : ℤ), Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => 1)) (fun _ => 0) i))
      (by
        rintro ((i | i) | i)
        · exact M.hF i
        · exact M.hE i
        · exact (M.hZ i).1)
      (fun n : ℤ => ((0 : ℤ), n)) (Subalgebra.toSubmodule M.A)
      (fun n i x hx => M.aPart_le (n := n - Sum.elim (Sum.elim (fun _ => (-1 : ℤ)) (fun _ => 1)) (fun _ => 0) i)
        (by simpa [Model.aPart] using hx))
      f f.2 h0
    have hf' : f = ∑ i, (⟨a i, ha i⟩ : M.A) * Sum.elim (Sum.elim M.eqns.F M.eqns.E) M.eqns.Z i := by
      apply Subtype.ext
      rw [hfa, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl ?_
      rintro ((i | i) | i) - <;> rfl
    rw [hf']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    rcases i with (i | i) | i
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))
    · exact Or.inr ⟨i, rfl⟩
  · have hle : M.eqns.ideal ≤ RingHom.ker M.toSS := by
      refine Ideal.span_le.2 fun x hx => ?_
      have hk : (x : M.R) ∈ RingHom.ker M.π := by
        rw [M.ker]
        refine Ideal.subset_span ?_
        rcases hx with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
        · exact Or.inl (Or.inl ⟨i, rfl⟩)
        · exact i.elim0
        · exact Or.inl (Or.inr ⟨i, rfl⟩)
        · exact i.elim0
        · exact Or.inr ⟨i, rfl⟩
      exact Subtype.ext hk
    exact hle hf
  · rintro n x ⟨f, hf, hfx⟩
    exact ⟨⟨f, M.aPart_le (n := n) hf⟩, hf, Subtype.ext hfx⟩
  · intro n f hf
    exact ⟨f, hf, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompMap
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

section

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem adj_map' (f : R →+* R') (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp [adj_apply, RingHom.mapMatrix_apply]

private theorem smul_map' (f : R →+* R') (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

private theorem isGSp_map (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) : IsGSp (f ν) (f.mapMatrix g) := by
  unfold IsGSp at h ⊢
  have h2 := congrArg f.mapMatrix h
  rw [map_mul, smul_map', map_one, ← adj_map'] at h2
  exact h2

private theorem aeval_map' (f : R →+* R') (X : M4 R) (p : Polynomial R) :
    Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp

private theorem prj_map (f : R →+* R') (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  simp only [prj]
  rw [← aeval_map']
  congr 1
  simp [Polynomial.map_prod]

private theorem ord_map {H : Type} [Group H] (f : R →+* R') {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H}
    {r : H →* M4 R} {r' : H →* M4 R'} (hr : ∀ g, r' g = f.mapMatrix (r g)) {ps' : Fin 4 → H → R'}
    (hps : ∀ i g, ps' i g = f (ps i g)) (h : Ord I ps s₀ r) : Ord I ps' s₀ r' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hr, hps]
    rw [RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp
  · intro g i j hij
    simp only [hr, hps]
    rw [prj_map, prj_map, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · intro s hs i
    simp only [hr, hps]
    have e : f.mapMatrix (r s) - f (ps i s) • (1 : M4 R') = f.mapMatrix (r s - ps i s • 1) := by
      rw [map_sub, smul_map', map_one]
    rw [prj_map, e, ← map_mul, ← map_mul, h.inert s hs i, map_zero]

end

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] {R' : Type} [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

private theorem condL_map (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt l) R) (h : D.condL R ρ) :
    D.condL R' (ρ.map f) := by
  unfold Raw.condL at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hr : ∀ g, (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    intro g
    ext a b
    rw [Lift.map_hom]
    rfl
  refine ⟨fun g => ?_, ord_map (f : R →+* R') hr (fun i g => (f.commutes _).symm) h2⟩
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h1 g)

private theorem condP_map (p : ℕ) (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt p) R) (h : D.condP p R ρ) :
    D.condP p R' (ρ.map f) := by
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · have := isGSp_map (f : R →+* R') (h.1 g)
    rw [RingHom.coe_coe, f.commutes] at this
    exact this
  · show (f : R →+* R').mapMatrix (ρ.hom g) = 1
    rw [h.2 g hg, map_one]

private theorem mult_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Mult ρ.hom) : D.Mult (ρ.map f).hom := by
  intro g
  have hr : (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    ext a b
    rw [Lift.map_hom]
    rfl
  rw [hr, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h g)

private theorem unr_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.UnrT ρ.hom 1) :
    D.UnrT (ρ.map f).hom 1 := by
  intro A hA g hg h1
  show (f : R →+* R').mapMatrix (ρ.hom g) = 1
  rw [h A hA g hg h1, map_one]

private theorem hEl_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp [Raw.hEl, Lift.map_hom, map_add (f := _), map_mul, f.commutes]

private theorem loc_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (v : ℕ) :
    D.loc (ρ.map f) v = (D.loc ρ v).map f := by
  apply Lift.ext
  rfl

private theorem nrm_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Nrm ρ.hom) : D.Nrm (ρ.map f).hom := by
  refine ⟨fun i j hij => ?_, ?_, ?_⟩
  · rw [Lift.map_hom, h.1 i j hij, map_zero]
  · rw [hEl_map, h.2.1, map_zero]
  · rw [hEl_map, h.2.2, map_zero]

end

private theorem onComp_map {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ]
    [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)} {P : Cond O rbar} {ρ₀ : Γ →* Matrix ι ι O}
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R']
    (f : R →ₐ[O] R') {r : Lift O rbar R} (h : OnComp P ρ₀ r) : OnComp P ρ₀ (r.map f) := by
  obtain ⟨B, i1, i2, i3, i4, ρ', hP, hρ, y, hy⟩ := h
  refine ⟨B, i1, i2, i3, i4, ρ', hP, hρ, f.comp y, ?_⟩
  subst hy
  apply Lift.ext
  ext g a b
  simp [Lift.map_hom]

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptMap :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), (D.IsPt ρ → D.IsEq ρ) ∧ ∀ (R' : Type) [CommRing R'] [Algebra c.O R'] [IsCO c.O R'] (f : R →ₐ[c.O] R'), (D.IsPt ρ → D.IsPt (ρ.map f)) ∧ (D.IsEq ρ → D.IsEq (ρ.map f)) := by
  intro Ω _ _ _ l _ c D _ R _ _ _ ρ
  have hL : ∀ {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt l) S),
      OnComp D.condL (D.r0At l) r → D.condL S r := by
    intro S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hP, _, y, rfl⟩ := hr
    exact condL_map D y ρ' hP
  have hP : ∀ (p : ℕ) {S : Type} [CommRing S] [Algebra c.O S] [IsCO c.O S] (r : Lift c.O (D.rbarAt p) S),
      OnComp (D.condP p) (D.r0At p) r → D.condP p S r := by
    intro p S _ _ _ r hr
    obtain ⟨B, i1, i2, i3, i4, ρ', hQ, _, y, rfl⟩ := hr
    exact condP_map D p y ρ' hQ
  refine ⟨fun h => ⟨h.mult, h.unr, h.nrm, hL _ h.atL, fun p hp => hP p _ (h.atP p hp)⟩, ?_⟩
  intro R' _ _ _ f
  refine ⟨fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩,
    fun h => ⟨mult_map D f ρ h.mult, unr_map D f ρ h.unr, nrm_map D f ρ h.nrm, ?_, fun p hp => ?_⟩⟩
  · rw [loc_map]
    exact onComp_map f h.atL
  · rw [loc_map]
    exact onComp_map f (h.atP p hp)
  · rw [loc_map]
    exact condL_map D f _ h.atL
  · rw [loc_map]
    exact condP_map D p f _ (h.atP p hp)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.XvanExt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cob_of_coord {H k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (a : H → k₀) (z : H → k)
    (h : ∀ φ : k →ₗ[k₀] k₀, ∃ m, ∀ g, φ (z g) = a g * m - m) :
    ∃ m, ∀ g, z g = algebraMap k₀ k (a g) * m - m := by
  by_cases ha : ∀ g, a g = 1
  · refine ⟨0, fun g => ?_⟩
    rw [mul_zero, sub_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ (z g)).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    rw [hm g, ha g, one_mul, sub_self]
  · push_neg at ha
    obtain ⟨g₀, hg₀⟩ := ha
    have hne : a g₀ - 1 ≠ 0 := sub_ne_zero.2 hg₀
    refine ⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩
    rw [← Algebra.smul_def, ← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ _).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    have key : φ ((a g₀ - 1)⁻¹ • z g₀) = m := by
      rw [map_smul, hm g₀, smul_eq_mul, ← sub_one_mul, inv_mul_cancel_left₀ hne]
    rw [map_sub, map_sub, map_smul, key, hm g, smul_eq_mul, sub_self]

theorem UpperTheory.V.GradeZeroInterpolatingElement.xvanExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (k : Type) [Field k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ z : G ℚ Ω → k, IsLocallyConstant z → (∀ g h, z (g * h) = z g + red (γ g : c.O) * z h) → D.UnrT z 0 → (∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, z g = red (γ g : c.O) * m - m) → ∃ m, ∀ g, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD k _ red hred γ hγ z hz hcoc hunr hloc
  have hlh : IsLocalHom red := ⟨fun a ha => by
    by_contra hn
    have h0 := hred a ((mem_maximalIdeal a).2 hn)
    rw [h0] at ha
    exact not_isUnit_zero ha⟩
  letI : Algebra (ResidueField c.O) k := (ResidueField.lift red).toAlgebra
  have hι : ∀ a : c.O, red a = algebraMap (ResidueField c.O) k (residue c.O a) := fun a =>
    (ResidueField.lift_residue_apply red a).symm
  have hX : D.XVan γ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hD.xvan D.al (by simp)).1
    · exact (hD.xvan D.be (by simp)).1
    · exact (hD.xvan D.th (by simp)).1
    · exact (hD.xvan D.al (by simp)).2
    · exact (hD.xvan D.be (by simp)).2
    · exact (hD.xvan D.th (by simp)).2
  simp only [hι]
  apply cob_of_coord (fun g => Raw.bar γ g) z
  intro φ
  have h1 : ∀ g h, φ (z (g * h)) = φ (z g) + Raw.bar γ g * φ (z h) := by
    intro g h
    rw [hcoc g h, map_add (f := _), hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have h2 : D.UnrT (fun g => φ (z g)) 0 := by
    intro A hA g hg hb
    simp only [hunr A hA g hg hb, map_zero]
  have h3 : ∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, φ (z g) = Raw.bar γ g * m - m := by
    intro v hv
    obtain ⟨m, hm⟩ := hloc v hv
    refine ⟨φ m, fun g hg => ?_⟩
    rw [hm g hg, hι, ← Algebra.smul_def, map_sub, map_smul, smul_eq_mul]
  exact hX (fun g => φ (z g)) (hz.comp fun x => φ x) h1 h2 h3
end
