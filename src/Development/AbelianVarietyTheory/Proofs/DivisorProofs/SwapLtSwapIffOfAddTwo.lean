module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapLtSwapIffOfAddTwo
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

theorem swap_lt_swap_iff_of_add_two {n : ℕ} (A A' a b : Fin n) (hA : A'.val = A.val + 2) (hab : a < b) :
    Equiv.swap A A' a < Equiv.swap A A' b ↔ (a < A ∨ A' < b) := by
  rw [Fin.lt_iff_val_lt_val] at hab
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h3 h4 <;>
    simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem val_rev_lo_of_last {n : ℕ} (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : ¬ Even n) :
    ((lo k).rev : Fin n).val = (lo k).val + 2 := by
  have h2 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hn)
  have := k.isLt
  simp only [Fin.val_rev, lo, Fin.coe_castLE]
  omega

theorem mem_cellU_last_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ u : GU σ n, u ∈ cellU y ↔ IsUnipU u ∧ ∀ i j : Fin n, i < j → (i < lo k ∨ (lo k).rev < j) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro L _ _ _ ϖ σ q _ n k hk hn y _ hy u
  have hw : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hA := val_rev_lo_of_last k hk hn
  rw [hw] at hy
  let M : GL (Fin n) L → Matrix (Fin n) (Fin n) L := fun x => x.val
  have weylRep_inv_mul_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (p : Fin n) :
      (M x⁻¹) p (w p) * (M x) (w p) p = 1 := by
    have h : (M (x⁻¹ * x)) p p = (M (1 : GL (Fin n) L)) p p := by rw [inv_mul_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

  have weylRep_mul_inv_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (p : Fin n) :
      (M x) (w p) p * (M x⁻¹) p (w p) = 1 := by
    have h : (M (x * x⁻¹)) (w p) (w p) = (M (1 : GL (Fin n) L)) (w p) (w p) := by rw [mul_inv_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
    rwa [Finset.sum_eq_single p (fun b _ hb => by
        rw [hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)] at h

  have weylRep_inv {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) : IsWeylRep w⁻¹ x⁻¹ := by
    intro p a hpa
    have hne : (M x) a (w⁻¹ a) ≠ 0 := by
      intro h0
      have := weylRep_mul_inv_diag hx (w⁻¹ a)
      rw [show w (w⁻¹ a) = a by simp] at this
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    have h : (M (x⁻¹ * x)) p (w⁻¹ a) = (M (1 : GL (Fin n) L)) p (w⁻¹ a) := by rw [inv_mul_cancel]
    dsimp only [M] at h
    rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
    rw [Finset.sum_eq_single a (fun b _ hb => by
        rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
    exact (mul_eq_zero.1 h).resolve_right hne

  have weylRep_conj_apply {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (u : GL (Fin n) L)
      (p q : Fin n) : (M (x⁻¹ * u * x)) p q = (M x⁻¹) p (w p) * (M u) (w p) (w q) * (M x) (w q) q := by
    have hi := weylRep_inv hx
    dsimp only [M]
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
      (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
      Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

  dsimp only [M] at weylRep_inv_mul_diag weylRep_mul_inv_diag weylRep_conj_apply
  have mem_cell_iff {w : Equiv.Perm (Fin n)} {x : GL (Fin n) L} (hx : IsWeylRep w x) (u : GL (Fin n) L) :
      u ∈ cell x ↔ u ∈ unipB L (Fin n) ∧ ∀ a b, a < b → w⁻¹ a < w⁻¹ b → (M u) a b = 0 := by
    dsimp only [M]
    rw [mem_cell, mem_unipBLower]
    refine and_congr_right fun hu => ?_
    rw [mem_unipB] at hu
    constructor
    · rintro ⟨hl, -⟩ a b hab hw
      have h := hl _ _ hw
      rw [weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp] at h
      have h1 := weylRep_inv_mul_diag hx (w⁻¹ a)
      have h2 := weylRep_mul_inv_diag hx (w⁻¹ b)
      rw [show w (w⁻¹ a) = a by simp] at h1
      rw [show w (w⁻¹ b) = b by simp] at h2
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
        · exact h
      · rw [h, zero_mul] at h2; exact absurd h2 zero_ne_one
    · intro h
      refine ⟨fun p q hpq => ?_, fun p => ?_⟩
      · rw [weylRep_conj_apply hx]
        rcases lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl
        · rw [h _ _ hl (by simpa using hpq), mul_zero, zero_mul]
        · rw [hu.1 _ _ hl, mul_zero, zero_mul]
      · rw [weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]

  rw [cellU, Subgroup.mem_subgroupOf, mem_cell_iff hy, mem_unipB, Equiv.swap_inv]
  unfold IsUnipU IsBorelU
  refine and_congr_right fun _ => forall₂_congr fun a b => ?_
  constructor
  · intro h hab hor
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).2 hor)
  · intro h hab hs
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).1 hs)

end WeylUnipotentShell

end WeylCell

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTDim

theorem card_torsion_of_ev {La Q : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] [Group Q]
    (ev : La → Q) (ℓ : ℕ) (hℓ : 0 < ℓ) (hadd : ∀ x y, ev (x + y) = ev x * ev y)
    (hker : ∀ x, ev x = 1 ↔ ∃ y, x = ℓ • y) (honto : ∀ q, q ^ ℓ = 1 ↔ ∃ x, ev x = q) :
    Nat.card {q : Q // q ^ ℓ = 1} = ℓ ^ Module.finrank ℤ La := by
  haveI : NeZero ℓ := ⟨by omega⟩
  let f : La →+ Additive Q := AddMonoidHom.mk' (fun x => Additive.ofMul (ev x)) fun x y => by
    rw [hadd]; rfl
  let r := Module.finrank ℤ La
  let b := Module.finBasis ℤ La
  let g : La →+ (Fin r → ZMod ℓ) := AddMonoidHom.mk' (fun x i => ((b.repr x i : ℤ) : ZMod ℓ)) fun x y => by
    ext i; simp
  have hg : Function.Surjective g := by
    intro v
    choose w hw using fun i => ZMod.intCast_surjective (v i)
    refine ⟨b.equivFun.symm w, funext fun i => ?_⟩
    show ((b.repr (b.equivFun.symm w) i : ℤ) : ZMod ℓ) = v i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hw]
  have hk : f.ker = g.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
    change Additive.ofMul (ev x) = 0 ↔ _
    rw [ofMul_eq_zero, hker]
    constructor
    · rintro ⟨y, rfl⟩
      ext i
      simp [g]
    · intro h
      have hd : ∀ i, (ℓ : ℤ) ∣ b.repr x i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact congrFun h i
      choose c hc using hd
      refine ⟨b.equivFun.symm c, b.ext_elem fun i => ?_⟩
      have hcy : b.repr (b.equivFun.symm c) i = c i := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [map_nsmul, Finsupp.smul_apply, hcy, hc i, nsmul_eq_mul]
  have e1 : Nat.card {q : Q // q ^ ℓ = 1} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun q => ?_)
    rw [honto, AddMonoidHom.mem_range]
    rfl
  rw [e1, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientAddEquivOfEq hk).toEquiv,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv]
  simp [Nat.card_eq_fintype_card, r]

variable {p : ℕ} [Fact p.Prime]

theorem relDim {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b N s) : SmoothOfRelativeDimension D.g o.A.hom := by
  have := o.ab.smooth
  choose n W hW hd using H1.exists_dim o.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension D.g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension D.g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := AlgebraicClosure (o.A.left.residueField y)
  let z : Sp k ⟶ o.A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (o.A.left.residueField y) k)) ≫ o.A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ o.A.hom
  let β : R →+* k := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  let B := (Over.pullback x).obj o.A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj x o.A o.ab
  obtain ⟨m, hm⟩ := GlobalTheory.AbVarRelDim.exists_relDim k B hB
  let z' : Sp k ⟶ pullback o.A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst o.A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ o.A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hℓp : (p + 1).Coprime p := Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)
  have hℓk : ((p + 1 : ℕ) : k) ≠ 0 := by
    intro h0
    have := (b.unit (p + 1) hℓp).map β
    rw [map_natCast, h0] at this
    exact not_isUnit_zero this
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨I, -⟩ := o.geom k x β hβ
  have c1 := card_torsion_of_ev (I.ev (p + 1)) (p + 1) (by omega) (I.add (p + 1)) (I.ker (p + 1) (by omega) hℓp)
    (I.onto (p + 1) (by omega) hℓp)
  have c2 := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B m (p + 1) hB hm hℓk
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback o.A x) (𝟙 (Sp k)) x
    (Category.id_comp x).symm
  have c3 : Nat.card {q : 𝟙_ (Over (Sp k)) ⟶ B // q ^ (p + 1) = 1} =
      Nat.card {q : Over.mk x ⟶ o.A // q ^ (p + 1) = 1} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun q => by
      change q ^ (p + 1) = 1 ↔ e q ^ (p + 1) = 1
      rw [← map_pow, map_eq_one_iff e e.injective])
  have hr := D.rankLa
  have h2 : 2 * m = Module.finrank ℤ D.La :=
    Nat.pow_right_injective (by have := (Fact.out : p.Prime).two_le; omega : 2 ≤ p + 1) (by
      show (p + 1) ^ (2 * m) = (p + 1) ^ Module.finrank ℤ D.La
      rw [← c2, c3, c1])
  have hg : D.g = m := by
    show D.m * D.n * Module.finrank ℚ D.F / 2 = m
    omega
  rw [hg, ← e₁]
  exact hd y

theorem relDim_and_isLB : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), SmoothOfRelativeDimension D.g o.A.hom ∧ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB :=
  fun _ _ _ _ _ _ _ _ _ o => ⟨relDim o, LB.isLB_pull o.isLB _⟩

end GlobalTheory.HTDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRelDimAndDiagonalIsLineBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_relDim_and_diagonal_isLineBundle : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s), SmoothOfRelativeDimension D.g o.A.hom ∧ (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := by
  first | exact @GlobalTheory.HTDim.relDim_and_isLB | exact GlobalTheory.HTDim.relDim_and_isLB | (intros; apply GlobalTheory.HTDim.relDim_and_isLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory

noncomputable section

namespace GlobalTheory.HCF.FormsSub

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isAutForm_zero : IsAutForm (0 : Sm E a) := by
  constructor
  · intro γ g
    rfl
  · have : {k | finRep E a k (0 : Sm E a) = 0} = Set.univ := Set.eq_univ_of_forall fun k => map_zero _
    rw [this]; exact isOpen_univ
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp
  · intro g
    exact ⟨0, 0, fun y => by simp⟩

theorem isAutForm_add {φ ψ : Sm E a} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) : IsAutForm (φ + ψ) := by
  constructor
  · intro γ g
    change φ.1 _ + ψ.1 _ = φ.1 _ + ψ.1 _
    rw [hφ.left, hψ.left]
  · exact isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
      ((hφ.level.inter hψ.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
        have h1 : finRep E a k φ = φ := hk.1
        have h2 : finRep E a k ψ = ψ := hk.2
        change finRep E a k (φ + ψ) = φ + ψ
        rw [map_add (f := _), h1, h2]
  · have := hφ.kfin
    have := hψ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) ⊔
      Submodule.span ℂ (Set.range fun k => cptRep E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  · have := hφ.zfin
    have := hψ.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) ⊔
      Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z ψ) '' Zalg E a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩) (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C1, N1, h1⟩ := hφ.growth g
    obtain ⟨C2, N2, h2⟩ := hψ.growth g
    refine ⟨|C1| + |C2|, N1 + N2, fun y => ?_⟩
    have hy := one_le_height y
    have e1 : height y ^ N1 ≤ height y ^ (N1 + N2) := pow_le_pow_right₀ hy (by omega)
    have e2 : height y ^ N2 ≤ height y ^ (N1 + N2) := pow_le_pow_right₀ hy (by omega)
    have p1 : 0 ≤ height y ^ N1 := by positivity
    have p2 : 0 ≤ height y ^ N2 := by positivity
    change ‖φ.1 _ + ψ.1 _‖ ≤ _
    calc ‖φ.1 (g * infGL E a y) + ψ.1 (g * infGL E a y)‖
        ≤ ‖φ.1 (g * infGL E a y)‖ + ‖ψ.1 (g * infGL E a y)‖ := norm_add_le _ _
      _ ≤ C1 * height y ^ N1 + C2 * height y ^ N2 := add_le_add (h1 y) (h2 y)
      _ ≤ |C1| * height y ^ (N1 + N2) + |C2| * height y ^ (N1 + N2) := by
          exact add_le_add ((mul_le_mul_of_nonneg_right (le_abs_self C1) p1).trans
              (mul_le_mul_of_nonneg_left e1 (abs_nonneg _)))
            ((mul_le_mul_of_nonneg_right (le_abs_self C2) p2).trans
              (mul_le_mul_of_nonneg_left e2 (abs_nonneg _)))
      _ = _ := by ring

theorem isAutForm_smul (c : ℂ) {φ : Sm E a} (hφ : IsAutForm φ) : IsAutForm (c • φ) := by
  constructor
  · intro γ g
    change c • φ.1 _ = c • φ.1 _
    rw [hφ.left]
  · exact isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
      (hφ.level.mem_nhds (by simp)) fun k hk => by
        have h1 : finRep E a k φ = φ := hk
        change finRep E a k (c • φ) = c • φ
        rw [map_smul, h1]
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [SetLike.mem_coe, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · have := hφ.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩)
  · intro g
    obtain ⟨C, N, h1⟩ := hφ.growth g
    refine ⟨‖c‖ * C, N, fun y => ?_⟩
    change ‖c • φ.1 _‖ ≤ _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 y) (norm_nonneg _)

theorem foldr_lin (χ : Module.End ℂ (Sm E a) → ℂ) (c : ℂ) (φ ψ : Sm E a) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (c • φ + ψ) =
      c • zs.foldr (fun z f => z f - χ z • f) φ + zs.foldr (fun z f => z f - χ z • f) ψ := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.foldr_cons]
    rw [ih, map_add (f := _), map_smul]
    module

theorem foldr_zero (χ : Module.End ℂ (Sm E a) → ℂ) (zs : List (Module.End ℂ (Sm E a))) :
    zs.foldr (fun z f => z f - χ z • f) (0 : Sm E a) = 0 := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp only [List.foldr_cons, ih, map_zero, smul_zero, sub_zero]

end GlobalTheory.HCF.FormsSub


open GlobalTheory.HCF.FormsSub in
theorem GlobalTheory.HCF.formsGL_single_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ),
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W {χ} N), φ ∈ formsGL E a L W {χ} N := by
  intro E _ _ _ a L W χ N
  let S : Submodule ℂ (Sm E a) :=
    { carrier := formsGL E a L W {χ} N
      zero_mem' := by
        refine ⟨isAutForm_zero, fun k _ => map_zero _, fun g => ?_, χ, rfl, fun zs _ _ => foldr_zero χ zs⟩
        have : (fun k : Kinf E a => (cptRep E a k (0 : Sm E a)).1 g) = 0 := by
          funext k; simp
        rw [this]; exact W.zero_mem
      add_mem' := by
        rintro φ ψ ⟨a1, b1, c1, χ1, e1, d1⟩ ⟨a2, b2, c2, χ2, e2, d2⟩
        rw [Set.mem_singleton_iff] at e1 e2
        rw [e1] at d1
        rw [e2] at d2
        refine ⟨isAutForm_add a1 a2, fun k hk => by rw [map_add (f := _), b1 k hk, b2 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (φ + ψ)).1 g) =
              (fun k : Kinf E a => (cptRep E a k φ).1 g) + (fun k : Kinf E a => (cptRep E a k ψ).1 g) := by
            funext k; simp
          rw [this]; exact W.add_mem (c1 g) (c2 g)
        · have := foldr_lin χ 1 φ ψ zs
          rw [one_smul, one_smul] at this
          rw [this, d1 zs hl hz, d2 zs hl hz, add_zero]
      smul_mem' := by
        rintro c φ ⟨a1, b1, c1, χ1, e1, d1⟩
        rw [Set.mem_singleton_iff] at e1
        rw [e1] at d1
        refine ⟨isAutForm_smul c a1, fun k hk => by rw [map_smul, b1 k hk], fun g => ?_, χ, rfl,
          fun zs hl hz => ?_⟩
        · have : (fun k : Kinf E a => (cptRep E a k (c • φ)).1 g) = c • (fun k : Kinf E a => (cptRep E a k φ).1 g) := by
            funext k; simp
          rw [this]; exact W.smul_mem c (c1 g)
        · have := foldr_lin χ c φ 0 zs
          rw [add_zero, foldr_zero, add_zero] at this
          rw [this, d1 zs hl hz, smul_zero] }
  intro φ hφ
  exact (Submodule.span_le (p := S)).2 le_rfl hφ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMemStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraFiniteFormsGL_single_char_span_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W {χ} N), φ ∈ formsGL E a L W {χ} N := by
  first | exact @GlobalTheory.HCF.formsGL_single_span | exact GlobalTheory.HCF.formsGL_single_span | (intros; apply GlobalTheory.HCF.formsGL_single_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeff
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ B : X → ℚ) (a b : ℚ) (x : X), IsQCart B → a ≤ b → (KltAt p n (Γ + b • B) x → KltAt p n (Γ + a • B) x) ∧ (LcAt p n (Γ + b • B) x → LcAt p n (Γ + a • B) x) := by
  intro X _ _ _ p n _ _ Γ B a b x hB hab
  obtain ⟨m', f, hm', hf, hBf⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p B hB x
  have key : ∀ (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ), 0 < m →
      IsLogEqn p (Γ + b • B) η x m g →
      ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + a • B) η x m'' g'' ∧
        ∀ E : DivOver p, E.Through x → discrep E η m g ≤ discrep E η m'' g'' := by
    intro η m g hm hlog
    obtain ⟨m'', g'', hm'', hlog'', hd⟩ :=
      GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n (Γ + b • B) B η x m m' g f (a - b) hm hm' hlog hBf
    have e : Γ + b • B + (a - b) • B = Γ + a • B := by
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e] at hlog''
    refine ⟨m'', g'', hm'', hlog'', fun E hE => ?_⟩
    have h0 : (0 : ℚ) ≤ E.ord f := by exact_mod_cast (E.ord_nonneg_iff f).2 (hE _ hf)
    have h1 : (0 : ℚ) ≤ (E.ord f : ℚ) / m' := div_nonneg h0 (Nat.cast_nonneg _)
    rw [hd E]
    nlinarith [mul_nonneg (sub_nonneg.2 hab) h1]
  refine ⟨fun ⟨η, m, g, hη, hm, hlog, hk⟩ => ?_, fun ⟨η, m, g, hη, hm, hlog, hk⟩ => ?_⟩
  · obtain ⟨m'', g'', hm'', hlog'', hle⟩ := key η m g hm hlog
    exact ⟨η, m'', g'', hη, hm'', hlog'', fun E hE => lt_of_lt_of_le (hk E hE) (hle E hE)⟩
  · obtain ⟨m'', g'', hm'', hlog'', hle⟩ := key η m g hm hlog
    exact ⟨η, m'', g'', hη, hm'', hlog'', fun E hE => le_trans (hk E hE) (hle E hE)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeffStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kltAt_and_lcAt_antitone_coeff : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ B : X → ℚ) (a b : ℚ) (x : X), IsQCart B → a ≤ b → (KltAt p n (Γ + b • B) x → KltAt p n (Γ + a • B) x) ∧ (LcAt p n (Γ + b • B) x → LcAt p n (Γ + a • B) x) := by
  first | exact @GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff | exact GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff | (intros; apply GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RatFinIso

variable {D : D7}

theorem symplOH_ratW_finRat_neg (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 := by
  set u : WO S T := ratW T S v - GlobalTheory.VacUnique.finRat S T v with hu
  have hfin : u.map (finPart D) = 0 := by
    funext i j
    have e1 := congrFun (congrFun (GlobalTheory.VacUnique.finRat_fin S T v) i) j
    show finPart D (ratW T S v i j - GlobalTheory.VacUnique.finRat S T v i j) = 0
    rw [RingHom.map_sub]
    simp only [Matrix.map_apply] at e1
    rw [e1, sub_self]
  have hr : ratW T S v = u + GlobalTheory.VacUnique.finRat S T v := by rw [hu, sub_add_cancel]
  rw [hr, GlobalTheory.FinTranslate.symplOH_add_left, map_neg, GlobalTheory.FinTranslate.symplOH_neg_right,
    GlobalTheory.FinTranslate.symplOH_neg_right, GlobalTheory.FinTranslate.symplOH_self,
    GlobalTheory.FinTranslate.symplOH_real_fin (GlobalTheory.VacUnique.finRat_inf S T v) hfin]
  simp

theorem isotropic : ∀ {D : D7} (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
    symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 :=
  fun S T v => symplOH_ratW_finRat_neg S T v

end GlobalTheory.RatFinIso

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPoint_finitePart_isotropic_pairing : ∀ {D : D7} (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E), symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 := by
  first | exact @GlobalTheory.RatFinIso.isotropic | exact GlobalTheory.RatFinIso.isotropic | (intros; apply GlobalTheory.RatFinIso.isotropic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementUnique
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IdTorus

theorem idelicFrameTorusElement_apply_column_decomposition {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y l a) (z : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J a).1 *ᵥ z =
      adMat F X *ᵥ (diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)) +
      adMat F Y *ᵥ (diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) *ᵥ
          (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) +
      (z - adMat F X *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z)
         - adMat F Y *ᵥ (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ z)) := by
  set P := adMat F (Formalism.UG.cT (σ : E →+* E) X * J)
  set Q := adMat F (Formalism.UG.cT (σ : E →+* E) Y * J)
  have mm : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E),
      adMat F A * adMat F B = adMat F (A * B) := fun A B => (Matrix.map_mul).symm
  have hPX : P * adMat F X = 0 := by rw [mm, hW.xx]; simp
  have hPY : P * adMat F Y = 1 := by rw [mm, hW.xy]; simp
  have hQX : Q * adMat F X = 1 := by rw [mm, yx h hJ hW]; simp
  have hQY : Q * adMat F Y = 0 := by rw [mm, hW.yy]; simp
  set w := z - adMat F X *ᵥ (Q *ᵥ z) - adMat F Y *ᵥ (P *ᵥ z) with hw
  have hPw : P *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := P) (N := adMat F X), mulVec_mulVec (M := P) (N := adMat F Y), hPX, hPY,
      zero_mulVec, one_mulVec]; simp
  have hQw : Q *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_sub, mulVec_mulVec (M := Q) (N := adMat F X), mulVec_mulVec (M := Q) (N := adMat F Y), hQX, hQY,
      zero_mulVec, one_mulVec]; simp
  have hmem : w ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
    refine ⟨(Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_,
      (Submodule.mem_iInf _).2 fun i => (Submodule.mem_iInf _).2 fun _ => LinearMap.mem_ker.2 ?_⟩
    · exact congrFun hPw i
    · exact congrFun hQw i
  have hz : z = adMat F X *ᵥ (Q *ᵥ z) + adMat F Y *ᵥ (P *ᵥ z) + w := by rw [hw]; abel
  conv_lhs => rw [hz]
  rw [mulVec_add, mulVec_add, mulVec_mulVec (N := adMat F X), mulVec_mulVec (N := adMat F Y), ha.1, ha.2.1,
    ha.2.2 w hmem, ← mulVec_mulVec, ← mulVec_mulVec]

theorem isIdTorusElt_uniq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}, IsIdTorusElt σ J X Y l a → IsIdTorusElt σ J X Y l b → a = b := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a b ha hb
  apply matHom_injective (AF F) σ J
  apply Units.ext
  have hv : ∀ z, (matHom _ σ J a).1 *ᵥ z = (matHom _ σ J b).1 *ᵥ z := fun z => by
    rw [idelicFrameTorusElement_apply_column_decomposition h hJ hW ha, idelicFrameTorusElement_apply_column_decomposition h hJ hW hb]
  ext i j
  simpa [mulVec_single_one] using congrFun (hv (Pi.single j 1)) i

end GlobalTheory.IdTorus

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhase
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolLowOnce

open GlobalTheory.HolDict.HolTo GlobalTheory.HolDict.CoefExt

theorem extLine_of_holShape : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S),
    GlobalTheory.HolDict.HolShape M → ExtLine M := by
  intro D V S M hM v v' hv hv' τ
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have h1 : ∀ ρ, M.σ ρ 1 = 1 := fun ρ => (M.ds ρ).2.2.1.1.1
  have hv0 : ∀ ρ, ((v ρ : M.sm ρ) : M.H ρ) ≠ 0 := by
    intro ρ h0
    have hn := (hv ρ).1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  choose w hw using fun ρ c => wt_int (h1 ρ) (hv0 ρ) (hv ρ).2.2 (arr (nNeg (M.ε ρ)) c)
  have hW : WtIs M w := fun ρ c => hw ρ c
  obtain ⟨hsm, hk⟩ := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hM hW hv τ
  obtain ⟨hC, hU, hI, hO⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
  haveI := hC
  have hOF := (hO hM).1

  have hdet : (x0Mat M τ).det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hOF.2
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at hd
    refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num

  set x : M.H τ := ((v τ : M.sm τ) : M.H τ) with hx
  set y : M.H τ := ((v' τ : M.sm τ) : M.H τ) with hy
  set c : ℂ := ⟪x, y⟫_ℂ with hc
  have hxx : ⟪x, x⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, (hv τ).1]
    norm_num
  have horth : ⟪y - c • x, x⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_smul_left, hxx, mul_one, hc, inner_conj_symm, sub_self]
  have htor : ∀ s, M.rep τ (torEl (fun _ : Unit => x0Mat M τ) s ()) (y - c • x) =
      torCh (fun _ : Unit => w τ) s • (y - c • x) := by
    intro s
    have ex := torus_wt M hW τ (hv τ).2.2 s hdet
    have ey := torus_wt M hW τ (hv' τ).2.2 s hdet
    rw [map_sub, map_smul, ex, ey, smul_sub, smul_comm c]
  have hz := eq_zero_of_orth hOF hU hI hsm (hv0 τ) hk (y - c • x) (fun s => torEl_mem hOF s) htor horth
  have hyx : y = c • x := sub_eq_zero.mp hz
  refine ⟨c, ?_, ?_⟩
  · have hn := congrArg norm hyx
    rw [norm_smul, hy, (hv' τ).1, hx, (hv τ).1, mul_one] at hn
    exact hn.symm
  · exact Subtype.ext hyx

end GlobalTheory.HolLowOnce
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhaseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremal_vectors_holomorphic_model_unique_up_to_phase : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), GlobalTheory.HolDict.HolShape M → ExtLine M := by
  first | exact @GlobalTheory.HolLowOnce.extLine_of_holShape | exact GlobalTheory.HolLowOnce.extLine_of_holShape | (intros; apply GlobalTheory.HolLowOnce.extLine_of_holShape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEq
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

theorem mat_eq_of_isIdTorusElt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, IsIdTorusElt σ J X Y l a →
    (matHom _ σ J a).1 = 1 + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J) := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW l a ha
  obtain ⟨h1, h2, h3⟩ := ha
  have hxx : adMat F (cT (σ : E →+* E) X * J) * adMat F X = 0 := by
    rw [← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  have hxy : adMat F (cT (σ : E →+* E) X * J) * adMat F Y = 1 := by
    rw [← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [← Matrix.map_mul, GlobalTheory.StdPar.yx h hJ hW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hyy : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  set A := (matHom _ σ J a).1 with hAdef
  set Xs := adMat F (cT (σ : E →+* E) X * J) with hXs
  set Ys := adMat F (cT (σ : E →+* E) Y * J) with hYs
  set P := 1 - adMat F X * Ys - adMat F Y * Xs with hP
  have hXP : Xs * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hxx, hxy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hYP : Ys * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hyx, hyy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hAP : A * P = P := by
    ext i j
    have hz : (fun k => P k j) ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ := by
      rw [Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Xs *ᵥ fun k => P k j) k = 0
        rw [show (Xs *ᵥ fun k => P k j) k = (Xs * P) k j from rfl, hXP]; rfl
      · simp only [colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
        intro k _
        change (Ys *ᵥ fun k => P k j) k = 0
        rw [show (Ys *ᵥ fun k => P k j) k = (Ys * P) k j from rfl, hYP]; rfl
    have := congrFun (h3 _ hz) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hsum : P + adMat F X * Ys + adMat F Y * Xs = 1 := by rw [hP]; abel
  have hA : A = P + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Ys
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) * Xs := by
    calc A = A * (P + adMat F X * Ys + adMat F Y * Xs) := by rw [hsum, Matrix.mul_one]
      _ = _ := by
        rw [Matrix.mul_add, Matrix.mul_add, hAP, ← Matrix.mul_assoc, h1, ← Matrix.mul_assoc A, h2]
  have hd : ∀ f : Fin r → AF F ⊗[F] E, diagonal (fun k => f k - 1) = diagonal f - 1 := fun f => by
    rw [← diagonal_one, diagonal_sub]
  rw [hA, hd, hd, Matrix.mul_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_one, hP]
  abel

end GlobalTheory.IdTorus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicFrameTorusElementMatrixEqStatement
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicFrameTorusElement_matrix_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {l : Fin r → (AF F ⊗[F] E)ˣ} {a : GAd σ J}, IsIdTorusElt σ J X Y l a →
    (matHom _ σ J a).1 = 1 + adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) Y * J)
      + adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) * adMat F (cT (σ : E →+* E) X * J) := by
  first | exact @GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt | exact GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt | (intros; apply GlobalTheory.IdTorus.mat_eq_of_isIdTorusElt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.SmallBall

theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

theorem mul_exp_le_one_iff (x c d : ℝ) (h : d = 2 * c) : x * Real.exp (-d) ≤ 1 ↔ x ≤ Real.exp c ^ 2 := by
  rw [sq, ← Real.exp_add, ← two_mul, ← h, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos d)]

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem encard_eq_Bl (P : Pair p) {a b : ℤ} {N : HermLB p} (h : P.Rep a b N) (S : Set N.B.Sec) (R : ℝ) (hR : 0 ≤ R)
    (hS : ∀ u, u ∈ S ↔ ∀ σ (y : CxPts p σ), (N.φ σ).nsq (secVal p σ u) y ≤ R ^ 2) :
    S.encard = (P.Bl a b R).encard := by
  obtain ⟨e, he, hr, hn, -⟩ := GlobalTheory.T.representedBundle_sections_rationalFunctions_dict k X p P a b N h
  have hi : e '' S = P.Bl a b R := by
    ext f
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, fun σ y => ?_⟩
      · have : e u ∈ Set.range e := ⟨u, rfl⟩
        rw [hr] at this
        exact this
      · have h1 := (hS u).1 hu σ y
        rw [← hn] at h1
        exact (pow_le_pow_iff_left₀ (nu_nonneg P a b σ y _) hR two_ne_zero).1 h1
    · rintro ⟨hf, hb⟩
      have : f ∈ Set.range e := by rw [hr]; exact hf
      obtain ⟨u, rfl⟩ := this
      refine ⟨u, (hS u).2 fun σ y => ?_, rfl⟩
      rw [← hn]
      exact pow_le_pow_left₀ (nu_nonneg P a b σ y _) (hb σ y) 2
  rw [← hi, he.encard_image]

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∀ (t : ℝ) (m : ℕ), ((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.encard = (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard ∧ (M.pow m).smallSec.encard = (P.Bl (m * a) (m * b) 1).encard ∧ (M.shift (fun _ => t) fun _ => rfl).smallSec.encard = (P.Bl a b (Real.exp t)).encard := by
  intro k _ X _ p P a b M hM t m
  have hm := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P a b M m hM
  refine ⟨?_, ?_, ?_⟩
  · refine encard_eq_Bl P hm _ _ (Real.exp_pos _).le fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq]
    refine forall_congr' fun σ => forall_congr' fun y => ?_
    have e := nsq_shift_pow M (fun _ => t) (fun _ => rfl) m σ (secVal p σ u) y
    exact (iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))
  · refine encard_eq_Bl P hm _ _ zero_le_one fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  · refine encard_eq_Bl P hM _ _ (Real.exp_pos _).le fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq]
    refine forall_congr' fun σ => forall_congr' fun y => ?_
    have e := HermLB.nsq_shift M (fun _ => t) (fun _ => rfl) (σ := σ) (secVal p σ u) y
    exact (iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))

end GlobalTheory.VolBr.SmallBall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBallStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallSections_twistedPower_encard_eq_ball : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∀ (t : ℝ) (m : ℕ), ((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.encard = (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard ∧ (M.pow m).smallSec.encard = (P.Bl (m * a) (m * b) 1).encard ∧ (M.shift (fun _ => t) fun _ => rfl).smallSec.encard = (P.Bl a b (Real.exp t)).encard := by
  first | exact @GlobalTheory.VolBr.SmallBall.main | exact GlobalTheory.VolBr.SmallBall.main | (intros; apply GlobalTheory.VolBr.SmallBall.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterPrescribedCentre
open NumberField

namespace GlobalTheory.SplitCentreChar

theorem exists_hChar_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ), 0 < d →
    ∀ s : ℂ, ∃ χ : Formalism.L2.Host.HChar E, ∀ t : ℝ,
      ((GlobalTheory.CuspRep.chiDet d χ (GlobalTheory.UnitaryBC.splitCentre E d t) : ℂˣ) : ℂ) = Complex.exp (-(t * s)) := by
  intro E _ _ _ d hd s
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) hd (-s)
  exact ⟨χ, fun t => by rw [hχ t]; congr 1; ring⟩

end GlobalTheory.SplitCentreChar
end
