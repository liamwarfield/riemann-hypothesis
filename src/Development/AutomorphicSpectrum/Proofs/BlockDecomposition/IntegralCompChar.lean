module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralSiegelRuleDoubledWeil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalAddOfKill
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureEulerProduct

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

theorem absA_pos (z : (AE D)ˣ) : 0 < absA D z := by
  have h : absA D z * absA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact pos_iff_ne_zero.2 fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h

theorem npow_neg_nat {r : ℝ≥0} (hr : 0 < r) (m : ℕ) : ((((r ^ m)⁻¹ : ℝ≥0) : ℝ) : ℂ) = npow r (-(m : ℂ)) := by
  have h0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem integral_comp_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (f : A → ℂ) :
    ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ := by
  have hmap : μ.map φ = (addEquivAddHaarChar φ)⁻¹ • μ := by
    have key := addEquivAddHaarChar_smul_map μ φ
    have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
    calc μ.map φ = ((addEquivAddHaarChar φ)⁻¹ * addEquivAddHaarChar φ) • μ.map φ := by
          rw [inv_mul_cancel₀ hne, one_smul]
      _ = (addEquivAddHaarChar φ)⁻¹ • μ := by rw [mul_smul, key]
  have hint : ∫ u, f u ∂(μ.map φ) = ∫ y, f (φ y) ∂μ :=
    integral_map_equiv (μ := μ) φ.toHomeomorph.toMeasurableEquiv f
  rw [← hint, hmap, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem nb_add {nb : hermA D n → G D n} (h : IsNMap nb) (x y : hermA D n) : nb (x + y) = nb x * nb y :=
  mat_inj (by
    rw [mat_mul, h, h, h, submatrix_fromBlocks_mul]
    simp [add_comm])

def cg (a : GL (Fin n) (AE D)) (c : hermA D n) : hermA D n :=
  ⟨a.1 * c.1 * adj a.1, by
    change adj (a.1 * c.1 * adj a.1) = a.1 * c.1 * adj a.1
    have hc : adj c.1 = c.1 := c.2
    rw [adj_mul, adj_mul, adj_adj, hc, Matrix.mul_assoc]⟩

theorem adj_mul_adj_inv (a : GL (Fin n) (AE D)) : (adj a.1 : Mx D n n) * adj (a⁻¹).1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

theorem adj_inv_mul_adj (a : GL (Fin n) (AE D)) : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by
  rw [← adj_mul]; simp [adj_one]

def ad (a : GL (Fin n) (AE D)) : GL (Fin n) (AE D) :=
  ⟨adj (a⁻¹).1, adj a.1, adj_inv_mul_adj a, adj_mul_adj_inv a⟩

theorem nb_cg_mul {nb : hermA D n → G D n} (h : IsNMap nb) (a : GL (Fin n) (AE D)) {m : G D n}
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (c : hermA D n) : nb (cg a c) * m = m * nb c :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, h, h, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    have e : a.1 * c.1 * adj a.1 * adj (a⁻¹).1 = a.1 * c.1 := by
      rw [Matrix.mul_assoc, adj_mul_adj_inv, Matrix.mul_one]
    simp [cg, e, -Matrix.coe_units_inv])

theorem weyl_mul {w m m' : G D n} (hw : mat w = blk4 0 1 (-1) 0) (a : GL (Fin n) (AE D))
    (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) (hm' : mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1) : w * m = m' * w :=
  mat_inj (by
    rw [mat_mul, mat_mul, hm, hw, hm', submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp)

theorem mulVec_mem_upper {g : G D n} {x y : Mx D n n} (hg : mat g = blk4 x 0 0 y) {v : Fin (n + n) → AE D}
    (hv : v ∈ upperHalf D n) : (mat g).mulVec v ∈ upperHalf D n := by
  have hv' : ∀ i : Fin n, v (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 := fun i => congrFun hv i
  refine LinearMap.mem_ker.2 (funext fun i => ?_)
  simp only [LinearMap.funLeft_apply, Pi.zero_apply, hg, Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    hv', mul_zero, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

theorem levi_mem_P {g g' : G D n} {x y x' y' : Mx D n n} (hg : mat g = blk4 x 0 0 y) (hg' : mat g' = blk4 x' 0 0 y')
    (h1 : g' * g = 1) : g ∈ P D n := by
  have hinv : g⁻¹ = g' := inv_eq_of_mul_eq_one_left h1
  intro v
  refine ⟨fun hv => mulVec_mem_upper hg hv, fun hv => ?_⟩
  have h2 := mulVec_mem_upper hg' (v := (mat g).mulVec v) hv
  rwa [Matrix.mulVec_mulVec, ← mat_mul, h1, mat_one, Matrix.one_mulVec] at h2

theorem height_mul {H : G D n → ℝ≥0} (hH : IsHeight H) {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D))
    (ha : blkA (mat p) = a.1) (x : G D n) :
    H (p * x) = absA D (Matrix.GeneralLinearGroup.det a) * H x := by
  obtain ⟨q, hq, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
  obtain ⟨c, hc⟩ := exists_blkA hq
  have e : blkA (mat (p * q)) = (a * c).1 := by rw [blkA_mul hq, ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hq) (a * c) e k hk, hH q hq c hc k hk, map_mul, map_mul]

end GlobalTheory.CompanionTheory.IwaAd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProduct
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.Parabolic (Embeds)

namespace GlobalTheory.CompanionTheory.SegUniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_ne_zero_of_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible)
    (φ : ρ.IntertwiningMap σ) (hφ : Function.Injective φ) : ∃ v, φ v ≠ 0 := by
  haveI := Model.nontrivial_of_isIrreducible hρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩

theorem exists_ne_zero_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (φ : ρ.IntertwiningMap σ) (hφ : Function.Surjective φ) : ∃ v, φ v ≠ 0 := by
  haveI := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hφ u
  exact ⟨v, hu⟩

theorem bot_ne_top_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (h : IsSubquotient σ ρ) : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
  obtain ⟨S, f, hf⟩ := h
  intro hb
  haveI := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf u
  have hv : (v : V) ∈ (⊥ : Subrepresentation ρ) := hb ▸ trivial
  have hv0 : v = 0 := Subtype.ext hv
  exact hu (by rw [hv0, map_zero])

theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) : FineJac Δ := by
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have h0 := Δ.len_pos
    obtain h1 | h2 | h3 : n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
    · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ (h.trans h1)
    · exact @GlobalTheory.T.fine_jacquet_segment_length_two k _ _ _ _ hA hZ Δ (h.trans h2)
    · exact @GlobalTheory.T.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem exists_eq_of_embeds_one {c : ℕ} (hc : c = 1) (x : Fin c → IrrGL (k := k)) (y : IrrGL (k := k))
    (hd : ∑ a, (x a).1 = y.1) (φ : y.rep.IntertwiningMap (prodIrr x hd)) (hφ : Function.Injective φ) :
    ∃ a, y = x a := by
  subst hc
  obtain ⟨z, rfl⟩ : ∃ z, x = fun _ => z := ⟨x 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  refine ⟨0, ?_⟩
  obtain ⟨n, c⟩ := y
  obtain ⟨m, c'⟩ := z
  have hnm : m = n := by simpa using hd
  subst hnm
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨m, c'⟩ : IrrGL (k := k)) hd
  have hS := (isSocle_self (⟨m, c'⟩ : IrrGL (k := k)).2.rep.irr).of_equiv (.refl _) ψ
  obtain ⟨a⟩ := hS.equiv_of_embeds (⟨m, c⟩ : IrrGL (k := k)).2.rep.irr ⟨φ, hφ⟩
  exact congrArg (Sigma.mk m) (irrCl_eq_iff.2 ⟨a⟩)

theorem sum_concat_fst {s N : ℕ} (y : Fin s → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) (c : Fin s → ℕ)
    (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hx : ∀ a, ∑ i, (x a i).1 = (y a).1) :
    ∑ i, (concat c x i).1 = N := by
  have h1 : ∑ i, (concat c x i).1 = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 :=
    Equiv.sum_comp finSigmaFinEquiv.symm (fun p : Σ a, Fin (c a) => (x p.1 p.2).1)
  rw [h1, Fintype.sum_sigma, ← hy]
  exact Finset.sum_congr rfl fun a _ => hx a

theorem eq_dec_of_one_le_jm (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} (fine : FineJac Δ) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hL : IsLSeg Δ π)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (y : Fin Δ.len → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N)
    (hpos : ∀ a, 0 < (y a).1) (h1 : 1 ≤ jm y hy π) : y = dec Δ := by
  have hemb := fun a => GlobalTheory.T.support_subscheme_embedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  choose c x hx hcusp φ hφ using hemb
  have hne : ∀ a, ∃ v, φ a v ≠ 0 := fun a =>
    exists_ne_zero_of_injective (y a).2.rep.irr (φ a) (hφ a)
  have hjm : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a =>
    GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth (φ a) (hne a)
  have hcat := sum_concat_fst y hy c x hx
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hy c x hx hcat hjm π hs (hasFiniteLength_of_isIrreducible hi)
  have hcc : ∀ i, (concat c x i).IsCusp := fun i => hcusp _ _
  obtain ⟨hlen, -⟩ := (fine π hL).2 _ (concat c x) hcat hcc (h1.trans hle)
  have hc1 : ∀ a, 1 ≤ c a := fun a => by
    by_contra hc
    have hc0 : c a = 0 := by omega
    have h2 := hx a
    have h3 := hpos a
    have : IsEmpty (Fin (c a)) := by rw [hc0]; infer_instance
    rw [Fintype.sum_empty] at h2
    omega
  have hsum : ∑ a : Fin Δ.len, 1 = ∑ a, c a := by simpa using hlen.symm
  have hc : ∀ a, c a = 1 := fun a =>
    ((Finset.sum_eq_sum_iff_of_le fun a _ => hc1 a).1 hsum a (Finset.mem_univ a)).symm
  have hyc : ∀ a, (y a).IsCusp := fun a => by
    obtain ⟨b, hb⟩ := exists_eq_of_embeds_one (hc a) (x a) (y a) (hx a) (φ a) (hφ a)
    exact hb ▸ hcusp a b
  obtain ⟨h, hdec⟩ := (fine π hL).2 _ y hy hyc h1
  exact funext fun a => by simpa using hdec a

theorem isLSeg_of_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth τ) (hi : τ.IsIrreducible)
    (f : τ.IntertwiningMap (prodIrr (dec Δ) hd)) (hf : Function.Injective f), IsLSeg Δ τ := by
  intro k _ _ _ _ hA hZ Δ N hd V _ _ τ hs hi f hf
  have fine : FineJac Δ := @fineJac_all k _ _ _ _ hA hZ Δ
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_segment_representation hA Δ
  have hN : Δ.deg = N := by
    rw [← hd]
    show Δ.deg = ∑ _ : Fin Δ.len, Δ.d
    simp [Segment.deg]
  subst hN
  have hone := (fine L.ρ hL).1 hd
  let e := stdBlocks (fun a => (dec Δ a).1) hd
  have hfl : HasFiniteLength (GlobalTheory.SmGL.jac e L.ρ) :=
    GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ e _ L.ρ L.smooth (hasFiniteLength_of_isIrreducible L.irr)
  haveI : WellFoundedGT (Subrepresentation (GlobalTheory.SmGL.jac e L.ρ)) := ((hasFiniteLength_iff_wellFounded _).1 hfl).1
  have h0 : jm (dec Δ) hd L.ρ ≠ 0 := by rw [hone]; exact one_ne_zero
  have hne : (⊥ : Subrepresentation (GlobalTheory.SmGL.jac e L.ρ)) ≠ ⊤ :=
    bot_ne_top_of_isSubquotient (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec Δ)) (jhMult_ne_zero_iff.1 h0)
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation (GlobalTheory.SmGL.jac e L.ρ))).resolve_left hne
  let q : (GlobalTheory.SmGL.jac e L.ρ).IntertwiningMap (subQuot ⊤ M) :=
    ⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation (GlobalTheory.SmGL.jac e L.ρ)).toSubmodule
      LinearMap.id (fun v => trivial), fun g => rfl⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨v, rfl⟩
  have hirr : (subQuot ⊤ M).IsIrreducible := isIrreducible_subQuot hM.covBy_top
  have hsq : IsSubquotient (subQuot ⊤ M) (GlobalTheory.SmGL.jac e L.ρ) := .of_surjective q hq
  obtain ⟨σ, ⟨ψ⟩⟩ := GlobalTheory.T.levi_irreducible_tensor_decomposition hA (fun a => (dec Δ a).1)
    ⟨_, subQuot ⊤ M, hsq.isSmooth (isSmooth_jac e L.smooth), hirr⟩
  let y : Fin Δ.len → IrrGL (k := k) := fun a => ⟨(dec Δ a).1, σ a⟩
  have hy : ∑ a, (y a).1 = Δ.deg := hd
  let g : (GlobalTheory.SmGL.jac (stdBlocks (fun a => (y a).1) hy) L.ρ).IntertwiningMap (piTensor fun a => (y a).rep) :=
    ψ.toIntertwiningMap.comp q
  have hg : Function.Surjective g := ψ.toLinearEquiv.surjective.comp hq
  have h1 : 1 ≤ jm y hy L.ρ :=
    ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective g hg))
  have hyeq : y = dec Δ := eq_dec_of_one_le_jm hA fine L.ρ hL L.smooth L.irr y hy
    (fun a => Δ.d_pos) h1
  obtain ⟨w, hw⟩ := exists_ne_zero_of_surjective (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA y) g hg
  have hfrob := GlobalTheory.T.frobenius_reciprocity_nonzero y hy L.ρ L.smooth g ⟨w, hw⟩
  have htr : ∀ (y' : Fin Δ.len → IrrGL (k := k)) (_ : y = y') (hy' : ∑ a, (y' a).1 = Δ.deg),
      (∃ g : L.ρ.IntertwiningMap (prodIrr y hy), ∃ v, g v ≠ 0) →
        ∃ g : L.ρ.IntertwiningMap (prodIrr y' hy'), ∃ v, g v ≠ 0 := by
    rintro _ rfl _ h
    exact h
  obtain ⟨g', v, hv⟩ := htr _ hyeq hd hfrob
  have hemb : Embeds L.ρ (prodIrr (dec Δ) hd) :=
    (isotypic_ne_bot_iff_embeds L.irr).1 (isotypic_ne_bot_iff.2 ⟨g', fun e' => hv (by rw [e']; rfl)⟩)
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_socle_segment_product hA Δ hd
  obtain ⟨a⟩ := hS.equiv_of_embeds hi ⟨f, hf⟩
  obtain ⟨b⟩ := hS.equiv_of_embeds L.irr hemb
  exact hL.of_equiv (b.trans a.symm)

end GlobalTheory.CompanionTheory.SegUniq

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProductStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_sub_segment_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) {N : ℕ} (hd : ∑ a, (dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth τ) (hi : τ.IsIrreducible) (f : τ.IntertwiningMap (prodIrr (dec Δ) hd)) (hf : Function.Injective f), IsLSeg Δ τ := by
  first | exact @GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec | exact GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec | (intros; apply GlobalTheory.CompanionTheory.SegUniq.isLSeg_of_dec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantOfLieOneLEqZero
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.CuspFinGL.Split

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hφ.1.level
  exact GlobalTheory.CompanionTheory.SiegelDecay.rapid_decay_of_one_parabolic_bounds E a φ.1 hc
    (GlobalTheory.CompanionTheory.GGPS.ggps_bound E a φ.1 hs (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E a φ hφ.1)
      (GlobalTheory.CompanionTheory.AutLevel.exists_open_level E a φ hφ.1) (GlobalTheory.CompanionTheory.CuspBridge.isCuspidal_of_isCuspForm E a φ hφ)
      (GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ hs hφ.1) (GlobalTheory.CompanionTheory.BoxBound.box_bound E a φ hφ.1))

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem cuspFin_zero : CuspFin E 0 := by
  intro L hL W _ _ _ ρ hρ J hJ
  haveI : Finite (GA E 0) := Finite.of_subsingleton
  haveI : FiniteDimensional ℂ (GA E 0 → ℂ) := inferInstance
  infer_instance

theorem invariant_of_lie_oneL_eq_zero {a : ℕ} (ψ : Sm E a) (h : lie E a (oneL E a) ψ = 0) (t : ℝ) (g : GA E a) :
    ψ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = ψ.1 g := by
  rw [CuspidalL2GL.splitCentre_comm]
  have hd : ∀ s, HasDerivAt (fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) 0 s := by
    intro s
    have := (GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre) E a ψ g s
    rwa [h] at this
  have := is_const_of_deriv_eq_zero (f := fun s : ℝ => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [CuspidalL2GL.splitCentre_zero] using this

theorem cuspFin_pos {a : ℕ} (ha : 0 < a) : CuspFin E a := by
  intro L hL W _ _ _ ρ hρ J hJ
  set V := Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1} with hV
  have hVC : ∀ φ ∈ V, φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := (GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms) E a L W ρ J
  set z := lie E a (oneL E a) with hz
  obtain ⟨p, hpm, hp⟩ := GlobalTheory.CompanionTheory.Affgl.minpoly_on_killed E a J hJ z (GlobalTheory.CompanionTheory.CapelliTrace.lie_oneL_mem_Zalg E a)
  obtain ⟨T, w, hTw⟩ := (GlobalTheory.CompanionTheory.LinearODE.deriv_zero_eq_sum) p hpm
  have hstab : ∀ φ ∈ V, z φ ∈ V := by
    intro φ hφ
    obtain ⟨hg, hc⟩ := hVC φ hφ
    have key : z φ = ∑ t ∈ T, w t • rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ := by
      apply Subtype.ext
      funext g
      have h := hTw (fun k s => ((z ^ k) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
        (fun k s => by
          have h := (GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre) E a ((z ^ k) φ) g s
          rwa [← Module.End.mul_apply, ← pow_succ'] at h)
        (fun s => by
          have h0 := congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (hp φ hg.2.2.2)
          simpa [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply] using h0)
      simp only [pow_one, pow_zero, Module.End.one_apply, CuspidalL2GL.splitCentre_zero, mul_one] at h
      rw [h, Submodule.coe_sum, Finset.sum_apply]
      rfl
    rw [key]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
      (Submodule.subset_span ((GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem) E a L W ρ J hJ.1 φ hg hc t))
  refine (GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces) (Sm E a) z V hstab p hpm.ne_zero (fun v hv => hp v (hVC v hv).1.2.2.2) fun c => ?_
  obtain ⟨χ, L', J', hL', hJ', hχ⟩ := (GlobalTheory.CompanionTheory.CuspTwist.twist_central) E a ha L hL W ρ hρ J hJ c
  have hfin := (GlobalTheory.CompanionTheory.CuspInvariant.cuspInvFin) cuspFormsBoundedGL (GlobalTheory.CompanionTheory.UnifAlpha.unifAlpha) E a L' hL' W ρ hρ J' hJ'
  have hle : (Submodule.span ℂ {v | v ∈ V ∧ z v = c • v}).map (mulChi a χ).toLinearMap ≤
      Submodule.span ℂ {φ | φ ∈ genSpace L' ρ J' ∧ IsCuspidal φ.1 ∧
        ∀ t g, φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = φ.1 g} := by
    rw [Submodule.map_span_le]
    rintro v ⟨hv, hzv⟩
    obtain ⟨hg, hc⟩ := hVC v hv
    obtain ⟨h1, h2, h3⟩ := hχ v hg hc hzv
    exact Submodule.subset_span ⟨h1, h2, invariant_of_lie_oneL_eq_zero _ h3⟩
  haveI := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ (mulChi a χ).injective _).symm

theorem cuspFin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspFin E a := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact cuspFin_zero
  · exact cuspFin_pos ha

end GlobalTheory.CompanionTheory.CuspFinGL.Split
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSum
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem dsum_stronglyMeasurable : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ), StronglyMeasurable Φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖)) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.dsum ψ b₀ Φ v.2 v.1) := by
  intro D ρ p ψ hψ b₀ Φ hΦ hs
  haveI := (GlobalTheory.T.countable_matrices_and_cosets D ρ p).1
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, hc⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀
  have hterm : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, Measurable fun v : Mx D ρ p × Mx D ρ p =>
      GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.2 (GlobalTheory.CompanionTheory.FJE.rt ξ) * Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + v.1) := by
    intro ξ
    have h1 : Measurable fun y : Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ y (GlobalTheory.CompanionTheory.FJE.rt ξ) :=
      (hc.comp (continuous_id.prodMk continuous_const)).measurable
    have h2 : Measurable fun y : Mx D ρ p => Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y) :=
      hΦ.measurable.comp (continuous_const_add (GlobalTheory.CompanionTheory.FJE.rt ξ)).measurable
    exact (h1.comp measurable_snd).mul (h2.comp measurable_fst)
  exact (Measurable.tsum hterm).stronglyMeasurable

end GlobalTheory.CompanionTheory.FJE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StronglyMeasurableTwistedLatticeSumStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stronglyMeasurable_twisted_lattice_sum : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ), StronglyMeasurable Φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖)) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.dsum ψ b₀ Φ v.2 v.1) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.dsum_stronglyMeasurable | exact GlobalTheory.CompanionTheory.FJE.dsum_stronglyMeasurable | (intros; apply GlobalTheory.CompanionTheory.FJE.dsum_stronglyMeasurable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormula
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

theorem rv_zero_apply (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    rv v 0 s = if s ≠ 0 ∧ s ∈ v.adicCompletionIntegers F then 1 else 0 := by
  unfold rv
  rw [tsum_eq_single 0]
  · have h : (s ∈ v.adicCompletionIntegers F) ↔ Valued.v s ≤ 1 :=
      HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v
    simp [h]
  · intro i hi
    simp [hi]

theorem rv_zero_of_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v} (h0 : s ≠ 0)
    (hs : s ∈ v.adicCompletionIntegers F) : rv v 0 s = 1 := by
  rw [rv_zero_apply, if_pos ⟨h0, hs⟩]

theorem rv_zero_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v}
    (hs : s ∉ v.adicCompletionIntegers F) : rv v 0 s = 0 := by
  rw [rv_zero_apply, if_neg fun h => hs h.2]

theorem pure_rv_zero_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ) :
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a =
      if ∀ v, v ∉ S → (a : AF F).2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G (a : AF F).1 * ∏ v ∈ S, g v ((a : AF F).2 v)) else 0 := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), (a : AF F).2 v ≠ 0 := fun v =>
    IdeleGroup.finite_ne_zero a v
  unfold PositivityTheory.Rg.Base1.pure
  split_ifs with h
  · rw [finprod_eq_one_of_forall_eq_one (fun v : {v // v ∉ S} => rv_zero_of_mem v.1 (hne v.1) (h v.1 v.2)),
      mul_one]
  · push_neg at h
    obtain ⟨v, hvS, hv⟩ := h
    have hfin : (Function.mulSupport fun v : {v // v ∉ S} => rv v.1 0 ((a : AF F).2 v.1)).Finite := by
      have hco : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
          (a : AF F).2 v ∈ v.adicCompletionIntegers F := (a : AF F).2.2
      refine Set.Finite.subset (Set.Finite.preimage Subtype.val_injective.injOn hco) ?_
      intro w hw
      by_contra hmem
      exact hw (rv_zero_of_mem w.1 (hne w.1) (not_not.1 hmem))
    rw [finprod_eq_zero _ (⟨v, hvS⟩ : {v // v ∉ S}) (rv_zero_of_not_mem v hv) hfin, mul_zero,
      ENNReal.ofReal_zero]

end GlobalTheory.CompanionTheory.BasePsi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_adelic_function_formula : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a =
      if ∀ v, v ∉ S → (a : AF F).2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G (a : AF F).1 * ∏ v ∈ S, g v ((a : AF F).2 v)) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply | exact GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply | (intros; apply GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSet
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSet
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi.Den

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (Fv F v) t) = v.valuation F t :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t

theorem exists_valued_bound (v : HeightOneSpectrum (𝓞 F)) {C : Set (Fv F v)} (hC : IsCompact C) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ x ∈ C, Valued.v x ≤ γ := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  obtain ⟨s, -, hs⟩ := hC.elim_nhds_subcover
    (fun x => {y : Fv F v | y - x ∈ v.adicCompletionIntegers F}) (fun x _ => by
      have hopen : IsOpen {y : Fv F v | y - x ∈ v.adicCompletionIntegers F} :=
        hO.preimage (continuous_id.sub continuous_const)
      exact hopen.mem_nhds (by simp))
  obtain ⟨M, hM⟩ := (s.image fun x => Valued.v x).exists_le
  refine ⟨max M 1, (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).ne', fun y hy => ?_⟩
  obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp (hs hy)
  have h1 : Valued.v (y - x) ≤ 1 := hxy
  have h2 : Valued.v x ≤ M := hM _ (Finset.mem_image_of_mem _ hx)
  have h3 : y = (y - x) + x := by ring
  rw [h3]
  exact (Valuation.map_add _ _ _).trans
    (max_le (h1.trans (le_max_right _ _)) (h2.trans (le_max_left _ _)))

theorem exists_finset_inv_integral {D : Set (AF F)ˣ} (hD : IsCompact D) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ u ∈ D, ∀ v, v ∉ T →
      ((u⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
  obtain ⟨s, -, hs⟩ := hD.elim_nhds_subcover
    (fun a : (AF F)ˣ => {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F}) (fun a _ => by
      have hopen : IsOpen {u : (AF F)ˣ | a⁻¹ * u ∈ IdeleGroup.standardOpenSubgroup F} :=
        (IdeleGroup.isOpen_standardOpenSubgroup F).preimage (continuous_const.mul continuous_id)
      exact hopen.mem_nhds (by simp [one_mem]))
  have hfin : ∀ a : (AF F)ˣ, {v : HeightOneSpectrum (𝓞 F) |
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∉ v.adicCompletionIntegers F}.Finite := fun a =>
    Filter.eventually_cofinite.mp ((a⁻¹ : (AF F)ˣ) : AF F).2.2
  refine ⟨s.biUnion fun a => (hfin a).toFinset, fun u hu v hv => ?_⟩
  obtain ⟨a, ha, hau⟩ := Set.mem_iUnion₂.mp (hs hu)
  have hav : ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F := by
    by_contra hcon
    exact hv (Finset.mem_biUnion.mpr ⟨a, ha, (hfin a).mem_toFinset.mpr hcon⟩)
  have hh := ((IdeleGroup.mem_standardOpenSubgroup F).mp hau v).2
  have hu' : u⁻¹ = (a⁻¹ * u)⁻¹ * a⁻¹ := by group
  have hmul : ((u⁻¹ : (AF F)ˣ) : AF F).2 v =
      (((a⁻¹ * u)⁻¹ : (AF F)ˣ) : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v := by
    conv_lhs => rw [hu']
    rfl
  rw [hmul]
  exact mul_mem hh hav

theorem exists_inv_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧ ∀ u ∈ D, Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ γ := by
  have hc : Continuous fun u : (AF F)ˣ => ((u⁻¹ : (AF F)ˣ) : AF F).2 v :=
    Units.continuous_val.comp ((IdeleGroup.continuous_finiteProj (K := F) v).comp continuous_inv)
  obtain ⟨γ, h0, hγ⟩ := exists_valued_bound v (hD.image hc)
  exact ⟨γ, h0, fun u hu => hγ _ (Set.mem_image_of_mem _ hu)⟩

theorem exists_bound {D : Set (AF F)ˣ} (hD : IsCompact D) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (A : HeightOneSpectrum (𝓞 F) → WithZero (Multiplicative ℤ)),
      ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
        (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
        ∀ v, v.valuation F t ≤ if v ∈ T then A v else 1 := by
  obtain ⟨T₀, hT₀⟩ := exists_finset_inv_integral hD
  choose B _ hB using fun v => exists_inv_bound hD v
  have hG : ∀ v : HeightOneSpectrum (𝓞 F), ∃ γ : WithZero (Multiplicative ℤ), v ∈ S →
      ∀ x ∈ C v, Valued.v x ≤ γ := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨γ, -, h⟩ := exists_valued_bound v (hC v hv)
      exact ⟨γ, fun _ => h⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose G hG using hG
  refine ⟨T₀ ∪ S, fun v => max (G v) 1 * B v, fun u hu t h1 h2 v => ?_⟩
  have hinv : (u : AF F).2 v * ((u⁻¹ : (AF F)ˣ) : AF F).2 v = 1 :=
    congrArg (fun a : AF F => a.2 v) (Units.mul_inv u)
  have hx : algebraMap F (Fv F v) t =
      (algebraMap F (Fv F v) t * (u : AF F).2 v) * ((u⁻¹ : (AF F)ˣ) : AF F).2 v := by
    rw [mul_assoc, hinv, mul_one]
  have hval : v.valuation F t = Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) *
      Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) := by
    rw [← valued_algebraMap, ← map_mul, ← hx]
  have hfirst : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ max (G v) 1 := by
    by_cases hv : v ∈ S
    · exact (hG v hv _ (h1 v hv)).trans (le_max_left _ _)
    · have a : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hv
      exact a.trans (le_max_right _ _)
  by_cases hvT : v ∈ T₀ ∪ S
  · rw [if_pos hvT, hval]
    exact mul_le_mul' hfirst (hB v u hu)
  · rw [if_neg hvT, hval]
    have hvS : v ∉ S := fun h => hvT (Finset.mem_union_right _ h)
    have hvT₀ : v ∉ T₀ := fun h => hvT (Finset.mem_union_left _ h)
    have a1 : Valued.v (algebraMap F (Fv F v) t * (u : AF F).2 v) ≤ 1 := h2 v hvS
    have a2 : Valued.v (((u⁻¹ : (AF F)ˣ) : AF F).2 v) ≤ 1 := hT₀ u hu v hvT₀
    simpa using mul_le_mul' a1 a2

theorem valuation_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    v.valuation F (n : F) ≤ 1 := by
  have := HeightOneSpectrum.valuation_le_one (K := F) v (n : 𝓞 F)
  simpa using this

theorem exists_nat_mul_le_one (v : HeightOneSpectrum (𝓞 F)) (A : WithZero (Multiplicative ℤ)) :
    ∃ n : ℕ, 0 < n ∧ v.valuation F (n : F) * A ≤ 1 := by
  by_cases hA : A = 0
  · exact ⟨1, one_pos, by simp [hA]⟩
  have hlt : v.valuation F ((Ideal.absNorm v.asIdeal : ℕ) : F) < 1 := by
    have h := (v.valuation_lt_one_iff_mem (K := F) ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)).2
      (Ideal.absNorm_mem _)
    simpa using h
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hlt (Units.mk0 _ (inv_ne_zero hA))
  have hpos : 0 < Ideal.absNorm v.asIdeal := by
    refine Nat.pos_of_ne_zero fun h => v.ne_bot ?_
    exact Ideal.absNorm_eq_zero_iff.mp h
  refine ⟨Ideal.absNorm v.asIdeal ^ k, pow_pos hpos k, ?_⟩
  have h3 : v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) < A⁻¹ := by
    push_cast
    rw [map_pow]
    exact hk
  calc v.valuation F (((Ideal.absNorm v.asIdeal ^ k : ℕ)) : F) * A ≤ A⁻¹ * A :=
        mul_le_mul' h3.le le_rfl
    _ = 1 := inv_mul_cancel₀ hA

theorem common_denominator (F : Type) [Field F] [NumberField F] (D : Set (AF F)ˣ) (hD : IsCompact D)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hC : ∀ v ∈ S, IsCompact (C v)) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
      (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
      ∃ y : 𝓞 F, (y : F) = N * t := by
  obtain ⟨T, A, hA⟩ := exists_bound hD S C hC
  choose n hn0 hn using fun v => exists_nat_mul_le_one (F := F) v (A v)
  refine ⟨∏ v ∈ T, n v, Finset.prod_pos fun v _ => hn0 v, fun u hu t h1 h2 => ?_⟩
  refine exists_eq_of_forall_mem_adicCompletionIntegers F _ fun v => ?_
  rw [coe_mem_adicCompletionIntegers_iff, map_mul]
  have ht := hA u hu t h1 h2 v
  by_cases hv : v ∈ T
  · rw [if_pos hv] at ht
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hv
    have hN : v.valuation F (((∏ v ∈ T, n v : ℕ)) : F) ≤ v.valuation F (n v : F) := by
      rw [hm]
      push_cast
      rw [map_mul]
      simpa using mul_le_mul' (le_refl (v.valuation F (n v : F))) (valuation_natCast_le_one v m)
    exact (mul_le_mul' hN ht).trans (hn v)
  · rw [if_neg hv] at ht
    simpa using mul_le_mul' (valuation_natCast_le_one v (∏ v ∈ T, n v)) ht

end GlobalTheory.CompanionTheory.BasePsi.Den

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_denominators_compact_idele_set : ∀ (F : Type) [Field F] [NumberField F] (D : Set (AF F)ˣ), IsCompact D → ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ S, IsCompact (C v)) →
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ D, ∀ t : F, (∀ v ∈ S, algebraMap F (Fv F v) t * (u : AF F).2 v ∈ C v) →
      (∀ v, v ∉ S → algebraMap F (Fv F v) t * (u : AF F).2 v ∈ v.adicCompletionIntegers F) →
      ∃ y : 𝓞 F, (y : F) = N * t := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.Den.common_denominator | exact GlobalTheory.CompanionTheory.BasePsi.Den.common_denominator | (intros; apply GlobalTheory.CompanionTheory.BasePsi.Den.common_denominator <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianEulerProductStandard
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianEulerProductStandard
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg

theorem isHermND_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) :
    IsHermND σ (1 : Matrix (Fin M) (Fin M) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem exists_test_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ n : ℕ, 0 < n → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ k, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ y))) := by
  intro F E _ _ _ _ _ σ hCM n hn ψ hψ db hdb d b laminf lam hinf hlam
  obtain ⟨S₁, h⟩ := GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx F E σ hCM (2 * n + 1) 1 (isHermND_one σ _) n
    (by omega) ψ hψ db hdb d b laminf lam hinf hlam
  refine ⟨S₁, fun S hS => ?_⟩
  obtain ⟨ρ, U, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h S hS
  exact ⟨ρ, U, a1, a2, fun k v => ⟨(a3 k v).1, (a3 k v).2.1, (a3 k v).2.2.1⟩, a4, fun k v => (a3 k v).2.2.2, a5, a6, a7, a8⟩

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianEulerProductStandardStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_euler_product_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ n : ℕ, 0 < n → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ k, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ y))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg.exists_test_approx | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg.exists_test_approx | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg.exists_test_approx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayNormAndModuleFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayNormAndModuleFormula
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

theorem norm_theta {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (ε : ℝ) (w : InfinitePlace F) : ‖θ ε w‖ = |ε| := by
  have hw : w.IsReal := hF.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ρ : ℝ →+* ℝ := (e : w.Completion →+* ℝ).comp ((Pi.evalRingHom _ w).comp θ)
  have hρ : ρ ε = ε := by
    have : ρ = RingHom.id ℝ := Subsingleton.elim _ _
    rw [this]; rfl
  have hnorm : ‖θ ε w‖ = ‖e (θ ε w)‖ := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) _).symm
  rw [hnorm]
  change ‖ρ ε‖ = |ε|
  rw [hρ, Real.norm_eq_abs]

theorem norm_md_ray : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F,
    Continuous θ → ∀ r, IsRay θ r → (∀ (ε : ℝ) (w : InfinitePlace F), ‖θ ε w‖ = |ε|) ∧
      ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  intro F _ _ hF θ _ r hr
  refine ⟨norm_theta hF θ, fun δ hδ => ?_⟩
  obtain ⟨h1, h2⟩ := hr δ hδ
  have hmd : md (r δ) = (∏ w : InfinitePlace F, ‖(r δ : AF F).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ := IdeleGroup.ideleModule_eq _
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [h2]
    exact norm_one
  rw [hmd, hfin, mul_one, h1]
  simp only [norm_theta hF θ δ, abs_of_pos hδ]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayNormAndModuleFormulaStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_norm_and_module_formula : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → (∀ (ε : ℝ) (w : InfinitePlace F), ‖θ ε w‖ = |ε|) ∧ ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay.norm_md_ray | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay.norm_md_ray | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay.norm_md_ray <;> assumption)
end
end
