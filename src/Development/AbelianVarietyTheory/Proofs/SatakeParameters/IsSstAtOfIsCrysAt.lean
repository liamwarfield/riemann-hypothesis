module

public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivial
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattened
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealTiedSetDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CrysSst

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PMon Module TensorProduct

theorem finrank_Dst_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) :
    FiniteDimensional ℚ_[l] ↥(Dst P ρ) ∧
      finrank ℚ_[l] ↥(Dst P ρ) ≤ finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg ρ
  haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
    Module.rank_lt_aleph0_iff.mp (hup.trans_lt Cardinal.natCast_lt_aleph0)
  have hup' : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := by
    rw [← finrank_eq_rank] at hup
    exact_mod_cast hup
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp hs g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ Dst P ρ}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ℚ_[l] V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : Dst P ρ ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hbS j.2) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp hs g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    exact this
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  have h1 : finrank ℚ_[l] ↥(Dst P ρ) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  exact h1.trans (Nat.mul_le_mul_right _ (hli.fintype_card_le_finrank.trans hup'))

theorem isSst_of_isCrys {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (h : IsCrys (P.PD K) ρ) : IsSst P ρ := by
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  obtain ⟨hfin, hb⟩ := finrank_Dst_le P AI T (GlobalTheory.PstCoeff.resQ ρ)
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  have hfin' : FiniteDimensional ℚ_[l] ↥((Dst P ρ).restrictScalars ℚ_[l]) := hD ▸ hfin
  haveI : Module.Finite ℚ_[l] ↥(Dst P ρ) := hfin'
  haveI : FiniteDimensional ↥LL.1 ↥(Dst P ρ) :=
    Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 ↥(Dst P ρ)
  have hV : finrank ℚ_[l] V = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 V := (finrank_mul_finrank ℚ_[l] ↥LL.1 V).symm
  have hup : finrank ↥LL.1 ↥(Dst P ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
    rw [e, hV] at hb
    refine Nat.le_of_mul_le_mul_left ?_ (finrank_pos (R := ℚ_[l]) (M := ↥LL.1))
    calc finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ)
        ≤ finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 V * finrank ℚ_[l] ↥(K0 K) := hb
      _ = finrank ℚ_[l] ↥LL.1 * (finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V) := by ring
  have hle : (Dcris (P.PD K) ρ).map (crisIncl P ↥LL.1 V) ≤ Dst P ρ := fun x hx =>
    ((mem_Dst_and_monV_eq_zero_iff l P K LL V ρ x).mpr hx).1
  have hlo : finrank ↥LL.1 ↥(Dcris (P.PD K) ρ) ≤ finrank ↥LL.1 ↥(Dst P ρ) := by
    rw [(Submodule.equivMapOfInjective _ (crisIncl_injective P) (Dcris (P.PD K) ρ)).finrank_eq]
    exact Submodule.finrank_mono hle
  unfold IsCrys at h
  unfold IsSst
  exact le_antisymm hup (h ▸ hlo)

end GlobalTheory.CrysSst

theorem GlobalTheory.CrysSst.isSstAt_of_isCrysAt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)), IsCrysAt P Bw r → IsSstAt P Bw r := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r hc
  obtain ⟨T⟩ := hT
  obtain ⟨LL', r', hm, hcr⟩ := hc
  exact ⟨LL', r', hm, GlobalTheory.CrysSst.isSst_of_isCrys P AI T (Bw.repE LL' r') hcr⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceUnitsCharacterEqOfAgreeOnField
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceUnitsCharacterEqOfAgreeOnField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjDense

open Filter Topology

theorem denseRange_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    DenseRange (s.i : L → s.v.adicCompletion (maximalRealSubfield L)) := by
  refine (s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩

theorem eq_of_agree : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, ξ u = μ (Units.map c.toMonoidHom u) := by
  intro L _ _ _ s c hc hci μ ξ hμ ⟨N, hN⟩ hglob d
  obtain ⟨z, hz⟩ := s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))
  have hξo : GlobalTheory.SmGL.IsSmoothChar ξ := by
    have hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ |
        Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z} := by
      have h1 := (Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage
        (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))
      simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)
    · simp only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]
      exact WithZero.exp_pos
    · have hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z := hx
      exact hN x (by rw [← hz]; exact hx'.le)
  have hcu : Continuous (Units.map c.toMonoidHom :
      (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ) := by
    rw [Units.continuous_iff]
    exact ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩
  have hs := hξo.mul (hμ.comp _ hcu).inv
  have hcl := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 ?_
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U := by
    have : d ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (denseRange_i s).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  have hm : Units.map c.toMonoidHom
      (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) =
      Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0) := Units.ext (hci k)
  show ξ _ * (μ (Units.map c.toMonoidHom _))⁻¹ = 1
  rw [hm, ← hglob]
  exact mul_inv_cancel _

end GlobalTheory.ConjDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceUnitsCharacterEqOfAgreeOnFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_unitsCharacter_eq_of_agree_on_field : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, ξ u = μ (Units.map c.toMonoidHom u) := by
  first | exact @GlobalTheory.ConjDense.eq_of_agree | exact GlobalTheory.ConjDense.eq_of_agree | (intros; apply GlobalTheory.ConjDense.eq_of_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeft
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.ProdReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_line_left {r : ℕ} (h : 0 + r = r) {M V : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin 0) k) M) (κ : M ≃ₗ[ℂ] ℂ)
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) :
    Nonempty ((ind₂ (stdSum h) (extTensor σ π)).Equiv π) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  have hE : ∀ g w, σ g w = w := fun g w => by rw [Subsingleton.elim g 1, map_one]; rfl
  let L : V ≃ₗ[ℂ] M ⊗[ℂ] V :=
    (TensorProduct.lid ℂ V).symm ≪≫ₗ TensorProduct.congr κ.symm (LinearEquiv.refl ℂ V)
  let u := κ.symm 1
  have hL : ∀ v, L v = u ⊗ₜ[ℂ] v := fun v => by simp [L, u]
  have hs : ∀ i : Fin r, stdSum h (Sum.inr i) = i := fun i => Fin.ext (by simp)
  have hl : ∀ p : parab k (two (stdSum h)), (leviProj k (two (stdSum h)) p true : GL (Fin r) k) = p :=
    fun p => by
      ext i j
      rw [leviProj_apply, two_true, two_true, hs, hs]
  have hd : ∀ p : parab k (two (stdSum h)),
      deltaHalf k (Two (Fin 0) (Fin r)) (leviProj k (two (stdSum h)) p) = 1 := fun p => by
    have : leviProj k (two (stdSum h)) p =
        leviTwo k _ _ ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)) :=
      ((leviTwo k _ _).apply_symm_apply _).symm
    rw [this, deltaHalf_two,
      Subsingleton.elim ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)).1 1]
    simp
  have hP : ∀ g : GL (Fin r) k, g ∈ parab k (two (stdSum h)) := fun g =>
    (mem_parab_two k).2 fun j i => i.elim0
  have law : ∀ (p : parab k (two (stdSum h))) v,
      (deltaHalf k (Two (Fin 0) (Fin r)) (leviProj k (two (stdSum h)) p) : ℂ) •
        (extTensor σ π) ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)) (L v) =
          L (π p v) := fun p v => by
    rw [hd, Units.val_one, one_smul, hL, hL, extTensor_tmul, hE]
    congr 1
    exact congrArg (fun g => π g v) (hl p)
  let f : π.IntertwiningMap (ind₂ (stdSum h) (extTensor σ π)) :=
    { toFun := fun v => ⟨⟨fun x => L (π x v), fun p x => by
          show L (π (↑p * x) v) = (deltaHalf k _ (leviProj k _ p) : ℂ) •
            (extTensor σ π) ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k _ p)) (L (π x v))
          rw [law, map_mul, Module.End.mul_apply]⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          rw [map_mul, Module.End.mul_apply, hg'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (v + w)) = L (π x v) + L (π x w)
        rw [map_add (f := _), map_add (f := _)]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x ((c : ℂ) • v)) = (c : ℂ) • L (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (π g v)) = L (π (x * g) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hb : Function.Bijective f := by
    refine ⟨fun v w hvw => ?_, fun φ => ⟨L.symm (φ.1.1 1), ?_⟩⟩
    · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1 1) hvw
      rw [map_one, Module.End.one_apply, Module.End.one_apply] at h1
      exact L.injective h1
    · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
      have h1 := φ.1.2 ⟨x, hP x⟩ 1
      rw [mul_one] at h1
      refine (law ⟨x, hP x⟩ _).symm.trans ?_
      rw [L.apply_symm_apply]
      exact h1.symm
  exact ⟨(GlobalTheory.LocGL.equivOfBijective f hb).symm⟩


variable (k) in
theorem ind₂_unit_left (r t : ℕ) (h : t + r = r) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) (d : Fin 0 → ℕ) (X : Fin 0 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (e : (Σ a, Fin (d a)) ≃ Fin t) :
    Nonempty ((ind₂ (stdSum h) (extTensor (multiProd e τ) π)).Equiv π) := by
  have ht : t = 0 := by omega
  subst ht
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let ev1 : IndSp e (piTensor τ) →ₗ[ℂ] ⨂[ℂ] i, X i :=
    { toFun := fun f => f.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let κ : IndSp e (piTensor τ) ≃ₗ[ℂ] ℂ := (LinearEquiv.ofBijective ev1 ⟨fun f g hfg =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact hfg)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      GlobalTheory.SmGL.MultiIrr.mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩).trans
    (PiTensorProduct.isEmptyEquiv _)
  exact ind₂_line_left h (multiProd e τ) κ π hπ

end GlobalTheory.ProdReorder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeftStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInductionTwoBlocks_empty_product_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (h : t + r = r) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin r) k) V), IsSmooth π → ∀ (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin t), Nonempty ((ind₂ (stdSum h) (extTensor (multiProd e τ) π)).Equiv π) := by
  first | exact @GlobalTheory.ProdReorder.ind₂_unit_left | exact GlobalTheory.ProdReorder.ind₂_unit_left | (intros; apply GlobalTheory.ProdReorder.ind₂_unit_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharacterEqInvAtTransposeInvLowerBlockDet
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharacterEqInvAtTransposeInvLowerBlockDet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BlockConjDet

open ValuativeRel

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_det_mul_sub_one_lt {r t : ℕ} {h : GL (Fin (r + t)) k} (hh : h ∈ blockGrp k r t) :
    valuation k (((h⁻¹ : GL (Fin (r + t)) k).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
  obtain ⟨g, hg⟩ := hh.1
  have hi := ((blockGrp k r t).inv_mem hh).2
  have hinv : (h⁻¹ : GL (Fin (r + t)) k) = Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g⁻¹ := by
    rw [← hg, map_inv]
  have hC : ∀ (i : Fin t) (j : Fin r),
      (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t j) ∈ 𝓂[k] := by
    intro i j
    have := hi (Fin.natAdd r i) j
    have hne : Fin.natAdd r i ≠ Fin.castAdd t j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    rw [hinv, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    change valuation k (algebraMap 𝒪[k] k ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t j))) < 1 at this
    exact (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr this)
  have hres : (((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)) *
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r))).map (IsLocalRing.residue 𝒪[k]) = 1 := by
    ext i j
    have e1 : ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val * g.val) (Fin.natAdd r i) (Fin.natAdd r j) =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) (Fin.natAdd r i) (Fin.natAdd r j) := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_apply, Fin.sum_univ_add] at e1
    have hm : ∑ x : Fin r, (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t x) *
        g.val (Fin.castAdd t x) (Fin.natAdd r j) ∈ 𝓂[k] :=
      Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (hC i x)
    have e2 : (((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)) *
        (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r))) i j =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) (Fin.natAdd r i) (Fin.natAdd r j) -
          ∑ x : Fin r, (g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val (Fin.natAdd r i) (Fin.castAdd t x) *
            g.val (Fin.castAdd t x) (Fin.natAdd r j) := by
      simp only [Matrix.mul_apply, Matrix.submatrix_apply]; rw [← e1]; ring
    rw [Matrix.map_apply, e2, map_sub, (IsLocalRing.residue_eq_zero_iff _).2 hm, sub_zero]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  have hm : ((g⁻¹ : GL (Fin (r + t)) 𝒪[k]).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det *
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply,
      hres, Matrix.det_one, map_one, sub_self]
  have hv := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ∀ G : GL (Fin (r + t)) 𝒪[k],
      ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) G).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
        (((G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) := by
    intro G
    rw [show (((G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) =
      algebraMap 𝒪[k] k (G.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det from rfl, RingHom.map_det]
    rfl
  rw [hinv, ← hg, e, e]
  simpa only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one] using hv

end

end GlobalTheory.BlockConjDet

namespace GlobalTheory.BlockConjDet

theorem blockChar_eq_inv_detDD : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → ∃ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (u : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r (d * b * d⁻¹) ∧ ∀ μ : (s.w.adicCompletion L)ˣ →* ℂˣ, IsTame μ → blockChar μ (Matrix.GeneralLinearGroup.map c.toRingHom a) = (((μ (Units.map c.toMonoidHom u))⁻¹ : ℂˣ) : ℂ) := by
  intro L _ _ _ s r t c _ a b hb ha ϖ hϖ d hd
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖ; exact (WithZero.exp_ne_zero hϖ.symm).elim
  have hdinv : (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val =
      Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹) := by
    have h1 : d.val * Matrix.diagonal (fun i : Fin (r + t) =>
        if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹) = 1 := by
      rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; ext i; split_ifs <;> simp [hϖ0]
    calc (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val
        = (d⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val * (d.val * Matrix.diagonal (fun i : Fin (r + t) =>
          if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ⁻¹)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hDD : NG.detDD s r (d * b * d⁻¹) =
      ((a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    let e : Fin t ≃ {x : Fin (r + t) // r ≤ x.val} :=
      { toFun := fun i => ⟨Fin.natAdd r i, by simp⟩
        invFun := fun x => ⟨x.1.val - r, by omega⟩
        left_inv := fun i => by ext; simp
        right_inv := fun x => by ext; simp; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose]
    congr 1
    ext i j
    have hn : ∀ x : Fin t, ¬ ((Fin.natAdd r x : Fin (r + t)) : ℕ) < r := by intro x; simp
    simp only [e, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.coe_fn_mk, Units.val_mul,
      hdinv, hd, Matrix.mul_diagonal, Matrix.diagonal_mul, hb]
    rw [if_neg (hn _), if_neg (hn _), mul_comm ϖ, mul_inv_cancel_right₀ hϖ0]
  have hc : c (NG.detDD s r (d * b * d⁻¹)) =
      (((Matrix.GeneralLinearGroup.map c.toRingHom a)⁻¹ : GL (Fin (r + t)) (s.w.adicCompletion L)).val.submatrix
        (Fin.natAdd r) (Fin.natAdd r)).det := by
    rw [hDD, ← map_inv]
    exact RingHom.map_det c.toRingHom _
  have hv := val_det_mul_sub_one_lt ha
  have hne : ∀ x y : s.w.adicCompletion L, ValuativeRel.valuation _ (x * y - 1) < 1 → x ≠ 0 ∧ y ≠ 0 := by
    intro x y h
    constructor <;> rintro rfl <;> simp at h
  obtain ⟨h1, h2⟩ := hne _ _ hv
  have hF : NG.detDD s r (d * b * d⁻¹) ≠ 0 := fun h0 => h1 (by rw [← hc, h0, map_zero])
  refine ⟨Units.mk0 _ hF, rfl, fun μ hμ => ?_⟩
  rw [blockChar_eq μ _ (Units.mk0 _ h2) rfl]
  have ht := hμ (Units.map c.toMonoidHom (Units.mk0 _ hF) * Units.mk0 _ h2) (by
    simp only [Units.val_mul, Units.coe_map, Units.val_mk0]
    rw [show (c.toMonoidHom : _ →* _) (NG.detDD s r (d * b * d⁻¹)) = c (NG.detDD s r (d * b * d⁻¹)) from rfl, hc]
    exact hv)
  rw [map_mul] at ht
  rw [eq_inv_of_mul_eq_one_right ht]

end GlobalTheory.BlockConjDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharacterEqInvAtTransposeInvLowerBlockDetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockCharacter_eq_inv_at_transposeInv_lowerBlockDet : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), (∀ x, Valued.v (c x) = Valued.v x) → ∀ (a b : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))), b.val = (a⁻¹ : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose → Matrix.GeneralLinearGroup.map c.toRingHom a ∈ blockGrp (s.w.adicCompletion L) r t → ∀ ϖ : s.v.adicCompletion (maximalRealSubfield L), Valued.v ϖ = WithZero.exp (-1) → ∀ d : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), d.val = Matrix.diagonal (fun i : Fin (r + t) => if (i : ℕ) < r then (1 : s.v.adicCompletion (maximalRealSubfield L)) else ϖ) → ∃ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (u : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r (d * b * d⁻¹) ∧ ∀ μ : (s.w.adicCompletion L)ˣ →* ℂˣ, IsTame μ → blockChar μ (Matrix.GeneralLinearGroup.map c.toRingHom a) = (((μ (Units.map c.toMonoidHom u))⁻¹ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.BlockConjDet.blockChar_eq_inv_detDD | exact GlobalTheory.BlockConjDet.blockChar_eq_inv_detDD | (intros; apply GlobalTheory.BlockConjDet.blockChar_eq_inv_detDD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacter
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.TripleGal GlobalTheory.Pst
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CharAboveRead

open scoped TensorProduct

theorem exists_isInduced_of {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (τ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (A : ValuationSubring Ω) (hA : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
    (hj : Induces Bw) : ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' := by
  let jE : E →+* Om l := Bw.j.comp (algebraMap E Ω)
  have hjE : ∀ x : 𝓞 E, ‖jE (x : E)‖ < 1 ↔ x ∈ w.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := GlobalTheory.GalFirstClause.Emb.norm_eq_of_samePlace τ jE w hw hτ hjE
  have hker : ∀ t ∈ RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE), GlobalTheory.GalFirstClause.Emb.tensLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((GlobalTheory.GalFirstClause.Emb.norm_tensLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (GlobalTheory.GalFirstClause.Emb.tensLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (a ⊗ₜ y) ∈ _
      rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((GlobalTheory.GalFirstClause.Emb.tensLift jE).range : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule (GlobalTheory.GalFirstClause.Emb.tensLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (GlobalTheory.GalFirstClause.Emb.tensLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by
      change GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x) = jE x; rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (GlobalTheory.GalFirstClause.Emb.tensLift jE)) (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker).comp
      (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict Bw.LL.1.toSubalgebra (fun y => Bw.LL_split σ y), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = GlobalTheory.GalFirstClause.Emb.tensLift jE (1 ⊗ₜ x)
    rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (GlobalTheory.GalFirstClause.Emb.tensLift τ) hker
    ((Ideal.quotientKerEquivRange (GlobalTheory.GalFirstClause.Emb.tensLift jE)).symm (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = GlobalTheory.GalFirstClause.Emb.tensLift τ (1 ⊗ₜ x)
  rw [GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul]

theorem continuous_rankOneOperator {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (μ : Γ →* Kˣ) (hμ : Continuous μ) : Continuous fun g => ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) := by
  have hv : Continuous fun g => ((μ g : Kˣ) : K) := Units.continuous_val.comp hμ
  refine continuous_pi fun i => continuous_pi fun k => ?_
  have e : ∀ g, ((rk1 μ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) i k = ((μ g : Kˣ) : K) := fun g => by
    fin_cases i; fin_cases k; simp [rk1]
  simp only [e]
  exact hv

end GlobalTheory.CharAboveRead

namespace GlobalTheory.CharAboveRead


set_option maxHeartbeats 1000000 in
theorem deRham_and_jumps_rankOne_lAdic_character : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (μ : G D.host.E D.nd.Om →* (Qbar l)ˣ), Continuous μ → ∀ (J : (D.host.E →+* Qbar l) → Multiset ℤ)
    (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l →
    (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
      IsdRAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ (J τ)) →
    W.IsdRW l ι (rk1 μ) w ∧ ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
      W.jumpsW l ι (rk1 μ) τ = J τ := by
  intro D T W l _ ι μ hμ J w hw H
  have hcont : Continuous fun g => (rk1 μ g : Matrix (Fin 1) (Fin 1) (Qbar l)) := continuous_rankOneOperator μ hμ
  obtain ⟨K, ρ, hρc, hρ⟩ := GlobalTheory.GalFirstClause.finextRep l D.host.E D.nd.Om 1 (rk1 μ) hcont
  obtain ⟨j, L0, hj, hLL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l D.host.E D.nd.Om w (D.nd.plOm.1 w) hw (D.nd.plOm.2 w)
  obtain ⟨Bw, hBj, hBLL, -, hBto⟩ := hLL L0 le_rfl
  have hind : Induces Bw := fun x => by rw [hBj]; exact hj x
  let LL' : FinExt l := supExt K Bw.LL
  have hK : K.1 ≤ LL'.1 := le_sup_left
  have hB : Bw.LL.1 ≤ LL'.1 := le_sup_right
  let ρ' : G D.host.E D.nd.Om →* GL (Fin 1) ↥LL'.1 := mapRep (IntermediateField.inclusion hK).toRingHom ρ
  have hρ' : mapRep (algebraMap ↥LL'.1 (Om l)) ρ' = rk1 μ := by
    rw [← hρ]
    ext g i k
    rfl
  have hρ'c : Continuous fun g => (ρ' g : Matrix (Fin 1) (Fin 1) ↥LL'.1) := by
    have hi : Continuous (IntermediateField.inclusion hK) :=
      continuous_induced_rng.2 continuous_subtype_val
    exact hρc.matrix_map hi
  have hmodel : IsModel Bw (resDec D.nd.plOm.1 (rk1 μ) w) LL'
      (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    ⟨hB, by rw [← hρ']; rfl⟩
  let φ : ↥(OL L0) →+* Qbar l := L0.1.val.toRingHom.comp (OL L0).val.toRingHom
  have hφ : ∀ x, φ x = ((Bw.toLL x : ↥Bw.LL.1) : Om l) := fun x => (hBto x).symm
  have hcl := (W.loc l ι w hw _ Bw hind φ hφ).2 LL' hB 1 ρ' hρ'c
  rw [hρ'] at hcl
  have hab := H _ Bw hind
  have hdR : Bw.IsdRE (D.loc l) LL' (ρ'.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    (hmodel.isdRAt_iff (D.loc l)).1 hab.1
  refine ⟨hcl.2.1.2 hdR, fun τ hτ => ?_⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_isInduced_of τ w hw hτ _ (D.nd.plOm.2 w) _ Bw hind
  let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1 := (IntermediateField.inclusion hB).comp τ₀
  have hτ'' : IsInduced Bw τ τ'' := fun x => hτ₀ x
  have hJ := hab.2 τ LL' τ'' hτ''
  ext n
  apply Nat.cast_injective (R := ℤ)
  rw [(hcl.2.2.2 τ τ'' hτ'').2 hdR n, IsJumpsAt.count_eq (D.loc l) hmodel hτ'' hJ n]

end GlobalTheory.CharAboveRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.TripleGal GlobalTheory.Pst

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_jumps_of_continuous_lAdic_char :
    ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (W : GlobalTheory.HeightCounting.WDSide D T)
      (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (μ : G D.host.E D.nd.Om →* (Qbar l)ˣ),
    Continuous μ → ∀ (J : (D.host.E →+* Qbar l) → Multiset ℤ) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w ∈ placesOver D.host.E l →
    (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
      IsdRAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ (J τ)) →
    W.IsdRW l ι (rk1 μ) w ∧ ∀ τ : D.host.E →+* Qbar l,
      (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → W.jumpsW l ι (rk1 μ) τ = J τ :=
  @GlobalTheory.CharAboveRead.deRham_and_jumps_rankOne_lAdic_character
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlocksLtOfParabolicUnipotentRadicalNeBot
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlocksLtOfParabolicUnipotentRadicalNeBot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.UnipRadProper

theorem blocks_lt_of_unipRad_ne_bot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := by
  intro k _ _ _ _ n s d e h a
  by_contra hle
  push_neg at hle
  apply h
  have hcard : ∑ b, d b = n := by simpa using (Fintype.card_congr e)
  have hzero : ∀ b, b ≠ a → d b = 0 := by
    intro b hb
    have h2 : d a + d b ≤ ∑ c, d c :=
      Finset.add_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ b) (Ne.symm hb)
    omega
  have hblk : ∀ (b : Fin s) (j : Fin (d b)), b = a := by
    intro b j
    by_contra hb
    exact (hzero b hb ▸ j).elim0
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext i j
  obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨c, j⟩, rfl⟩ := e.surjective j
  obtain rfl := hblk b i
  obtain rfl := hblk c j
  rw [(mem_unipRad.1 hg).2]
  simp [Matrix.one_apply]

end GlobalTheory.UnipRadProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlocksLtOfParabolicUnipotentRadicalNeBotStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blocks_lt_of_parabolicUnipotentRadical_ne_bot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := by
  first | exact @GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot | exact GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot | (intros; apply GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupport
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.CuspidalSupportZero

theorem exists_isCuspSupport_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (π : Irr k 0) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let d : Fin 0 → ℕ := fun a => a.elim0
  let σ : ∀ a, Irr k (d a) := fun a => a.elim0
  refine ⟨0, d, σ, π.irr, fun a => a.elim0, ?_⟩
  let e : (Σ a, Fin (d a)) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  refine ⟨e, ?_⟩
  obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := k) e (fun a => (σ a).π)
  have hirr := π.irr

  obtain ⟨v₀, hv₀⟩ : ∃ v : π.V, v ≠ 0 := by
    by_contra h
    push_neg at h
    apply (bot_ne_top : (⊥ : Subrepresentation π.π) ≠ ⊤)
    ext v
    simp [h v]
  let L : Subrepresentation π.π := ⟨ℂ ∙ v₀, fun g v hv => by
    rw [Subsingleton.elim g 1, map_one]; exact hv⟩
  have hL : L = ⊤ := by
    rcases eq_bot_or_eq_top L with h | h
    · exfalso
      have : v₀ ∈ L.toSubmodule := Submodule.mem_span_singleton_self v₀
      rw [h] at this
      exact hv₀ ((Submodule.mem_bot ℂ).1 this)
    · exact h
  let f : (multiProd e fun a => (σ a).π).IntertwiningMap π.π :=
    { toLinearMap := (LinearMap.toSpanSingleton ℂ π.V v₀) ∘ₗ φ.toLinearEquiv.toLinearMap
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]; rfl }
  refine IsSubquotient.of_surjective f fun v => ?_
  have hv : v ∈ L.toSubmodule := by rw [hL]; trivial
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  refine ⟨φ.toLinearEquiv.symm c, ?_⟩
  show (LinearMap.toSpanSingleton ℂ π.V v₀) (φ.toLinearEquiv (φ.toLinearEquiv.symm c)) = c • v₀
  erw [LinearEquiv.apply_symm_apply]
  rfl

end GlobalTheory.CuspidalSupportZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidal_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (π : Irr k 0), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  first | exact @GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero | exact GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero | (intros; apply GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.CuspSupportExist

theorem L_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (π : Irr k 0), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := GlobalTheory.T.exists_cuspidal_support

theorem L_jacq : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ¬ Subsingleton (Jacquet π.π (unipRad k e)) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible ∧ IsSmooth τ ∧ IsSubquotient τ (GlobalTheory.SmGL.jac e π.π) ∧ ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := GlobalTheory.T.exists_injective_parInd_of_jacquet_nontrivial

theorem L_tens : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (GlobalTheory.SmGL.jac e π.π) → ∃ σ : ∀ a, Irr k (d a), IsSubquotient τ (piTensor fun a => (σ a).π) := GlobalTheory.T.exists_irreducible_tensor_of_jacquet_subquotient

theorem L_ind : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := GlobalTheory.T.parabolicInduction_preserves_subquotient

theorem L_lt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := GlobalTheory.T.blocks_lt_of_parabolicUnipotentRadical_ne_bot

theorem L_pit : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)] (X Y : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (ρ' : ∀ a, Representation ℂ (Γ a) (Y a)), (∀ a, IsSubquotient (ρ a) (ρ' a)) → IsSubquotient (piTensor ρ) (piTensor ρ') := GlobalTheory.T.piExteriorTensor_isSubquotient_of_forall

theorem L_stage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)] (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)), (∀ a b, IsSmooth (ρ a b)) → ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n, IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a)) (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := GlobalTheory.T.isSubquotient_parInd_products_flattened

theorem cusp_case (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (hn : 0 < n) (π : Irr k n) (hc : IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  let e : (Σ _ : Fin 1, Fin n) ≃ Fin n :=
    { toFun := fun p => p.2, invFun := fun i => ⟨0, i⟩,
      left_inv := fun p => by
        obtain ⟨a, i⟩ := p
        obtain rfl : a = 0 := Subsingleton.elim _ _
        rfl
      right_inv := fun _ => rfl }
  obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one π.smooth e (fun _ _ => rfl)
  exact ⟨1, fun _ => n, fun _ => π, π.irr, fun _ => ⟨hn, π.irr, hc⟩, e,
    .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective⟩

theorem reduce (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (π : Irr k n) (hc : ¬ IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (σ : ∀ a, Irr k (d a)),
      (∀ a, d a < n) ∧ IsSubquotient π.π (multiProd e fun a => (σ a).π) := by
  obtain ⟨s, d, e, hne, hns⟩ : ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n),
      unipRad k e ≠ ⊥ ∧ ¬ Subsingleton (Jacquet π.π (unipRad k e)) := by
    by_contra h
    push_neg at h
    exact hc ⟨π.smooth, fun s d e hne => h s d e hne⟩
  obtain ⟨Y, _, _, τ, hτi, hτs, hτq, φ, hφ⟩ := L_jacq hBZ k n π s d e hns
  obtain ⟨σ, hσ⟩ := L_tens hGL k n π s d e Y τ hτi hτq
  exact ⟨s, d, e, σ, L_lt k n s d e hne, (IsSubquotient.of_injective φ hφ).trans
    (L_ind k _ _ _ e _ _ τ _ (isSmooth_piTensor fun a => (σ a).smooth) hσ)⟩

theorem glue (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (σ : ∀ a, Irr k (d a)) (hsub : IsSubquotient π.π (multiProd e fun a => (σ a).π))
    (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (τ : ∀ a b, Irr k (d' a b))
    (hτ : ∀ a, IsCuspSupport (σ a).π (d' a) (fun b => (τ a b).π)) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  have h3 := fun a => (hτ a).2.2
  choose e' he' using h3
  have step1 : IsSubquotient (multiProd e fun a => (σ a).π)
      (multiProd e fun a => multiProd (e' a) fun b => (τ a b).π) :=
    L_ind k _ _ _ e _ _ _ _ (isSmooth_piTensor fun a => isSmooth_parInd _ _)
      (L_pit _ _ _ _ _ _ he')
  obtain ⟨E, hE⟩ := L_stage k s n d e t d' e' _ (fun a b => (τ a b).π) fun a b => (τ a b).smooth
  exact ⟨∑ a, t a, _, fun c => τ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, π.irr,
    fun c => (hτ _).2.1 _, E, hsub.trans (step1.trans hE)⟩

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) := by
  intro hBZ hGL k _ _ _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact L_zero k π
  by_cases hc : IsCuspidal π.π
  · exact cusp_case k n hn π hc
  · obtain ⟨s, d, e, σ, hlt, hsub⟩ := reduce hBZ hGL k n π hc
    have h := fun a => ih (d a) (hlt a) (σ a)
    choose t d' τ hτ using h
    exact glue k n π s d e σ hsub t d' τ hτ

end GlobalTheory.CuspSupportExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGLStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidalSupport_irreducibleSmoothGL : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) := by
  first | exact @GlobalTheory.CuspSupportExist.main | exact GlobalTheory.CuspSupportExist.main | (intros; apply GlobalTheory.CuspSupportExist.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

open Matrix

namespace GlobalTheory.EllU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* UA E n where
  toFun g := ⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1),
    GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin g)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem finPart_mem (g : UA E n) : finPart g ∈ finU (E := E) (n := n) := pInf_finGL _

theorem finPart_of_finU {k : UA E n} (hk : k ∈ finU (E := E) (n := n)) : finPart k = k :=
  Subtype.ext (GlobalTheory.DefU.ClassFin.finGL_pFin ⟨k, hk⟩)

theorem finPart_of_infU {x : UA E n} (hx : x ∈ infU E n) : finPart x = 1 := by
  have h : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext ?_
  change finGL E n (GeneralLinearGroup.map (pFin E) x.1) = 1
  rw [h, map_one]

theorem inv_finPart_mul_mem (g : UA E n) : (finPart g)⁻¹ * g ∈ infU E n := by
  change GeneralLinearGroup.map (pFin E) ((finPart g)⁻¹ * g).1 = 1
  have h : GeneralLinearGroup.map (pFin E) (finPart g).1 = GeneralLinearGroup.map (pFin E) g.1 := pFin_finGL _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel]

theorem continuous_finPart : Continuous (finPart (E := E) (n := n)) := by
  have h1 : Continuous (GeneralLinearGroup.map (pFin E) : GA E n → GL (Fin n) (Af E)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
  exact Continuous.subtype_mk (GlobalTheory.DefU.ClassFin.continuous_finGL.comp (h1.comp continuous_subtype_val)) _

end GlobalTheory.EllU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceUnitaryLocEqTransposeInv
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceUnitaryLocEqTransposeInv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open TensorProduct

namespace GlobalTheory.ConjLoc

theorem proj_conjSP {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (a : AL L) :
    (GlobalTheory.TypeTame.conjSP s).proj a = s.proj (conjAL L a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x b =>
    simp [SplitPlace.proj, conjAL, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_conjSP : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (x : GAf L n), ((GlobalTheory.TypeTame.conjSP s).loc n x).val = ((s.loc n x)⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose := by
  intro L _ _ _ n s x
  have hx : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h1 : (s.loc n x).val * ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose = 1 := by
    have e : ((GlobalTheory.TypeTame.conjSP s).loc n x).val.transpose
        = (conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L))).map s.proj := by
      refine Matrix.ext fun i j => ?_
      exact proj_conjSP s _
    have e' : (s.loc n x).val = (x.1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj := rfl
    rw [e, e', ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 := Units.inv_eq_of_mul_eq_one_right h1
  rw [h2, Matrix.transpose_transpose]

end GlobalTheory.ConjLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceUnitaryLocEqTransposeInvStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateSplitPlace_unitaryLoc_eq_transpose_inv : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (x : GAf L n), ((GlobalTheory.TypeTame.conjSP s).loc n x).val = ((s.loc n x)⁻¹ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))).val.transpose := by
  first | exact @GlobalTheory.ConjLoc.loc_conjSP | exact GlobalTheory.ConjLoc.loc_conjSP | (intros; apply GlobalTheory.ConjLoc.loc_conjSP <;> assumption)
end
end
