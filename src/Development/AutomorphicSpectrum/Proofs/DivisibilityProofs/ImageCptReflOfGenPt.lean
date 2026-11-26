module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPoint
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ImageCptReflOfGenPt
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MapDomainRelationLiftCommutingSquare
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem HostAut.s_symm_s (g : HostAut H) (a : 𝓞 E) : g.s (g.symm.s a) = a :=
  RingOfIntegers.ext (g.σ.apply_symm_apply (a : E))

theorem HostAut.hostAut_symm_s_s (g : HostAut H) (a : 𝓞 E) : g.symm.s (g.s a) = a :=
  RingOfIntegers.ext (g.σ.symm_apply_apply (a : E))

theorem HostAut.hostAut_refl_s (a : 𝓞 E) : (HostAut.refl H).s a = a :=
  RingOfIntegers.ext rfl

theorem oAct_eq {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] {u v : OAct O G}
    (h : ∀ a, u.act a = v.act a) : u = v := by
  cases u
  cases v
  have : ∀ a, _ = _ := h
  obtain rfl : _ = _ := funext this
  rfl

theorem twistSAB_eq_of_act {S : Scheme.{0}} (t : SAB H S) (g : HostAut H)
    (h : ∀ a, t.act.act (g.s a) = t.act.act a) : twistSAB t g = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct act g.s = act := oAct_eq h
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

theorem twistSAB_twistSAB {S : Scheme.{0}} (t : SAB H S) (g g' : HostAut H)
    (h : ∀ a, g.s (g'.s a) = a) : twistSAB (twistSAB t g) g' = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct (twistAct act g.s) g'.s = act := oAct_eq fun a => congrArg act.act (h a)
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

theorem twistSAB_symm_refl (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0})
    (t : SAB H S) (g : HostAut H) :
    twistSAB (twistSAB t g) g.symm = t ∧ twistSAB (twistSAB t g.symm) g = t ∧
      twistSAB t (HostAut.refl H) = t :=
  ⟨twistSAB_twistSAB t g g.symm g.s_symm_s, twistSAB_twistSAB t g.symm g g.hostAut_symm_s_s,
    twistSAB_eq_of_act t _ fun a => congrArg t.act.act (HostAut.hostAut_refl_s a)⟩

end GlobalTheory.CompanionTheory.Ar
end

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Indep

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem pp_monomial (M : Top.RootModel Ψ N) (II : IntersectionSystem) (m : Option (Ψ × Fin N) →₀ ℕ) (a : ℝ) :
    M.PP II (monomial m a) = a * limUnder (𝓝[>] (0:ℝ)) (fun t => M.arMono II t m) := by
  have : (monomial m a : Top.RPA Ψ N) = a • basisMonomials (Option (Ψ × Fin N)) ℝ m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, Top.RootModel.PP, Module.Basis.constr_basis, smul_eq_mul]

end GlobalTheory.CompanionTheory.Ar.Indep

namespace GlobalTheory.CompanionTheory.Ar.Indep

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem pp_toA_eq_of_tendsto (M M' : Top.RootModel Ψ N) (II : IntersectionSystem) (hconv : M.Converges II)
    (h : ∀ m : (Ψ × Fin N) →₀ ℕ, Tendsto (fun t => M.arMono II t (m.mapDomain some) -
      M'.arMono II t (m.mapDomain some)) (𝓝[>] (0:ℝ)) (𝓝 0)) (F : Top.RP Ψ N) :
    M.PP II (Top.toA F) = M'.PP II (Top.toA F) := by
  rw [F.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Top.toA, map_sum, rename_monomial, pp_monomial]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  obtain ⟨L, hL⟩ := hconv (m.mapDomain some)
  have hL' : Tendsto (fun t => M'.arMono II t (m.mapDomain some)) (𝓝[>] (0:ℝ)) (𝓝 L) := by
    have := hL.sub (h m)
    simpa using this
  rw [hL.limUnder_eq, hL'.limUnder_eq]

end GlobalTheory.CompanionTheory.Ar.Indep

namespace GlobalTheory.CompanionTheory.Ar.Indep

theorem spectrumMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem cst_of_factor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (A : HodgeCpt Y S y)
    (hβ : Mono (spMap β)) (x : Sp A.Ω₀ ⟶ Xo.XF c) (hx : A.ξ₀ = x ≫ Y.j) :
    spMap A.fn ≫ x ≫ Limits.pullback.snd _ _ = spMap A.cst := by
  rw [← cancel_mono (spMap β), spectrumMap_comp, ← A.cst_over, ← Y.jQ_over]
  have h1 : A.ξ ≫ A.f = spMap A.fn ≫ x ≫ Y.jQ ≫ Limits.pullback.fst _ _ := by
    have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this
    rw [this, hx]; rfl
  have h2 := h1 =≫ Y.s
  simp only [Category.assoc] at h2 ⊢
  rw [← Limits.pullback.condition]
  exact h2.symm

theorem imageCpt_refl_of_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y'), Mono (spMap β) → genPt A.ξ₀ = genPt A'.ξ₀ → IsImageCpt (Iso.refl Xo.X) A A' := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω Ω' _ _ K K' _ _ J J' y y' A A' hβ hgen
  obtain ⟨x, hx⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c O β Y S Ω K J y A hβ
  obtain ⟨x', hx'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c O β Y S Ω' K' J' y' A' hβ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.generic_point_field_iso Y.X A.Ω₀ A'.Ω₀ A.ξ₀ A'.ξ₀ A.gen₀ A'.gen₀ hgen
  haveI : Mono Y.j := by
    haveI := hβ
    haveI := Y.jQ_open
    unfold Model.j
    infer_instance
  have hxx : spMap ψ.toRingHom ≫ x' = x := by
    rw [← cancel_mono Y.j, Category.assoc, ← hx', ← hx, hψ]
  refine ⟨x, x', ψ, hx, hx', ?_, ?_, cst_of_factor A hβ x hx, cst_of_factor A' hβ x' hx'⟩
  · rw [← Category.assoc, hxx]
    exact (congrArg (x ≫ ·) (Category.comp_id _)).symm
  · rw [← Category.assoc, hxx]

end GlobalTheory.CompanionTheory.Ar.Indep

namespace GlobalTheory.CompanionTheory.Ar.Indep

end GlobalTheory.CompanionTheory.Ar.Indep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainArithVariety
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainArithVariety
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagRatioTrdeg GroundTheory.Heights₂.Heights.LowerBoundFree.FlagArithVar

theorem pivotRatio_algebraicIndependent (F : Type) [Field F] (Ψ : Type) (n : ℕ) :
    AlgebraicIndependent F (pivotRatio F Ψ n) := by
  classical
  have hy := pivot_indep F Ψ n
  let δ : PivotIdxLe Ψ n → PivotIdxLe Ψ n :=
    fun q => (q.1, ⟨q.2.1, ⟨Fin.castLE (Nat.sub_le n 1) q.2.1, by simp⟩⟩)
  have hz := ratio_indep F hy δ (fun q => rfl)
  let incl : PivotIdx Ψ n → PivotIdxLe Ψ n := fun q => (q.1, ⟨q.2.1, ⟨q.2.2.1, q.2.2.2.le⟩⟩)
  have hincl : Function.Injective incl := by
    rintro ⟨τ, a, b, hb⟩ ⟨τ', a', b', hb'⟩ h
    simp only [incl, Prod.mk.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨h0, h1, h2⟩ := h
    subst h0 h1
    simp only [heq_eq_eq, Subtype.mk.injEq] at h2
    subst h2
    rfl
  have hrat : (fun q : PivotIdxLe Ψ n => if δ q = q then pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 else
      pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / pivotMinor (genMatFr F Ψ n (δ q).1) (δ q).2.1 (δ q).2.2.1) ∘
        incl = pivotRatio F Ψ n := by
    funext q
    have hne : δ (incl q) ≠ incl q := by
      intro h
      have := congrArg (fun r : PivotIdxLe Ψ n => ((r.2.2.1 : Fin n) : ℕ)) h
      simp only [δ, incl, Fin.val_castLE] at this
      have := q.2.2.2
      omega
    simp only [Function.comp_apply, hne, if_false]
    rfl
  exact hrat ▸ hz.comp incl hincl

theorem flag_mem_of_le (F : Type) [Field F] {K : Type} [Field K] [Algebra F K] {m : ℕ}
    (g : Matrix (Fin m) (Fin m) K) (A : IntermediateField F K) (hL : ∀ a, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g a ≠ 0)
    (j : Fin (m - 1))
    (hA : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) ≤ j → (a : ℕ) < b → pivotMinor g a b / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g a ∈ A)
    (S : PluckerBlocks m m j) : flagMinor g j S / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g j ∈ A := by
  have hj : (j : ℕ) + 1 ≤ m := by have := j.2; omega
  have hent : ∀ (a : Fin (m - 1)) (b : Fin m), (a : ℕ) ≤ j → pivotMinor g a b / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g a ∈ A := by
    intro a b haj
    rcases lt_trichotomy (b : ℕ) a with h | h | h
    · rw [pivotMinor_eq_zero g a b h, zero_div]
      exact A.zero_mem
    · have e : b = Fin.castLE (Nat.sub_le m 1) a := Fin.ext h
      subst e
      show GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g a / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g a ∈ A
      rw [div_self (hL a)]
      exact A.one_mem
    · exact hA a b haj h
  let U : Matrix (Fin (j + 1)) (Fin (j + 1)) K := Matrix.of fun r s =>
    pivotMinor g ⟨r, by have := r.2; have := j.2; omega⟩ (S.1.orderEmbOfFin S.2 s) /
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩
  have hP : (pivotMatrix g).submatrix (Fin.castLE hj) (S.1.orderEmbOfFin S.2) =
      Matrix.diagonal (fun r : Fin (j + 1) => GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) * U := by
    ext r s
    rw [Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, U]
    rw [dite_eq_left (by simp only [Fin.val_castLE]; have := r.2; have := j.2; omega)]
    rw [mul_div_cancel₀ _ (hL _)]
    rfl
  have hdet : flagMinor (pivotMatrix g) j S =
      (∏ r : Fin (j + 1), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) * U.det := by
    unfold flagMinor
    rw [hP, Matrix.det_mul, Matrix.det_diagonal]
  have hid := FlagPivotIdentity.proof K m g j S
  rw [prod_Iic_fin, hdet] at hid
  have hne : (∏ r : Fin (j + 1), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g ⟨r, by have := r.2; have := j.2; omega⟩) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => hL _
  have hU : flagMinor g j S / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor g j = U.det := by
    rw [div_eq_iff (hL j)]
    apply mul_right_cancel₀ hne
    linear_combination hid
  rw [hU, Matrix.det_apply]
  refine A.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (A.prod_mem fun r _ => hent _ _ (by have := r.2; simp only; omega)) _

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

abbrev PivPos (j : K → FlBlock Ψ N) : Type := Σ k : K, {b : Fin N // ((j k).2 : ℕ) < b}

def pivPosIncl (j : K → FlBlock Ψ N) (x : PivPos j) : PivotIdx Ψ N := ((j x.1).1, ⟨(j x.1).2, x.2⟩)

theorem pivPosIncl_injective {j : K → FlBlock Ψ N} (hj : Function.Injective j) :
    Function.Injective (pivPosIncl j) := by
  rintro ⟨k, b, hb⟩ ⟨k', b', hb'⟩ h
  simp only [pivPosIncl, Prod.mk.injEq, Sigma.mk.inj_iff] at h
  obtain ⟨h0, h1, h2⟩ := h
  have hk : k = k' := hj (Prod.ext h0 h1)
  subst hk
  simp only [heq_eq_eq, Subtype.mk.injEq] at h2
  subst h2
  rfl

theorem card_pivPos [Fintype K] (j : K → FlBlock Ψ N) : Fintype.card (PivPos j) = cellDim j := by
  rw [Fintype.card_sigma, cellDim]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun b : Fin N => ((j k).2 : ℕ) < b) =
      Finset.Ioi (Fin.castLE (Nat.sub_le N 1) (j k).2) := by
    ext b
    simp [Fin.lt_def]
  rw [this, Fin.card_Ioi]
  simp

theorem pivotRatio_algebraicIndependent_of_eq (Ψ : Type) (N : ℕ) (I : Algebra ℚ (ΩFl Ψ N))
    (hI : I = OreLocalization.instAlgebra) :
    @AlgebraicIndependent _ ℚ (ΩFl Ψ N) (pivotRatio ℚ Ψ N) _ _ I := by
  subst hI
  exact pivotRatio_algebraicIndependent ℚ Ψ N

theorem pivotRatio_rat_algebraicIndependent (Ψ : Type) (N : ℕ) :
    AlgebraicIndependent ℚ (pivotRatio ℚ Ψ N : PivotIdx Ψ N → ΩFl Ψ N) :=
  pivotRatio_algebraicIndependent_of_eq Ψ N _ (Subsingleton.elim _ _)

theorem isArithVar_pPart (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [Nonempty K]
    (j : K → FlBlock Ψ N) (hj : IsChain j) : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (PPart j) (cellDim j + 1) := by
  classical
  let e : PivPos j ≃ Fin (cellDim j) := Fintype.equivFinOfCardEq (card_pivPos j)
  let t : Fin (cellDim j) → ΩFl Ψ N := fun i => pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i))
  let c : ∀ k, PIdx j k := fun k => leadIdx Ψ N (j k)
  have hL : ∀ (τ : Ψ) (a : Fin (N - 1)), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr ℚ Ψ N τ) a ≠ 0 := fun τ a =>
    GenLeadMinorNeZero.full ℚ Ψ N τ a
  have hc : ∀ k, yPart j ⟨k, c k⟩ ≠ 0 := fun k => by
    show yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ≠ 0
    rw [yFl_lead]
    exact hL _ _
  have hind : AlgebraicIndependent ℚ t := by
    exact (pivotRatio_rat_algebraicIndependent Ψ N).comp _
      ((pivPosIncl_injective hj.inj).comp e.symm.injective)
  have hmem : ∀ i, t i ∈ IntermediateField.adjoin ℚ (coneRatios (yPart j) c) := by
    intro i
    refine IntermediateField.subset_adjoin ℚ _ ?_
    show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm i)) ∈ coneRatios (yPart j) c
    obtain ⟨k, b, hb⟩ := e.symm i
    let S : PluckerBlocks N N (j k).2 := ⟨Finset.univ.image (pivotCols (j k).2 b), card_image_pivotCols _ b hb.le⟩
    refine ⟨⟨k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩, ?_⟩
    have h1 := flagMinor_eq_yFl Ψ N (j k).1 (j k).2 S
    have h2 := pivotMinor_eq_flagMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b hb.le
    have h3 := yFl_lead Ψ N (j k)
    show yFl Ψ N ⟨j k, ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ /
      yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ = pivotMinor (genMatFr ℚ Ψ N (j k).1) (j k).2 b /
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr ℚ Ψ N (j k).1) (j k).2
    rw [h3]
    congr 1
    exact h1.symm.trans h2.symm
  have halg : ∀ r ∈ coneRatios (yPart j) c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r := by
    rintro _ ⟨⟨k, A⟩, rfl⟩
    have hT : ∀ (k' : K) (b : Fin N) (h : ((j k').2 : ℕ) < b),
        pivotMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 b / GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.leadMinor (genMatFr ℚ Ψ N (j k').1) (j k').2 ∈
          IntermediateField.adjoin ℚ (Set.range t) := fun k' b h =>
      IntermediateField.subset_adjoin ℚ _ ⟨e ⟨k', b, h⟩, by
        show pivotRatio ℚ Ψ N (pivPosIncl j (e.symm (e ⟨k', b, h⟩))) = _
        rw [e.symm_apply_apply]
        rfl⟩
    have hm : yPart j ⟨k, A⟩ / yPart j ⟨k, c k⟩ ∈ IntermediateField.adjoin ℚ (Set.range t) := by
      show yFl Ψ N ⟨j k, A⟩ / yFl Ψ N ⟨j k, leadIdx Ψ N (j k)⟩ ∈ _
      rw [yFl_lead, yFl_eq_flagMinor]
      refine flag_mem_of_le ℚ (genMatFr ℚ Ψ N (j k).1) _ (hL _) (j k).2 (fun a b ha hb => ?_) _
      obtain ⟨k', hk'⟩ := hj.down k ((j k).1, a) rfl ha
      have h := hT k' b (by rw [hk']; exact hb)
      rw [hk'] at h
      exact h
    exact isAlgebraic_algebraMap (⟨_, hm⟩ : IntermediateField.adjoin ℚ (Set.range t))
  exact CoordConeArithVar.full K (PIdx j) (ΩFl Ψ N) (yPart j) c (cellDim j) t ‹_› hc hind hmem halg

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainArithVarietyStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_chain_arith_variety : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (K : Type) [Fintype K] [Nonempty K] (j : K → FlBlock Ψ N), IsChain j → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (PPart j) (cellDim j + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.isArithVar_pPart <;> assumption)
end
end
