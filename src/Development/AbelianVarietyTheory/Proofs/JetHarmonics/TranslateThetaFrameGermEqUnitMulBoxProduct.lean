module

public import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivPointsOfIsPowGrp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyPowerDegree
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralBox

open GlobalTheory.BoxIndep GlobalTheory.FieldBaseChange

theorem span_of_indep_residue {V M M' : Type} [CommRing V] [IsLocalRing V] [AddCommGroup M] [Module V M]
    [AddCommGroup M'] [Module (ResidueField V) M'] (π : M →ₛₗ[residue V] M') {I : Type} [Fintype I]
    (b t : I → M) (hb : ∀ s, ∃ c : I → V, s = ∑ i, c i • b i)
    (ht : ∀ c : I → ResidueField V, ∑ a, c a • π (t a) = 0 → c = 0) (s : M) :
    ∃ c : I → V, s = ∑ a, c a • t a := by
  classical
  choose w hw using fun a => hb (t a)
  let A : Matrix I I V := Matrix.of w
  have hA : IsUnit A.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det]
    intro h
    obtain ⟨c, hc, hc'⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    refine hc (ht c ?_)
    have e : ∀ i, ∑ a, c a * residue V (w a i) = 0 := fun i => congrFun hc' i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, map_sum, map_smulₛₗ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ => by rw [← Finset.sum_smul, e, zero_smul]
  obtain ⟨d, rfl⟩ := hb s
  refine ⟨Matrix.vecMul d A⁻¹, ?_⟩
  have e : ∀ i, ∑ a, Matrix.vecMul d A⁻¹ a * w a i = d i := fun i =>
    congrFun (show Matrix.vecMul (Matrix.vecMul d A⁻¹) A = d by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]) i
  simp only [hw, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_smul, e]

theorem exists_tensor_pow (F O : Type) [Field F] [CommRing O] [Algebra F O] {m : ℕ} (j : ℕ)
    (β : Fin j → Fin m → O) (hβ : ∀ i, LinearIndependent F (β i)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra F B) (em : Fin j → (O →ₐ[F] B)),
      LinearIndependent F (fun a : Fin j → Fin m => ∏ i, em i (β i (a i))) := by
  induction j with
  | zero =>
    refine ⟨F, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    rw [linearIndependent_unique_iff]
    simp
  | succ j ih =>
    obtain ⟨B, _, _, em, h⟩ := ih (fun i => β i.succ) (fun i => hβ _)
    refine ⟨TensorProduct F O B, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (em i)), ?_⟩
    have h2 := ((hβ 0).tmul_of_isDomain h).comp (Fin.consEquiv (fun _ : Fin (j+1) => Fin m)).symm
      (Equiv.injective _)
    refine (congrArg (fun v : (Fin (j + 1) → Fin m) → TensorProduct F O B => LinearIndependent F v)
      (funext fun a => ?_)).mpr h2
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, AlgHom.comp_apply, Function.comp_apply]
    rw [← map_prod, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rfl

variable {X Y Z : Scheme.{0}}

theorem exists_test {F : Type} [Field F] (p : X ⟶ Spec (CommRingCat.of F)) (x : X) {j : ℕ} {U : Fin j → X.Opens}
    (hx : ∀ i, x ∈ U i) {m : ℕ} (s : ∀ i, Fin m → Γ(X, U i))
    (hs : ∀ i (c : Fin m → F), ∑ l, germOf p x (c l) * gs (𝟙 X) x (U i) (s i l) = 0 → c = 0) :
    ∃ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Fin j → (Z ⟶ X)), (∀ i, r i ≫ p = q) ∧
      (∀ i z, r i z ∈ U i) ∧ ∀ c : (Fin j → Fin m) → F,
        (∀ z, ∑ a, germOf q z (c a) * ∏ i, gs (r i) z (U i) (s i (a i)) = 0) → c = 0 := by
  let : Algebra F (X.presheaf.stalk x) := (germOf p x).toAlgebra
  have hβ : ∀ i, LinearIndependent F (fun l => gs (𝟙 X) x (U i) (s i l)) := fun i =>
    Fintype.linearIndependent_iff.2 fun c hc => congrFun (hs i c (by simp only [Algebra.smul_def] at hc; exact hc))
  obtain ⟨B, _, _, em, h⟩ := exists_tensor_pow F _ j _ hβ
  refine ⟨Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap F B)),
    fun i => (Spec.map (CommRingCat.ofHom (em i).toRingHom) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x,
    fun i => ?_, fun i z => fromSpecStalk_mem x (hx i) _, fun c hc => ?_⟩
  · rw [Category.assoc, fromSpecStalk_comp]
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact (em i).commutes a
  · funext a
    refine Fintype.linearIndependent_iff.1 h c (eq_zero_of_germOf (B := CommRingCat.of B) _ fun z => ?_) a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc z, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    congr 1
    · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [gs_fromSpecStalk x (hx i)]
      exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom (em i).toRingHom) z _).symm

theorem eq_zero_of_generic [IsIntegral Y] {R : Type} [CommRing R] (π : Y ⟶ Spec (CommRingCat.of R)) {L : LB X}
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : SecOver π (LB.LinComb L φ ε)) {J}
    (hJ : Good L (genericPoint Y) J) (h : sval s (𝟙 Y) (genericPoint Y) J = 0) : s = 0 := by
  refine SecOps.sec_ext fun jj => fn_ext fun y hy => congrArg _ ?_
  have hy' : genericPoint Y ∈ LB.wchart L φ jj :=
    ((genericPoint_spec _).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr ⟨y, trivial, hy⟩
  apply germ_injective_of_isIntegral _ _ hy'
  refine (gs_eq (𝟙 _) _ _ hy' _).symm.trans (Eq.trans ?_ (map_zero _).symm)
  exact (sec_trans s (𝟙 _) _ hy' (hJ.mem φ _)).trans ((congrArg _ h).trans (mul_zero _))

theorem sval_comb {R : Type} [CommRing R] (π : Y ⟶ Spec (CommRingCat.of R)) {L : LB X}
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {I : Type} [Fintype I] (c : I → R)
    (s : I → SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) :
    sval (∑ i, c i • s i : SecOver π _) r z J =
      ∑ i, germOf (B := CommRingCat.of R) (r ≫ π) z (c i) * sval (s i) r z J := by
  rw [sval_sum' hJ]
  exact Finset.sum_congr rfl fun i _ => by rw [sval_smul' hJ, germOf_apply]; rfl

section Box

variable {V : Type} [CommRing V] [IsDomain V] {R : Type} [CommRing R] (φ : V →+* R) (D : DegPre V)

theorem isPullback_snd : IsPullback (snd (Over.mk (spMap φ)) D.P.A).left (fst (Over.mk (spMap φ)) D.P.A).left
    D.P.A.hom (spMap φ) := (IsPullback.of_hasPullback (spMap φ) D.P.A.hom).flip

abbrev SecMod (k : ℕ) (α : D.X) : Type := SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k))

abbrev SecModBC (k : ℕ) (α : D.X) : Type :=
  SecOver (R := R) (fst (Over.mk (spMap φ)) D.P.A).left
    (LB.LinComb D.P.L (fun a => (snd (Over.mk (spMap φ)) D.P.A).left ≫ D.famφB α a) (DegPre.famε k))

noncomputable def pullBC (k : ℕ) (α : D.X) : SecMod D k α →ₛₗ[φ] SecModBC φ D k α :=
  pullOver D.P.L (DegPre.famε k) (isPullback_snd φ D).w (fun _ => rfl)

theorem sval_pullBC {k : ℕ} {α : D.X} (s : SecMod D k α) (r : Z ⟶ (Over.mk (spMap φ) ⊗ D.P.A).left) {z : Z} {J}
    (hJ : Good D.P.L z J) :
    sval (pullBC φ D k α s) r z J = sval s (r ≫ (snd (Over.mk (spMap φ)) D.P.A).left) z J :=
  sval_pullOver (isPullback_snd φ D).w (fun _ => rfl) s r hJ

theorem exists_basis [IsLocalRing V] [IsNoetherianRing V] (hT : TwistBaseChangeStatement) {k : ℕ} (hk : 1 ≤ k)
    (α : D.X) : ∃ b : Fin (k ^ D.P.g) → SecMod D k α, (∀ s, ∃ c : Fin (k ^ D.P.g) → V, s = ∑ i, c i • b i) ∧
      ∀ c : Fin (k ^ D.P.g) → R, ∑ i, c i • pullBC φ D k α (b i) = 0 → c = 0 := by
  have hL := D.P.isLB
  obtain ⟨m, b, rfl, hb⟩ := hT V D k hk α
  have H₀ : IsPullback (𝟙 D.P.A.left) D.P.A.hom D.P.A.hom (spMap (RingHom.id V)) := by
    have : spMap (RingHom.id V) = 𝟙 _ := by simp [spMap]
    rw [this]
    exact IsPullback.id_horiz _
  have hψ₀ : ∀ k, D.famφB α k = 𝟙 _ ≫ D.famφB α k := fun k => (Category.id_comp _).symm
  have h0 := ZH.BasisBaseChange.basis_of_isPullback (RingHom.id V) hL (D.famφB α) (DegPre.famε k) b
    (hb V (RingHom.id V) _ fun _ _ => rfl) H₀ hψ₀
  have e0 : ∀ i, pullOver D.P.L (DegPre.famε k) H₀.w hψ₀ (b i) = b i := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H₀.w hψ₀ _ _ hJ).trans (by rw [Category.comp_id])
  simp only [e0] at h0
  have h1 := ZH.BasisBaseChange.basis_of_isPullback φ hL (D.famφB α) (DegPre.famε k) b
    (hb R φ _ fun _ _ => rfl) (isPullback_snd φ D) (fun _ => rfl) (0 : SecModBC φ D k α)
  exact ⟨b, fun s => (h0 s).exists, fun c hc => h1.unique hc.symm
    (Finset.sum_eq_zero fun i _ => zero_smul R _).symm⟩

end Box

theorem box_indep {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] (φ : V →+* F) {j : ℕ}
    {D D' : DegPre V} (pD : IsPowDeg D' D j) {k m : ℕ} (b : ∀ α, Fin m → SecMod D k α)
    (hb : ∀ α (c : Fin m → F), ∑ i, c i • pullBC φ D k α (b α i) = 0 → c = 0) (α' : D'.X)
    (c : (Fin j → Fin m) → F)
    (hc : ∑ a, c a • pullBC φ D' k α' (boxFamB pD k (fun i α => b α (a i)) α') = 0) : c = 0 := by
  let T₀ : Over (Spec (CommRingCat.of V)) := Over.mk (spMap φ)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have hg := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.P.A.hom
  have hint : IsIntegral (T₀ ⊗ D.P.A).left := hg.geometrically_isIntegral _ _ _ (isPullback_snd φ D)
  choose J₀ hJ₀ using fun χ : (T₀ ⊗ D.P.A).left ⟶ D.P.A.left =>
    exists_chart D.P.isLB (χ (genericPoint (T₀ ⊗ D.P.A).left))
  have hJ₀ : Good D.P.L _ J₀ := hJ₀
  obtain ⟨Z, q, r, hq, hr, H⟩ := exists_test (F := F) (fst T₀ D.P.A).left _
    (fun i => hJ₀.mem (fun a => (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a) (𝟙 _))
    (fun i l => (pullBC φ D k (pD.xe α' i) (b _ l)).f _)
    (fun i c hc => hb _ c (eq_zero_of_generic _ _ hJ₀ ((sval_comb _ c _ (𝟙 _) hJ₀).trans (by
      rw [Category.id_comp]; exact hc))))
  let T : Over (Spec (CommRingCat.of V)) := Over.mk (q ≫ T₀.hom)
  let q' : T ⟶ T₀ := Over.homMk q rfl
  let r' : Fin j → (T ⟶ T₀ ⊗ D.P.A) := fun i => Over.homMk (r i) (by
    rw [← Over.w (fst T₀ D.P.A), ← Category.assoc, hq]; rfl)
  let ρ : T ⟶ T₀ ⊗ D'.P.A := lift q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _)
  have hρ : ∀ i, (ρ ≫ snd _ _) ≫ pD.pw.pr i = r' i ≫ snd _ _ := fun i => by
    rw [lift_snd]
    exact Fan.IsLimit.fac pD.pw.lim _ i
  have hρ' : ∀ i, ((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ (pD.pw.pr i).left =
      r i ≫ (snd T₀ D.P.A).left := fun i => congrArg (fun g => g.left) (hρ i)
  have hρq : (ρ.left : Z ⟶ _) ≫ (fst T₀ D'.P.A).left = q :=
    congrArg (fun g => g.left) (lift_fst q' (Fan.IsLimit.lift pD.pw.lim fun i => r' i ≫ snd _ _))
  refine H c fun z => ?_
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  choose J' hJ' using fun ψ : Z ⟶ D'.P.A.left => exists_chart D'.P.isLB (ψ z)
  have hJ' : Good D'.P.L z J' := hJ'
  have E := (sval_comb _ c _ (ρ.left : Z ⟶ _) hJ').symm.trans
    ((congrArg (fun s : SecModBC φ D' k α' => sval (Z := Z) s ρ.left z J') hc).trans (sval_zero' hJ' _))
  rw [hρq] at E
  obtain ⟨u, hu⟩ : ∃ u : Z.presheaf.stalk z, ∀ a : Fin j → Fin m,
      u * sval (Z := Z) (pullBC φ D' k α' (boxFamB pD k (fun i α => b α (a i)) α')) ρ.left z J' =
      ∏ i, sval (pullBC φ D k (pD.xe α' i) (b _ (a i))) (r i) z J := by
    refine ⟨(∏ a, bw pD.w (((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ D'.famφB α' a) z
      (fun i => J ((((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ D'.famφB α' a) ≫ (pD.pw.pr i).left))
      (J' (((ρ.left : Z ⟶ _) ≫ (snd T₀ D'.P.A).left) ≫ D'.famφB α' a)) ^ DegPre.famε k a).val, fun a => ?_⟩
    obtain ⟨hψ, H'⟩ := isBoxFamB_boxFamB pD k (fun i α => b α (a i)) α'
    refine (congrArg _ (sval_pullBC φ D' _ _ hJ')).trans ((BoxFamScalar.box_sval pD.w hψ _ _ _ H' _ z hJ hJ').trans
      (Finset.prod_congr rfl fun i _ => ?_))
    rw [sval_pullBC φ D _ _ hJ]
    exact congrArg (fun g => sval (b _ (a i)) g z J) (hρ' i)
  obtain ⟨v, hv⟩ : ∃ v : Fin j → Z.presheaf.stalk z, ∀ i l,
      gs (r i) z (LB.wchart D.P.L (fun a => (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a)
          (fun a => J₀ (𝟙 _ ≫ (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a)))
        ((pullBC φ D k (pD.xe α' i) (b _ l)).f
          (fun a => J₀ (𝟙 _ ≫ (snd T₀ D.P.A).left ≫ D.famφB (pD.xe α' i) a))) =
      v i * sval (pullBC φ D k (pD.xe α' i) (b _ l)) (r i) z J :=
    ⟨_, fun i l => sec_trans _ (r i) z (hr i z) (hJ.mem _ (r i))⟩
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) ((Finset.mul_sum _ _ ((∏ i, v i) * u)).symm.trans
    ((congrArg _ E).trans (mul_zero _)))
  refine Eq.trans (congrArg _ (((Finset.prod_congr rfl fun i _ => hv i (a i)).trans Finset.prod_mul_distrib).trans
    (congrArg _ (hu a).symm))) ?_
  exact (congrArg _ (_root_.mul_assoc _ _ _).symm).trans (mul_left_comm _ _ _)

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegPre V) (pD : IsPowDeg D' D j) (k : ℕ), 1 ≤ k → ∀ (α' : D'.X) (β' : D'.SecB k α'), ∃ (l : ℕ) (c : Fin l → V) (f : Fin l → Fin j → ∀ α : D.X, D.SecB k α) (f' : Fin l → ∀ α : D'.X, D'.SecB k α), (∀ a, IsBoxFamB pD k (f' a) (f a)) ∧ ∀ jj, β'.f jj = ∑ a, constFn D'.P.A.hom _ (c a) * (f' a α').f jj := by
  intro _ _ _ hT V _ _ _ _ j D D' pD k hk α' β'
  choose b _ hb using exists_basis (residue V) D hT hk
  obtain ⟨b', hb', -⟩ := exists_basis (residue V) D' hT hk α'
  have hg := (rank_and_g_of_isPowDeg V j D D' pD).2
  let e : Fin (k ^ D'.P.g) ≃ (Fin j → Fin (k ^ D.P.g)) := Fintype.equivOfCardEq (by
    simp [hg, ← pow_mul, mul_comm])
  obtain ⟨c, hc⟩ := span_of_indep_residue (pullBC (residue V) D' k α') b'
    (fun n => boxFamB pD k (fun i α => b α (e n i)) α') hb' (fun c hc => by
      have := box_indep (residue V) pD b hb α' (fun a => c (e.symm a)) (by
        rw [← hc, ← e.sum_comp]
        simp only [Equiv.symm_apply_apply])
      funext n
      simpa using congrFun this (e n)) β'
  exact ⟨_, c, fun n i α => b α (e n i), fun n => boxFamB pD k (fun i α => b α (e n i)),
    fun n => isBoxFamB_boxFamB pD k _, (ZH.BasisBaseChange.isLin_iff D'.P.A.hom _ c β').2 hc⟩

end GlobalTheory.IntegralBox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FiniteOrderThetaOperatorsRatioRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FiniteOrderThetaOperatorsRatioRootOfUnity
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem exists_rootOfUnity_smul_of_pow_eq_one {F N : Type} [Field F] [AddCommGroup N] [Module F N]
    (Φ : Module.End F N) (ζ ξ : F) {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (h : (ζ • Φ) ^ M = 1) (h' : (ξ • Φ) ^ M' = 1) :
    ∃ u : F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ ξ • Φ = u • (ζ • Φ) := by
  rcases subsingleton_or_nontrivial (Module.End F N) with hs | hn
  · exact ⟨1, ⟨1, Nat.one_pos, one_pow _⟩, Subsingleton.elim _ _⟩
  have hζ : ζ ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_pow (by omega)] at h
    exact zero_ne_one h
  have e : ξ • Φ = (ξ / ζ) • (ζ • Φ) := by rw [smul_smul, div_mul_cancel₀ _ hζ]
  refine ⟨ξ / ζ, ⟨M * M', by positivity, ?_⟩, e⟩
  have a : (ξ • Φ) ^ (M * M') = 1 := by rw [mul_comm M M', pow_mul, h', one_pow]
  rw [e, smul_pow, pow_mul (ζ • Φ), h, one_pow] at a
  have b : ((ξ / ζ) ^ (M * M') - 1) • (1 : Module.End F N) = 0 := by rw [sub_smul, a, one_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 b).resolve_right one_ne_zero)

theorem finOrd_ratio_rootOfUnity : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ ζ' : F), w.IsGen → w'.IsGen → FinOrd D F k p w ζ → FinOrd D F k p w' ζ' → ∃ u : F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ ∀ s t₀ t t₀' t' : Fam D.toPre F k, PhiRel D.toPre F k p w s t₀ → Fam.IsSmul D.toPre F ζ t₀ t → PhiRel D.toPre F k p w' s t₀' → Fam.IsSmul D.toPre F ζ' t₀' t' → Fam.IsSmul D.toPre F u t t' := by
  intro V _ _ _ _ ϖ _ D F _ _ k hk p w w' ζ ζ' hw hw' h h'
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ D F k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG V _ D F k hk p w' hw'
  obtain ⟨c, hc⟩ := ThetaFinOrd.exists_scalar hG p w' w hw' hw Φ' Φ
    (fun s => (hΦ' _ _).2 rfl) (fun s => (hΦ _ _).2 rfl)
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p w ζ Φ hΦ).1 h
  obtain ⟨M', hM', hW⟩ := (ThetaFinOrd.finOrd_iff p w' ζ' Φ' hΦ').1 h'
  rw [hc, smul_smul] at hW
  obtain ⟨u, hu, e⟩ := exists_rootOfUnity_smul_of_pow_eq_one (F := F) (N := Fam D.toPre F k) Φ ζ (ζ' * c)
    hM hM' hU hW
  refine ⟨u, hu, fun s t₀ t t₀' t' a b a' b' => ?_⟩
  rw [hΦ] at a
  rw [hΦ'] at a'
  rw [DVR.isSmul_iff] at b b' ⊢
  have f := LinearMap.congr_fun e s
  simp only [LinearMap.smul_apply] at f
  rw [b', a', b, a, hc, LinearMap.smul_apply, smul_smul, f]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FiniteOrderThetaOperatorsRatioRootOfUnityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteOrder_thetaOperators_ratio_rootOfUnity : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ ζ' : F), w.IsGen → w'.IsGen → FinOrd D F k p w ζ → FinOrd D F k p w' ζ' → ∃ u : F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ ∀ s t₀ t t₀' t' : Fam D.toPre F k, PhiRel D.toPre F k p w s t₀ → Fam.IsSmul D.toPre F ζ t₀ t → PhiRel D.toPre F k p w' s t₀' → Fam.IsSmul D.toPre F ζ' t₀' t' → Fam.IsSmul D.toPre F u t t' := by
  first | exact @GlobalTheory.finOrd_ratio_rootOfUnity | exact GlobalTheory.finOrd_ratio_rootOfUnity | (intros; apply GlobalTheory.finOrd_ratio_rootOfUnity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameFamiliesDifferByValuationZeroUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameFamiliesDifferByValuationZeroUnit
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ThetaFrameLine

section
variable {V : Type} [CommRing V] [IsDomain V]

theorem cst_prB (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (y : (DegPre.BF D F).left) (a : V) :
    Geo.Tor.cst ((𝟙 _ ≫ (DegPre.prB D F).left) ≫ D.P.A.hom) y a =
      gs (𝟙 _) y ⊤ (gF D F (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a))) := by
  have hw : (DegPre.prB D F).left ≫ D.P.A.hom = (fst (TF (R := V) F) D.P.A).left ≫ jFK (R := V) F ≫ jK V :=
    (Over.w (DegPre.prB D F)).trans (Over.w (fst (TF (R := V) F) D.P.A)).symm
  have e : (jFK (R := V) F ≫ jK V).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a)) := by
    have h := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))))
    have h' := congrArg (fun f => f.hom a) h
    rw [jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact h'.symm
  rw [Category.assoc, hw, Geo.Tor.cst]
  refine (gs_pull (𝟙 _) _ y ⊤ trivial _).symm.trans (congrArg (gs (𝟙 _) y ⊤) ?_)
  exact congrArg (fst (TF (R := V) F) D.P.A).left.appTop.hom e

end

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ θ θ' : Fam D.toPre F 1, ThFrame D ϖ F θ → ThFrame D ϖ F θ' → ∃ u : F, v u = 0 ∧ Fam.IsSmul D.toPre F u θ θ' := by
  intro V _ _ _ _ ϖ hϖ D F _ _ v hv θ θ' h h'
  obtain ⟨σ, σF, hs, he, hn⟩ := h
  obtain ⟨τ, τF, ht, hf, hm⟩ := h'
  have hL := D.toPre.P.isLB
  have gσ := GlobalTheory.IndivisibleSection.secBGenerates_of_not_dvd GlobalTheory.firstFiveLaws.1.secBaseChange V ϖ hϖ D σ hn
  obtain ⟨a, ha, -⟩ := gσ τ
  have hu : IsUnit a := by
    by_contra hna
    have hmem : a ∈ maximalIdeal V := hna
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hmem
    obtain ⟨b, rfl⟩ := hmem
    refine hm ⟨SecOps.secScale (Out.scal D.toPre.P.A.hom b) σ, ?_⟩
    show SecIsMul D.toPre.P.A.hom ϖ τ (SecOps.secScale (Out.scal D.toPre.P.A.hom b) σ)
    intro j
    refine (ha j).trans ?_
    simp only [SecOps.secScale, Out.scal, resTop, map_mul, _root_.mul_assoc]
  refine ⟨algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a), ?_, ?_⟩
  · have := hv (algebraMap V (FractionRing V) a) 0 ⟨hu.unit, by simp⟩
    simpa using this
  · set u := algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a) with hudef
    have eθ : θ.s 0 = σF := SecOps.sec_ext he
    have eθ' : θ'.s 0 = τF := SecOps.sec_ext hf
    have h0 : ∀ j, (θ'.s 0).f j = ((u • θ).s 0).f j := by
      refine sec_ext_val hL fun y J hJ => ?_
      have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hs (𝟙 _) y hJ
      have e₂ := GlobalTheory.PullIntegral.sval_of_secScal ht (𝟙 _) y hJ
      have e₃ := GlobalTheory.IndivisibleSection.sval_of_secIsMul ha (𝟙 _ ≫ (DegPre.prB D.toPre F).left) y hJ
      have o : gs (𝟙 (DegPre.BF D.toPre F).left) y ⊤ 1 = 1 := by
        rw [gs_eq _ y ⊤ trivial, map_one, map_one]
      rw [o, _root_.one_mul] at e₁ e₂
      rw [e₁, e₂, cst_prB, ← eθ, ← eθ'] at e₃
      refine e₃.trans ?_
      have hmem := hJ.mem (DegPre.famφ D.toPre F 0) (𝟙 _)
      exact ((gs_mul (𝟙 _) y _ hmem _ _).trans (congrArg₂ (· * ·) (gs_res (𝟙 _) y le_top hmem _) rfl)).symm
    refine (isSmul_iff u θ θ').2 (sub_eq_zero.1 (fam_ext fun α j => TG.fam_eq_zero hϖ (θ' - u • θ) (fun j => ?_) α j))
    exact (congrArg (· + -((u • θ).s 0).f j) (h0 j)).trans (add_neg_cancel _)

end GlobalTheory.ThetaFrameLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameFamiliesDifferByValuationZeroUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFrameFamilies_differ_by_valuationZero_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ θ θ' : Fam D.toPre F 1, ThFrame D ϖ F θ → ThFrame D ϖ F θ' → ∃ u : F, v u = 0 ∧ Fam.IsSmul D.toPre F u θ θ' := by
  first | exact @GlobalTheory.ThetaFrameLine.main | exact GlobalTheory.ThetaFrameLine.main | (intros; apply GlobalTheory.ThetaFrameLine.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DvdOfPullEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFamThrough
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitBallBox

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem box_secScal {S : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    {f' : ∀ α : D'.X, D'.SecB k α} {f : Fin j → ∀ α : D.X, D.SecB k α} (hf : IsBoxFamB pD k f' f) (α' : D'.X)
    (h : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F (pD.xe α' i)) (DegPre.famε k) ((s i).s (pD.xe α' i))
      (D.famφB (pD.xe α' i)) (DegPre.famε k) (f i (pD.xe α' i)) (DegPre.prB D F).left 1) :
    GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' F α') (DegPre.famε k) (S.s α')
      (D'.famφB α') (DegPre.famε k) (f' α') (DegPre.prB D' F).left 1 := by
  obtain ⟨hφ, H⟩ := hS α'
  obtain ⟨hψ, H'⟩ := hf α'
  have e₄ : ∀ i, (DegPre.prB D' F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D F).left := fun i => by
    rw [← Over.comp_left, ← Over.comp_left]; congr 1; exact (whiskerLeft_snd _ _).symm
  exact BoxFamScalar.secScal_box D.P.isLB D'.P.isLB pD.w (GC.famφ_eq D' F α') e₄
    (S.s α') (fun i => (s i).s (pD.xe α' i)) (f' α') (fun i => f i (pD.xe α' i))
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hφ (S.s α') (fun i => (s i).s (pD.xe α' i)) _ H (𝟙 _) y hJ hJ')
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hψ (f' α') (fun i => f i (pD.xe α' i)) _ H' _ y hJ hJ')
    (fun _ => 1) 1 (fun y => by simp only [NuBox.gs_one, Finset.prod_const_one]) h

end Fam


end GlobalTheory.UnitBallBox
end
end

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.BoxFrame

open GlobalTheory.IntegralBox

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem dvd_iff (D : DegPre V) {k : ℕ} {α : D.X} (a : V) (σ τ : SecMod D k α) :
    (∀ j, LB.Sec.f σ j = constFn D.P.A.hom _ a * LB.Sec.f τ j) ↔ σ = a • τ :=
  ⟨fun h => SecOps.sec_ext h, fun h j => congrArg (fun s : SecMod D k α => LB.Sec.f s j) h⟩

theorem dvd_of_pull_eq_zero (hT : TwistBaseChangeStatement) {ϖ : V} (hϖ : Irreducible ϖ) (D : DegPre V) {k : ℕ}
    (hk : 1 ≤ k) {α : D.X} (σ : SecMod D k α) (h : pullBC (residue V) D k α σ = 0) :
    ∃ τ : SecMod D k α, σ = ϖ • τ := by
  obtain ⟨b, hb, hb'⟩ := exists_basis (residue V) D hT hk α
  obtain ⟨c, rfl⟩ := hb σ
  have h0 := hb' (fun i => residue V (c i)) (by simpa only [map_sum, map_smulₛₗ] using h)
  have hd : ∀ i, ϖ ∣ c i := fun i => by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, ← residue_eq_zero_iff]
    exact congrFun h0 i
  choose d hd using hd
  exact ⟨∑ i, d i • b i, by simp only [hd, Finset.smul_sum, smul_smul]⟩

theorem exists_pull_ne_zero (hT : TwistBaseChangeStatement) (D : DegPre V) (α : D.X) :
    ∃ σ : SecMod D 1 α, pullBC (residue V) D 1 α σ ≠ 0 := by
  classical
  obtain ⟨b, -, hb'⟩ := exists_basis (residue V) D hT le_rfl α
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  refine ⟨b i₀, fun h => ?_⟩
  have h0 := hb' (Pi.single i₀ 1) (by
    rw [Finset.sum_eq_single i₀, h, smul_zero]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h)
  simpa using congrFun h0 i₀

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (n : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre n) (F : Type) [Field F] [Algebra (FractionRing V) F] (θ : Fam D.toPre F 1) (Θ : Fam D'.toPre F 1), ThFrame D ϖ F θ → IsBoxFam pD F 1 Θ (fun _ => θ) → ThFrame D' ϖ F Θ := by
  intro V _ _ _ _ ϖ hϖ n D D' pD F _ _ θ Θ ⟨σ, σF, hs, he, hn⟩ hB
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  have hex : ∀ α : D.toPre.X, ∃ s : SecMod D.toPre 1 α, pullBC (residue V) D.toPre 1 α s ≠ 0 ∧
      (α = 0 → GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε 1) (θ.s α)
        (D.toPre.famφB α) (DegPre.famε 1) s (DegPre.prB D.toPre F).left 1) := fun α => by
    by_cases hα : α = 0
    · subst hα
      refine ⟨σ, fun h => ?_, fun _ => ?_⟩
      · obtain ⟨τ, hτ⟩ := dvd_of_pull_eq_zero hT hϖ D.toPre le_rfl σ h
        exact hn ⟨τ, (dvd_iff D.toPre ϖ σ τ).2 hτ⟩
      · rw [show θ.s 0 = σF from SecOps.sec_ext he]
        exact hs
    · obtain ⟨s, hs⟩ := exists_pull_ne_zero hT D.toPre α
      exact ⟨s, hs, fun h => absurd h hα⟩
  choose f hf hf' using hex
  refine ⟨boxFamB pD 1 (fun _ α => f α) 0, Θ.s 0,
    UnitBallBox.box_secScal pD hB (isBoxFamB_boxFamB pD 1 _) 0
      (fun i => hf' _ (by rw [map_zero]; rfl)), fun _ => rfl, ?_⟩
  rintro ⟨τ, hτ⟩
  have h1 := (dvd_iff D'.toPre ϖ _ τ).1 hτ
  have h2 : residue V ϖ = 0 := (residue_eq_zero_iff _).2 (by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
  have h3 : pullBC (residue V) D'.toPre 1 0 (boxFamB pD 1 (fun _ α => f α) 0) = 0 := by
    exact (congrArg _ h1).trans ((map_smulₛₗ (pullBC (residue V) D'.toPre 1 0) ϖ τ).trans (by rw [h2, zero_smul]))
  have h4 := box_indep (residue V) pD (m := 1) (fun α _ => f α) (fun α c hc => by
    rw [Fin.sum_univ_one, smul_eq_zero] at hc
    funext i
    rw [Subsingleton.elim i 0]
    exact hc.resolve_right (hf α)) 0 (fun _ => 1) (Finset.sum_eq_zero fun a _ => (congrArg _ h3).trans (smul_zero _))
  exact one_ne_zero (congrFun h4 fun _ => 0)

end GlobalTheory.BoxFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsBoxQkToA
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnboxQk

open GlobalTheory.BoxFamily GlobalTheory.BoxQk GlobalTheory.TorusExt

section Deg

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R} (pD : IsPowDeg D' D j)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

def intersection_update_fsHerm_neg_one (i : Fin j) (χ : D.X) : D'.X := pD.xe.symm (Pi.single i χ)

theorem xe_position (i : Fin j) (χ : D.X) : pD.xe (intersection_update_fsHerm_neg_one pD i χ) = Pi.single i χ := pD.xe.apply_symm_apply _

theorem xe_position_self (i : Fin j) (χ : D.X) : pD.xe (intersection_update_fsHerm_neg_one pD i χ) i = χ := by
  rw [xe_position, Pi.single_eq_same]

theorem xe_position_ne {i i' : Fin j} (h : i' ≠ i) (χ : D.X) : pD.xe (intersection_update_fsHerm_neg_one pD i χ) i' = 0 := by
  rw [xe_position, Pi.single_eq_of_ne h]

theorem position_add (i : Fin j) (χ χ' : D.X) : intersection_update_fsHerm_neg_one pD i (χ + χ') = intersection_update_fsHerm_neg_one pD i χ + intersection_update_fsHerm_neg_one pD i χ' := by
  rw [intersection_update_fsHerm_neg_one, Pi.single_add, map_add (f := _)]; rfl

theorem position_zero (i : Fin j) : intersection_update_fsHerm_neg_one pD i 0 = 0 := by
  rw [intersection_update_fsHerm_neg_one, Pi.single_zero, map_zero]

theorem sum_position (x : D'.X) : ∑ i, intersection_update_fsHerm_neg_one pD i (pD.xe x i) = x := by
  apply pD.xe.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [xe_position]
  exact Finset.univ_sum_single _

theorem exists_gt_at {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) (b : TF (R := R) F ⟶ D.P.A)
    (f : D.X → ((TF (R := R) F).left.presheaf.stalk y)ˣ) (f₀ : f 0 = 1)
    (hf : ∀ χ χ', f (χ + χ') * th D y J (cP D _ χ) (cP D _ χ') b = f χ * f χ') :
    ∃ g : GtPtF D F, g.b = b ∧ ∀ χ, charVal g χ y J = f χ := by
  choose v hv vv using fun χ => Geo.Tor.exists_gen_val (F := F) D.P.isLB (DegPre.gtφ D F b χ) DegPre.gtε hJ (f χ)
  refine (exists_gt b v hv (fun _ _ _ _ => rfl) (fun y' J' hJ' => ?_) (fun χ χ' y' J' hJ' => ?_)).imp
    fun _ h => ⟨h.1, fun χ => (h.2 χ y J hJ).trans (vv χ)⟩
  · obtain rfl := pt_eq y y'
    refine (val_eq_of_val_eq (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => ?_) (hv 0) oneGen_isGen hJ hJ'
      ((vv 0).trans (f₀.trans (val_one _).symm))).trans (val_one _)
    rw [prod_gt, cPoint_zero, _root_.one_mul]; simp
  · obtain rfl := pt_eq y y'
    refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ' _ _ _))).symm.trans
      (Eq.trans (val_eq_of_val_eq (fun U _ h => ?_) (mulGen_isGen _ _ _ _ _ _ _ (hv _) (cubAt_isGen _ _ _))
        (mulGen_isGen _ _ _ _ _ _ _ (hv χ) (hv χ')) hJ hJ'
        (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vv _) (val_cubAt hJ _ _ _))).trans ((hf χ χ').trans
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vv _) (vv _))).symm))) (val_mul hJ' _ _ _))
    refine (prod_sum₂ (K := Fin 4) (K' := thK) (U := U) _ (prod_gt b (χ + χ') h)
      (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gt b χ h) (prod_gt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

section Values

variable {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}
  {J' : ((TF (R := R) F).left ⟶ D'.P.A.left) → D'.P.L.ι} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
include hJ

theorem prod_th_factor (i : Fin j) (χ : D.X) (x w : TF (R := R) F ⟶ D'.P.A) :
    ∏ i', th D y J (cP D' _ (intersection_update_fsHerm_neg_one pD i χ) ≫ pD.pw.pr i') (x ≫ pD.pw.pr i') (w ≫ pD.pw.pr i') =
      th D y J (cP D _ χ) (x ≫ pD.pw.pr i) (w ≫ pD.pw.pr i) := by
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [Finset.prod_eq_single i (fun i' _ h => by rw [cPoint_pr, xe_position_ne pD h, cPoint_zero, C.face]) (by simp),
    cPoint_pr, xe_position_self]

include hJ'

theorem position_val {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g) (i : Fin j) (χ : D.X) :
    omL pD y J J' (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) g'.b * charVal g' (intersection_update_fsHerm_neg_one pD i χ) y J' = charVal (g i) χ y J := by
  have e₂ : ∏ i', charVal (g i') (pD.xe (intersection_update_fsHerm_neg_one pD i χ) i') y J = charVal (g i) χ y J := by
    rw [Finset.prod_eq_single i (fun i' _ h => by rw [xe_position_ne pD h, charVal_zero _ hJ]) (by simp), xe_position_self]
  exact (box_val pD hJ hJ' h (intersection_update_fsHerm_neg_one pD i χ)).trans e₂

theorem tau_position (hB : D.TauBimult) (i : Fin j) (χ : D.X) (z : D'.X) :
    omL pD y J J' (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) (cP D' _ z) * tauVal D' F z (intersection_update_fsHerm_neg_one pD i χ) y J' =
      tauVal D F (pD.xe z i) χ y J := by
  have e₂ : ∏ i', tauVal D F (pD.xe z i') (pD.xe (intersection_update_fsHerm_neg_one pD i χ) i') y J = tauVal D F (pD.xe z i) χ y J := by
    rw [Finset.prod_eq_single i (fun i' _ h => ?_) (by simp), xe_position_self]
    have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 (pD.xe z i')
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    rw [xe_position_ne pD h]
    exact (tau_symm (𝟙 (TF (R := R) F)) hJ _ _).trans (mul_eq_left.1 t.symm)
  exact (tau_box pD hJ hJ' z (intersection_update_fsHerm_neg_one pD i χ)).trans e₂

theorem exists_comp (hG : GlobalFnsSt) (g' : GtPtF D' F) (i : Fin j) :
    ∃ g : GtPtF D F, g.b = g'.b ≫ pD.pw.pr i ∧ ∀ χ, charVal g χ y J =
      omL pD y J J' (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) g'.b * charVal g' (intersection_update_fsHerm_neg_one pD i χ) y J' := by
  refine exists_gt_at hJ _ _ ?_ fun χ χ' => ?_
  · rw [position_zero, cPoint_zero, omL_one', charVal_zero g' hJ', _root_.one_mul]
  · have e := th_box pD hJ hJ' hG (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) (cP D' _ (intersection_update_fsHerm_neg_one pD i χ')) g'.b
    rw [prod_th_factor pD hJ, cPoint_pr, xe_position_self, ← cPoint_add, ← position_add] at e
    have e₂ := charVal_add g' hJ' (intersection_update_fsHerm_neg_one pD i χ) (intersection_update_fsHerm_neg_one pD i χ')
    rw [← position_add] at e₂
    have a₁ := congrArg Additive.ofMul e
    have a₂ := congrArg Additive.ofMul e₂
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₂ - a₁

end Values

theorem exists_unboxGt (hG : GlobalFnsSt) (g' : GtPtF D' F) : ∃ g : Fin j → GtPtF D F, IsBoxGtF pD F g' g := by
  obtain ⟨y, J, hJ⟩ := exists_good_chart D F
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  choose g hb hv using exists_comp pD hJ hJ' hG g'
  obtain ⟨g'', h⟩ := exists_boxGt pD hG g
  have eb : g''.b = g'.b := pt_ext pD fun i => (h.1 i).trans (hb i)
  have add : ∀ a b, charVal g'' a y J' = charVal g' a y J' → charVal g'' b y J' = charVal g' b y J' →
      charVal g'' (a + b) y J' = charVal g' (a + b) y J' := fun a b ha hb => by
    have e₁ := charVal_add g'' hJ' a b
    rw [eb, ha, hb, ← charVal_add g' hJ' a b] at e₁
    exact mul_right_cancel e₁
  have all : ∀ x, charVal g'' x y J' = charVal g' x y J' := fun x => by
    rw [← sum_position pD x]
    refine Finset.sum_induction _ (fun x => charVal g'' x y J' = charVal g' x y J') add
      ((charVal_zero g'' hJ').trans (charVal_zero g' hJ').symm) fun i _ => ?_
    have e := (position_val pD hJ hJ' h i (pD.xe x i)).trans (hv i _)
    rw [eb] at e
    exact mul_left_cancel e
  obtain rfl : g'' = g' := gt_ext_val_at eb hJ' all
  exact ⟨g, h⟩

theorem unbox_isZero {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g) (hz : g'.IsZero)
    (i : Fin j) : (g i).IsZero := by
  haveI := pD.pw.hom i
  obtain ⟨b, v⟩ := (isZero_iff_val _).1 hz
  refine (isZero_iff_val _).2 ⟨by rw [← h.1, b, MonObj.one_comp], fun χ y J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  rw [← position_val pD hJ hJ' h, v _ y J' hJ', b, omL_one, _root_.mul_one]

theorem unbox_isAdd (hG : GlobalFnsSt) {g₁' g₂' g₃' : GtPtF D' F} {g₁ g₂ g₃ : Fin j → GtPtF D F}
    (h₁ : IsBoxGtF pD F g₁' g₁) (h₂ : IsBoxGtF pD F g₂' g₂) (h₃ : IsBoxGtF pD F g₃' g₃)
    (ha : g₁'.IsAdd g₂' g₃') (i : Fin j) : (g₁ i).IsAdd (g₂ i) (g₃ i) := by
  haveI := pD.pw.hom i
  obtain ⟨b, v⟩ := (isAdd_iff_val _ _ _).1 ha
  refine (isAdd_iff_val _ _ _).2 ⟨by rw [← h₃.1, ← h₁.1, ← h₂.1, b, MonObj.mul_comp], fun χ y J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  have e := th_box' pD hJ hJ' hG (cP D' _ (intersection_update_fsHerm_neg_one pD i χ)) g₁'.b g₂'.b
  rw [prod_th_factor pD hJ, ← b, h₁.1, h₂.1] at e
  rw [← position_val pD hJ hJ' h₁, ← position_val pD hJ hJ' h₂, ← position_val pD hJ hJ' h₃]
  have a₁ := congrArg Additive.ofMul e
  have a₂ := congrArg Additive.ofMul (v (intersection_update_fsHerm_neg_one pD i χ) y J' hJ')
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₂ - a₁

theorem unbox_isIota (hB : D.TauBimult) {g' : GtPtF D' F} {g : Fin j → GtPtF D F} (h : IsBoxGtF pD F g' g)
    {x : D'.X} (hι : GtPtF.IsIota x g') (i : Fin j) : GtPtF.IsIota (pD.xe x i) (g i) := by
  obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 hι
  refine (isIota_iff_val _ _).2 ⟨by rw [← h.1, b, cPoint_pr], fun χ y J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_at D'.P.isLB y
  rw [← position_val pD hJ hJ' h, v _ y J' hJ', b]
  exact tau_position pD hJ hJ' hB i χ x

theorem exists_unbox (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (p' : QkPt D' F k) :
    ∃ p : Fin j → QkPt D F k, IsBoxQk pD F k p' p := by
  choose ub hub using fun g' : GtPtF D' F => exists_unboxGt pD hG g'
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p'.eq
  exact ⟨fun i => ⟨pD.xe p'.y i, ub p'.g i, ub h i,
    ⟨fun n => ub (gs n) i, unbox_isZero pD (hub _) g₀ i,
      fun n => unbox_isAdd pD hG (hub _) (hub _) (hub _) (gst n) i, congrArg (fun g => ub g i) gl⟩,
    unbox_isIota pD hB (hub _) hι i⟩, rfl, hub _⟩

end Deg


open FieldBaseChange TorsionImage in
theorem image_unique (hL : Laws) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Unif I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ) (hn : 1 ≤ n)
    (p : QkPt D.toPre F n) (x x' : TFK (R := R) F ⟶ A.A) (hx : QkToAkU U.toUnifPre F n p x)
    (hx' : QkToAkU U.toUnifPre F n p x') : x = x' := by
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨θ, rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x (hx w₀ hw₀).1
  obtain ⟨θ', rfl, -⟩ := TorsionTheta.exists_theta_acts hL.kerPow _ A F _ n hn x' (hx' w₀ hw₀).1
  obtain ⟨w, hw, h⟩ := (hx w₀ hw₀).2 θ rfl
  obtain ⟨w', hw', h'⟩ := (hx' w₀ hw₀).2 θ' rfl
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hL.globalFns U F hn w₀ hw₀
  obtain ⟨c, hc, hcs⟩ := exists_smul_of_phiVal p w w' hw hw'
  refine pt_eq_of_proportional hL.secBaseChange A _ hn θ θ'
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))
    fun t u u' hu hu' y J hJ => ?_
  have a := hcs _ _ _
    ((DVR.phiRel_iff hL.globalFns p w hw _ _).1 (h t u _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu))
    ((DVR.phiRel_iff hL.globalFns p w' hw' _ _).1 (h' t u' _ _ ((he _ _).2 rfl) ((he _ _).2 rfl) hu'))
  obtain rfl := e.injective (a.trans (e.map_smul c u).symm)
  exact (sval_smul' hJ _ c _).trans (congrArg (· * _) (gs_unit _ y ⊤ trivial
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc))))

theorem exists_isBoxQk_toA : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → ∀ (j : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre j) (pA : IsPowPolAV A' P.A j) (pG : IsPowGrp G' t.G j) (U' : Unif (maximalIdeal V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (k : ℕ), 1 ≤ k → ∀ p' : QkPt D'.toPre F k, ∃ p : Fin j → QkPt P.D.toPre F k, IsBoxQk pD F k p' p ∧ ∀ x' : TFK (R := V) F ⟶ A'.A, QkToAkU U'.toUnifPre F k p' x' → ∀ i, P.ToA F k (p i) (x' ≫ pA.pr i) := by
  intro hL _ _ _ V _ _ _ _ _ E _ _ _ H t P hT j D' A' G' _ _ pD pA pG U' PU F _ _ _ k hk p'
  obtain ⟨p, hp⟩ := exists_unbox pD hL.globalFns P.D.tau_bimult p'
  refine ⟨p, hp, fun x' hx' i => ?_⟩
  obtain ⟨f, hf, -⟩ := hT F k hk
  let x'' : TFK (R := V) F ⟶ A'.A := pA.lim.lift (Fan.mk _ fun i => f (p i))
  have hx : ∀ i, x'' ≫ pA.pr i = f (p i) := fun i => pA.lim.fac (Fan.mk _ fun i => f (p i)) ⟨i⟩
  have h := ProdTorsion.qkToAk_box hL V _ j P.D D' P.A A' t.G G' pD pA pG U' P.U PU
    (expansion_bijective_over_fields hL.globalFns V _ _ _ _ P.U)
    (expansion_bijective_over_fields hL.globalFns V _ _ _ _ U') F k hk p' p hp x'' (fun i => f (p i)) hx
    (fun i => (hf _ _).2 rfl)
  rw [image_unique hL U' F k hk p' x' x'' hx' h, hx]
  exact (hf _ _).2 rfl

end GlobalTheory.UnboxQk
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ColumnSplit

theorem val_eq_zero_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {u : F} {m : ℕ} (hm : 0 < m)
    (h : u ^ m = 1) : v u = 0 := by
  have h1 : m • v u = 0 := by rw [← AddValuation.map_pow, h, AddValuation.map_one]
  induction hv : v u using WithTop.recTopCoe with
  | top =>
    rw [hv] at h1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp [succ_nsmul] at h1
  | coe a =>
    rw [hv, ← WithTop.coe_nsmul, WithTop.coe_eq_zero] at h1
    simpa [hm.ne'] using h1

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ τ : Frames P.U.LG.L (κ := Fin 1 × Fin (chD C.ch)) C.xT, τ.Gen → IsEL P C.xT C.actT C.eT C.wPT τ → ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → ∀ (θ₁ : Fam P.D.toPre F 1) (θα₁ : Fam P.D.toPre F (1 * N)), ThFrame P.D ϖ F θ₁ → PullAl P.D F P.oD α 1 N θ₁ θα₁ → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → ∃ (u : F) (p₁ : Fin n → QkPt P.D.toPre F (1 * N)) (w₁ : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b) (DegPre.lineε (1 * N)))) (ζ₁ : Fin n → F) (r₀ r : Fin n → Fam P.D.toPre F (1 * N)) (σ₁ : Fin n → P.U.toUnifPre.SecGF F q) (f : Fin n → PS F 1 (chD C.ch)), v u = 0 ∧ h = u • boxSer f ∧ ∀ i, (w₁ i).IsGen ∧ FinOrd P.D F (1 * N) (p₁ i) (w₁ i) (ζ₁ i) ∧ P.ToA F (1 * N) (p₁ i) (x ≫ pA.pr i) ∧ PhiRel P.D.toPre F (1 * N) (p₁ i) (w₁ i) θα₁ (r₀ i) ∧ Fam.IsSmul P.D.toPre F (ζ₁ i) (r₀ i) (r i) ∧ P.U.toUnifPre.ExpandsG F q (σ₁ i) (PowGerm.famCast (Dp := P.D.toPre) (F := F) e (r i)) ∧ GermA P.U.toUnifPre (κ := Fin 1 × Fin (chD C.ch)) C.xT τ F q (σ₁ i) (f i) := by
  obtain ⟨hL, hL2, -, hL4, -⟩ := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hTr P hTor _ ϖ hϖ Q _ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact τ hτ hEL
    α N hN hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀ t q e σ' h hw _ hfin hpx hΦt hsm hexp hgerm
  subst e
  have hG := hL.globalFns
  have hk : 1 ≤ 1 * N := by omega
  haveI : CharZero T.V := (algebraMap T.V F).charZero
  obtain ⟨p₁, hp, hp₁⟩ := UnboxQk.exists_isBoxQk_toA hL hL2 hL4 hT T.V E H C.I.G P hTor n D' A' G' pD pA pG U' PU F
    (1 * N) hk p
  have hw₁ : ∀ i, ∃ w₁ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b)
      (DegPre.lineε (1 * N))), w₁.IsGen := fun i =>
    H1.ClosedPointWeilPower.gen_local_linComb P.D.toPre.P.L P.D.toPre.P.isLB _ _
  choose w₁ hw₁ using hw₁
  choose ζ₁ _ hζ₁ using fun i => H1.finOrdExists_of (phiFun_of hL) (H1.phiPow_of hL) T.V P.D F (1 * N) hk (p₁ i) (w₁ i)
    (hw₁ i)
  choose Φ₁ hΦ₁ using fun i => phiFun_of hL T.V _ P.D F (1 * N) hk (p₁ i) (w₁ i) (hw₁ i)
  obtain ⟨τ₀, hτ₀, hEL₀, hT₀⟩ := frame1St_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT
  have hLB : P.U.LG.L.IsLB := (congrArg RigLB.L P.bundle).symm ▸ C.I.G.PP.isLB
  obtain rfl : τ = τ₀ := funext fun m => TorusExt.gen_ext_val hLB (hτ m) (hτ₀ m) fun y J hJ =>
    (hEL m y J hJ).trans (hEL₀ m y J hJ).symm
  have hz₁ := GlobalTheory.T.universal_statement E H Dw l Xo c T io y C
  obtain ⟨gm₁, -, hgm₁⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V P.D P.A C.I.G.G P.U _ _ hz₁ τ hτ
    (hT₀ hTr) F (1 * N) hk
  choose σ₁ hσ₁ hf using fun i => hgm₁ (ζ₁ i • Φ₁ i θα₁)
  have exists_boxFam_multilinear : ∀ k : ℕ, ∃ bx : ((i : Fin n) → Fam P.D.toPre F k) →ₘₗ[F] Fam D'.toPre F k, ∀ (s : Fin n → Fam P.D.toPre F k) (S : Fam D'.toPre F k), IsBoxFam pD F k S s ↔ S = bx s := by
    intro k
    choose bx hbx using BoxFamily.exists_isBoxFam hG T.V n P.D.toPre D'.toPre pD F k
    refine ⟨⟨bx, fun s i a b => BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
      fun s i c a => BoxLinear.box_smul pD (hbx _) (hbx _)⟩, fun s S => ⟨fun h => ?_, fun h => ?_⟩⟩
    · exact BoxLinear.box_unique pD h (hbx s)
    · rw [h]; exact hbx s
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear 1
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear (1 * N)
  obtain ⟨u₀, hu₀, hθu⟩ := GlobalTheory.T.thetaFrameFamilies_differ_by_valuationZero_unit T.V ϖ hϖ D' F v hv _ θ
    (BoxFrame.main T.V ϖ hϖ n P.D D' pD F θ₁ _ hθ₁ ((hbx₁ _ _).2 rfl)) hθ
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 α N 1 hN le_rfl hα
  have hpull := BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact α N 1 hN le_rfl hα
    (fun _ => θ₁) (fun _ => θα₁) _ _ (fun _ => hθα₁) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  have hθα' : θα = u₀ • bx fun _ => θα₁ := by
    rw [(hpl _ _).1 hθα, (hpl _ _).1 hpull, (isSmul_iff _ _ _).1 hθu, map_smul]
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (1 * N) p p₁ hp w₁ hw₁
  have hfin' := finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (1 * N) hk p p₁ hp w₁ w' hw₁ hw' hΦ ζ₁ hζ₁
  obtain ⟨u₁, ⟨m, hm, hum⟩, hu₁⟩ := GlobalTheory.T.finiteOrder_thetaOperators_ratio_rootOfUnity T.V ϖ hϖ D' F (1 * N) hk p w' w (∏ i, ζ₁ i) ζ hw' hw hfin' hfin
  obtain ⟨Φ', hΦ'⟩ := phiFun_of hL T.V _ D' F (1 * N) hk p w' hw'
  have hbΦ : bx (fun i => Φ₁ i θα₁) = Φ' (bx fun _ => θα₁) :=
    (hΦ' _ _).1 (hΦ _ _ _ _ (fun i => (hΦ₁ i _ _).2 rfl) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl))
  have ht : t = (u₁ * u₀) • bx fun i => ζ₁ i • Φ₁ i θα₁ := by
    rw [(isSmul_iff _ _ _).1 (hu₁ θα _ _ t₀ t ((hΦ' _ _).2 rfl) ((isSmul_iff _ _ _).2 rfl) hΦt hsm), hθα', map_smul,
      MultilinearMap.map_smul_univ, hbΦ, smul_comm (∏ i, ζ₁ i) u₀, smul_smul]
    rfl
  obtain ⟨τn, hτn, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT hz₁
  obtain ⟨gm, hgm, hgmex⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τn hτn (hτT hTr)
    F (1 * N) hk
  obtain ⟨σb, hσb, -⟩ := hgmex (bx fun i => ζ₁ i • Φ₁ i θα₁)
  have hbox := boxGermSt_holds hL hL2 hL4 hT E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT
    C.eT C.wPT C.chartT C.frameT C.primT τ hτ hEL n D' A' G' pD pA pG U' PU F (1 * N) hk σ₁ _ _ σb _
    (fun i => ⟨hσ₁ i, hf i⟩) ((hbx _ _).2 rfl) hσb
  refine ⟨u₁ * u₀, p₁, w₁, ζ₁, fun i => Φ₁ i θα₁, fun i => ζ₁ i • Φ₁ i θα₁, σ₁, fun i => gm₁ (ζ₁ i • Φ₁ i θα₁), ?_, ?_,
    fun i => ⟨hw₁ i, hζ₁ i, hp₁ x hpx i, (hΦ₁ i _ _).2 rfl, (isSmul_iff _ _ _).2 rfl, hσ₁ i, hf i⟩⟩
  · rw [AddValuation.map_mul, hu₀, val_eq_zero_of_pow_eq_one v hm hum, add_zero]
  · rw [hgm t σ' h hexp ((hiff F _ σ' h).1 hgerm), hgm _ σb _ hσb ((hiff F _ σb _).1 hbox), ht, map_smul]

end GlobalTheory.ColumnSplit
