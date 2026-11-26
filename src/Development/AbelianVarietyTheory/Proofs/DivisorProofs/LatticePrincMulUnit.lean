module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePrincMulUnit
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.ClassInv

theorem finPart_unit {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hχ : IsValChar φ s κ 𝔣 Q χ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits (condQ 𝔣 Q)) : finPart χ u = 1 := by
  refine OrderUnits.finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hu
  by_cases hv : v ∈ Q
  · refine ⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩
    rw [pow_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
  · exact ⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _,
      fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩

theorem lamInf_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E}
    (h : HasInfRatio χ φ fun i => (κ i : ℤ) + s) (α : Eˣ) :
    lamInf φ (2 * s) κ α =
      ((χ.inf α : ℂˣ) : ℂ) * (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) := by
  have hN : (((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|) ^ s : ℝ) : ℂ) = ∏ i, (φ i α * starRingEnd ℂ (φ i α)) ^ s := by
    rw [← TermUnit.prod_norm_sq hφ (α : E), ← Finset.prod_pow]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.mul_conj']
  rw [hN, (hasInfRatio_iff χ φ _).1 h α]
  unfold lamInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : φ i α ≠ 0 := by simp
  have h2 : starRingEnd ℂ (φ i α) ≠ 0 := by simp
  have h3 : ((κ i : ℤ) + s) = ((κ i + s : ℕ) : ℤ) := by push_cast; ring
  rw [h3, zpow_natCast, div_pow, inv_pow]
  field_simp
  ring

theorem lattice_princ_mul_unit {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} (y : (Af E)ˣ) (α : Eˣ)
    {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) :
    lattice c (Units.map (algebraMap E (Af E)).toMonoidHom α * y * u) = (fun x => (α : E) * x) '' lattice c y := by
  rw [lattice_mul_unit _ hu]
  ext x
  constructor
  · intro hx
    refine ⟨(α : E)⁻¹ * x, (mul_mem_lattice_princ c y α _).1 ?_, by simp⟩
    simpa using hx
  · rintro ⟨z, hz, rfl⟩
    exact (mul_mem_lattice_princ c y α z).2 hz

theorem classInvariance : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → (∀ (s : ℕ) (L : Set E), Homothety φ (2 * s) L) → ∀ s : ℕ, ClassInvariance φ s := by
  intro E _ _ _ I _ _ φ hφ hH s 𝔣 Q κ χ _ _ hχ y y' S S' hq hS hS'
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)
  set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha
  have hy' : y' = a * y * u := by
    have : y' = y * (a * u) := by rw [hau]; group
    rw [this]; exact (by ac_rfl : y * (a * u) = a * y * u)
  subst hy'
  have hL := lattice_princ_mul_unit (c := condQ 𝔣 Q) y α hu
  rw [hL] at hS'
  have hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0 := (hH s _ κ α S hS).2 S' hS'
  have hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]
  have hfu : finPart χ u = 1 := finPart_unit hχ hu
  have hmu : modF u = 1 := ObjModel.modF_unit hu
  have hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹ := IdeleModule.modF_princ α
  have hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0 := by
    have h0 : Algebra.norm ℚ (α : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 α.ne_zero
    exact abs_ne_zero.2 (by exact_mod_cast h0)
  have hmy : modF y ≠ 0 := (IdeleModule.modF_pos y).ne'
  rw [hS0, lamInf_eq hφ hχ.2.2.1 α]
  unfold lamFin
  rw [map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]
  have hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹ := eq_inv_of_mul_eq_one_left hAB
  have hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmy' : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmy
  rw [hA']
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end GlobalTheory.ClassInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodBoundLastLog
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder Matrix

noncomputable section

namespace GlobalTheory.LastPeriod

open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum

theorem gramSum_one {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) :
    gramSum hN (1 : Matrix (Fin n) (Fin n) K) 1 = 1 := by
  ext a b
  have ha := a.2
  have hb := b.2
  simp only [gramSum, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff, Br.iL]
  split_ifs <;> first | rfl | omega

theorem coefOpLe_brAt (hL : LastMapNorm) {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]
    {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (T : ℝ) (hT : 0 < T) (t : ι → K)
    (ht : ∀ τ, star (σ (t τ)) * σ (t τ) = (T : ℂ)) :
    CoefOpLe σ lam sg (Br.brAt hN lam sg t) (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * orthNormSq hN lam sg) := by
  intro x
  have h := (hL ℂ (RingHom.id ℂ) (fun _ => rfl) ι N n hN lam sg hI hS (fun _ => 1)
    (fun _ => by simpa using Matrix.PosDef.one) T hT (fun _ => 1) (fun τ => σ (t τ))
    (fun τ => by simpa using ht τ)).2.2.1
    ⟨MvPolynomial.map σ (x : Pol K ι N), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩
  simp only [gramSum_one] at h
  rw [GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]
  refine le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ sg _ _ ?_) h
  simp only [Br.brAt, Br.brStd, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_smul, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_prod σ]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (map_zpow₀ σ _ _).symm

theorem sqAt_eq_dot {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (x : Formalism.L2.DIV.VV K lam) :
    sqAt σ lam x = (star (fun i => σ ((bVV K lam).repr x i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map σ *ᵥ
      fun i => σ ((bVV K lam).repr x i)).re := by
  simp only [sqAt, pairK_one_basis, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply,
    starRingEnd_apply, mul_assoc]

theorem sum_pair_le {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ}
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (B : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K sg) (t : ℝ)
    (hB : CoefOpLe σ lam sg B t) {C : Type} [Fintype C] (w : C → ℕ) (x : C → Formalism.L2.DIV.VV K lam)
    (y : C → Formalism.L2.DIV.VV K sg) :
    ‖σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c))‖ ^ 2 ≤
      t * (∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ lam (x c)) * ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (y c) := by
  have hG := (gramB_posDef sg σ).posSemidef
  have hre : ∀ z : C → Formalism.L2.DIV.VV K sg, (wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c i => σ ((bVV K sg).repr (z c) i)) (fun c i => σ ((bVV K sg).repr (z c) i))).re =
      ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (z c) := fun z => by
    rw [wForm, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sqAt_eq_dot, ← Complex.re_ofReal_mul]
    push_cast
    rfl
  have e3 : σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c)) = wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, wForm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_inv₀, map_natCast, star_star, map_pairBK]
  have h := wForm_le w hG (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i))
  rw [wForm_star w (by rw [← Matrix.transpose_map, GlobalTheory.TestLat.Compare.gramB_transpose]), ← e3] at h
  have h0 := (Complex.nonneg_iff.1 (wForm_nonneg w hG (fun c i => σ ((bVV K sg).repr (y c) i)))).1
  rw [hre] at h0
  rw [hre fun c => B (x c), hre] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ h0)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

theorem sqAt_nonneg {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : 0 ≤ sqAt σ lam x := by
  rw [sqAt_eq_dot]
  exact (Complex.nonneg_iff.1 ((gramB_posDef lam σ).posSemidef.dotProduct_mulVec_nonneg _)).1

theorem re_inv_mul (w : ℕ) (z : ℂ) : ((w : ℂ)⁻¹ * z).re = (w : ℝ)⁻¹ * z.re := by
  rw [← Complex.re_ofReal_mul]
  push_cast
  rfl

end GlobalTheory.LastPeriod

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoords
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieCoordMult

theorem lieMult_iff_finrank_eig : ∀ (W : Type) [CommRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n : ℕ) (k : Type) [Field k] (β : W →+* k) (T : (Fin n → k) → (epsPtR (spMap β) ⟶ G)) (A : O → Matrix (Fin n) (Fin n) k), Function.Injective T → (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : k) c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) → (∀ a c, T c ≫ act.act a = T ((A a).mulVec c)) → ∀ (τ : O →+* k) (N : ℕ), LieMult act (spMap β) τ N ↔ Module.finrank k (⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  intro W _ G _ _ O _ act n k _ β T A hinj htan hadd hsc hact τ N
  set E : Submodule k (Fin n → k) :=
    ⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) with hE
  have memE : ∀ x, x ∈ E ↔ ∀ a, (A a).mulVec x = τ a • x := by
    intro x
    simp [hE, Submodule.mem_iInf, sub_eq_zero]
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → k)), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ w, IsLieEigen act (spMap β) τ w ↔ ∃ x ∈ E, w = T x := by
    intro w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨x, rfl⟩ := (htan w).1 h1
      refine ⟨x, (memE x).2 fun a => hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2 a, hsc]
      rfl
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(htan _).2 ⟨x, rfl⟩, fun a => ?_⟩
      rw [hact, (memE x).1 hx a, hsc]
      rfl
  have comb : ∀ (x : Fin N → (Fin n → k)) (y : Fin n → k) (c : Fin N → k),
      (∃ u : Fin N → (epsPt (spMap β) ⟶ G), (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (T (x i)).left) ∧
        T y = (List.ofFn u).prod) ↔ y = ∑ i, c i • x i := by
    intro x y c
    constructor
    · rintro ⟨u, hu, hy⟩
      have hu' : u = fun i => T (c i • x i) := funext fun i => Over.OverMorphism.ext ((hu i).trans (hsc _ _).symm)
      rw [hu', Tsum] at hy
      exact hinj hy
    · intro hy
      exact ⟨fun i => T (c i • x i), fun i => hsc _ _, by rw [Tsum, hy]⟩
  show (∃ v : Fin N → (epsPt (spMap β) ⟶ G), (∀ i, IsLieEigen act (spMap β) τ (v i)) ∧ ∀ w, IsLieEigen act (spMap β) τ w →
    ∃! c : Fin N → k, ∃ u : Fin N → (epsPt (spMap β) ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod) ↔ _
  constructor
  · rintro ⟨v, hv, H⟩
    choose x hxE hx using fun i => (eig _).1 (hv i)
    obtain rfl : v = fun i => T (x i) := funext hx
    let b : Fin N → E := fun i => ⟨x i, hxE i⟩
    have bij : Function.Bijective (Fintype.linearCombination k b) := by
      refine (Function.bijective_iff_existsUnique _).2 fun y => ?_
      refine (existsUnique_congr fun c => ?_).1 (H (T y) ((eig _).2 ⟨y, y.2, rfl⟩))
      rw [comb x y c, Subtype.ext_iff, Fintype.linearCombination_apply]
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, b]
      exact eq_comm
    rw [← (LinearEquiv.ofBijective _ bij).finrank_eq, Module.finrank_fin_fun]
  · intro h
    let b := Module.finBasisOfFinrankEq k E h
    refine ⟨fun i => T (b i), fun i => (eig _).2 ⟨_, (b i).2, rfl⟩, fun w hw => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (eig w).1 hw
    refine (existsUnique_congr fun c => ?_).2
      ((Function.bijective_iff_existsUnique _).1 b.equivFun.symm.bijective ⟨y, hy⟩)
    rw [comb (fun i => (b i : Fin n → k)) y c, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact eq_comm

end GlobalTheory.LieCoordMult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoordsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords : ∀ (W : Type) [CommRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n : ℕ) (k : Type) [Field k] (β : W →+* k) (T : (Fin n → k) → (epsPtR (spMap β) ⟶ G)) (A : O → Matrix (Fin n) (Fin n) k), Function.Injective T → (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : k) c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) → (∀ a c, T c ≫ act.act a = T ((A a).mulVec c)) → ∀ (τ : O →+* k) (N : ℕ), LieMult act (spMap β) τ N ↔ Module.finrank k (⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  first | (exact @GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (exact GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (intros; apply GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.CutTransfer

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem proj_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (finGL E n (locGL E n w g)) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 := congrArg (fun z => (GeneralLinearGroup.map (pLoc E w) z).val i j) (pFin_finGL (E := E) (locGL E n w g))
  simp only [pLoc_locGL] at h1
  exact h1

theorem gl_ext_pLoc {x y : GL (Fin n) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

variable [_root_.NumberField.IsTotallyComplex E]

theorem comm_of_proj_eq_one (w : HeightOneSpectrum (𝓞 E)) {x : GA E n}
    (hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1) (g : GL (Fin n) (w.adicCompletion E)) :
    x * finGL E n (locGL E n w g) = finGL E n (locGL E n w g) * x := by
  have hxw : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z.val i j) hx
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_finGL, mul_one, one_mul]
  · simp only [map_mul, pFin_finGL]
    refine gl_ext_pLoc fun v => ?_
    simp only [map_mul]
    by_cases hv : v = w
    · subst hv
      rw [hxw, one_mul, mul_one]
    · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

theorem superDiag_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    GlobalTheory.Whittaker.superDiag (finGL E n (locGL E n w u)) = sFin E (sLoc E w (GlobalTheory.Whittaker.superDiag u)) := by
  unfold GlobalTheory.Whittaker.superDiag
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := by
    intro h
    subst h
    simp at hj
  change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
      sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = _
  simp [Matrix.one_apply_ne hij]

theorem psiN_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    psiN (finGL E n (locGL E n w u)) = psiLoc w (GlobalTheory.Whittaker.superDiag u) := by
  unfold psiN psiLoc
  rw [superDiag_finGL_locGL]

theorem finGL_locGL_mem_NA' (w : HeightOneSpectrum (𝓞 E)) {u : GL (Fin n) (w.adicCompletion E)}
    (hu : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n)) : finGL E n (locGL E n w u) ∈ NA (E := E) (a := n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = 0
    simp [Matrix.one_apply_ne hij.ne', h1 i j hij]
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i i - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i)) = 1
    simp [h2 i]

end GlobalTheory.JSW.CutTransfer

namespace GlobalTheory.JSW.CutTransfer

theorem transfer : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  intro E _ _ _ m w ψ hψ K U hU X A hcut
  classical
  obtain ⟨T₀, hT₀⟩ := hcut
  let Φ : GL (Fin (m + 1)) (w.adicCompletion E) →* GA E (m + 1) := (finGL E (m + 1)).comp (locGL E (m + 1) w)
  have hΦ : ∀ g, Φ g = finGL E (m + 1) (locGL E (m + 1) w g) := fun _ => rfl
  refine ⟨T₀.mapDomain Φ, ?_, ?_⟩
  · intro k hk
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hk)
    exact ⟨g, rfl⟩
  · intro W hN hK y hy
    set yw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y with hyw
    set x := y * (Φ yw)⁻¹ with hxdef
    have hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1 := by
      rw [hxdef, map_mul, map_inv, hΦ, proj_finGL_locGL, ← hyw, mul_inv_cancel]
    have hcomm : ∀ g, x * Φ g = Φ g * x := fun g => comm_of_proj_eq_one w hx g
    have hxy : ∀ g, x * Φ (yw * g) = y * Φ g := by
      intro g
      rw [map_mul, hxdef, mul_assoc, ← mul_assoc (Φ yw)⁻¹, inv_mul_cancel, one_mul]
    let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (x * Φ g)
    have hf1 : GlobalTheory.JSW.KirFin.Eqv ψ f := by
      intro u hu g
      show W (x * Φ (u * g)) = ψ (GlobalTheory.Whittaker.superDiag u) * W (x * Φ g)
      rw [map_mul, ← mul_assoc, hcomm u, mul_assoc, hΦ u, hN _ (finGL_locGL_mem_NA' w hu), psiN_finGL_locGL, hψ]
      rfl
    have hf2 : ∀ u ∈ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))), ∀ g, f (g * u) = f g := by
      intro u hu g
      show W (x * Φ (g * u)) = W (x * Φ g)
      rw [map_mul, ← mul_assoc, hΦ u, hK _ (hU u hu)]
    have key := hT₀ f hf1 hf2 yw hy
    have hact : GlobalTheory.JSW.Cut.act (T₀.mapDomain Φ) W y = GlobalTheory.JSW.Cut.act T₀ f yw := by
      unfold GlobalTheory.JSW.Cut.act
      rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ * W (y * Φ k) = _ * W (x * Φ (yw * k))
      rw [hxy]
    rw [hact, key]
    by_cases h : yw ∈ X
    · have h' : y ∈ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      show W (x * Φ yw) = W y
      rw [hxdef, mul_assoc, inv_mul_cancel, mul_one]
    · have h' : y ∉ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

end GlobalTheory.JSW.CutTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittakerStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCutOperator_transfer_adelicWhittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  first | (exact @GlobalTheory.JSW.CutTransfer.transfer) | (exact GlobalTheory.JSW.CutTransfer.transfer) | (intros; apply GlobalTheory.JSW.CutTransfer.transfer  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartIndependentClosedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartIndependentClosedField
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DepthField

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth

section Monomials

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem toE_mono {x y : WithTop ℝ} (h : x ≤ y) : toE x ≤ toE y := WithBot.coe_le_coe.2 h

theorem le_toE_sum {ι : Type} (S : Finset ι) (g : ι → C) {r : EReal} (h : ∀ i ∈ S, r ≤ toE (v (g i))) :
    r ≤ toE (v (∑ i ∈ S, g i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, v.map_zero]; exact le_top
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine le_trans ?_ (toE_mono (v.map_add _ _))
    rcases min_choice (v (g a)) (v (∑ i ∈ S, g i)) with e | e <;> rw [e] <;> assumption

theorem derivAt0_subst {σ τ : Type} {E : σ → MvPowerSeries τ C} (hE : HasSubst E) (P : MvPolynomial τ C)
    (f : MvPowerSeries σ C) : ∃ S : Finset (σ →₀ ℕ),
      derivAt0 P (subst E f) = ∑ β ∈ S, coeff β f * derivAt0 P (subst E (monomial β (1 : C))) := by
  classical
  refine ⟨P.support.biUnion fun α => (coeff_subst_finite hE f α).toFinset, ?_⟩
  simp only [derivAt0, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [coeff_subst hE, finsum_eq_sum_of_support_subset (s := P.support.biUnion
    fun α => (coeff_subst_finite hE f α).toFinset) _ fun β hβ => by
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
      exact ⟨α, hα, (Set.Finite.mem_toFinset _).2 hβ⟩, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [subst_monomial hE, map_one, one_mul, smul_eq_mul]
  ring

variable {κ : Type} {d : κ → ℕ} {ι : κ → Type} [∀ b, Fintype (ι b)]

theorem hasSubst_lin (u : ∀ b, ι b → Fin (d b) → C) (b : κ) :
    ∀ e : Fin (d b), constantCoeff (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := by
  intro e
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

theorem hasSubst_expAlong [Finite κ] (G : ∀ b, LogFGL v (d b)) (u : ∀ b, ι b → Fin (d b) → C) :
    HasSubst (expAlong G u) :=
  hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)) (hasSubst_lin u x.1)
      ((isExp_expOf (G x.1)).1 x.2)

theorem depth_eq_iInf_monomial [Finite κ] (G : ∀ b, LogFGL v (d b)) (u : ∀ b, ι b → Fin (d b) → C)
    (P : MvPolynomial (Σ b, ι b) C) :
    depth G u P = ⨅ β : (Σ b, Fin (d b)) →₀ ℕ,
      toE (v (derivAt0 P (subst (expAlong G u) (monomial β (1 : C))))) := by
  classical
  refine le_antisymm (le_iInf fun β => iInf_le_of_le ⟨monomial β 1, fun α => ?_⟩ le_rfl) (le_iInf fun f => ?_)
  · rw [IsIntV, coeff_monomial]
    split_ifs <;> simp
  · obtain ⟨S, hS⟩ := derivAt0_subst (hasSubst_expAlong G u) P f.1
    rw [hS]
    refine le_toE_sum S _ fun β _ => iInf_le_of_le β (toE_mono ?_)
    rw [v.map_mul]
    exact le_add_of_nonneg_left (f.2 β)

end Monomials

section Map

variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {v : AddValuation C (WithTop ℝ)}
  {w : AddValuation K (WithTop ℝ)}

theorem derivAt0_map {σ : Type} (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (MvPolynomial.map φ P) (MvPowerSeries.map φ g) = φ (derivAt0 P g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [derivAt0, MvPolynomial.support_map_of_injective _ φ.injective, map_sum, map_mul,
    MvPolynomial.coeff_map, coeff_map, mfact, Finsupp.prod, map_prod, map_natCast]

theorem expOf_map {d : ℕ} (G : LogFGL w d) (G' : LogFGL v d)
    (h : ∀ a, G'.lg a = MvPowerSeries.map φ (G.lg a)) (a : Fin d) :
    expOf G' a = MvPowerSeries.map φ (expOf G a) := by
  have he := isExp_expOf G
  have : IsExp G' fun a => MvPowerSeries.map φ (expOf G a) := by
    refine ⟨fun a => by simp [he.1 a], fun a => ?_⟩
    rw [h, ← map_subst (hasSubst_of_constantCoeff_zero he.1), he.2, map_X]
  rw [← isExp_unique G' this]

theorem depth_map {κ : Type} [Finite κ] {d : κ → ℕ} {ι : κ → Type} [∀ b, Fintype (ι b)]
    (hv : ∀ x, v (φ x) = w x) (G : ∀ b, LogFGL w (d b)) (G' : ∀ b, LogFGL v (d b))
    (h : ∀ b a, (G' b).lg a = MvPowerSeries.map φ ((G b).lg a)) (u : ∀ b, ι b → Fin (d b) → K)
    (P : MvPolynomial (Σ b, ι b) K) :
    depth G' (fun b a e => φ (u b a e)) (MvPolynomial.map φ P) = depth G u P := by
  have hE : expAlong G' (fun b a e => φ (u b a e)) = fun x => MvPowerSeries.map φ (expAlong G u x) := by
    funext x
    simp only [expAlong]
    rw [map_subst (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)), expOf_map φ _ _ (h x.1)]
    congr 1
    funext e
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, smul_eq_C_mul]
  rw [depth_eq_iInf_monomial, depth_eq_iInf_monomial, hE]
  refine iInf_congr fun β => ?_
  rw [← hv, ← derivAt0_map, map_subst (hasSubst_expAlong G u), map_monomial, φ.map_one]

theorem detPow_map (i c : ℕ) : MvPolynomial.map φ (detPow K i c) = detPow C i c := by
  rw [detPow, detPow, map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv i f) = MvPowerSeries.pderiv i (MvPowerSeries.map φ f) := by
  ext α
  simp [MvPowerSeries.coeff_pderiv]

theorem om_map {d : ℕ} (G : FGLaw K d) :
    Om (GlobalTheory.FBMap.mapLaw φ G) = (Om G).map (MvPowerSeries.map φ) := by
  have hJ : JM (GlobalTheory.FBMap.mapLaw φ G) = (JM G).map (MvPowerSeries.map φ) := by
    ext1 i b
    simp only [JM, Jac, Matrix.map_apply, Matrix.of_apply]
    rw [GlobalTheory.FBMap.map_ev2 φ (GlobalTheory.FBMap.nc_pt _) GlobalTheory.FBMap.nc_zero, GlobalTheory.FBMap.mapPt_pt, GlobalTheory.FBMap.mapPt_zero,
      map_pderiv]
    rfl
  refine Matrix.inv_eq_left_inv ?_
  rw [hJ, ← Matrix.map_mul, om_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem logOf_map [CharZero K] [CharZero C] {d : ℕ} (G : FGLaw K d) (a : Fin d) :
    logOf (GlobalTheory.FBMap.mapLaw φ G) a = MvPowerSeries.map φ (logOf G a) := by
  rw [← sub_eq_zero, eq_C_of_pderiv_zero (g := logOf (GlobalTheory.FBMap.mapLaw φ G) a - MvPowerSeries.map φ (logOf G a))]
  · simp [logOf, constantCoeff_prim]
  · rintro ⟨j, b⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [map_sub, ← map_pderiv, pderiv_logOf, pderiv_logOf, om_map, Matrix.map_apply, sub_self]

theorem lg_logFGLOf_map [CharZero K] [CharZero C] {d : ℕ} (G : FGLaw K d) (hG) (hG') (a : Fin d) :
    (logFGLOf v (GlobalTheory.FBMap.mapLaw φ G) hG').lg a = MvPowerSeries.map φ ((logFGLOf w G hG).lg a) := by
  show subst (oneVar C d) (logOf (GlobalTheory.FBMap.mapLaw φ G) a) = MvPowerSeries.map φ (subst (oneVar K d) (logOf G a))
  rw [logOf_map, map_subst hs_oneVar]
  congr 1
  funext q
  simp [oneVar]

end Map

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth

theorem nuFacC_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X X' : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch X' f k := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X X' f k
  letI := io.toAlgebra
  haveI : CharZero T.Fr := X.ιF.charZero
  let w : AddValuation T.Fr (WithTop ℝ) := (vX_vp X).comap X.ιF
  have hw : ∀ (Y : ValExt T p) x, vX_vp Y (Y.ιF x) = w x := by
    intro Y x
    show _ = vX_vp X (X.ιF x)
    by_cases hx : x = 0
    · rw [hx, Y.ιF.map_zero, X.ιF.map_zero, AddValuation.map_zero, AddValuation.map_zero]
    · rw [vX_vp_ιF Y hx, vX_vp_ιF X hx]
  have hG : ∀ a, MvIsInt w (subst (twoVars T.Fr _) (Ch.ch.B.G.F a)) := by
    intro a α
    have h := (fgl Ch X).F_int a α
    have e : (fgl Ch X).F a = MvPowerSeries.map X.ιF (subst (twoVars T.Fr _) (Ch.ch.B.G.F a)) := by
      rw [map_subst hs_twoVars]
      show subst (twoVars X.C _) (MvPowerSeries.map X.ιF (Ch.ch.B.G.F a)) = _
      congr 1
      funext q
      simp [twoVars]
    rw [e, coeff_map] at h
    exact h
  have key : ∀ Y : ValExt T p, nuFacC Ch Y f k = detDepth (logFGLOf w Ch.ch.B.G hG)
      (fun (a : Fin (rk f)) e => algebraMap T.V T.Fr (Ch.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩ e)) k := by
    intro Y
    rw [nuFacC, detDepth, detDepth, ← detPow_map Y.ιF]
    exact depth_map Y.ιF (hw Y) _ _ (fun _ a => lg_logFGLOf_map Y.ιF _ hG _ a) _ _
  rw [key, key]

end GlobalTheory.DepthField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartIndependentClosedFieldStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFactorDepthInChart_independent_closedField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X X' : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch X' f k := by
  first | exact @GlobalTheory.DepthField.nuFacC_field | exact GlobalTheory.DepthField.nuFacC_field | (intros; apply GlobalTheory.DepthField.nuFacC_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValCoordOfMemHatOUnits
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LUnit

theorem intAt_mul {l : ℕ} {a b : ℂ} (ha : IntAt l a) (hb : IntAt l b) : IntAt l (a * b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
  have e : ((n * m : ℕ) : ℂ) * (a * b) = (n * a) * (m * b) := by push_cast; ring
  rw [e]; exact ha.mul hb

theorem intAt_one (l : ℕ) : IntAt l 1 := ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one⟩

theorem unitAt_one (l : ℕ) : UnitAt l 1 := ⟨one_ne_zero, intAt_one l, by rw [inv_one]; exact intAt_one l⟩

theorem unitAt_mul {l : ℕ} {a b : ℂ} (ha : UnitAt l a) (hb : UnitAt l b) : UnitAt l (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, intAt_mul ha.2.1 hb.2.1, by rw [mul_inv]; exact intAt_mul ha.2.2 hb.2.2⟩

theorem unitAt_inv {l : ℕ} {a : ℂ} (ha : UnitAt l a) : UnitAt l a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unitAt_pow {l : ℕ} {a : ℂ} (ha : UnitAt l a) (n : ℕ) : UnitAt l (a ^ n) := by
  induction n with
  | zero => simpa using unitAt_one l
  | succ n ih => rw [pow_succ]; exact unitAt_mul ih ha

theorem unitAt_zpow {l : ℕ} {a : ℂ} (ha : UnitAt l a) (n : ℤ) : UnitAt l (a ^ n) := by
  cases n with
  | ofNat n => simpa using unitAt_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact unitAt_inv (unitAt_pow ha _)

theorem unitAt_prod {l : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitAt l (f i)) :
    UnitAt l (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one l
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitAt_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitAt_neg {l : ℕ} {a : ℂ} (ha : UnitAt l a) : UnitAt l (-a) := by
  have h1 : UnitAt l (-1) := ⟨by norm_num, ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one.neg⟩,
    ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one.neg⟩⟩
  simpa using unitAt_mul h1 ha

theorem intAt_of_pow {l : ℕ} {a : ℂ} {h : ℕ} (hh : 0 < h) (ha : IntAt l (a ^ h)) : IntAt l a := by
  obtain ⟨n, hn, hi⟩ := ha
  refine ⟨n, hn, IsIntegral.of_pow hh ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have e : ((n : ℂ) * a) ^ (k + 1) = (n : ℂ) ^ k * ((n : ℂ) * a ^ (k + 1)) := by ring
  rw [e]; exact ((isIntegral_natCast (R := ℤ) n).pow _).mul hi

theorem unitAt_of_pow {l : ℕ} {a : ℂ} {h : ℕ} (hh : 0 < h) (ha : UnitAt l (a ^ h)) : UnitAt l a :=
  ⟨fun h0 => ha.1 (by rw [h0, zero_pow hh.ne']), intAt_of_pow hh ha.2.1,
    intAt_of_pow hh (by rw [inv_pow]; exact ha.2.2)⟩

variable {E : Type} [Field E] [NumberField E]

theorem exists_coprime_mul_mem {l : ℕ} (hl : l.Prime) (α : E)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E α ≤ 1) :
    ∃ n : ℕ, n.Coprime l ∧ ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = n * α := by
  have hal : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨d, hd0, hd⟩ := hal.exists_integral_multiple
  have hD0 : IsIntegral ℤ (((d.natAbs : ℤ)) • α) := by
    rcases Int.natAbs_eq d with e | e
    · rw [← e]; exact hd
    · have : (d.natAbs : ℤ) = -d := by omega
      rw [this, neg_smul]; exact hd.neg
  have hD : IsIntegral ℤ ((d.natAbs : E) * α) := by
    have : ((d.natAbs : ℤ) • α) = (d.natAbs : E) * α := by rw [zsmul_eq_mul, Int.cast_natCast]
    rw [← this]; exact hD0
  obtain ⟨e, m, hm, hDm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hd0) l hl.one_lt.ne'
  refine ⟨m, (Nat.Prime.coprime_iff_not_dvd hl).2 hm |>.symm, ?_⟩
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun w => ?_
  have hval_nat : ∀ k : ℕ, w.valuation E (k : E) ≤ 1 := fun k => by
    have : (k : E) = algebraMap (𝓞 E) E (k : 𝓞 E) := by simp
    rw [this]; exact w.valuation_le_one _
  by_cases hw : (l : 𝓞 E) ∈ w.asIdeal
  · rw [map_mul]
    exact (mul_le_mul' (hval_nat m) (h w hw)).trans_eq (one_mul _)
  · have h1 : w.valuation E ((l : E) ^ e) = 1 := by
      have : (l : E) = algebraMap (𝓞 E) E (l : 𝓞 E) := by simp
      rw [map_pow, this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hw, one_pow]
    have h2 : w.valuation E ((d.natAbs : E) * α) ≤ 1 := by
      have : (d.natAbs : E) * α = algebraMap (𝓞 E) E ⟨_, hD⟩ := rfl
      rw [this]; exact w.valuation_le_one _
    rw [hDm] at h2
    push_cast at h2
    rw [mul_assoc, map_mul, h1, one_mul] at h2
    exact h2

theorem unitAt_embed {l : ℕ} (hl : l.Prime) (α : Eˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1) (σ : E →+* ℂ) :
    UnitAt l (σ α) := by
  have key : ∀ x : E, (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E x ≤ 1) → IntAt l (σ x) := by
    intro x hx
    obtain ⟨n, hn, b, hb⟩ := exists_coprime_mul_mem hl x hx
    refine ⟨n, hn, ?_⟩
    have : (n : ℂ) * σ x = σ.toIntAlgHom (algebraMap (𝓞 E) E b) := by
      rw [hb]; simp
    rw [this]
    exact (RingOfIntegers.isIntegral_coe b).map _
  refine ⟨by simp, key _ fun w hw => (h w hw).le, ?_⟩
  rw [← map_inv₀]
  exact key _ fun w hw => by rw [map_inv₀, h w hw, inv_one]

end GlobalTheory.CMVal.LUnit

namespace GlobalTheory.CMVal.LUnit

variable {E : Type} [Field E] [NumberField E]

theorem mul_coord' (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z * z') w = z w * z' w := rfl

theorem pow_coord (z : Af E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (z ^ n) w = (z w) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem val_coord_of_mem_hatOUnits {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((u : Af E) w) = 1 := by
  have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Conv.mem_integers_of_mem_hatO hu.1 w)
  have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Conv.mem_integers_of_mem_hatO hu.2 w)
  have h3 : Valued.v ((u : Af E) w) * Valued.v ((↑u⁻¹ : Af E) w) = 1 := by
    rw [← map_mul, ← mul_coord', Units.mul_inv]
    exact map_one _
  refine le_antisymm h1 ?_
  by_contra hlt
  rw [not_le] at hlt
  have h4 : Valued.v ((u : Af E) w) * Valued.v ((↑u⁻¹ : Af E) w) ≤ Valued.v ((u : Af E) w) * 1 := mul_le_mul' le_rfl h2
  rw [h3, mul_one] at h4
  exact absurd h4 (not_le.2 hlt)

theorem modF_of_mem_hatOUnits {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) : modF u = 1 := by
  unfold modF
  simp [val_coord_of_mem_hatOUnits hu]

theorem modF_pow (y : (Af E)ˣ) (n : ℕ) : modF (y ^ n) = modF y ^ n := by
  induction n with
  | zero =>
    unfold modF
    simp only [pow_zero, Units.val_one]
    exact finprod_eq_one_of_forall_eq_one fun w => by
      have : (1 : Af E) w = 1 := rfl
      rw [this, map_one]; simp
  | succ n ih => rw [pow_succ, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, ih, pow_succ]

theorem unitAt_norm {l : ℕ} (hl : l.Prime) (α : Eˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1) :
    UnitAt l (((|(Algebra.norm ℚ (α : E) : ℝ)| : ℝ) : ℂ)) := by
  have h1 : UnitAt l (((Algebra.norm ℚ (α : E) : ℝ) : ℂ)) := by
    have e : (((Algebra.norm ℚ (α : E) : ℝ) : ℂ)) = algebraMap ℚ ℂ (Algebra.norm ℚ (α : E)) := by simp
    rw [e, Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact unitAt_prod _ _ fun σ _ => unitAt_embed hl α h σ.toRingHom
  rcases abs_choice ((Algebra.norm ℚ (α : E) : ℝ)) with e | e
  · rw [e]; exact h1
  · rw [e, Complex.ofReal_neg]; exact unitAt_neg h1

end GlobalTheory.CMVal.LUnit


open GlobalTheory.CMVal.LUnit in
theorem GlobalTheory.CMVal.value_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (l : ℕ), c ≠ ⊥ → l.Prime →
    HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ y ∈ hatOUnits c, finPart χ y = 1) → ∀ y : (Af E)ˣ,
    (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v ((y : Af E) w) = 1) →
    UnitAt l ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)) := by
  intro E _ _ _ I _ φ _ s κ c χ l hc hl hinf hχ y hy
  classical
  have hfin := GlobalTheory.CMVal.PicFin.finite_picO E c hc
  have hpos : 0 < Nat.card (PicO c) := Nat.card_pos
  have hmem : y ^ Nat.card (PicO c) ∈ (princ ⊔ hatOUnits c : Subgroup (Af E)ˣ) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨p, ⟨α, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 hmem
  set h := Nat.card (PicO c)

  have hval : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1 := by
    intro w hw
    have e1 : Units.map (algebraMap E (Af E)).toMonoidHom α = y ^ h * u⁻¹ := eq_mul_inv_of_mul_eq hpu
    have e2 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom α : (Af E)ˣ) : Af E) w) = w.valuation E (α : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (α : E)
    rw [← e2, e1, Units.val_mul, mul_coord', Units.val_pow_eq_pow_val, pow_coord, map_mul, map_pow, hy w hw, one_pow,
      one_mul, val_coord_of_mem_hatOUnits (inv_mem hu) w]

  have hf : ((finPart χ y : ℂ)) ^ h = ((χ.inf α : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpu, map_mul, hχ u hu, mul_one,
      eq_inv_of_mul_eq_one_left (finPart_mul_inf χ α), Units.val_inv_eq_inv_val]
  have hm : modF y ^ h = (|(Algebra.norm ℚ (α : E) : ℝ)|)⁻¹ := by
    rw [← modF_pow, ← hpu, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, modF_of_mem_hatOUnits hu, mul_one,
      (GlobalTheory.CMVal.modF_mul_pos_principal E).2.2]
  have hpow : ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)) ^ h =
      ((χ.inf α : ℂˣ) : ℂ)⁻¹ * ((((|(Algebra.norm ℚ (α : E) : ℝ)| : ℝ) : ℂ))⁻¹) ^ s := by
    rw [mul_pow, hf, ← Complex.ofReal_pow, ← pow_mul, mul_comm s h, pow_mul, hm]
    push_cast
    ring
  refine unitAt_of_pow hpos ?_
  rw [hpow]
  refine unitAt_mul (unitAt_inv ?_) (unitAt_pow (unitAt_inv (unitAt_norm hl α hval)) s)
  rw [(hasInfRatio_iff χ φ _).1 hinf α]
  refine unitAt_prod _ _ fun i _ => unitAt_zpow (unitAt_mul (unitAt_embed hl α hval (φ i)) (unitAt_inv ?_)) _
  exact unitAt_embed hl α hval ((starRingEnd ℂ).comp (φ i))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivOfIsLBSplitTorus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TorusPic

theorem triv_of_isLB_splitTorus : ∀ (A : Type) [CommRing A], IsField A → ∀ (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : LB (splitTorus (Sp A) X).left), N.IsLB → Triv N := by
  intro A _ hA X _ _ _ N hN
  letI := hA.toField
  have : IsAffine (splitTorus (Sp A) X).left := by
    have := Diag.isAffineHom_hom (Sp A) X
    exact isAffine_of_isAffineHom (splitTorus (Sp A) X).hom
  have := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus A X
  exact GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top hN

end GlobalTheory.TorusPic
end
end
