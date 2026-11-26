module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormTwoSmulAndKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointIffBiextensionPullbacksIsomorphic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPTateSimilitudeComplexTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPTateSimilitudeComplexTorus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTTate

theorem torsion_card (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) {n : ℕ} (hn : 0 < n) {K : Type} [Field K]
    [IsSepClosed K] (t : Sp K ⟶ Sp ℂ) (z : Sp K) :
    Finite {x : Over.mk t ⟶ A // x ^ n = 1} ∧
      Nat.card {x : Over.mk t ⟶ A // x ^ n = 1} = (torsion A n).hom.finrank (t z) := by
  have hu : IsUnit (n : Γ(Sp ℂ, ⊤)) := GlobalTheory.SepClosedTorsion.isUnit_natCast_top (by exact_mod_cast hn.ne')
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hu
  let e2 : (Over.mk t ⟶ torsion A n) ≃ {x : Sp K ⟶ (torsion A n).left // x ≫ (torsion A n).hom = t} :=
    { toFun := fun y => ⟨y.left, Over.w y⟩
      invFun := fun x => Over.homMk x.1 x.2
      left_inv := fun y => Over.OverMorphism.ext rfl
      right_inv := fun x => rfl }
  let e : {x : Over.mk t ⟶ A // x ^ n = 1} ≃ {x : Sp K ⟶ (torsion A n).left // x ≫ (torsion A n).hom = t} :=
    (GlobalTheory.TorsionUnram.torsionEquiv A n (Over.mk t)).symm.trans e2
  obtain ⟨h1, h2⟩ := GlobalTheory.FinEt.card_points_eq_finrank (torsion A n).hom t z
  exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans h2⟩

def toC {k : Type} [Field k] (j : ℂ →+* k) : Over.mk (spMap j) ⟶ Over.mk (𝟙 (Sp ℂ)) :=
  Over.homMk (spMap j) (Category.comp_id _)

theorem toC_left {k : Type} [Field k] (j : ℂ →+* k) : (toC j).left = spMap j := rfl

theorem pre_injective {k : Type} [Field k] (j : ℂ →+* k) (A : Over (Sp ℂ)) [GrpObj A] :
    Function.Injective (preHom (G := A) (toC j)) := by
  intro x y h
  have hf : Flat (spMap j) := by
    rw [Flat.SpecMap_iff]
    letI := j.toAlgebra
    exact (inferInstance : Module.Flat ℂ k)
  have hs : Surjective (spMap j) := ⟨fun q => ⟨default, Subsingleton.elim (α := PrimeSpectrum ℂ) _ _⟩⟩
  have : Epi (spMap j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  have h' := congrArg (fun z => z.left) h
  simp only [preHom, MonoidHom.mk'_apply, Over.comp_left, toC_left] at h'
  exact (cancel_epi (spMap j)).1 h'

theorem pre_onto {k : Type} [Field k] [IsAlgClosed k] (j : ℂ →+* k) (A : Over (Sp ℂ)) [GrpObj A]
    (hA : IsAbelianScheme A) {n : ℕ} (hn : 0 < n) (x : Over.mk (spMap j) ⟶ A) (hx : x ^ n = 1) :
    ∃ y : Over.mk (𝟙 (Sp ℂ)) ⟶ A, y ^ n = 1 ∧ preHom (toC j) y = x := by
  obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨f₁, c₁⟩ := torsion_card A hA hn (spMap j) z
  obtain ⟨f₀, c₀⟩ := torsion_card A hA hn (𝟙 (Sp ℂ)) (spMap j z)
  let F : {x : Over.mk (𝟙 (Sp ℂ)) ⟶ A // x ^ n = 1} → {x : Over.mk (spMap j) ⟶ A // x ^ n = 1} :=
    fun y => ⟨preHom (toC j) y.1, by rw [← map_pow, y.2, map_one]⟩
  have hF : Function.Injective F := fun y y' h => Subtype.ext (pre_injective j A (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (hF.bijective_of_nat_card_le (by rw [c₀, c₁]; rfl)).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

theorem unitOn_pull {k : Type} [Field k] (j : ℂ →+* k) (c : ℂˣ) :
    Units.map (toC j).left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) := by
  rw [toC_left]
  apply Units.ext
  exact (congrArg (fun q => q.hom (c : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem one_comp_hom {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ] :
    (1 : T ⟶ G) ≫ φ = 1 := by
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]

end GlobalTheory.HTTate

namespace GlobalTheory.UPel.HT


open Classical in
theorem exists_tateIsoO_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (L : LB A.left) (D' : PLat D.O D.inv) t (Q : D'.La →+ (Fin D.g → ℂ)) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A)), 0 < N → N.Coprime p → IsAbelianScheme A → L.IsLB → Genus p N D.plat D' t → IsPeriod D' ρ Q → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A L k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (t a))) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ), ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A L n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y := by
  intro p _ D N ρ A _ _ act L D' t Q e eta hN hNp hA hL hG hP hadd hsurj hker hact hW heta k _ _ x
  obtain ⟨f, ν, rfl, htow, hgen⟩ := hG
  obtain ⟨j, rfl⟩ : ∃ j : ℂ →+* k, spMap j = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hGF : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let π := preHom (G := A) (GlobalTheory.HTTate.toC j)
  have hπ : Function.Injective π := GlobalTheory.HTTate.pre_injective j A
  let e' : Multiplicative (Fin D.g → ℂ) →* (Over.mk (𝟙 (Sp ℂ)) ⟶ A) :=
    MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have hpow : ∀ (n : ℕ) z, e z ^ n = e (n • z) := fun n z => (map_pow e' (Multiplicative.ofAdd z) n).symm
  have hsm : ∀ n : ℕ, 0 < n → ∀ z : Fin D.g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n hn z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have hsm' : ∀ n : ℕ, 0 < n → ∀ z : Fin D.g → ℂ, (n : ℂ)⁻¹ • n • z = z := fun n hn z => by
    rw [smul_comm, hsm n hn]
  have hshift : ∀ n : ℕ, 0 < n → ∀ a c : D'.La, e ((n : ℂ)⁻¹ • Q (a + n • c)) = e ((n : ℂ)⁻¹ • Q a) := by
    intro n hn a c
    rw [map_add (f := _), smul_add, hadd, map_nsmul, hsm' n hn, (hker _).2 ⟨c, rfl⟩, _root_.mul_one]
  let ev : ℕ → D.La → (Over.mk (spMap j) ⟶ A) := fun n a =>
    if 0 < n ∧ n.Coprime p then π (e ((n : ℂ)⁻¹ • Q (f n a))) else 1
  have hev : ∀ n, 0 < n → n.Coprime p → ∀ a, ev n a = π (e ((n : ℂ)⁻¹ • Q (f n a))) :=
    fun n hn hc a => if_pos ⟨hn, hc⟩
  have hev' : ∀ n, ¬ (0 < n ∧ n.Coprime p) → ∀ a, ev n a = 1 := fun n h a => if_neg h
  refine ⟨{ ζ := fun n => Units.map j.toMonoidHom (GlobalTheory.PeriodTate.rt n (ν n))
            ζ_prim := fun n hn hc => (GlobalTheory.PeriodTate.rt_prim hn (hgen n hn hc).1).map_of_injective
              (Units.map_injective j.injective)
            ζ_pow := fun n m hn hm hc => by
              rw [← map_pow, GlobalTheory.PeriodTate.rt_pow hm, GlobalTheory.PeriodTate.rt_congr hn (htow n m hn hm hc).1]
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn hc a => ?_
            onto := fun n hn hc q => ?_
            tower := fun n m hn hm hc a => ?_
            isom := fun n hn hc a b => ?_ }, fun y => ?_⟩
  · by_cases h : 0 < n ∧ n.Coprime p
    · have hf : f n (a + b) = f n a + f n b := (f n).map_add a b
      rw [hev n h.1 h.2, hev n h.1 h.2, hev n h.1 h.2, hf, map_add (f := _), smul_add, hadd, map_mul]
    · rw [hev' n h, hev' n h, hev' n h, _root_.mul_one]
  · by_cases h : 0 < n ∧ n.Coprime p
    · rw [hev n h.1 h.2, hev n h.1 h.2]
      obtain ⟨d, hd⟩ := (hgen n h.1 h.2).2.1 c a
      replace hd : f n (c • a) = c • f n a + n • d := hd
      show π _ = π _ ≫ _
      rw [hd, hshift n h.1, show π (e ((n : ℂ)⁻¹ • Q (f n a))) ≫ act.act c =
        π (e ((n : ℂ)⁻¹ • Q (f n a)) ≫ act.act c) from Category.assoc _ _ _, ← hact, hP.1, Matrix.mulVec_smul]
    · rw [hev' n h, hev' n h]
      haveI := act.hom c
      exact (GlobalTheory.HTTate.one_comp_hom (act.act c)).symm
  · rw [hev n hn hc, map_eq_one_iff π hπ, hker]
    have hk : (∃ e, f n a = n • e) ↔ ∃ e : D.La, a = n • e := (hgen n hn hc).2.2.1 a
    rw [← hk]
    constructor
    · rintro ⟨c, hc'⟩
      exact ⟨c, hP.2.1 (by rw [map_nsmul, hc', hsm n hn])⟩
    · rintro ⟨c, hc'⟩
      exact ⟨c, by rw [hc', map_nsmul, hsm' n hn]⟩
  · constructor
    · intro hq
      obtain ⟨y, hy, rfl⟩ := GlobalTheory.HTTate.pre_onto j A hA hn q hq
      obtain ⟨z, rfl⟩ := hsurj y
      rw [hpow, hker] at hy
      obtain ⟨a', ha'⟩ := hy
      obtain ⟨a, c, rfl⟩ := (hgen n hn hc).2.2.2.1 a'
      refine ⟨a, (hev n hn hc a).trans (congrArg π ?_)⟩
      rw [← hshift n hn _ c, ha', hsm' n hn]
    · rintro ⟨a, rfl⟩
      rw [hev n hn hc, ← map_pow, hpow, hsm n hn, (hker _).2 ⟨_, rfl⟩, map_one]
  · have hn' : n.Coprime p := Nat.Coprime.coprime_dvd_left (Nat.dvd_mul_right n m) hc
    obtain ⟨c, hc'⟩ := (htow n m hn hm hc).2 a
    replace hc' : f (n * m) a = f n a + n • c := hc'
    rw [hev _ (Nat.mul_pos hn hm) hc, hev n hn hn', ← map_pow, hpow, Nat.cast_mul, mul_inv_rev, mul_smul,
      hsm m hm, hc', hshift n hn]
  · show Out.WeilIs A L n (ev n a) (ev n b)
      (unitOn (Units.map j.toMonoidHom (GlobalTheory.PeriodTate.rt n (ν n)) ^ (2 * D.EF a b)))
    have h := GlobalTheory.CommPairing.weilIs_pull hGF hA hL (GlobalTheory.HTTate.toC j)
      (hW n (f n a) (f n b) (GlobalTheory.PeriodTate.rt n _) hn (GlobalTheory.PeriodTate.rt_val _ _))
    have e2 : D.plat.EF a b = 2 * D.EF a b := by
      show ((2 : ℤ) • D.EF) a b = _
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    have hν : (n : ℤ) ∣ D'.EF (f n a) (f n b) - ν n * (2 * D.EF a b) := by
      rw [← e2]; exact (hgen n hn hc).2.2.2.2 a b
    rw [GlobalTheory.HTTate.unitOn_pull, GlobalTheory.PeriodTate.rt_congr hn hν, GlobalTheory.PeriodTate.rt_mul, map_zpow] at h
    rw [hev n hn hc, hev n hn hc]
    exact h
  · show toUnit _ ≫ eta y = ev N y
    rw [hev N hN hNp]
    show _ = GlobalTheory.HTTate.toC j ≫ e _
    rw [← heta, ← Category.assoc]
    congr 1
end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPTateSimilitudeComplexTorusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeToP_tateSimilitude_complexTorus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (L : LB A.left) (D' : PLat D.O D.inv) t (Q : D'.La →+ (Fin D.g → ℂ)) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A)), 0 < N → N.Coprime p → IsAbelianScheme A → L.IsLB → Genus p N D.plat D' t → IsPeriod D' ρ Q → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A L k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (t a))) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ), ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A L n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y := by
  first | exact @GlobalTheory.UPel.HT.exists_tateIsoO_of_period | exact GlobalTheory.UPel.HT.exists_tateIsoO_of_period | (intros; apply GlobalTheory.UPel.HT.exists_tateIsoO_of_period <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectors
open NumberField Polynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieProj

theorem aeval_mul_of_mul_eq {g : ℕ} {T P : Matrix (Fin g) (Fin g) ℂ} {r : ℂ} (h : T * P = r • P) (q : ℂ[X]) :
    aeval T q * P = q.eval r • P := by
  have hp : ∀ k : ℕ, T ^ k * P = r ^ k • P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, mul_smul_comm, h, smul_smul, pow_succ, mul_comm (r ^ k)]
  induction q using Polynomial.induction_on' with
  | add p q hp' hq' => rw [map_add (f := _), add_mul, hp', hq', eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, eval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, hp,
      smul_smul]

theorem X_sub_C_mul_basis {s : Finset ℂ} {r : ℂ} (hr : r ∈ s) :
    (X - C r) * Lagrange.basis s id r = C (Lagrange.nodalWeight s id r) * Lagrange.nodal s id := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hr, mul_left_comm]
  congr 1
  exact EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero r) (Lagrange.X_sub_C_dvd_nodal id hr)

theorem spectral (K : Type) [Field K] [NumberField K] (g : ℕ) (Φ : K →+* Matrix (Fin g) (Fin g) ℂ) :
    ∃ E : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ, (∀ τ, E τ * E τ = E τ) ∧ ∑ τ, E τ = 1 ∧
      (∀ τ x, Φ x * E τ = τ x • E τ) ∧ (∀ τ x, E τ * Φ x = τ x • E τ) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ K
  let θ := pb.gen
  let T := Φ θ
  let f : ℂ[X] := (minpoly ℚ θ).map (algebraMap ℚ ℂ)
  let S : Finset ℂ := f.roots.toFinset
  have hfmon : f.Monic := (minpoly.monic (Algebra.IsIntegral.isIntegral θ)).map _
  have hnod : f.roots.Nodup := nodup_roots (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ θ))
  have hnodal : Lagrange.nodal S id = f := by
    rw [Lagrange.nodal]
    conv_rhs => rw [(IsAlgClosed.splits f).eq_prod_roots_of_monic hfmon]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnod.dedup]
    rfl
  have hfT : aeval T f = 0 := by
    rw [aeval_map_algebraMap, show T = Φ.toRatAlgHom θ from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hroot : ∀ r : ℂ, r ∈ S ↔ aeval r (minpoly ℚ θ) = 0 := by
    intro r
    rw [Multiset.mem_toFinset, mem_roots hfmon.ne_zero, IsRoot.def, eval_map_algebraMap]
  have hmemS : ∀ τ : K →+* ℂ, τ θ ∈ S := by
    intro τ
    rw [hroot, show τ θ = τ.toRatAlgHom θ from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have himage : Finset.univ.image (fun τ : K →+* ℂ => τ θ) = S := by
    ext r
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp h
      exact hmemS τ
    · have h' := (hroot r).mp h
      exact Finset.mem_image.mpr ⟨(pb.lift r h').toRingHom, Finset.mem_univ _, pb.lift_gen r h'⟩
  have hinjθ : ∀ τ τ' : K →+* ℂ, τ θ = τ' θ → τ = τ' := by
    intro τ τ' h
    have := pb.algHom_ext (f := τ.toRatAlgHom) (g := τ'.toRatAlgHom) h
    ext x
    exact DFunLike.congr_fun this x
  have hpoly : ∀ x : K, ∃ q : ℂ[X], Φ x = aeval T q ∧ ∀ τ : K →+* ℂ, τ x = q.eval (τ θ) := by
    intro x
    obtain ⟨h, -, hh⟩ := pb.exists_eq_aeval x
    refine ⟨h.map (algebraMap ℚ ℂ), ?_, fun τ => ?_⟩
    · rw [aeval_map_algebraMap, hh, show T = Φ.toRatAlgHom θ from rfl, aeval_algHom_apply]
      rfl
    · rw [eval_map_algebraMap, hh, show τ θ = τ.toRatAlgHom θ from rfl, aeval_algHom_apply]
      rfl
  let P : ℂ → Matrix (Fin g) (Fin g) ℂ := fun r => aeval T (Lagrange.basis S id r)
  have heig : ∀ r ∈ S, T * P r = r • P r := by
    intro r hr
    have h := congrArg (aeval T) (X_sub_C_mul_basis hr)
    simp only [map_mul, map_sub, aeval_X, aeval_C, hnodal, hfT, mul_zero] at h
    rw [sub_mul, sub_eq_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
    exact h
  have hinjS : Set.InjOn (id : ℂ → ℂ) S := fun _ _ _ _ h => h
  refine ⟨fun τ => P (τ θ), fun τ => ?_, ?_, fun τ x => ?_, fun τ x => ?_⟩
  · show aeval T (Lagrange.basis S id (τ θ)) * P (τ θ) = P (τ θ)
    rw [aeval_mul_of_mul_eq (heig _ (hmemS τ))]
    have := Lagrange.eval_basis_self (v := id) hinjS (hmemS τ)
    simp only [id] at this
    rw [this, one_smul]
  · have hne : S.Nonempty := ⟨_, hmemS (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
    rw [← Finset.sum_image (f := P) (fun τ _ τ' _ h => hinjθ τ τ' h), himage]
    show ∑ r ∈ S, aeval T (Lagrange.basis S id r) = 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Lagrange.sum_basis hinjS hne, map_one]
  · obtain ⟨q, hq, hτq⟩ := hpoly x
    rw [hq, aeval_mul_of_mul_eq (heig _ (hmemS τ)), hτq]
  · obtain ⟨q, hq, hτq⟩ := hpoly x
    show aeval T (Lagrange.basis S id (τ θ)) * Φ x = _
    rw [hq, ← map_mul, mul_comm, map_mul, aeval_mul_of_mul_eq (heig _ (hmemS τ)), hτq]

end GlobalTheory.UPel.HT.LieProj

namespace GlobalTheory.UPel.HT.LieProj

theorem exists_mul_eq_nat {K : Type} [Field K] [NumberField K] {x : 𝓞 K} (hx : x ≠ 0) :
    ∃ (y : 𝓞 K) (N : ℕ), N ≠ 0 ∧ x * y = N := by
  have hI : Ideal.span {x} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {x}))
  exact ⟨y, _, fun h => hI (Ideal.absNorm_eq_zero_iff.mp h), by rw [mul_comm, hy]⟩

theorem extend {K : Type} [Field K] [NumberField K] {g : ℕ} (ψ : 𝓞 K →+* Matrix (Fin g) (Fin g) ℂ) :
    ∃ Φ : K →+* Matrix (Fin g) (Fin g) ℂ, ∀ c : 𝓞 K, Φ (c : K) = ψ c := by
  have hcomm : ∀ a ∈ Set.range ψ, ∀ b ∈ Set.range ψ, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, mul_comm, map_mul]
  letI : IsMulCommutative (Algebra.adjoin ℚ (Set.range ψ)) :=
    Algebra.isMulCommutative_adjoin ℚ (fun a ha b hb _ => hcomm a ha b hb)
  letI : CommRing (Algebra.adjoin ℚ (Set.range ψ)) := by
    open scoped IsMulCommutative in infer_instance
  let ψ' : 𝓞 K →+* Algebra.adjoin ℚ (Set.range ψ) :=
    ψ.codRestrict (Algebra.adjoin ℚ (Set.range ψ)) fun x => Algebra.subset_adjoin ⟨x, rfl⟩
  have hu : ∀ y : nonZeroDivisors (𝓞 K), IsUnit (ψ' y) := by
    intro y
    obtain ⟨y', N, hN, hy⟩ := exists_mul_eq_nat (nonZeroDivisors.coe_ne_zero y)
    refine IsUnit.of_mul_eq_one (ψ' y' * algebraMap ℚ _ (N : ℚ)⁻¹) ?_
    rw [← mul_assoc, ← map_mul, hy, map_natCast, ← map_natCast (algebraMap ℚ (Algebra.adjoin ℚ (Set.range ψ))),
      ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hN), map_one]
  refine ⟨(Algebra.adjoin ℚ (Set.range ψ)).val.toRingHom.comp
    (IsLocalization.lift (M := nonZeroDivisors (𝓞 K)) (S := K) (g := ψ') hu), fun c => ?_⟩
  have := IsLocalization.lift_eq (M := nonZeroDivisors (𝓞 K)) (S := K) (g := ψ') hu c
  simp only [RingHom.comp_apply]
  erw [this]
  rfl

theorem idem_eq_zero {g : ℕ} {P : Matrix (Fin g) (Fin g) ℂ} (h : P * P = P) (ht : P.trace = 0) : P = 0 := by
  have hPid : IsIdempotentElem (Matrix.toLinAlgEquiv' P) := (show IsIdempotentElem P from h).map _
  have hPtr : LinearMap.trace ℂ (Fin g → ℂ) (Matrix.toLinAlgEquiv' P) = 0 := by
    show LinearMap.trace ℂ (Fin g → ℂ) (Matrix.toLin' P) = 0
    rw [Matrix.trace_toLin'_eq, ht]
  have := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero (e := Matrix.toLinAlgEquiv' P) hPid hPtr
  exact (map_eq_zero_iff _ (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)).injective).mp this

end GlobalTheory.UPel.HT.LieProj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.LieProj

theorem lie_projectors : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ), b.IsType σ ρ → ∃ E : Fin D.a → Matrix (Fin D.g) (Fin D.g) ℂ, (∀ i, E i * E i = E i) ∧ (∀ i, (E i).trace = (D.m : ℂ)) ∧ (∀ i c, ρ (algebraMap (𝓞 D.F) D.O c) * E i = σ (b.t i c) • E i) ∧ (∀ i c, E i * ρ (algebraMap (𝓞 D.F) D.O c) = σ (b.t i c) • E i) ∧ (2 * σ b.ρ - D.tr) • ∑ i, E i = ρ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
  intro p _ D R _ b σ ρ hT
  classical
  obtain ⟨Φ, hΦ⟩ := extend (ρ.comp (algebraMap (𝓞 D.F) D.O))
  obtain ⟨E, hidem, hsum, hl, hr⟩ := spectral D.F D.g Φ
  have hΦ' : ∀ c : 𝓞 D.F, ρ (algebraMap (𝓞 D.F) D.O c) = Φ (c : D.F) := fun c => (hΦ c).symm
  set lam : ℂ := σ b.ρ with hlam
  have hinj : ∀ i, Function.Injective (σ.comp (b.t i)) := by
    intro i
    refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    by_contra h0
    obtain ⟨y, N, hN, hy⟩ := exists_mul_eq_nat h0
    have := congrArg (σ.comp (b.t i)) hy
    rw [map_mul, hx, zero_mul, map_natCast] at this
    exact hN (by exact_mod_cast this.symm)
  let τ : Fin D.a → (D.F →+* ℂ) := fun i => IsFractionRing.lift (hinj i)
  have hτ : ∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c) := fun i c =>
    IsFractionRing.lift_algebraMap (hinj i) c
  have hτinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub]
      rw [← hτ, ← hτ, hij, sub_self]
    have h1 : (1 : R) ∈ RingHom.ker σ := hle (by rw [b.comax i j hne]; exact Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hroot : lam ^ 2 - D.tr * lam + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hnreal : (starRingEnd ℂ) lam ≠ lam := by
    intro h
    have hr := Complex.conj_eq_iff_re.mp h
    rw [← hr] at hroot
    have h2 : (lam.re) ^ 2 - D.tr * lam.re + D.nm = 0 := by exact_mod_cast hroot
    have h3 : ((D.tr : ℝ)) ^ 2 - 4 * D.nm < 0 := by exact_mod_cast D.disc_neg
    nlinarith [sq_nonneg (2 * lam.re - D.tr)]
  have hω : ∀ τ' : D.F →+* ℂ, (τ' (D.ω : D.F)) ^ 2 - D.tr * τ' (D.ω : D.F) + D.nm = 0 := by
    intro τ'
    have h0 : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have := congrArg (τ'.comp (algebraMap (𝓞 D.F) D.F)) h0
    simp only [map_sub, map_add (f := _), map_mul, map_pow, map_intCast, map_zero] at this
    exact this
  have hτω : ∀ i, τ i (D.ω : D.F) = lam := fun i => by rw [hτ, b.t_ω]
  have hexp : ∀ x : D.F, Φ x = ∑ τ', τ' x • E τ' := by
    intro x
    rw [← mul_one (Φ x), ← hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ' _ => hl τ' x
  set I := Finset.univ.image τ with hIdef
  set J := Finset.univ.image (fun i => (starRingEnd ℂ).comp (τ i)) with hJdef
  have hJinj : Function.Injective fun i => (starRingEnd ℂ).comp (τ i) := by
    intro i j h
    apply hτinj
    ext x
    have := congrArg (fun f : D.F →+* ℂ => (starRingEnd ℂ) (f x)) h
    simpa using this
  have hnJ : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) = lam → τ' ∉ J := by
    intro τ' hω' hm
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    have := congrArg (fun f : D.F →+* ℂ => f (D.ω : D.F)) hj
    simp only [RingHom.comp_apply, hτω, hω'] at this
    exact hnreal this
  let coef : (D.F →+* ℂ) → ℂ := fun τ' => (D.m : ℂ) * ((if τ' ∈ I then 1 else 0) +
    (if τ' (D.ω : D.F) = lam then 0 else (D.n : ℂ)) - (if τ' ∈ J then 1 else 0))
  have hdiff : ∀ c : 𝓞 D.F, ∑ τ', ((E τ').trace - coef τ') * τ' (c : D.F) = 0 := by
    intro c
    have h1 := hT c
    have hI : ∑ i, σ (b.t i c) = ∑ τ', (if τ' ∈ I then τ' (c : D.F) else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image (fun i _ j _ h => hτinj h)]
      exact Finset.sum_congr rfl fun i _ => (hτ i c).symm
    have hJ : ∑ i, (starRingEnd ℂ) (σ (b.t i c)) = ∑ τ', (if τ' ∈ J then τ' (c : D.F) else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image (fun i _ j _ h => hJinj h)]
      exact Finset.sum_congr rfl fun i _ => by simp [hτ i c]
    rw [hI, hJ, Finset.sum_filter, hΦ', hexp, Matrix.trace_sum] at h1
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, ← sub_eq_zero,
      ← Finset.sum_sub_distrib] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun τ' _ => ?_
    simp only [coef, Matrix.trace_smul, smul_eq_mul]
    split_ifs <;> first | ring1 | (exfalso; tauto)
  have hlin := (linearIndependent_monoidHom (𝓞 D.F) ℂ).comp
    (fun τ' : D.F →+* ℂ => ((τ'.comp (algebraMap (𝓞 D.F) D.F)).toMonoidHom : 𝓞 D.F →* ℂ)) (by
      intro a a' h
      apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.F))
      ext x
      exact DFunLike.congr_fun h x)
  have hcoef : ∀ τ', (E τ').trace - coef τ' = 0 := by
    refine Fintype.linearIndependent_iff.mp hlin _ ?_
    funext c
    rw [Finset.sum_apply]
    simpa using hdiff c
  have hmτ : ∀ i, (E (τ i)).trace = D.m := by
    intro i
    have h := hcoef (τ i)
    have h1 : τ i ∈ I := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    simp only [coef, h1, hτω i, hnJ (τ i) (hτω i), if_true, if_false] at h
    linear_combination h
  have hzero : ∀ τ', τ' ∉ I → τ' (D.ω : D.F) = lam → E τ' = 0 := by
    intro τ' hI' hω'
    refine idem_eq_zero (hidem τ') ?_
    have h := hcoef τ'
    simp only [coef, hI', hω', hnJ τ' hω', if_true, if_false] at h
    linear_combination h
  refine ⟨fun i => E (τ i), fun i => hidem _, hmτ, fun i c => ?_, fun i c => ?_, ?_⟩
  · rw [hΦ', hl, hτ]
  · rw [hΦ', hr, hτ]
  · have hL : ∑ i, E (τ i) = ∑ τ', (if τ' ∈ I then E τ' else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image (fun i _ j _ h => hτinj h)]
    have h1 : ((D.tr : ℂ) - lam) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) = ∑ τ', ((D.tr : ℂ) - lam) • E τ' := by
      rw [← hsum, Finset.smul_sum]
    rw [hL, h1, hΦ', hexp, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ' _ => ?_
    by_cases hI' : τ' ∈ I
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hI'
      rw [if_pos hI', ← sub_smul, hτω i]
      congr 1
      ring
    · rw [if_neg hI', smul_zero]
      by_cases hω' : τ' (D.ω : D.F) = lam
      · rw [hzero τ' hI' hω', smul_zero, smul_zero, sub_zero]
      · have hq : (τ' (D.ω : D.F) - lam) * (τ' (D.ω : D.F) - ((D.tr : ℂ) - lam)) = 0 := by
          linear_combination hω τ' - hroot
        have h2 := sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left (sub_ne_zero.mpr hω'))
        rw [← sub_smul, h2, sub_self, zero_smul]

end GlobalTheory.UPel.HT.LieProj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_representation_spectral_projectors : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ), b.IsType σ ρ → ∃ E : Fin D.a → Matrix (Fin D.g) (Fin D.g) ℂ, (∀ i, E i * E i = E i) ∧ (∀ i, (E i).trace = (D.m : ℂ)) ∧ (∀ i c, ρ (algebraMap (𝓞 D.F) D.O c) * E i = σ (b.t i c) • E i) ∧ (∀ i c, E i * ρ (algebraMap (𝓞 D.F) D.O c) = σ (b.t i c) • E i) ∧ (2 * σ b.ρ - D.tr) • ∑ i, E i = ρ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
  first | exact @GlobalTheory.UPel.HT.LieProj.lie_projectors | exact GlobalTheory.UPel.HT.LieProj.lie_projectors | (intros; apply GlobalTheory.UPel.HT.LieProj.lie_projectors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TanScalDecomp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieCoordMult

theorem tanScal_decomp : ∀ (O : Type) [Ring O] (F' : Type) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (act : OActN O G) (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (n a : ℕ) (T : (Fin n → R') → (epsPtR x ⟶ G)) (A : O → Matrix (Fin n) (Fin n) R') (emb : F' → O) (ω : F') (l : R') (χ : Fin a → F' → R'), Function.Injective T → (∀ v : epsPtR x ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → (∀ b c, T c ≫ act.act b = T (A b *ᵥ c)) → (∀ y : Fin n → R', A (emb ω) *ᵥ y = l • y → ∃ z : Fin a → Fin n → R', (∀ i c, A (emb c) *ᵥ z i = χ i c • z i) ∧ y = ∑ i, z i) → ∀ v : epsPtR x ⟶ G, IsTanScal act x (emb ω) l v → ∃ w : Fin a → (epsPtR x ⟶ G), (∀ i c, IsTanScal act x (emb c) (χ i c) (w i)) ∧ v = (List.ofFn w).prod := by
  intro O _ F' S G _ _ act R' _ x n a T A emb ω l χ hinj htan hadd hsc hact hdec v hv
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → R')), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ (b : O) (c : R') (w : epsPtR x ⟶ G), IsTanScal act x b c w ↔ ∃ y, A b *ᵥ y = c • y ∧ w = T y := by
    intro b c w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := (htan w).1 h1
      refine ⟨y, hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2, hsc]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(htan _).2 ⟨y, rfl⟩, ?_⟩
      rw [hact, hy, hsc]
  obtain ⟨y, hy, rfl⟩ := (eig _ _ _).1 hv
  obtain ⟨z, hz, rfl⟩ := hdec y hy
  exact ⟨fun i => T (z i), fun i c => (eig _ _ _).2 ⟨z i, hz i c, rfl⟩, (Tsum a z).symm⟩

end GlobalTheory.LieCoordMult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSpecDecomp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.SpecBC

theorem baseChange_specDecomp : ∀ (g a m : ℕ) (O : Type) [CommRing O] (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (χ : Fin a → (O →+* ℂ)) (ω : O) (l l' : ℂ) (E : Fin a → Matrix (Fin g) (Fin g) ℂ), l ≠ l' → (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → (∀ i, E i * E i = E i) → (∀ i, (E i).trace = (m : ℂ)) → (∀ i c, ρ c * E i = χ i c • E i) → (∀ i c, E i * ρ c = χ i c • E i) → (l - l') • ∑ i, E i = ρ ω - l' • (1 : Matrix (Fin g) (Fin g) ℂ) → (∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'), (ρ ω).map j *ᵥ x = j l • x → ∃ y : Fin a → Fin g → R', (∀ i c, (ρ c).map j *ᵥ y i = j (χ i c) • y i) ∧ x = ∑ i, y i) ∧ ∀ (k : Type) [Field k] (j : ℂ →+* k) (i : Fin a), χ i ω = l → Module.finrank k (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) : Submodule k (Fin g → k)) = m := by
  intro g a m O _ ρ χ ω l l' E hll hsep hidem htr hrE hEr hsum
  have hsm : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (r : ℂ) (M : Matrix (Fin g) (Fin g) ℂ),
      (r • M).map j = j r • M.map j := by
    intro R' _ j r M; ext; simp
  have hmul : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (M N : Matrix (Fin g) (Fin g) ℂ),
      (M * N).map j = M.map j * N.map j := by
    intro R' _ j M N; exact Matrix.map_mul

  have hrel : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'),
      j (l - l') • ∑ i, (E i).map j *ᵥ x = (ρ ω).map j *ᵥ x - j l' • x := by
    intro R' _ j x
    have h := congrArg (fun M => (RingHom.mapMatrix j M) *ᵥ x) hsum
    simp only [RingHom.mapMatrix_apply] at h
    have hs : (∑ i, E i).map j = ∑ i, (E i).map j := by ext; simp [Matrix.sum_apply]
    rw [hsm, hs, Matrix.smul_mulVec, Matrix.sum_mulVec] at h
    rw [h, Matrix.map_sub _ (map_sub j), Matrix.sub_mulVec, hsm, Matrix.smul_mulVec, Matrix.map_one _ (map_zero j) (map_one j),
      Matrix.one_mulVec]
  refine ⟨fun R' _ j x hx => ?_, fun k _ j i hi => ?_⟩
  · refine ⟨fun i => (E i).map j *ᵥ x, fun i c => ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    · have hu : IsUnit (j (l - l')) := (sub_ne_zero.mpr hll).isUnit.map j
      have h := hrel R' j x
      rw [hx, ← sub_smul, ← map_sub] at h
      exact (hu.smul_left_cancel.mp h).symm
  · have hj : ∀ z : ℂ, z ≠ 0 → j z ≠ 0 := fun z hz => (hz.isUnit.map j).ne_zero
    have hK : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) :
        Submodule k (Fin g → k)) = LinearMap.range (Matrix.mulVecLin ((E i).map j)) := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range]
      constructor
      · intro hy
        refine ⟨y, ?_⟩
        have hz : ∀ i', i' ≠ i → (E i').map j *ᵥ y = 0 := by
          intro i' hne
          obtain ⟨c, hc⟩ := hsep i' i hne
          have h1 : (E i').map j *ᵥ ((ρ c).map j *ᵥ y) = j (χ i' c) • ((E i').map j *ᵥ y) := by
            rw [Matrix.mulVec_mulVec, ← hmul, hEr, hsm, Matrix.smul_mulVec]
          rw [hy c, Matrix.mulVec_smul] at h1
          have h2 : (j (χ i' c) - j (χ i c)) • ((E i').map j *ᵥ y) = 0 := by
            rw [sub_smul, ← h1, sub_self]
          rw [← map_sub] at h2
          exact (smul_eq_zero.mp h2).resolve_left (hj _ (sub_ne_zero.mpr hc))
        have h := hrel k j y
        rw [hy ω, hi, ← sub_smul, ← map_sub,
          Finset.sum_eq_single i (fun b _ hb => hz b hb) (by simp)] at h
        exact smul_right_injective _ (hj _ (sub_ne_zero.mpr hll)) h
      · rintro ⟨z, rfl⟩ c
        rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    rw [hK]
    have hPP : (E i).map j * (E i).map j = (E i).map j := by rw [← hmul, hidem]
    have he : IsIdempotentElem (Matrix.mulVecLin ((E i).map j)) := by
      unfold IsIdempotentElem
      rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hPP]
    have h1 := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
    rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin g)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h1
    have htj : ((E i).map j).trace = j (E i).trace := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum]
    rw [htj, htr, map_natCast] at h1
    haveI : CharZero k := (RingHom.charZero_iff j.injective).1 inferInstance
    exact_mod_cast h1.symm

end GlobalTheory.SpecBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.lie_of_complexExp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension D.g A.hom → IsExp (𝟙 (Sp ℂ)) e → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → b.IsType σ ρ → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ) (β : R →+* k), x ≫ spMap σ = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  intro p _ D R _ b N σ ρ A _ _ act e hab hsm hexp hlin hty
  have hsmooth : Smooth A.hom := SmoothOfRelativeDimension.smooth D.g A.hom
  obtain ⟨n, M, hT⟩ := GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group ℂ A hsmooth
  obtain ⟨T0, h0inj, h0tan, h0add, h0sc, h0act⟩ := hT ℂ (RingHom.id ℂ)
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by simp [spMap]
  obtain ⟨L, hL⟩ := GlobalTheory.ExpCoord.expCoord D.g n A e (spMap (RingHom.id ℂ)) T0 hid hexp h0inj h0tan h0add h0sc
  have hLρ : ∀ (a : D.O) w, L (ρ a *ᵥ w) = M (act.act a) *ᵥ L w := fun a w => by
    have := hL (act.act a) (act.hom a) ((M (act.act a)).map (RingHom.id ℂ)) (ρ a)
      (fun c => h0act _ (act.hom a) c) (hlin a) w
    simpa using this
  have hn : n = D.g := by simpa using L.finrank_eq.symm
  subst hn
  set P : Matrix (Fin D.g) (Fin D.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hP
  have hPv : ∀ w, P *ᵥ w = L w := fun w => LinearMap.toMatrix'_mulVec _ w
  have hMP : ∀ a, M (act.act a) * P = P * ρ a := fun a => by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hPv]
    exact (hLρ a w).symm
  have hPdet : IsUnit P.det := by
    rw [hP, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' L
  have key : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R'), ∃ T' : (Fin D.g → R') → (epsPtR (spMap j) ⟶ A),
      Function.Injective T' ∧
      (∀ v : epsPtR (spMap j) ⟶ A, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
        (1 : Over.mk (spMap j) ⟶ A).left ↔ v ∈ Set.range T') ∧
      (∀ c c', T' (c + c') = T' c * T' c') ∧
      (∀ (s : R') c, (T' (s • c)).left = spMap (epsScaleR s) ≫ (T' c).left) ∧
      ∀ (a : D.O) c, T' c ≫ act.act a = T' ((ρ a).map j *ᵥ c) := by
    intro R' _ j
    obtain ⟨T, hinj, htan, hadd, hsc, hact⟩ := hT R' j
    have hu : IsUnit (P.map j) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have : (P.map j).det = j P.det := by rw [RingHom.map_det]; rfl
      rw [this]
      exact hPdet.map j
    have hinv : (P.map j)⁻¹ * P.map j = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
    have hPinj : Function.Injective (P.map j).mulVec := fun c c' h => by
      have := congrArg ((P.map j)⁻¹ *ᵥ ·) h
      simpa [Matrix.mulVec_mulVec, hinv] using this
    have hPsurj : Function.Surjective (P.map j).mulVec := Matrix.mulVec_surjective_iff_isUnit.2 hu
    refine ⟨fun c => T (P.map j *ᵥ c), hinj.comp hPinj, fun v => ?_, fun c c' => ?_, fun s c => ?_, fun a c => ?_⟩
    · rw [htan v]
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨c, rfl⟩ := hPsurj y
        exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
    · simp only [Matrix.mulVec_add, hadd]
    · simp only [Matrix.mulVec_smul, hsc]
    · simp only
      rw [hact _ (act.hom a), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, hMP]
  obtain ⟨E, hE1, hE2, hE3, hE4, hE5⟩ := GlobalTheory.T.lie_representation_spectral_projectors p D R b σ ρ hty
  have hroot : σ b.ρ ^ 2 - D.tr * σ b.ρ + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hne : σ b.ρ ≠ (D.tr : ℂ) - σ b.ρ := by
    intro h
    have h2 : (((D.tr ^ 2 - 4 * D.nm : ℤ)) : ℂ) = 0 := by
      push_cast
      linear_combination (2 * σ b.ρ - D.tr) * h - 4 * hroot
    have := D.disc_neg
    rw [Int.cast_eq_zero] at h2
    omega
  have hdist : ∀ i j, i ≠ j → ∃ c, (σ.comp (b.t i)) c ≠ (σ.comp (b.t j)) c := by
    intro i j hij
    by_contra hc
    push Not at hc
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub]
      exact sub_eq_zero.2 (hc x)
    rw [b.comax i j hij, top_le_iff] at hle
    have h1 : (1 : R) ∈ RingHom.ker σ := hle ▸ Submodule.mem_top
    simp at h1
  have hE5' : (σ b.ρ - ((D.tr : ℂ) - σ b.ρ)) • ∑ i, E i =
      (ρ.comp (algebraMap (𝓞 D.F) D.O)) D.ω - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
    rw [show σ b.ρ - ((D.tr : ℂ) - σ b.ρ) = 2 * σ b.ρ - D.tr by ring]
    exact hE5
  have hbc := GlobalTheory.SpecBC.baseChange_specDecomp D.g D.a D.m (𝓞 D.F) (ρ.comp (algebraMap (𝓞 D.F) D.O)) (fun i => σ.comp (b.t i)) D.ω
    (σ b.ρ) ((D.tr : ℂ) - σ b.ρ) E hne hdist hE1 hE2 hE3 hE4 hE5'
  have hpt : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β →
      ∃ j : ℂ →+* R', x = spMap j ∧ β = j.comp σ := by
    intro R' _ β x hx
    have hxj : x = spMap (Spec.preimage x).hom := by simp [spMap]
    generalize (Spec.preimage x).hom = j at hxj
    subst hxj
    refine ⟨j, rfl, ?_⟩
    have e1 : spMap (j.comp σ) = spMap j ≫ spMap σ := by
      simp [spMap, ← Spec.map_comp]
    rw [hx] at e1
    have := Spec.map_injective e1
    exact (congrArg CommRingCat.Hom.hom this).symm
  refine ⟨fun R' _ β x hx v hv => ?_, fun k _ _ x β hx i => ?_⟩
  · obtain ⟨j, rfl, rfl⟩ := hpt R' β x hx
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := key R' j
    exact GlobalTheory.LieCoordMult.tanScal_decomp D.O (𝓞 D.F) (Sp ℂ) A act R' (spMap j) D.g D.a T' (fun a => (ρ a).map j)
      (algebraMap (𝓞 D.F) D.O) D.ω ((j.comp σ) b.ρ) (fun i c => (j.comp σ) (b.t i c)) h1 h2 h3 h4 h5
      (fun y hy => hbc.1 R' j y hy) v hv
  · obtain ⟨j, rfl, rfl⟩ := hpt k β x hx
    obtain ⟨T', h1, h2, h3, h4, h5⟩ := key k j
    exact (GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig ℂ A (𝓞 D.F) (act.toF D) D.g k j T' (fun c => (ρ (algebraMap (𝓞 D.F) D.O c)).map j) h1 h2 h3 h4
      (fun a c => h5 _ c) ((j.comp σ).comp (b.t i)) D.m).2 (hbc.2 k j i (by simp only [RingHom.comp_apply, b.t_ω]))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieCondition_of_complexExp_intertwines_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension D.g A.hom → IsExp (𝟙 (Sp ℂ)) e → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → b.IsType σ ρ → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ) (β : R →+* k), x ≫ spMap σ = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  first | exact @GlobalTheory.UPel.HT.lie_of_complexExp | exact GlobalTheory.UPel.HT.lie_of_complexExp | (intros; apply GlobalTheory.UPel.HT.lie_of_complexExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Build

lemma exp_nsmul {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (hadd : ∀ z w, e (z + w) = e z * e w) (z : Fin g → ℂ) : ∀ n : ℕ, e (n • z) = e z ^ n := by
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this |>.symm ▸ rfl
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

lemma exists_nsmul_eq_of_dvd {La : Type} [AddCommGroup La] (EF E₁ : LinearMap.BilinForm ℤ La) (hE₁ : EF = (2:ℤ) • E₁)
    (e₀ : ℕ) (a : La) (k : ℕ) (hdv : ∀ y, (k : ℤ) ∣ E₁ a y) (nondeg : ∀ x, (∀ y, EF x y = 0) → x = 0)
    (hperf : ∀ f : La →ₗ[ℤ] ℤ, ∃ x, E₁ x = e₀ • f) : ∃ x', e₀ • a = k • x' := by
  let φ : La →ₗ[ℤ] ℤ :=
    { toFun := fun y => E₁ a y / k
      map_add' := fun u v => by
        rw [map_add (f := _)]; exact Int.add_ediv_of_dvd_left (hdv u)
      map_smul' := fun c u => by
        rw [map_zsmul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hdv u) }
  obtain ⟨x', hx''⟩ := hperf φ
  refine ⟨x', ?_⟩
  rw [← sub_eq_zero]
  apply nondeg
  intro y
  have hφ : E₁ x' y = e₀ * (E₁ a y / k) := by
    have := congrArg (fun F : La →ₗ[ℤ] ℤ => F y) hx''
    simpa [φ] using this
  have hm : (k : ℤ) * (E₁ a y / k) = E₁ a y := Int.mul_ediv_cancel' (hdv y)
  rw [hE₁]
  simp only [LinearMap.smul_apply, map_sub, map_nsmul, LinearMap.sub_apply, smul_eq_mul, nsmul_eq_mul, hφ]
  linear_combination (-2 * (e₀:ℤ)) * hm

lemma half_unique {La : Type} [AddCommGroup La] (E E' : LinearMap.BilinForm ℤ La) (h : (2:ℤ) • E = (2:ℤ) • E') :
    E = E' := by
  ext u v
  have h2 := congrArg (fun B : LinearMap.BilinForm ℤ La => B u v) h
  simp only [LinearMap.smul_apply, smul_eq_mul] at h2
  omega

end GlobalTheory.UPel.HT.Build


open GlobalTheory.UPel.HT.Build in
theorem GlobalTheory.UPel.HT.exists_obj_unifAt_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) t Q, 0 < N → N.Coprime p → b.IsType σ ρ → D.Cls N D' t → IsPeriod D' ρ Q → ∃ (o : Obj b N (spMap σ)) (h : _) (hL : _) (e : _), UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  intro p _ D R _ b N σ ρ D' t Q hN hNp htype hcls hper
  obtain ⟨hgen, E₁, hE₁, e₀, he₀p, hperf⟩ := hcls
  obtain ⟨A, _, _, act, P, e, hab, hdim, hP, r₁, r₂, hsy, ham, hexp, hker, hact, hweil⟩ :=
    GlobalTheory.T.exists_abelianVariety_of_halved_periodMap D.O D.inv D.g ρ D' Q E₁ hper hE₁
  have hadd := hexp.1
  have hsurj := hexp.2.1
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.T.lieCondition_of_complexExp_intertwines_action p D R b N σ ρ A act e hab hdim hexp hact htype
  have hgen' := hgen
  obtain ⟨f, ν, rfl, -, hf⟩ := hgen
  have hfN := hf N hN hNp
  let eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun a => e ((N : ℂ)⁻¹ • Q (f N a))
  have heta : ∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (f N a)) := fun a => Category.id_comp _
  have hsc : ∀ (c : D.O) (k : ℂ) (x : D'.La), e (k • Q (c • x)) = e (k • Q x) ≫ act.act c := by
    intro c k x
    rw [hper.1, ← Matrix.mulVec_smul, hact]
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQ1 : ∀ x, e (Q x) = 1 := fun x => (hker _).2 ⟨x, rfl⟩
  have hgeom := GlobalTheory.T.exists_primeToP_tateSimilitude_complexTorus p D N ρ A act _ D' (f N) Q e eta hN hNp hab (pull_isLB hP _) hgen' hper hadd hsurj hker
    hact hweil heta
  let o : Obj b N (spMap σ) :=
    { A := A
      ab := hab
      act := act
      P := P
      isLB := hP
      rig₁ := r₁
      rig₂ := r₂
      symm := hsy
      ample := ham
      kerP := ⟨e₀, he₀p, GlobalTheory.T.birigidified_bundle_kernel_killed_of_complex_points A D.g hab hdim P hP r₁ r₂ hsy ham e₀ (fun x hx => by
        obtain ⟨k, hk, hxk⟩ := GlobalTheory.T.exists_pow_eq_one_of_poincareKernel_complex A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1
          hper.2.2.2.1 hker hweil x hx
        obtain ⟨z, rfl⟩ := hsurj x
        have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        have h1 : e (k • z) = 1 := by rw [exp_nsmul e hadd]; exact hxk
        obtain ⟨a, ha⟩ := (hker _).1 h1
        have hz : z = (k : ℂ)⁻¹ • Q a := by
          rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk', one_smul]
        obtain ⟨E₁', hE₁', hdiv⟩ := GlobalTheory.T.diag_form_two_smul_and_ker_alt A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp
          hper.2.1 hker hweil
        have hx' : ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a))
            (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen := by
          rw [← hz]; exact hx
        have hdv : ∀ y, (k : ℤ) ∣ E₁' a y := (hdiv k a hk).2 hx'
        have hEE : E₁' = E₁ := half_unique _ _ (hE₁'.symm.trans hE₁)
        rw [hEE] at hdv
        obtain ⟨x', key⟩ := exists_nsmul_eq_of_dvd D'.EF E₁ hE₁ e₀ a k hdv D'.nondeg hperf
        have hQ : Q x' = e₀ • ((k : ℂ)⁻¹ • Q a) := by
          rw [smul_comm, ← map_nsmul, key, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk',
            one_smul]
        show e z ^ e₀ = 1
        rw [← exp_nsmul e hadd, hz, ← hQ]
        exact hQ1 x')⟩
      rosati := fun c => by
        refine (GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic A D.g hab hdim P hP r₁ r₂ hsy ham e D'.La Q D'.EF hexp hper.2.1 hker hweil
          (act.act c) (act.act (D.star c).unop) (AddMonoidHom.mk' (fun x => c • x) (smul_add c))
          (AddMonoidHom.mk' (fun x => (D.star c).unop • x) (smul_add _)) (act.hom c) (act.hom _)
          (fun k x _ => hsc c _ x) (fun k x _ => hsc _ _ x)).2 ?_
        intro x y
        exact D'.adj c x y
      lie := hlie
      lieRank := fun k _ _ x β hx i => hlieR k x β hx i
      eta := eta
      eta_add := fun x y => by
        show e _ = e _ * e _
        erw [map_add (f N) x y, map_add, smul_add, hadd]
        rfl
      eta_lin := fun c x => by
        obtain ⟨e', he'⟩ := hfN.2.1 c x
        show e _ = e _ ≫ _
        erw [he', map_add, smul_add, hadd, hsc, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1, _root_.mul_one]
      eta_ker := fun x => by
        show e _ = 1
        erw [map_nsmul (f N) N x, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hNz, one_smul, hQ1]
      geom := fun k _ _ x β _ => hgeom k x }
  refine ⟨o, hdim, pull_isLB hP _, e, ?_⟩
  refine ⟨Category.id_comp _, hper, hexp, hker, hact, hweil, heta⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylor_object_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) t Q, 0 < N → N.Coprime p → b.IsType σ ρ → D.Cls N D' t → IsPeriod D' ρ Q → ∃ (o : Obj b N (spMap σ)) (h : _) (hL : _) (e : _), UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  first | (exact @GlobalTheory.UPel.HT.exists_obj_unifAt_of_period) | (exact GlobalTheory.UPel.HT.exists_obj_unifAt_of_period) | (intros; apply GlobalTheory.UPel.HT.exists_obj_unifAt_of_period <;> assumption)
end
