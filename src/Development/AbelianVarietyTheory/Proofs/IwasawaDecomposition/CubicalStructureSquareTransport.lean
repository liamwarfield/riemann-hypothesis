module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RepresentativeImagePointOfLift
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalStructureSquareTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalStructureSquareTransport
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqCube

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.LamBiext

section Transport

variable {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']

theorem transport (hG : GlobalFnsSt) (hA' : IsAbelianScheme A') (Φ : A' ⟶ A) [IsMonHom Φ]
    {M : LB A.left} {M' : LB A'.left} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (M.pull Φ.left)) (hw : w.IsGen)
    (c : LB.Gen (LB.LinComb M (thφ A (x3 A)) thε)) (c' : LB.Gen (LB.LinComb M' (thφ A' (x3 A')) thε))
    (hc : c.IsGen) (hc' : c'.IsGen)
    (n : ∀ (y : (𝟙_ (Over S)).left) J, Good M y J →
      val c (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J = 1)
    (n' : ∀ (y : (𝟙_ (Over S)).left) J, Good M' y J →
      val c' (lift (1 : 𝟙_ (Over S) ⟶ A') (lift 1 1)).left y J = 1)
    {T : Over S} {z : T.left} {J J'} (hJ : Good M z J) (hJ' : Good M' z J') (x x' y : T ⟶ A') :
    val c (lift (x ≫ Φ) (lift (x' ≫ Φ) (y ≫ Φ))).left z J =
      (∏ I : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) z
        (J (((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) ≫ Φ.left))
        (J' ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I)) ^ thε I) * val c' (lift x (lift x' y)).left z J' := by
  let m3 : G3 A' ⟶ G3 A := lift (x3 A' 0 ≫ Φ) (lift (x3 A' 1 ≫ Φ) (x3 A' 2 ≫ Φ))
  let β : (G3 A' ⟶ A') →* (G3 A' ⟶ A) := MonoidHom.mk' (· ≫ Φ) fun a b => MonObj.mul_comp a b Φ
  have hx : ∀ i, m3 ≫ x3 A i = x3 A' i ≫ Φ := fun i => by fin_cases i <;> simp [m3, x3]
  have comm : ∀ I : thK.{0}, m3.left ≫ thφ A (x3 A) I = thφ A' (x3 A') I ≫ Φ.left := fun I => by
    have e : m3 ≫ psum A (x3 A) I.down = psum A' (x3 A') I.down ≫ Φ :=
      (psum_hom (Geo.Tor.preHom m3) (x3 A) I.down).trans ((congrArg (fun q => psum A q I.down) (funext hx)).trans
        (psum_hom β (x3 A') I.down).symm)
    exact congrArg (fun q => q.left) e
  have q : ∀ {T : Over S} (a b d : T ⟶ A'),
      (lift a (lift b d)).left ≫ m3.left = (lift (a ≫ Φ) (lift (b ≫ Φ) (d ≫ Φ))).left := fun a b d => by
    rw [← Over.comp_left]; congr 1; simp [m3, x3]
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hM hM' c' hc'
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 A').left) (z : Z) J J', Good M z J → Good M' z J' →
      val t r z J = (∏ I : thK.{0}, gw w (r ≫ thφ A' (x3 A') I) z
        (J ((r ≫ thφ A' (x3 A') I) ≫ Φ.left)) (J' (r ≫ thφ A' (x3 A') I)) ^ thε I) * val c' r z J' :=
    fun Z r z J J' hJ hJ' => by
      refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans
        (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
      rw [Category.assoc]
  let e : 𝟙_ (Over S) ⟶ G3 A' := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd A' (A' ⊗ A')).left ≫ (snd A' A').left ≫ A'.hom).appTop.hom :=
    surj_comp (surj_snd hG hA' _) (surj_comp (surj_snd hG hA' _) (hG _ _ hA').2)
  have he : e.left ≫ (snd A' (A' ⊗ A')).left ≫ (snd A' A').left ≫ A'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' hM (φ := fun I => m3.left ≫ thφ A (x3 A) I) (ε := thε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) (comm I).symm)
    _ e.left he sj (pullGen_isGen _ _ _ _ hc m3.left) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over S)).left ⟶ A'.left => exists_chart hM' (χ y)
      have p := prod_cub (1 : 𝟙_ (Over S) ⟶ A') 1 1 (fun q => gw w q y (I (q ≫ Φ.left)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (n' y I' hI'))).symm
      rw [val_pull hI, q, MonObj.one_comp, n y I hI]
      simp) _ (lift x (lift x' y)).left z J hJ
  rw [val_pull hJ, q] at key
  exact key.trans (hv' _ _ z J J' hJ hJ')

end Transport

section Chart

variable {X Y : Scheme.{0}} {L : LB X}

theorem good_sq {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    Good (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) y (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => by simpa using hJ ψ

theorem adj_sq (hL : L.IsLB) {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (χ : Y ⟶ X) :
    adj (fun _ : Fin 1 => 𝟙 X) (fun _ => (2 : ℤ)) y (fun q _ => J q) J χ = 1 := by
  have m := hJ.mem (fun _ : Fin 1 => 𝟙 X) χ
  simp only [Category.comp_id] at m
  unfold adj
  simp only [Category.comp_id]
  exact trF_self hL _ _ χ y m

end Chart

section Square

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem sq_formEq : FormEq (Sum.elim (thφ G (x3 G)) (thφ G (x3 G))) (Sum.elim thε thε)
    (flatφ (fun _ : Fin 1 => 𝟙 G.left) (thφ G (x3 G))) (flatε (fun _ : Fin 1 => (2 : ℤ)) thε) := fun U _ h => by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, flatφ, flatε, Category.comp_id]
  rw [zpow_mul, zpow_two]

theorem exists_sqCube {L : RigLB G} (c : CubicalStr G L) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (thφ G (x3 G)) thε),
      u.IsGen ∧ (∀ {T : Over S} (y : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L y J →
        ∀ (JP : (T.left ⟶ G.left) → Fin 1 → L.L.ι), Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        ∀ a b d : T ⟶ G, val u (lift a (lift b d)).left y JP =
          (∏ I : thK.{0}, adj (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2) y JP J ((lift a (lift b d)).left ≫ thφ G (x3 G) I) ^ thε I) *
            cubV c y J a b d ^ 2) ∧
      ∀ (y : (𝟙_ (Over S)).left) JP, Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        val u (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left y JP = 1 := by
  obtain ⟨s, hs, hv⟩ := exists_gen L.isLB sq_formEq (LB.mulGen L.L (thφ G (x3 G)) thε (thφ G (x3 G)) thε c.t c.t)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ c.isGen c.isGen)
  have F : ∀ {T : Over S} (y : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L y J →
        ∀ (JP : (T.left ⟶ G.left) → Fin 1 → L.L.ι), Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        ∀ a b d : T ⟶ G, val (nest L.L _ _ _ _ s) (lift a (lift b d)).left y JP =
          (∏ I : thK.{0}, adj (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2) y JP J ((lift a (lift b d)).left ≫ thφ G (x3 G) I) ^ thε I) *
            cubV c y J a b d ^ 2 := fun y J hJ JP hJP a b d => by
    rw [val_nest hs _ hJP hJ, hv _ _ y J hJ]
    exact congrArg _ ((val_mul hJ _ _ _).trans (sq _).symm)
  refine ⟨nest L.L _ _ _ _ s, nest_isGen hs, F, fun y JP hJP => ?_⟩
  choose J hJ using fun χ : (𝟙_ (Over S)).left ⟶ G.left => exists_chart L.isLB (χ y)
  change ((𝟙_ (Over S)).left ⟶ G.left) → Fin 1 → L.L.ι at JP
  set_option backward.isDefEq.respectTransparency false in
  have hcub : cubV c y J (1 : 𝟙_ (Over S) ⟶ G) 1 1 = 1 :=
    by
      have h := val_corr hJ (c.face 0) (lift (1 : 𝟙_ (Over S) ⟶ G) 1).left
      rw [val_one, val_pull hJ _ _ _, ← Over.comp_left] at h
      convert h using 1 <;> simp [cubV, faceMap, x2, pzero, Hom.one_def]
  rw [F y J hJ JP hJP]
  rw [prod_cub, hcub]
  simp

end Square

end GlobalTheory.SqCube

theorem GlobalTheory.cube_sq_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2 := by
  intro R _ _ _ _ D D' Φ w hw hΦ T z J J' hJ hJ' Ω hΩ a b c
  subst hΩ
  obtain ⟨u, hu, hvu, nu⟩ := GlobalTheory.SqCube.exists_sqCube D.toPre.cub
  obtain ⟨u', hu', hvu', nu'⟩ := GlobalTheory.SqCube.exists_sqCube D'.toPre.cub
  have key := GlobalTheory.SqCube.transport GlobalTheory.globalFns_holds D'.toPre.P.isAb Φ.hom
    (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (DVR.linComb_isLB _ D'.toPre.P.isLB _ _) w hw u u' hu hu' nu nu'
    (GlobalTheory.SqCube.good_sq hJ) (GlobalTheory.SqCube.good_sq hJ') a b c
  rw [hvu z J hJ _ (GlobalTheory.SqCube.good_sq hJ), hvu' z J' hJ' _ (GlobalTheory.SqCube.good_sq hJ')] at key
  simp only [GlobalTheory.SqCube.adj_sq D.toPre.P.isLB hJ, GlobalTheory.SqCube.adj_sq D'.toPre.P.isLB hJ', one_zpow,
    Finset.prod_const_one, _root_.one_mul] at key
  refine key.trans ?_
  rw [prod_cub a b c (fun q => gw w q z (fun _ => J (q ≫ Φ.hom.left)) (fun _ => J' q))]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CubicalStructureSquareTransportStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalStructure_square_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2 := by
  first | exact @GlobalTheory.cube_sq_transport | exact GlobalTheory.cube_sq_transport | (intros; apply GlobalTheory.cube_sq_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsBaseLevelLiftReadAtBaseEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftForms

theorem exists_mat {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n n' : ℕ} (hn : n = n')
    (V : Submodule K (Fin n → K)) (V' : Submodule K' (Fin n' → K'))
    (hV : V' = Submodule.span K' {x' | ∃ x ∈ V, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    ∃ G : Matrix (Fin (Module.finrank K' V')) (Fin (Module.finrank K V)) K', Function.Bijective G.mulVec ∧
      ∀ y : Fin (Module.finrank K V) → K, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' →
        (∑ l, (G.mulVec (fun i => φ (y i))) l • (Module.finBasis K' V' l : Fin n' → K')) k' =
          φ ((∑ i, y i • (Module.finBasis K V i : Fin n → K)) k) := by
  subst hn
  classical
  set b := Module.finBasis K V
  set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ
  have hrel : ∀ x' : Fin n → K', ∀ x : Fin n → K, (∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)) ↔ x' = Φ x := by
    intro x' x
    constructor
    · intro h; funext k; exact h k k rfl
    · rintro rfl k k' hk; rw [Fin.ext hk]
  have hS : {x' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = Φ '' V := by
    ext x'; simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, ((hrel x' x).1 h).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (hrel _ x).2 rfl⟩
  rw [hS] at hV
  have hΦadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y => by funext k; simp [hΦ]
  have hΦsmul : ∀ (a : K) x, Φ (a • x) = φ a • Φ x := fun a x => by funext k; simp [hΦ]
  have hΦsum : ∀ y : Fin (Module.finrank K V) → K, Φ (∑ i, y i • (b i : Fin n → K)) = ∑ i, φ (y i) • Φ (b i) := by
    intro y
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hΦ, Finset.sum_apply, map_sum]
  let c : Fin (Module.finrank K V) → Fin n → K' := fun i => Φ (b i)
  have hc_mem : ∀ i, c i ∈ V' := fun i => hV ▸ Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  have hli : LinearIndependent K' c := by
    letI := φ.toAlgebra
    have h0 : LinearIndependent K (fun i => (b i : Fin n → K)) := b.linearIndependent.map' V.subtype V.ker_subtype
    exact (linearIndependent_algebraMap_comp_iff).2 h0
  have hspan : Submodule.span K' (Set.range c) = V' := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hc_mem i
    · rw [hV, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (⟨x, hx⟩ : V) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
      have hx2 : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Fin n → K) := by
        have := congrArg Subtype.val hx'
        rw [Submodule.coe_sum] at this
        simpa only [Submodule.coe_smul] using this
      rw [hx2, hΦsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let cV : Fin (Module.finrank K V) → V' := fun i => ⟨c i, hc_mem i⟩
  have hliV : LinearIndependent K' cV := LinearIndependent.of_comp V'.subtype hli
  have hspV : ⊤ ≤ Submodule.span K' (Set.range cV) := by
    rintro ⟨x, hx⟩ _
    rw [← hspan] at hx
    have : Set.range c = V'.subtype '' Set.range cV := by
      ext z; simp [cV, c]
    rw [this, ← Submodule.map_span] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have : w = ⟨x, hspan ▸ (by rw [this, ← Submodule.map_span]; exact ⟨w, hw, hwx⟩)⟩ := Subtype.ext hwx
    rw [← this]; exact hw
  let bc : Module.Basis (Fin (Module.finrank K V)) K' V' := Module.Basis.mk hliV hspV
  set b' := Module.finBasis K' V'
  refine ⟨Matrix.of fun l i => b'.repr (bc i) l, ?_, ?_⟩
  · have hG : (Matrix.of fun l i => b'.repr (bc i) l).mulVec = fun y => b'.equivFun (bc.equivFun.symm y) := by
      funext y l
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, map_sum, mul_comm]
    rw [hG]
    exact b'.equivFun.bijective.comp bc.equivFun.symm.bijective
  · intro y k k' hk
    rw [← Fin.ext hk]
    have e1 : (∑ l, ((Matrix.of fun l i => b'.repr (bc i) l).mulVec (fun i => φ (y i))) l • (b' l : Fin n → K')) =
        ((∑ i, φ (y i) • bc i : V') : Fin n → K') := by
      have : ∑ l, ((Matrix.of fun l i => b'.repr (bc i) l).mulVec (fun i => φ (y i))) l • b' l = ∑ i, φ (y i) • bc i := by
        rw [← b'.sum_repr (∑ i, φ (y i) • bc i)]
        congr 1; funext l; congr 1
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
      have := congrArg Subtype.val this
      simpa [Submodule.coe_sum] using this
    rw [e1]
    have e2 : ((∑ i, φ (y i) • bc i : V') : Fin n → K') = ∑ i, φ (y i) • c i := by
      simp [Submodule.coe_sum, bc, cV]
    rw [e2, ← hΦsum]

theorem lat_coords {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K') {n n' d d' : ℕ}
    (hn : n = n') (b : Fin d → Fin n → K) (b' : Fin d' → Fin n' → K') (hb' : LinearIndependent K' b')
    (G : Matrix (Fin d') (Fin d) K')
    (hG : ∀ y : Fin d → K, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' →
        (∑ l, (G.mulVec (fun i => φ (y i))) l • b' l) k' = φ ((∑ i, y i • b i) k))
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : ∀ x ∈ M, x ∈ Submodule.span K (Set.range b))
    (M' : Submodule (𝓞 K') (Fin n' → K'))
    (hM' : M' = Submodule.span (𝓞 K') {x' | ∃ x ∈ M, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    M'.comap ((Fintype.linearCombination K' b').restrictScalars (𝓞 K')) =
      Submodule.span (𝓞 K') ((fun y : Fin d → K => G.mulVec fun i => φ (y i)) ''
        (M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) : Set (Fin d → K))) := by
  subst hn
  set L' := (Fintype.linearCombination K' b').restrictScalars (𝓞 K') with hL'
  have hL'apply : ∀ c, L' c = ∑ l, c l • b' l := fun c => by
    simp [hL', Fintype.linearCombination_apply]
  have key : ∀ y : Fin d → K, L' (G.mulVec fun i => φ (y i)) = fun k => φ ((∑ i, y i • b i) k) := by
    intro y; funext k; rw [hL'apply]; exact hG y k k rfl
  have hinj : Function.Injective L' := by
    intro c₁ c₂ h
    rw [hL'apply, hL'apply] at h
    have h0 : ∑ l, (c₁ - c₂) l • b' l = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext l
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb' _ h0 l)
  apply le_antisymm
  · intro c hc
    have hc' : L' c ∈ M' := hc
    have hle : M' ≤ (Submodule.span (𝓞 K') ((fun y : Fin d → K => G.mulVec fun i => φ (y i)) ''
        (M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) : Set (Fin d → K)))).map L' := by
      rw [hM', Submodule.span_le]
      rintro x' ⟨x, hx, hrel⟩
      obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hM x hx)
      have hyM : y ∈ M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) := by
        show (Fintype.linearCombination K b) y ∈ M
        rw [Fintype.linearCombination_apply, hy]; exact hx
      have : x' = L' (G.mulVec fun i => φ (y i)) := by
        rw [key y, hy]; funext k; exact hrel k k rfl
      rw [this]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, hyM, rfl⟩)
    obtain ⟨e, he, hec⟩ := hle hc'
    rw [← hinj hec]; exact he
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show L' (G.mulVec fun i => φ (y i)) ∈ M'
    rw [hM', key y]
    refine Submodule.subset_span ⟨∑ i, y i • b i, ?_, fun k k' hk => by rw [Fin.ext hk]⟩
    have : (Fintype.linearCombination K b) y ∈ M := hy
    rwa [Fintype.linearCombination_apply] at this

theorem complexPoints_baseLevelLift_readAtBaseEmbedding {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m)
    (y : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) :
    @Tw.out (twAt D.what₂.embLL A3.A.v0) _ ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y)) =
      (R.FW i).j (sg0 D A3.A) (∑ k, y k • R.toRealDat.bL F.lv2 false i k) := by
  have hpos : (0:ℝ) < RealDat.nP F.lv2 false := by
    unfold RealDat.nP; exact_mod_cast Nat.card_pos
  set s := twAt D.what₂.embLL A3.A.v0
  set WS := R.toRealDat.WS F.lv2 false i (sg0 D A3.A)
  have h2 : (@Tw.out s WS ((R.toCx3 F).wC false i A3.fam3.base3.v0 (cpt A3.fam3.base3.v0.embedding y))) =
      ∑ k, cj s (cpt A3.fam3.base3.v0.embedding y k) • (⟨R.toRealDat.bC F.lv2 false i (sg0 D A3.A) k, Submodule.subset_span ⟨k, rfl⟩⟩ : WS) := by
    simp only [CxData.wC, lin, Fintype.linearCombination_apply]
    rfl
  have h1 : ∀ x : Tw s WS, @Tw.out s _ ((R.toCx3 F).eW false i x) = (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) • ((Tw.out x : WS) : (R.HW i (sg0 D A3.A)).H) := fun x => rfl
  refine Eq.trans (h1 ((R.toCx3 F).wC false i A3.fam3.base3.v0 (cpt A3.fam3.base3.v0.embedding y))) ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, Submodule.coe_sum, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, map_smulₛₗ, smul_comm]
  have he : cj s (cpt A3.fam3.base3.v0.embedding y k) = sg0 D A3.A (y k) := by
    show cj s (A3.A.v0.embedding (y k)) = _
    rw [emb_eq D.what₂.embLL A3.A.v0 (y k), cj_cj]
  rw [he]
  congr 1
  show ((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ) • ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 false i k)) = _
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 hpos).ne', Complex.ofReal_one, one_smul]

theorem liftWeight_complexPoint_eq_twist {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m)
    (y : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) :
    HEq ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y))
      ((R.FW i).j D.what₂.embLL (∑ k, y k • R.toRealDat.bL F.lv2 false i k)) := by
  have e := complexPoints_baseLevelLift_readAtBaseEmbedding R F i y
  have hs : sg0 D A3.A = D.what₂.embLL := sgAt_mk _ R.hv0
  have key : ∀ (σ σ' : D.what₂.LL →+* ℂ), σ = σ' → ∀ v, HEq ((R.FW i).j σ v) ((R.FW i).j σ' v) := by
    intro σ σ' h v; subst h; rfl
  show HEq (@Tw.out (twAt D.what₂.embLL A3.A.v0) _ ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y))) _
  rw [e]
  exact key _ _ hs _

theorem nat_eq_of_heq {m m' : ℕ} (hm : m' = m) {f : Fin m → ℕ} {f' : Fin m' → ℕ} (h : HEq f' f) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') : f i = f' i' := by
  subst hm
  have := eq_of_heq h
  subst this
  rw [Fin.ext hi]

theorem mem_span_basis {K : Type} [Field K] {n : ℕ} (V : Submodule K (Fin n → K)) [Module.Finite K V] {x : Fin n → K}
    (hx : x ∈ V) : x ∈ Submodule.span K (Set.range fun k => (Module.finBasis K V k : Fin n → K)) := by
  have hx' : (⟨x, hx⟩ : V) = ∑ i, ((Module.finBasis K V).repr ⟨x, hx⟩ i) • Module.finBasis K V i := ((Module.finBasis K V).sum_repr _).symm
  have hx2 : x = ∑ i, ((Module.finBasis K V).repr ⟨x, hx⟩ i) • (Module.finBasis K V i : Fin n → K) := by
    have := congrArg Subtype.val hx'
    rw [Submodule.coe_sum] at this
    simpa only [Submodule.coe_smul] using this
  rw [hx2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.Mem.R3.LiftForms

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacter
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem exists_glint_of_rat [NeZero n] (P : HeightOneSpectrum (𝓞 E)) {z : GL (Fin n) (AfE F E)} (hz : z ∈ St (1 : GL (Fin n) (AfE F E)))
    (hr : ∀ i j, ∃ e : E, adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ e) :
    ∃ c : GLint E n P, (∀ i j, adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (c.1 (Pi.single j 1) i)) ∧
      GlobalTheory.TopStep.redGL n P c = redAt 1 P ⟨z, hz⟩ := by
  classical
  obtain ⟨y, hy, hyr⟩ := St_one_int hz
  obtain ⟨y', hy', -⟩ := St_one_int (inv_mem hz)
  choose A hA using hr
  have hmap : (z : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) = (Matrix.of A).map (algebraMap E (P.adicCompletion E)) :=
    Matrix.ext fun i j => hA i j
  have hdet : IsUnit (Matrix.of A).det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h1 := congrArg Matrix.det hmap
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det, h0, map_zero] at h1
    have hu : IsUnit (z : Matrix (Fin n) (Fin n) (AfE F E)).det := (Matrix.isUnit_iff_isUnit_det _).1 z.isUnit
    exact (hu.map (adAt F P)).ne_zero h1
  set γ : GL (Fin n) E := Matrix.nonsingInvUnit (Matrix.of A) hdet with hγ
  have hzγ : ∀ r s, adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E _ ((γ : Matrix (Fin n) (Fin n) E) r s) :=
    fun r s => hA r s
  have hzγ' := GlobalTheory.Mem.Col2.RatFrPt.adAt_inv hzγ
  have hint : ∀ {x : AfE F E} {e : E}, x ∈ RInt F E → adAt F P x = algebraMap E _ e → IntAt P e := fun {x e} hx he => by
    rw [GlobalTheory.CharValCompare.intAt_iff, ← valued_algebraMap, ← he]
    exact (mem_rInt_iff F E x).1 hx P
  have h1 : ∀ i j, IntAt P ((γ : Matrix (Fin n) (Fin n) E) i j) := fun i j => hint (hy i j ▸ (y i j).2) (hzγ i j)
  have h2 : ∀ i j, IntAt P (((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j) := fun i j => hint (hy' i j ▸ (y' i j).2) (hzγ' i j)
  have hmv : ∀ (N : Matrix (Fin n) (Fin n) E), (∀ i j, IntAt P (N i j)) → ∀ x : Sp E n, x ∈ stdAt E n P → N *ᵥ x ∈ stdAt E n P :=
    fun N hN x hx => GlobalTheory.TopStep.mem_stdAt.2 fun i => by
      show IntAt P (∑ j, N i j * x j)
      exact GlobalTheory.TopStep.intAt_sum _ fun j _ => (hN i j).mul (GlobalTheory.TopStep.mem_stdAt.1 hx j)
  have hc : GlobalTheory.Mem.Col2.RatFrPt.glEquiv γ ∈ GLint E n P := fun x => by
    rw [GlobalTheory.Mem.Col2.RatFrPt.glEquiv_apply]
    refine ⟨fun h => ?_, hmv _ h1 x⟩
    have := hmv _ h2 _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  refine ⟨⟨_, hc⟩, fun i j => ?_, Units.ext (Matrix.ext fun i j => ?_)⟩
  · rw [hzγ, GlobalTheory.Mem.Col2.RatFrPt.glEquiv_single]
  · have hR := GlobalTheory.Mem.Col2.LevLiftPt.isRed_of_red P _ hc _ (fun x hx => GlobalTheory.TopStep.redV_apply ⟨_, hc⟩ hx) z
      (fun r s => by rw [LinearMap.toMatrix'_apply, hzγ]; congr 1; exact (GlobalTheory.Mem.Col2.RatFrPt.glEquiv_single γ r s).symm) i j
    refine hR.unique ?_
    rw [hyr P i j, hy i j]
    have := GlobalTheory.Mem.Col2.PtExist.hasRes_redA (F := F) P (y i j).2
    rwa [redA_int P (y i j).2] at this

theorem isPtOf_mul_rat [NeZero n] {hcm : CMData F E} {SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g z : GL (Fin n) (AfE F E)}
    {p : DecoF E n ∅ SG Q} (hg : IsPtOf hcm g p) (hzU : z ∈ UAd hcm n) (hz : z ∈ St (1 : GL (Fin n) (AfE F E))) (c : GLQ E n Q)
    (hcz : ∀ (P : Q) i j, adAt F P.1 ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ ((c P).1 (Pi.single j 1) i)) :
    IsPtOf hcm (g * z) (((1, (fun w : SG => redAt 1 w.1 ⟨z, hz⟩)⁻¹, c⁻¹) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) := by
  have hInt : ∀ {x : GL (Fin n) (AfE F E)} (hx : x ∈ St (1 : GL (Fin n) (AfE F E))) (i j : Fin n),
      (x : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ∀ w : HeightOneSpectrum (𝓞 E),
        HasRes w (adAt F w ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j))
          (((redAt 1 w ⟨x, hx⟩ : GL (Fin n) (𝓞 E ⧸ w.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.asIdeal)) i j) := by
    intro x hx i j
    obtain ⟨y, hy, hr⟩ := St_one_int hx
    refine ⟨hy i j ▸ (y i j).2, fun w => ?_⟩
    rw [hr w i j, hy i j]
    have := GlobalTheory.Mem.Col2.PtExist.hasRes_redA (F := F) w (y i j).2
    rwa [redA_int w (y i j).2] at this
  have hzi : z⁻¹ ∈ St (1 : GL (Fin n) (AfE F E)) := inv_mem hz
  have hm := GlobalTheory.Mem.Col2.LevLiftPt.isPtOf_mul_fr (m := z⁻¹) hg (inv_mem hzU) (fun i j => (hInt hzi i j).1)
    (fun i j => by rw [inv_inv]; exact (hInt hz i j).1) (fun P hP => absurd hP (Finset.notMem_empty P))
    (h := (fun w : SG => redAt 1 w.1 ⟨z, hz⟩)⁻¹) (fun w i j => ?_) c⁻¹ (fun P i j => ?_)
  · rwa [inv_inv] at hm
  · have e : ((fun w : SG => redAt 1 w.1 ⟨z, hz⟩)⁻¹ w) = redAt 1 w.1 ⟨z⁻¹, hzi⟩ := by
      rw [Pi.inv_apply, ← map_inv]
      rfl
    rw [e]
    exact (hInt hzi i j).2 w.1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [inv_inv, Pi.inv_apply, inv_inv, Units.val_mul, Matrix.mul_apply, map_sum]
    have e : ∀ x, adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i x * (z : Matrix (Fin n) (Fin n) (AfE F E)) x j) =
        algebraMap E (P.1.adicCompletion E) (p.fr P (Pi.single x 1) i * (c P).1 (Pi.single j 1) x) := fun x => by
      rw [map_mul, map_mul, hg.fr P, hcz P]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun x _ => e x, ← map_sum]
    refine congrArg (algebraMap E (P.1.adicCompletion E)) ?_
    show _ = (p.fr P) ((c P).1 (Pi.single j 1)) i
    exact (Finset.sum_congr rfl fun k _ => mul_comm _ _).trans (GlobalTheory.TopStep.apply_eq_sum (p.fr P).toLinearMap _ i).symm

theorem glq_free {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {p : DecoF E n ST SG Q} {a b : GLG (E := E) (n := n) (SG := SG)} {c d : GLQ E n Q}
    (h : ((1, a, c) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = ((1, b, d) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) : c = d := by
  funext P
  have e := congrArg (fun q : DecoF E n ST SG Q => q.fr P) h
  change (1 : UF E n).1 * p.1.2 P * ((c P)⁻¹).1 = (1 : UF E n).1 * p.1.2 P * ((d P)⁻¹).1 at e
  exact inv_injective (Subtype.ext (mul_left_cancel e))

end Gen

section Blocks

variable {κ : Type} [CommRing κ] {n r b : ℕ}

theorem coarseBlockIndex_eq_twoBlock (hn : n = r + b) : (fun i : Fin n => coarse r [b] i.val) = Formalism.L2.DIV.blk2 r := by
  funext i
  unfold Formalism.L2.DIV.blk2
  by_cases hi : i.val < r
  · rw [if_pos hi, coarse_of_lt hi]
  · rw [if_neg hi, coarse_of_le (Nat.not_lt.mp hi)]
    have : i.val - r < b := by have := i.2; omega
    simp [blkIdx, this]

theorem mem_HQ_iff (hn : n = r + b) (M : GL (Fin n) κ) : M ∈ HQ κ n r b ↔ M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  show (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i : Fin n => coarse r [b] i.val) ↔
    (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (Formalism.L2.DIV.blk2 r)
  rw [coarseBlockIndex_eq_twoBlock hn]

theorem blkDet_HQ (hn : n = r + b) (M : GL (Fin n) κ) (h1 : M ∈ HQ κ n r b) (h2 : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    Formalism.L2.Col.blkDet n κ (coarse r [b]) 1 ⟨M, h1⟩ = Formalism.L2.DIV.blkDet (Formalism.L2.DIV.blk2 r) 1 ⟨M, h2⟩ := by
  apply Units.ext
  rw [Formalism.L2.Col.blkDet_val]
  have : ∀ β : Fin n → ℕ, β = Formalism.L2.DIV.blk2 r → ((M : Matrix (Fin n) (Fin n) κ).toSquareBlock β 1).det =
      ((M : Matrix (Fin n) (Fin n) κ).submatrix (Subtype.val : {a : Fin n // Formalism.L2.DIV.blk2 r a = 1} → Fin n) Subtype.val).det := by
    rintro _ rfl
    rfl
  exact this _ (coarseBlockIndex_eq_twoBlock hn)

end Blocks

section Chr

variable {X : Fields} {n : ℕ} {SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem chr_inv_val (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (emb : X.K →+* ℂ) (h : Λ.grp) (c : Θ.grp) :
    emb ((Λ.chr h⁻¹ * Θ.chr c⁻¹ : X.Kˣ) : X.K) =
      (∏ w, (emb (((Λ w).lam ⟨h.1 w, h.2 w (Set.mem_univ w)⟩ : X.Kˣ) : X.K))⁻¹) *
        ∏ P, (emb (((Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ : X.Kˣ) : X.K))⁻¹ := by
  have hc : (Θ.chr c : X.Kˣ) = ∏ P, (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ := by
    rw [LevQFam.chr]
    exact piChar_apply _ _ c
  rw [map_inv, map_inv, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀,
    LevFam.chr_apply, hc, Units.coe_prod, map_prod, Finset.prod_inv_distrib, Units.coe_prod, map_prod, Finset.prod_inv_distrib]

variable {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Formalism.L2.DIV.Tup X.F X.E X.K S}

theorem levQX_lam_inv (emb : X.K →+* ℂ) (hn : R.N R.m - 1 = R.r + R.m * R.t) (P : QE sel (mu : Chr X.F X.E X.K))
    (k : (levQX R sel mu P).H) (hk : GlobalTheory.TopStep.redGL _ P.1 k.1 ∈ blockTri (blk2 R.r)) :
    (emb (((levQX R sel mu P).lam k : X.Kˣ) : X.K))⁻¹ =
      emb ((resChar (mu : Chr X.F X.E X.K) P.1 (Formalism.L2.DIV.blkDet (blk2 R.r) 1 ⟨_, hk⟩) : X.Kˣ) : X.K) := by
  rw [levQX_lam]
  change (emb (((lamQP (mu : Chr X.F X.E X.K) P.1 (R.N R.m - 1) R.r (R.m * R.t))⁻¹ ⟨_, k.2⟩ : X.Kˣ) : X.K))⁻¹ = _
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, inv_inv, lamQP, lamQ_apply]
  exact congrArg (fun d => emb ((resChar (mu : Chr X.F X.E X.K) P.1 d : X.Kˣ) : X.K)) (blkDet_HQ hn _ _ hk)

end Chr

set_option maxHeartbeats 2000000 in
theorem rdLevOn_reads_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}, I.ReadsP a S.Lb S.U S.chi y lat st → ∀ (_c : (I.stX a).Cl) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ),
    (∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL)) →
    RdLevOn (E := B.fields.E) B.sp.cm (RatAt (I.Q a)) S.U S.chi (rowTyG I.Ch I.Ps) B.embLL (I.Q a)
      (fun _ => blockTri (blk2 B.R.r)) (fun P => (ξ P.1).comp (blkDet (blk2 B.R.r) 1)) := by
  intro B X I hOk hPins l Z a bad S y lat st h c ξ hξ z hzA hz hzU
  have hn : B.R.N B.R.m - 1 = B.R.r + B.R.m * B.R.t := Formalism.L2.Col.rank_X'_eq B.R
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  choose cc hcc hred using fun P : I.Q a => exists_glint_of_rat (F := B.host.F) P.1 hz (hzA P)
  have hpt := isPtOf_mul_rat (h.pt c) hzU hz (cc : GLQ B.fields.E (B.R.N B.R.m - 1) (I.Q a)) hcc
  set hv : GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) := fun w => redAt 1 w.1 ⟨z, hz⟩ with hhv
  have hΘ : ∀ P : I.Q a, cc P ∈ (levQX B.R I.sel (I.tup a) P).H ↔ redAt 1 P.1 ⟨z, hz⟩ ∈ blockTri (blk2 B.R.r) := fun P => by
    show GlobalTheory.TopStep.redGL _ P.1 (cc P) ∈ HQ _ _ B.R.r (B.R.m * B.R.t) ↔ _
    rw [hred P]
    exact mem_HQ_iff hn _
  refine ⟨(h.lev c z _ hpt).trans ⟨?_, ?_⟩, fun hU h1 h2 => ?_⟩
  · rintro ⟨⟨γ, a', c'⟩, hγ, e⟩
    obtain rfl : γ = 1 := Subtype.ext ((toGLm _ _).injective (hγ.trans (map_one _).symm))
    have e1 : a'.1 = hv⁻¹ := glg_free e
    have e2 : c'.1 = cc⁻¹ := glq_free e
    refine ⟨fun w => ?_, fun P => (hΘ P).1 ?_⟩
    · have := a'.2 w (Set.mem_univ w)
      rw [e1] at this
      exact inv_mem_iff.1 this
    · have := c'.2 P (Set.mem_univ P)
      rw [e2] at this
      exact inv_mem_iff.1 this
  · rintro ⟨h1, h2⟩
    exact ⟨(1, (⟨hv, fun w _ => h1 w⟩ : (rowTyG I.Ch I.Ps).grp)⁻¹,
      (⟨cc, fun P _ => (hΘ P).2 (h2 P)⟩ : (levQX B.R I.sel (I.tup a)).grp)⁻¹), by show ufGL _ _ 1 = 1; exact map_one _, rfl⟩
  · have hΛ : hv ∈ (rowTyG I.Ch I.Ps).grp := fun w _ => h1 w
    have hQ : cc ∈ (levQX B.R I.sel (I.tup a)).grp := fun P _ => (hΘ P).2 (h2 P)
    have key := h.chr c ⟨z, hU⟩ (1, (⟨hv, hΛ⟩ : (rowTyG I.Ch I.Ps).grp)⁻¹, (⟨cc, hQ⟩ : (levQX B.R I.sel (I.tup a)).grp)⁻¹)
      (by show ufGL _ _ 1 = 1; exact map_one _) hpt
    refine key.trans ?_
    change B.embLL (((rowTyG I.Ch I.Ps).chr (⟨hv, hΛ⟩ : (rowTyG I.Ch I.Ps).grp)⁻¹ *
      (levQX B.R I.sel (I.tup a)).chr (⟨cc, hQ⟩ : (levQX B.R I.sel (I.tup a)).grp)⁻¹ : B.LLˣ) : B.LL) = _
    refine (chr_inv_val (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup a)) B.embLL ⟨hv, hΛ⟩ ⟨cc, hQ⟩).trans ?_
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun P _ => ?_)
    have hP : GlobalTheory.TopStep.redGL _ P.1 (cc P) ∈ blockTri (blk2 B.R.r) := by rw [hred P]; exact h2 P
    refine (levQX_lam_inv B.embLL hn P ⟨cc P, hQ P (Set.mem_univ P)⟩ hP).trans ((hξ P.1 P.2 _).symm.trans ?_)
    have e : (⟨GlobalTheory.TopStep.redGL _ P.1 (cc P), hP⟩ : blockTri (blk2 B.R.r)) = ⟨redAt 1 P.1 ⟨z, hz⟩, h2 P⟩ := Subtype.ext (hred P)
    exact congrArg (fun M => ((ξ P.1 (Formalism.L2.DIV.blkDet (blk2 B.R.r) 1 M) : ℂˣ) : ℂ)) e

end GlobalTheory.SeeSaw.TwLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacterStatement
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTuple_reading_level_character : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}, I.ReadsP a S.Lb S.U S.chi y lat st → ∀ (_c : (I.stX a).Cl) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ),
    (∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL)) →
    RdLevOn (E := B.fields.E) B.sp.cm (RatAt (I.Q a)) S.U S.chi (rowTyG I.Ch I.Ps) B.embLL (I.Q a)
      (fun _ => blockTri (blk2 B.R.r)) (fun P => (ξ P.1).comp (blkDet (blk2 B.R.r) 1)) := by
  first | exact @GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | exact GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | (intros; apply GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCurry
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFundamentalSetChartPreimageFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFundamentalSetChartPreimageFundamentalDomain
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre.FundPre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ae_lact_notMem (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {Bad : Set (Frame X.Ψ r)} (hB : MeasurableSet Bad)
    (hinv : ∀ x, ∀ b ∈ Bor X.Ψ r, (rmul x b ∈ Bad ↔ x ∈ Bad))
    (h0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∉ Bad) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∀ᵐ z ∂muF X x0, lact γ (cpt X x0 z) ∉ Bad := by
  have hφ : Measurable (Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) :=
    measurable_one.indicator hB
  have hM := measInv_holds (E := E) r X x0 (lact γ x0) ho (KU.isOrth_lact X hγ ho)
    (Bad.indicator 1) hφ (fun x _ b hb => by
      classical
      simp only [Set.indicator_apply, hinv x b hb, Pi.one_apply])
  have h1 : ∫⁻ z, Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0), lintegral_zero]
    filter_upwards [h0] with z hz
    exact Set.indicator_of_notMem hz _
  rw [h1, KU.muF_lact X hγ] at hM
  have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X (lact γ x0) z) :=
    hφ.comp (KU.cont_cpt X _).measurable
  have h2 := (lintegral_eq_zero_iff hm).1 hM.symm
  filter_upwards [h2] with z hz hbad
  rw [← KU.cpt_lact] at hbad
  simp only [Set.indicator_of_mem hbad, Pi.one_apply, Pi.zero_apply] at hz
  exact one_ne_zero hz

theorem isFundSet_preimage (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ)
    (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ)
    (hp : X.p0 = r - j)
    (hfree : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1)
    (hnull : ∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 →
      muF X (x0F X) (proj X hj κ ⁻¹' N) = 0)
    (F : Set (Tau × Fin j × Fin (r - j) → ℂ)) (hF : IsFD (gammaU X hj κ) F) :
    ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧
      IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  obtain ⟨hFm, hFD, hcov, hbad⟩ := hF
  obtain ⟨N0, hN0, hN0m, hN0z⟩ := exists_measurable_superset_of_null hbad
  have ho := isOrth_x0F X
  have hOm : MeasurableSet (OmF X (x0F X)) :=
    ((FourierCoefficientDomain.isOpen_dom X).preimage (KU.cont_cpt X (x0F X))).measurableSet
  have hNm : MeasurableSet (F ∩ N0) := hFm.inter hN0m
  have hNz : muD Tau j (r - j) (F ∩ N0) = 0 := measure_mono_null Set.inter_subset_right hN0z
  refine ⟨F \ N0, hFm.diff hN0m, Set.sdiff_subset, ?_, ?_, Set.inter_subset_right, ?_, ?_⟩
  · rw [Set.sdiff_sdiff_right_self]; exact hNz
  · exact (measurable_proj X hj κ (hFm.diff hN0m)).inter hOm
  · rintro z ⟨⟨hz, hzN⟩, hzO⟩ z' ⟨⟨hz', -⟩, -⟩ γ hγ b hb h
    have hd : domPt X hj κ (cpt X (x0F X) z') = domPt X hj κ (lact γ (cpt X (x0F X) z)) := by
      rw [h, KU.lact_rmul', domPt_rmul X hj κ hb]
    have hfix : domPt X hj κ (lact γ (cpt X (x0F X) z)) = domPt X hj κ (cpt X (x0F X) z) := by
      by_contra hne
      apply hzN
      apply hN0
      refine ⟨hz, toUpq X hj κ γ, ⟨γ, hγ, rfl⟩, ?_, ?_⟩
      · change flat (moebI _ (domPt X hj κ (cpt X (x0F X) z))) ∈ F
        rw [← domPt_lact X hj κ hp γ hzO, ← hd]
        exact hz'
      · change moebI _ (domPt X hj κ (cpt X (x0F X) z)) ≠ domPt X hj κ (cpt X (x0F X) z)
        rw [← domPt_lact X hj κ hp γ hzO]
        exact hne
    have h1 := hfree γ hγ _ hzO hfix
    rw [h1, KU.lact_one] at h
    have hS : cpt X (x0F X) z' ∈ KU.Sset X (x0F X) {z} := by
      rw [h, KU.rmul_mem_S X hb, KU.cpt_mem_S X ho]
      rfl
    exact ((KU.cpt_mem_S X ho z').1 hS).symm
  · have := KU.countable_Γ X
    have hA : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (fun x => flat (domPt X hj κ x)) ⁻¹' (F ∩ N0) := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (measurable_domPt X hj κ hNm) ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_preimage, domPt_rmul X hj κ hb]
      · exact measure_eq_zero_iff_ae_notMem.1
          (hnull _ hNm (Set.inter_subset_left.trans hFD) hNz)
    have hB : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (KU.Sset X (x0F X) (OmF X (x0F X)))ᶜ := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (KU.meas_S X ho hOm).compl ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_compl_iff, KU.rmul_mem_S X hb]
      · filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hz hn
        exact hn ((KU.cpt_mem_S X ho z).2 hz)
    filter_upwards [hA, hB, ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hzA hzB hzO
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hγF⟩ := hcov _ (domPt_mem X hj κ hp hzO)
    rw [← domPt_lact X hj κ hp γ hzO] at hγF
    have h1 := hzA ⟨γ, hγ⟩
    obtain ⟨⟨z', b⟩, ⟨hz', hb⟩, he⟩ := not_not.1 (hzB ⟨γ, hγ⟩)
    have he' : rmul (cpt X (x0F X) z') b = lact γ (cpt X (x0F X) z) := he
    have hpr : proj X hj κ z' = flat (domPt X hj κ (lact γ (cpt X (x0F X) z))) := by
      rw [← he', domPt_rmul X hj κ hb]; rfl
    refine ⟨z', ⟨?_, hz'⟩, γ⁻¹, X.Γ.inv_mem hγ, b, hb, ?_⟩
    · rw [Set.mem_preimage, hpr]
      exact ⟨hγF, fun hn => h1 ⟨hγF, hn⟩⟩
    · rw [he', KU.lact_lact, inv_mul_cancel, KU.lact_one]

end GlobalTheory.FlagFibre.FundPre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFundamentalSetChartPreimageFundamentalDomainStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1) → (∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 → muF X (x0F X) (proj X hj κ ⁻¹' N) = 0) → ∀ F, IsFD (gammaU X hj κ) F → ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧ IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  first | exact @GlobalTheory.FlagFibre.FundPre.isFundSet_preimage | exact GlobalTheory.FlagFibre.FundPre.isFundSet_preimage | (intros; apply GlobalTheory.FlagFibre.FundPre.isFundSet_preimage <;> assumption)
end
end

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.FlagFibre

theorem measurePreserving_curry (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} (X : Data E r) (hj : j ≤ r) {Tau : Type}
  [Fintype Tau] (κ : Tau ≃ X.Ψ)

theorem mem_OmF_of_proj (hp : X.p0 = r - j) {z : V (nd X)} (hz : proj X hj κ z ∈ DomFlat Tau j (r - j)) :
    z ∈ OmF X (x0F X) := by
  intro τ
  obtain ⟨t, rfl⟩ := κ.surjective τ
  refine ⟨?_, fun i => ?_⟩
  · have e : mat (cpt X (x0F X) z) (κ t) = mat (x0F X) (κ t) * uni (coords X κ z t) := rfl
    rw [e, det_mul, det_uni, mul_one]
    exact det_x0F X _
  · rw [dmin_cpt X κ z t i, hp]
    refine GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) _ (reindex_sgn hj) _ ?_ i
    have h := hz t
    have e : unflat (proj X hj κ z) t = toMat (base (idx hj) (coords X κ z t)) := by
      ext a b; exact proj_eq X hj κ z t (a, b)
    rwa [e] at h

theorem inter_OmF (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hD : S ⊆ DomFlat Tau j (r - j)) :
    proj X hj κ ⁻¹' S ∩ OmF X (x0F X) = proj X hj κ ⁻¹' S :=
  Set.inter_eq_left.2 fun _ hz => mem_OmF_of_proj X hj κ hp (hD hz)

theorem densF_eq (z : V (nd X)) :
    densF X (x0F X) z = ∏ t, dens (sgnMat r X.p0) (coords X κ z t) := by
  rw [densF, ← κ.prod_comp]
  exact Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i _ => by rw [dmin_cpt X κ z t]

theorem muF_preimage (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hS : MeasurableSet S)
    (hD : S ⊆ DomFlat Tau j (r - j)) :
    muF X (x0F X) (proj X hj κ ⁻¹' S) =
      ENNReal.ofReal ((flagConst j * flagConst (r - j))⁻¹ ^ Fintype.card Tau) * muD Tau j (r - j) S := by
  have hS' := measurable_proj X hj κ hS
  set c := MeasurableEquiv.curry Tau (Fin j × Fin (r - j)) ℂ with hc
  set φ : (Tau → Fin j × Fin (r - j) → ℂ) → ℝ≥0∞ := (c.symm ⁻¹' S).indicator 1 with hφ
  have hφm : Measurable φ := measurable_one.indicator (c.symm.measurable hS)
  have hDm : Measurable fun y => ENNReal.ofReal (dens (sgnMat r (r - j)) y) := (measurable_dens _).ennreal_ofReal
  have key := GlobalTheory.T.lintegral_pi_fibre_measurePreserving Tau _ _ _ (glue (idx hj)) (base (idx hj)) _ φ (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ _ (isBlockOrderedSumEquiv_trueIndex hj))
    (measurable_base _) (base_glue (isBlockOrderedSumEquiv_trueIndex hj)) hDm hφm
  have hm : Measurable fun y : Tau → Low r → ℂ => φ (fun t => base (idx hj) (y t)) *
      ∏ t, ENNReal.ofReal (dens (sgnMat r (r - j)) (y t)) :=
    (hφm.comp (Measurable.of_eval fun t => (measurable_base _).comp (measurable_pi_apply t))).mul
      (Finset.measurable_prod _ fun t _ => hDm.comp (measurable_pi_apply t))
  rw [← (GlobalTheory.T.measurePreserving_flagFibreChartCoordinates E r X Tau κ).lintegral_comp hm,
    ← (measurePreserving_curry Tau (Fin j × Fin (r - j))).lintegral_comp_emb c.measurableEmbedding] at key
  rw [muF, muD, withDensity_apply _ hS', withDensity_apply _ hS, Measure.restrict_restrict hS',
    Measure.restrict_restrict hS, Set.inter_eq_left.2 hD,
    inter_OmF X hj κ hp hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator hS', ← lintegral_indicator hS]
  refine Eq.trans (lintegral_congr fun z => ?_) (key.trans (lintegral_congr fun v => ?_))
  · have e : c.symm (fun t => base (idx hj) (coords X κ z t)) = proj X hj κ z :=
      funext fun s => (proj_eq X hj κ z s.1 s.2).symm
    by_cases h : proj X hj κ z ∈ S
    · rw [Set.indicator_of_mem (show z ∈ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_mem (by rwa [Set.mem_preimage, e]), Pi.one_apply, one_mul, densF_eq X κ, hp,
        ENNReal.ofReal_prod_of_nonneg fun _ _ => dens_nonneg _ _]
    · rw [Set.indicator_of_notMem (show z ∉ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_notMem (by rwa [Set.mem_preimage, e]), zero_mul]
  · by_cases h : v ∈ S
    · rw [Set.indicator_of_mem h, hφ, Set.indicator_of_mem (show c v ∈ c.symm ⁻¹' S from h), Pi.one_apply, one_mul]
      have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
      have hv : ∀ t, toMat (c v t) ∈ hcDom j (r - j) := hD h
      have hpos : ∀ t, 0 ≤ (hQ (toMat (c v t))).det.re ^ (-((j + (r - j) : ℕ) : ℤ)) := fun t =>
        zpow_nonneg (Complex.pos_iff.1 (PosDef.det_pos (hv t))).1.le _
      rw [Finset.prod_congr rfl fun t _ => GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) (sgnMat r (r - j))
        (reindex_sgn hj) (c v t) (hv t), ← ENNReal.ofReal_prod_of_nonneg fun t _ => div_nonneg (hpos t) hc0.le,
        ← ENNReal.ofReal_mul (by positivity), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        div_eq_inv_mul, inv_pow]
      rfl
    · rw [Set.indicator_of_notMem h, hφ, Set.indicator_of_notMem (show c v ∉ c.symm ⁻¹' S from h), zero_mul]

theorem covol_eq_muD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r)
    (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ F, IsFD (gammaU X hj κ) F →
    muD Tau j (r - j) F < ⊤ ∧
      covol X = grassConst j (r - j) ^ Fintype.card Tau * (muD Tau j (r - j) F).toReal := by
  intro E _ _ _ r j X hj Tau _ κ hp F hF
  obtain ⟨F', hm, hsub, h0, hfs⟩ := GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain E r j X hj Tau κ hp (GlobalTheory.T.domain_point_stabilizer_trivial E r j X hj Tau κ hp)
    (fun N hN hD h => by rw [muF_preimage X hj κ hp hN hD, h, mul_zero]) F hF
  have hD := hsub.trans hF.2.1
  rw [inter_OmF X hj κ hp hD] at hfs
  obtain ⟨h1, h2⟩ := covol_eq X (isOrth_x0F X) hfs
  have e : muD Tau j (r - j) F' = muD Tau j (r - j) F := (measure_eq_measure_of_null_diff hsub h0)
  have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
  rw [muF_preimage X hj κ hp hm hD, e] at h1 h2
  refine ⟨?_, ?_⟩
  · refine lt_top_iff_ne_top.2 fun h => h1.ne ?_
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
  · have e1 : flagConst r = grassConst j (r - j) * (flagConst j * flagConst (r - j)) := by
      rw [← mul_assoc, ← flagConst_add, Nat.add_sub_cancel' hj]
    have e2 : X.Ψ.card = Fintype.card Tau := by rw [Fintype.card_congr κ, Fintype.card_coe]
    rw [h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), e1, e2, mul_pow, inv_pow]
    field_simp

end GlobalTheory.FlagFibre
end
end
