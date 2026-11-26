module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOffClosedFibreDescended
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionOfDeRhamClassUnique
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelign
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CrdMapBC

open GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.QCoh.Qcqs

theorem secMaps_baseChangeIso {o k : Type} [CommRing o] [CommRing k] (β : o →+* k) (n : ℕ) (j : Fin (n + 1)) :
    SecMaps (baseChangeIso n β) (secPull (coord o n j) (baseChange n β)) (coord k n j) := by
  rintro ⟨i, l⟩
  refine (baseChangeIso_coord n β j i l).trans ?_
  congr 1

theorem pCrd_comp_baseChange {o k A : Type} [CommRing o] [CommRing k] [CommRing A] (β : o →+* k) {n : ℕ}
    (x : Sp A ⟶ PSpace k n) (v : Fin (n + 1) → A) (h : PCrd x v) : PCrd (x ≫ baseChange n β) v := by
  refine (RepBC.secCoord_pull (O1 o n) (coord o n) (baseChange n β) x v).1 ?_
  exact (FibreEmbed.secCoord_iff_of_secMaps (LB.isLB_pull (O1_isLB o n) _) (O1_isLB k n)
    (w := baseChangeIso n β) (fun j => secMaps_baseChangeIso β n j)
    (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord o n) _) (iSup_nonzeroLocus_coord k n)).2 h

theorem exists_map_of_hasDiv : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (β : o →+* k) (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace o n, h ≫ PSpace.str o n = M.s ≫ spMap β ∧ PCrd (M.pt ≫ h) c := by
  intro k Ω o _ _ _ _ β M n c hc
  obtain ⟨h₀, hs, hp⟩ := GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv k Ω M n c hc
  refine ⟨h₀ ≫ baseChange n β, ?_, ?_⟩
  · rw [Category.assoc, baseChange_str, ← Category.assoc, hs]
  · rw [← Category.assoc]
    exact pCrd_comp_baseChange β _ c hp

end GlobalTheory.SiegTh.CrdMapBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (β : o →+* k) (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace o n, h ≫ PSpace.str o n = M.s ≫ spMap β ∧ PCrd (M.pt ≫ h) c := by
  first | exact @GlobalTheory.SiegTh.CrdMapBC.exists_map_of_hasDiv | exact GlobalTheory.SiegTh.CrdMapBC.exists_map_of_hasDiv | (intros; apply GlobalTheory.SiegTh.CrdMapBC.exists_map_of_hasDiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangent
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem lie_psi_cl_eq_tanVal (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A)
    (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
    (ψ : PrimitiveSubmodule A →ₗ[R] G.omega)
    (hψ : ∀ c : PrimitiveSubmodule A, GlobalTheory.PtExt.IsCan t c.1 (G.rigOfOmega (ψ c)))
    (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A)
    (hF : (⟨_, hβ⟩ : primDR A) ∈ PrimitiveSubmodule A) (x : G.Lie) (v : epsR R ⟶ A)
    (hx : t.LieCorr x v) : x (ψ ⟨_, hF⟩) = tanVal v β := by
  obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hβ
  have hw : ψ ⟨_, hF⟩ = w :=
    PDivGroup.rigOfOmega_injective_of_pow p R N hN G
      (isCan_unique R A p G t ⟨_, hβ⟩ hA _ _ (hψ ⟨_, hF⟩) hw2)
  rw [hw]
  exact lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 x v hx

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiePairingCanonicalRigidifiedExtensionTangentStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_pairing_canonical_rigidified_extension_tangent :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (G : PDivGroup p R) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A)
      (hF : (⟨_, hβ⟩ : primDR A) ∈ PrimitiveSubmodule A) (x : G.Lie) (v : epsR R ⟶ A),
    t.LieCorr x v → x (ψ ⟨_, hF⟩) = tanVal v β :=
  @PtExt.lie_psi_cl_eq_tanVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtingerDerivsCompHolomorphicPullbackDz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtingerDerivsCompHolomorphicPullbackDz
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.LineForm

theorem chain_sum_coordVec {n : ℕ} (w : V n) : w = ∑ b, w b • coordVec b := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem del_dbar_comp_holo_pull : ∀ (m n : ℕ) (τ : V m → V n) (c : V n → ℂ) (v : V m),
    DifferentiableAt ℂ τ v → DifferentiableAt ℝ c (τ v) →
    (∑ a, del (fun x => c (τ x)) v (coordVec a) • dz a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, del c (τ v) (coordVec a) • dz a) ∧
    (∑ a, dbar (fun x => c (τ x)) v (coordVec a) • dzb a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, dbar c (τ v) (coordVec a) • dzb a) := by
  intro m n τ c v hτ hc
  constructor
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [del_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [dbar_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).2, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smulₛₗ, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]

end GlobalTheory.LineForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtingerDerivsCompHolomorphicPullbackDzStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wirtingerDerivs_comp_holomorphic_pullback_dz : ∀ (m n : ℕ) (τ : V m → V n) (c : V n → ℂ) (v : V m), DifferentiableAt ℂ τ v → DifferentiableAt ℝ c (τ v) →
    (∑ a, del (fun x => c (τ x)) v (coordVec a) • dz a : Alt m) = pull (fderiv ℂ τ v) (∑ a, del c (τ v) (coordVec a) • dz a) ∧
    (∑ a, dbar (fun x => c (τ x)) v (coordVec a) • dzb a : Alt m) = pull (fderiv ℂ τ v) (∑ a, dbar c (τ v) (coordVec a) • dzb a) := by
  first | exact @GlobalTheory.LineForm.del_dbar_comp_holo_pull | exact GlobalTheory.LineForm.del_dbar_comp_holo_pull | (intros; apply GlobalTheory.LineForm.del_dbar_comp_holo_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCDvrTwoEmbeddings
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section
namespace GlobalTheory.TInj

theorem exists_cDvr_two_embeddings : ∀ (R R₁ R' : Type) [CommRing R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R₁), Function.Injective ρ → ρ.Finite → IsCN R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (η' : R' →+* V) (f₁ f₂ : R₁ →+* V), IsAdicComplete (maximalIdeal V) V ∧ Function.Injective η' ∧ Function.Injective f₁ ∧ Function.Injective f₂ ∧ IsLocalHom f₁ ∧ IsLocalHom f₂ ∧ f₁.comp ρ = η'.comp θ₁ ∧ f₂.comp ρ = η'.comp θ₂ := by
  intro R R₁ R' _ _ _ _ _ _ _ _ ρ hρ hfin hR' θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂
  obtain ⟨hN, hIC, hC, hCZ⟩ := hR'
  have hadm : AdmBase R' (maximalIdeal R') := ⟨hN, inferInstance, hIC, hC⟩
  obtain ⟨V₀, _, _, _, φ₀, hV₀, hφ₀, hI₀⟩ :=
    GlobalTheory.adic_base_embeds_valuation_algebraic_closure.1 R' (maximalIdeal R') hadm
  have hcz₀ : CharZero V₀ := charZero_of_injective_ringHom hφ₀
  have hloc₀ : IsLocalHom φ₀ := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnx
    have hxm : x ∈ maximalIdeal R' := (mem_maximalIdeal x).2 hnx
    have : φ₀ x ∈ maximalIdeal V₀ := hI₀ (Ideal.mem_map_of_mem φ₀ hxm)
    exact (mem_maximalIdeal _).1 this hx
  have hcd₀ : GlobalTheory.LN.CDvr V₀ := ⟨inferInstance, hV₀, hcz₀⟩
  obtain ⟨V₁, _, _, _, g₁, ψ₁, hcd₁, hg₁, hlg₁, hlψ₁, hc₁⟩ :=
    GlobalTheory.LocExt.exists_cDvr_ext_of_finite R R₁ ρ hρ hfin V₀ hcd₀ (φ₀.comp θ₁) inferInstance
  obtain ⟨V, _, _, _, g₂, ψ₂, hcd, hg₂, hlg₂, hlψ₂, hc₂⟩ :=
    GlobalTheory.LocExt.exists_cDvr_ext_of_finite R R₁ ρ hρ hfin V₁ hcd₁ (g₁.comp (φ₀.comp θ₂)) inferInstance
  obtain ⟨hdvr, hcomp, hcz⟩ := hcd
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hfin
  haveI : Algebra.IsIntegral R R₁ := Algebra.IsIntegral.of_finite R R₁
  have inj_of : ∀ f : R₁ →+* V, Function.Injective (f.comp ρ) → Function.Injective f := by
    intro f hf
    refine (RingHom.injective_iff_ker_eq_bot f).2 (Ideal.eq_bot_of_comap_eq_bot (R := R) ?_)
    have : Ideal.comap (algebraMap R R₁) (RingHom.ker f) = RingHom.ker (f.comp ρ) := rfl
    change Ideal.comap (algebraMap R R₁) (RingHom.ker f) = ⊥
    rw [this]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hf
  let η' : R' →+* V := g₂.comp (g₁.comp φ₀)
  have hη' : Function.Injective η' := hg₂.comp (hg₁.comp hφ₀)
  have e₁ : (g₂.comp ψ₁).comp ρ = η'.comp θ₁ := by
    rw [RingHom.comp_assoc, hc₁]; rfl
  have e₂ : ψ₂.comp ρ = η'.comp θ₂ := by
    rw [hc₂]; rfl
  refine ⟨V, inferInstance, inferInstance, hdvr, hcz, η', g₂.comp ψ₁, ψ₂, hcomp, hη', ?_, ?_, inferInstance,
    hlψ₂, e₁, e₂⟩
  · exact inj_of _ (by rw [e₁]; exact hη'.comp hθ₁)
  · exact inj_of _ (by rw [e₂]; exact hη'.comp hθ₂)

end GlobalTheory.TInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryPlaceNotDvdDifferentBaseField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryPlaceNotDvdDifferentBaseField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DifferentAtBasePlace

theorem ne_of_mod_eq_one' {p M k : ℕ} (hp : p % M = 1) (hk : k ∣ M) (hk1 : 1 < k) : p ≠ k := by
  rintro rfl
  have h := Nat.mod_mod_of_dvd p hk
  rw [hp, Nat.mod_self, Nat.mod_eq_of_lt hk1] at h
  exact one_ne_zero h

theorem natAbs_discr_F_dvd (D : D7) : (discr D.host.F).natAbs ∣ (discr D.host.E).natAbs := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow D.host.F (𝓞 D.host.F) D.host.E (𝓞 D.host.E)]
  exact Dvd.dvd.mul_left (dvd_pow_self _ Module.finrank_pos.ne') _

theorem leastSplitAuxiliaryPrime_not_dvd_discr_base (D : D7) : ¬ q0 D ∣ (discr D.host.F).natAbs := by
  obtain ⟨hp, hm, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  intro h
  have hc : q0 D ∣ Formalism.BasicNotions.LevelStarExponents.condE D :=
    D.host.der.discr_primes.1 _ hp (Int.natCast_dvd.2 (h.trans (natAbs_discr_F_dvd D)))
  exact ne_of_mod_eq_one' hm (dvd_mul_of_dvd_right hc _) hp.one_lt rfl

theorem not_dvd_different {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) :
    ¬ G.pl.v0.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro h
  have hdisc : ((discr D.host.F : ℤ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal :=
    Ideal.le_of_dvd h (discr_mem_differentIdeal D.host.F (𝓞 D.host.F))
  have hq : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ G.pl.v0.asIdeal := G.pl.basePlace_over_qZero
  have hcop : IsCoprime (q0 D : ℤ) (discr D.host.F) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm, Int.gcd, Int.natAbs_natCast]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (leastSplitAuxiliaryPrimeThetaChain_spec D).1).2 (leastSplitAuxiliaryPrime_not_dvd_discr_base D))
  obtain ⟨u, v, huv⟩ := hcop
  apply G.pl.v0.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have := congrArg (Int.cast : ℤ → 𝓞 D.host.F) huv
  push_cast at this
  rw [← this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by exact_mod_cast hq)) (Ideal.mul_mem_left _ _ hdisc)

end GlobalTheory.DifferentAtBasePlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryPlaceNotDvdDifferentBaseFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliary_place_not_dvd_different_base_field : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc), ¬ G.pl.v0.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  first | exact @GlobalTheory.DifferentAtBasePlace.not_dvd_different | exact GlobalTheory.DifferentAtBasePlace.not_dvd_different | (intros; apply GlobalTheory.DifferentAtBasePlace.not_dvd_different <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityFractionFieldMemberEqZetaPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityFractionFieldMemberEqZetaPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

theorem eq_yK_zeta_pow_of_pow_eq_one : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ u : FractionRing V, u ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1 → ∃ e : ℕ, u = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 u hu
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero V
  set k := (X₁.S.r * X₁.S.N) ^ 2 with hk
  have hkpos : 0 < k := by
    have h1 := X₁.S.r_pos; have h2 := X₁.S.N_ge
    positivity
  have hinj : Function.Injective (algebraMap X₁.o₁ X₁.S.R) := by
    intro a b hab
    apply X₁.ar.inj
    have := congrArg (fun x : X₁.S.R => (x : X₁.Ω₁)) hab
    simpa using this
  have hR : IsPrimitiveRoot (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) k := X₁.S.prim.map_of_injective hinj
  have hroot : (Polynomial.cyclotomic k (FractionRing V)).IsRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) := by
    have h := (hR.isRoot_cyclotomic hkpos).map (f := 𝔪.yK)
    rwa [Polynomial.map_cyclotomic] at h
  haveI : NeZero (k : FractionRing V) := ⟨by exact_mod_cast hkpos.ne'⟩
  have hK : IsPrimitiveRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) k :=
    (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨e, -, he⟩ := hK.eq_pow_of_pow_eq_one hu
  exact ⟨e, by rw [map_pow, map_pow, he]⟩

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityFractionFieldMemberEqZetaPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootOfUnity_fractionField_member_eq_zeta_pow : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ u : FractionRing V, u ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1 → ∃ e : ℕ, u = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) := by
  first | exact @GlobalTheory.Poinc.Sep.eq_yK_zeta_pow_of_pow_eq_one | exact GlobalTheory.Poinc.Sep.eq_yK_zeta_pow_of_pow_eq_one | (intros; apply GlobalTheory.Poinc.Sep.eq_yK_zeta_pow_of_pow_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_of_isSum {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {n j : ℤ} (τ : SecE U b n j)
    {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β)
    (hs : Small I s) (hF : IsSum I s F) (hτ : TExp U τ s) : TExp U τ (w := id) F := by
  classical
  intro S hS Z x z J J' hJ hJ'
  have h0 : ∀ i ∉ (hs e).toFinset, Van I (s i) e := fun i hi => by
    by_contra h
    exact hi ((hs e).mem_toFinset.2 h)
  have hx : x ≫ (U.gt e).pG.left =
      (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R I e) := (Category.assoc _ _ _).symm
  rw [hτ _ h0 Z x z J J' hJ hJ']
  have hsum : ∀ δ, sval (F δ) (x ≫ (U.gt e).pG.left) z J =
      ∑ i ∈ (hs e).toFinset.filter (fun i => w i = δ), sval (s i) (x ≫ (U.gt e).pG.left) z J := fun δ => by
    rw [hx]
    convert hF e _ h0 δ Z (x ≫ (U.gt e).q.left) z J hJ
  have hvan : ∀ δ ∉ S, sval (F δ) (x ≫ (U.gt e).pG.left) z J = 0 := fun δ hδ => by
    rw [hx]
    exact hS δ hδ Z (x ≫ (U.gt e).q.left) z J hJ
  have key : ∀ T : Finset D.toPre.X, (hs e).toFinset.image w ⊆ T →
      ∑ i ∈ (hs e).toFinset, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val =
      ∑ δ ∈ T, sval (F δ) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t δ) x z J).val := fun T hT => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := T) (fun i hi => hT (Finset.mem_image_of_mem w hi))]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain rfl := (Finset.mem_filter.1 hi).2
    rfl
  rw [key _ (Finset.subset_union_left (s₂ := S))]
  refine (Finset.sum_subset Finset.subset_union_right fun δ _ hδ => ?_).symm
  exact (congrArg (· * _) (hvan δ hδ)).trans (zero_mul _)

theorem texp_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U _ _ _ _ τ _ _ s F hs hF hτ => texp_of_isSum U.toUnifPre τ s F hs hF hτ

end GlobalTheory.TwFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedExpansion_adicSums_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F := by
  first | exact @GlobalTheory.TwFam.texp_sum | exact GlobalTheory.TwFam.texp_sum | (intros; apply GlobalTheory.TwFam.texp_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFrameRatioIntegralFrameChartIndepende
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFrameRatioIntegralFrameChartIndepende
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Poinc.FrameIndep

theorem ratio_indep {X H Y Z B B' : Scheme.{0}} {L : LB X} {M : LB H} {f : Y ⟶ H} {ψ : Y ⟶ X}
    (w : LB.Iso (L.pull ψ) (M.pull f)) (hw : w.IsGen) {e : B ⟶ X} {e' : B' ⟶ H}
    {a : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => e) (fun _ => 1))}
    {a' : LB.Gen (LB.LinComb M (K := Fin 1) (fun _ => e') (fun _ => 1))} (ha : a.IsGen)
    (ha' : a'.IsGen) (r : Z ⟶ Y) (t : Z ⟶ B) (t' : Z ⟶ B') (p : Z ⟶ X) (p' : Z ⟶ H)
    (h : r ≫ ψ = p) (h' : r ≫ f = p') (k : t ≫ e = p) (k' : t' ≫ e' = p') (z : Z)
    {J J' I I'} (hJ : Good L z J) (hJ' : Good M z J') (hI : Good L z I) (hI' : Good M z I') :
    Geo.Tor.gw w r z (J' p') (fun _ => J p) * val a t z J * (val a' t' z J')⁻¹ =
      Geo.Tor.gw w r z (I' p') (fun _ => I p) * val a t z I * (val a' t' z I')⁻¹ := by
  subst h h'
  have e₁ : val a t z J = _ * val a t z I := gen_trans ha t z (hJ.mem _ t) (hI.mem _ t)
  have e₂ : val a' t' z J' = _ * val a' t' z I' := gen_trans ha' t' z (hJ'.mem _ t') (hI'.mem _ t')
  have e₃ : Geo.Tor.gw w r z (J' (r ≫ f)) (fun _ => J (r ≫ ψ)) =
      _ * Geo.Tor.gw w r z (I' (r ≫ f)) (fun _ => I (r ≫ ψ)) :=
    (Geo.Tor.isGen_iff w).1 hw Z r z _ _ _ _ (hJ' (r ≫ f)) (hI' (r ≫ f))
      (mem_pull.2 (hJ (r ≫ ψ))) (mem_pull.2 (hI (r ≫ ψ)))
  rw [Geo.Tor.gm_pull_g L ψ r z _ _ (mem_pull.2 (hJ (r ≫ ψ))) (mem_pull.2 (hI (r ≫ ψ)))] at e₃
  rw [Geo.Tor.trF, Fintype.prod_unique, zpow_one] at e₁ e₂
  rw [k] at e₁
  rw [k'] at e₂
  rw [e₁, e₂, e₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem frame_ratio_indep : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x), e.IsGen → ∀ (h : 𝟙_ (Over (Sp V)) ⟶ G) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), f.IsGen → GlobalTheory.Poinc.IntTerm.Ext U x h → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA JA' : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG JG' : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → Good A.L z JA' → Good U.LG.L z JG' → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG)⁻¹ = Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG' (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA' x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA' * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG')⁻¹ := by
  intro V _ _ I D A G _ _ U w₀ hw₀ x e he h f hf hx z JA JA' JG JG' hJA hJG hJA' hJG'
  refine ratio_indep w₀ hw₀ he hf (x.left ≫ U.gen.inv.left) (𝟙 _) (toUnit (TF (R := V) (FractionRing V))).left
    x.left (toUnit (TF (R := V) (FractionRing V)) ≫ h).left ?_ ?_ (Category.id_comp _) rfl z hJA hJG hJA' hJG'
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (x.left ≫ ·) (congrArg (·.left) U.gen.inv_hom_id)).trans (Category.comp_id _)
  · exact (Category.assoc _ _ _).trans hx

end GlobalTheory.Poinc.FrameIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFrameRatioIntegralFrameChartIndependeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedFrame_ratio_integralFrame_chart_independent : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (D : DegData V I) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U), w₀.IsGen → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x), e.IsGen → ∀ (h : 𝟙_ (Over (Sp V)) ⟶ G) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), f.IsGen → GlobalTheory.Poinc.IntTerm.Ext U x h → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA JA' : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG JG' : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → Good A.L z JA' → Good U.LG.L z JG' → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG)⁻¹ = Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG' (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA' x.left) * val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA' * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG')⁻¹ := by
  first | exact @GlobalTheory.Poinc.FrameIndep.frame_ratio_indep | exact GlobalTheory.Poinc.FrameIndep.frame_ratio_indep | (intros; apply GlobalTheory.Poinc.FrameIndep.frame_ratio_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedIotaGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedIotaGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam

theorem exists_iota_of_rosati {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a a' : D.P.A ⟶ D.P.A)
    [IsMonHom a] [IsMonHom a'] (hr : RosatiAdj D.P.A D.P.L a a') (α δ : D.X) (hc : D.c δ = D.c α ≫ a') :
    ∃ u : LB.Gen (IotaLB D a α δ), IsIota u := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB a a' hr
  have cf : ∀ T, DVR.cP D T δ = DVR.cP D T α ≫ a' := fun T => by
    rw [DVR.cP, hc, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) δ) (D.Oφ a α)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (DVR.prod_neg _ _ (prod_ros a a' (𝟙 D.P.A) (DVR.cP D _ α) h)).trans (Eq.symm ?_)
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) δ h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D a α h)).trans ?_
      rw [cf, Category.id_comp, _root_.mul_comm (DVR.cP D _ α) a, _root_.mul_comm (DVR.cP D _ α ≫ a') (𝟙 _)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _))
  refine ⟨v, hv, fun Z r z J hJ => ?_⟩
  let T : Over (Spec (CommRingCat.of R)) := Over.mk r
  have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb a a' u hu u₀ (T := T) hJ 1 1 (DVR.cP D _ α)).1
  rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := T) z J 1 (DVR.cP D _ α) = 1 := mul_eq_left.1 e.symm
  have o : (1 : T ⟶ D.P.A).left = r ≫ eSec D.P.A := rfl
  have k : (r ≫ eSec D.P.A) ≫ (lift (𝟙 D.P.A) (DVR.cP D D.P.A α)).left = (lift (1 : T ⟶ D.P.A) (DVR.cP D T α)).left := by
    rw [← o, ← Over.comp_left, comp_lift, DVR.comp_cP, Category.comp_id]
  rw [vv Z _ z J hJ, val_inv, val_pull hJ, k]
  exact inv_eq_one.2 e'

theorem exists_iota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ α : D.toPre.X, ∃ u : LB.Gen (IotaLB D.toPre a α (h' α)), IsIota u := by
  intro R _ _ _ _ D a a' h h' hE α
  obtain ⟨h₁, h₂, hr, -, hc, -⟩ := hE
  exact exists_iota_of_rosati D.toPre a a' hr α (h' α) (hc α)

end GlobalTheory.TwFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedIotaGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedTwistedIotaGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ α : D.toPre.X, ∃ u : LB.Gen (IotaLB D.toPre a α (h' α)), IsIota u := by
  first | exact @GlobalTheory.TwFam.exists_iota | exact GlobalTheory.TwFam.exists_iota | (intros; apply GlobalTheory.TwFam.exists_iota <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportLinCombIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportLinCombIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenTransport

theorem exists_unflat {X X' Y : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (ε : J → ℤ) (ψ : K → (Y ⟶ X')) (δ : K → ℤ)
    (T : LB.Gen (LB.LinComb (LB.LinComb L F ε) ψ δ)) (hT : T.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι), Good L z I →
        val t r z I = val T r z (fun χ j => I (χ ≫ F j)) := by
  have le : ∀ p : K × J → L.ι, LB.wchart L (K := K × J) (fun p => ψ p.1 ≫ F p.2) p ≤
      LB.wchart (LB.LinComb L F ε) ψ (fun k j => p (k, j)) := fun p y hy =>
    Set.mem_iInter.2 fun k => by
      have h1 : ψ k y ∈ LB.wchart L F (fun j => p (k, j)) :=
        Set.mem_iInter.2 fun j => Set.mem_iInter.1 hy (k, j)
      exact h1
  let t : LB.Gen (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2)) :=
    ⟨fun p => res (le p) (T.s fun k j => p (k, j))⟩
  refine ⟨t, isGen_of_gm _ fun y p q hp hq => ?_, fun Z r z I hI => ?_⟩
  · refine (gm_res _ y (le p) hp _).trans (Eq.trans ?_ (congrArg _ (gm_res _ y (le q) hq _)).symm)
    refine (gen_trans hT (𝟙 Y) y (le p hp) (le q hq)).trans (congrArg (· * _) ?_)
    refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ δ k)
      (gm_linComb L F ε (𝟙 Y ≫ ψ k) y (fun j => p (k, j)) (fun j => q (k, j)) (Set.mem_iInter.1 (le p hp) k)
        (Set.mem_iInter.1 (le q hq) k))).trans ?_
    simp only [trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, mul_comm]
  · refine (gm_res r z (le _) (hI.mem (fun p : K × J => ψ p.1 ≫ F p.2) r) _).trans ?_
    exact (val_of T r z (fun χ j => I (χ ≫ F j)) _ fun k => funext fun j => congrArg I (Category.assoc _ _ _)).symm

theorem exists_transport : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {J K : Type} [Fintype J] [Fintype K], L.IsLB → L'.IsLB → ∀ (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)), w.IsGen → ∀ (φ' : K → (Y ⟶ X')) (δ : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' δ)), a.IsGen → ∃ t : LB.Gen (LB.LinComb L (fun p : K × J => φ' p.1 ≫ pr p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι) (I' : (Z ⟶ X') → L'.ι), Good L z I → Good L' z I' → val t r z I = (∏ k, gv w (r ≫ φ' k) z (fun j => I ((r ≫ φ' k) ≫ pr j)) (I' (r ≫ φ' k)) ^ δ k) * val a r z I' := by
  intro X X' Y L L' J K _ _ hL hL' pr ε w hw φ' δ a ha
  obtain ⟨T, hT, hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb hL' φ' δ)
    (LB.isLB_linComb (LB.isLB_linComb hL pr ε) φ' δ) (LB.linCombIso w φ' δ) (DVR.linCombIso_isGen w hw _ _) a ha
  obtain ⟨t, ht, hv'⟩ := exists_unflat pr ε φ' δ T hT
  refine ⟨t, ht, fun Z r z I I' hI hI' => (hv' Z r z I hI).trans ?_⟩
  have hI'' : Good (LB.LinComb L pr ε) z (fun χ j => I (χ ≫ pr j)) := fun χ => hI.mem pr χ
  refine (hv Z r z _ (fun k => I' (r ≫ φ' k)) (hI''.mem φ' r) (hI'.mem φ' r)).trans (congrArg₂ (· * ·) ?_ rfl)
  exact GlobalTheory.WtTower.gm_linCombIso w φ' δ (fun k j => I ((r ≫ φ' k) ≫ pr j), fun k => I' (r ≫ φ' k)) r z
    ⟨hI''.mem φ' r, hI'.mem φ' r⟩

end GlobalTheory.Mum.GenTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportLinCombIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_transport_linCombIso : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {J K : Type} [Fintype J] [Fintype K], L.IsLB → L'.IsLB → ∀ (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)), w.IsGen → ∀ (φ' : K → (Y ⟶ X')) (δ : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' δ)), a.IsGen → ∃ t : LB.Gen (LB.LinComb L (fun p : K × J => φ' p.1 ≫ pr p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι) (I' : (Z ⟶ X') → L'.ι), Good L z I → Good L' z I' → val t r z I = (∏ k, gv w (r ≫ φ' k) z (fun j => I ((r ≫ φ' k) ≫ pr j)) (I' (r ≫ φ' k)) ^ δ k) * val a r z I' := by
  first | exact @GlobalTheory.Mum.GenTransport.exists_transport | exact GlobalTheory.Mum.GenTransport.exists_transport | (intros; apply GlobalTheory.Mum.GenTransport.exists_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZe
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem torsion_lies_under : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V →
    ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N →
      ∀ β : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A, β ^ N = 1 →
      ∃ xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, xb ^ N = 1 ∧
        (∃ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 ∧
          QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb) ∧
        ∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 →
          QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → p.g.b = β := by
  intro V _ _ _ hCN D A G _ _ hG U N hN β hβ
  haveI : CharZero V := hCN.2.2.2
  have hA := GlobalTheory.TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA D A G hG U
    (AlgebraicClosure (FractionRing V)) N hN
  obtain ⟨p, hpy, hpb⟩ := GlobalTheory.TorusExt.exists_qkPt_of_torsion (F := AlgebraicClosure (FractionRing V))
    D.tau_bimult (n := N) (by omega) hβ
  refine ⟨f p, ?_, ⟨p, hpy, (hf.1 p (f p)).2 rfl⟩, fun p' hp'y hp' => ?_⟩
  · obtain ⟨w, hw⟩ := U.ext
    exact ((hf.1 p (f p)).2 rfl w hw).1
  · have e : f p = f p' := (hf.1 p' (f p)).1 hp'
    letI := GlobalTheory.TorusExt.gtGroup D.toPre (AlgebraicClosure (FractionRing V))
    obtain ⟨z, hy, w, hw₁, hw₂⟩ := (hf.2.2.1 p p').1 e
    have hg := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hw₂
    rw [hp'y, hpy, zero_add] at hy
    have hz : z = 0 := by
      have h2 : (N : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hy.symm
      rcases smul_eq_zero.1 h2 with h | h
      · omega
      · exact h
    subst hz
    have hw : w.b = 1 := by
      exact hw₁.1.trans (cPoint_zero _)
    rw [hg, GlobalTheory.TorusExt.add_b, hw, _root_.mul_one, hpb]

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N → ∀ β : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A, β ^ N = 1 → ∃ xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, xb ^ N = 1 ∧ (∃ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 ∧ QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb) ∧ ∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → p.g.b = β := by
  first | exact @GlobalTheory.Poinc.IntTerm.torsion_lies_under | exact GlobalTheory.Poinc.IntTerm.torsion_lies_under | (intros; apply GlobalTheory.Poinc.IntTerm.torsion_lies_under <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegEighth

theorem exists_isSharpBasis (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  have hS : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by rw [Matrix.mul_adjugate, hW.2, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by rw [Matrix.adjugate_mul, hW.2, one_smul]
  let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    { twistSnd (W + W.transpose).adjugate with
      invFun := twistSnd (W + W.transpose)
      left_inv := twistSnd_twistSnd _ _ h1
      right_inv := twistSnd_twistSnd _ _ h2 }
  refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd _ _ hS h1 _ _

theorem exists_polAV_sharpOver : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))), P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ (letI := P.isAb.comm; HypS P.A P.L) := by
  intro g n _ hn hno F W hW
  have hn0 : n ≠ 0 := by omega
  let b := cycBase hn0
  let c : SiegPre g n (b.ζ : cycAway n) (𝟙 F.X ≫ F.s) := GlobalTheory.LowChart.siegPull F.univ (𝟙 F.X) (𝟙 F.X ≫ F.s) rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ _ _ rfl F.princ
  have hd : SmoothOfRelativeDimension g c.A.hom :=
    SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit
  have hpow : b.ζ ^ n = 1 :=
    Units.ext ((Units.val_pow_eq_pow_val _ _).trans (Subtype.ext (Complex.isPrimitiveRoot_exp n hn0).pow_eq_one))
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsLocallyNoetherian (Sp (cycAway n)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  obtain ⟨bas, hb⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨t, ⟨pr, hpr, hu, hL, -, -⟩, hp⟩ := GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W _ a w w'
    bas hW hb hw hw' hs n (cycAway n) b F.X (𝟙 F.X ≫ F.s) c hpow hno hc hd
  obtain ⟨r, hr⟩ := t.rigid
  exact ⟨t.pol, r, rfl, ⟨c, GlobalTheory.LowChart.siegPB_siegPull F.univ _ _ rfl, pr, hpr, hu, hL⟩, hr,
    t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩

end GlobalTheory.SiegEighth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarised_E8ThetaPower_over_moduli : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))), P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ (letI := P.isAb.comm; HypS P.A P.L) := by
  first | exact @GlobalTheory.SiegEighth.exists_polAV_sharpOver | exact GlobalTheory.SiegEighth.exists_polAV_sharpOver | (intros; apply GlobalTheory.SiegEighth.exists_polAV_sharpOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionGenericFibreMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionGenericFibreMember
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem exists_points_frames_theta : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [hj]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨x, fr, th, rig, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩, fun a => ?_, hrig, fun a => (hfr a).1⟩
  · have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
    exact e.symm
  · have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
      (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
      (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) (hfr a).2 (s₀ := X₁.ρ.th₁) (s := th) hth
      (X₁.ρ.th_val a)
    intro z J hJ
    have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
    rw [Category.id_comp] at e
    refine e.trans ?_
    rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
    congr 1
    exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
      ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionGenericFibreMemberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_points_frames_thetaSection_genericFibre_member : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_points_frames_theta | exact GlobalTheory.Poinc.IntTerm.exists_points_frames_theta | (intros; apply GlobalTheory.Poinc.IntTerm.exists_points_frames_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicitiesGeometricPointsDescend
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicitiesGeometricPointsDescend
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieDesc

theorem lieMult_descend : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∀ i, LieMult (act₀.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ hG _ _ hpb hact hX k _ _ x β hx i
  haveI : Surjective π := hG.onto
  haveI : IsFinite π := hG.fin
  obtain ⟨y, rfl⟩ := GlobalTheory.ObjDesc.exists_geomPt_lift π k x
  have hc : ∀ c, ((act.toF D).act c).left ≫ φ = φ ≫ ((act₀.toF D).act c).left := fun c => hact _
  exact (GlobalTheory.LiePull.lieMult_pull _ _ _ A₀ A π φ (act₀.toF D) (act.toF D) hpb hc k y _ D.m).1
    (hX k y β (by rw [← Category.assoc]; exact hx) i)

end GlobalTheory.LieDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicitiesGeometricPointsDescendStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_multiplicities_geometric_points_descend : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∀ i, LieMult (act₀.toF D) x (β.comp (b.t i)) D.m) := by
  first | exact @GlobalTheory.LieDesc.lieMult_descend | exact GlobalTheory.LieDesc.lieMult_descend | (intros; apply GlobalTheory.LieDesc.lieMult_descend; all_goals assumption)
end
end
