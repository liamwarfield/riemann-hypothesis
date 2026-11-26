module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.ThirdLinkOfArchimedean
public import Formalism.LocalToGlobal.Columns.FockNormSubstitutionBound
public import Formalism.LocalToGlobal.Columns.TwistedLocalisationComparable

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL4.PacketOfFrameDegree
section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL4.NfAllSelfEq
section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL4.CfMemTwId
section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL4.CoeffMemOfIntSpanAt
section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL4.BcBasisApply
open Module NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions.flipTwoThree

section Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem bc_sum_repr (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (z : (D.sp.X 0).V) :
    CV.bc c τ z = ∑ i, CV.rho τ ((D.sp.X 0).frame.repr z i) • CV.bc c τ ((D.sp.X 0).frame i) := by
  conv_lhs => rw [← (D.sp.X 0).frame.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => CV.bc_smul c τ _ _

theorem span_bc_frame (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ⊤ ≤ Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i)) := by
  rw [← (CV.Q_good c τ).2.2]
  refine Submodule.span_le.2 ?_
  intro x hx
  have hx' : x ∈ (Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i))).restrictScalars (𝓞 D.what₂.LL) := by
    rw [CV.bc_L c τ] at hx
    refine (Submodule.span_le.2 ?_) hx
    rintro _ ⟨z, -, rfl⟩
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem, bc_sum_repr CV c τ z]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  exact hx'

theorem card_frame_eq (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Fintype.card (Fin (D.sp.X 0).rank) = finrank D.what₂.LL (CV.Q c τ).V := by
  rw [Fintype.card_fin, finrank_eq_card_basis (CV.Q c τ).b, Fintype.card_congr (CV.eQ c τ), Fintype.card_fin, D.sp.rank0, Ranks.N_zero]

def bcBasis (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Basis (Fin (D.sp.X 0).rank) D.what₂.LL (CV.Q c τ).V :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => CV.bc c τ ((D.sp.X 0).frame i)) (span_bc_frame CV c τ) (card_frame_eq CV c τ)

theorem bcBasis_apply (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (i : Fin (D.sp.X 0).rank) :
    bcBasis CV c τ i = CV.bc c τ ((D.sp.X 0).frame i) := by
  unfold bcBasis
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]

def bcFun (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) : (CV.Q c τ).V →ₗ[D.what₂.LL] D.what₂.LL :=
  (bcBasis CV c τ).constr D.what₂.LL fun i => CV.rho τ ((D.sp.X 0).hT y ((D.sp.X 0).frame i))

theorem bcFun_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y z : (D.sp.X 0).V) :
    bcFun CV c τ y (CV.bc c τ z) = CV.rho τ ((D.sp.X 0).hT y z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [bc_sum_repr CV c τ z, map_sum]
  simp_rw [map_smul]
  have h1 : ∀ i, bcFun CV c τ y (CV.bc c τ ((D.sp.X 0).frame i)) = CV.rho τ ((D.sp.X 0).hT y ((D.sp.X 0).frame i)) := fun i => by
    unfold bcFun
    rw [← bcBasis_apply CV c τ i, Basis.constr_basis]
  simp_rw [h1, smul_eq_mul, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  conv_rhs => rw [← (D.sp.X 0).frame.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

theorem bcFun_int (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) {y : (D.sp.X 0).V}
    (hy : y ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) {x : (CV.Q c τ).V} (hx : x ∈ (CV.Q c τ).L) :
    IsIntegral ℤ (bcFun CV c τ y x) := by
  rw [CV.bc_L c τ] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [bcFun_bc]
    obtain ⟨o, ho⟩ := hy z hz
    have e : (D.sp.X 0).hT y z = starRingEnd D.host.E ((D.sp.X 0).hT z y) := ((D.sp.X 0).herm.eq z y).symm
    rw [e, ← ho]
    exact ((o.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom).map (CV.rho τ).toIntAlgHom)
  | zero => rw [map_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact hx.add hy
  | smul a x _ hx =>
    rw [← algebraMap_smul D.what₂.LL a x, map_smul, smul_eq_mul]
    exact a.isIntegral_coe.mul hx

end Fun

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section G

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

def crdQ (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (CV.Q c τ).V ≃ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL) :=
  ((CV.Q c τ).b.reindex (CV.eQ c τ)).equivFun

def MQ (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Submodule (𝓞 D.what₂.LL) (Fin (D.R.N 0) → D.what₂.LL) :=
  (CV.Q c τ).L.map ((crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)).restrictScalars (𝓞 D.what₂.LL))

def gM (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
  Matrix.of fun a i => bcFun CV c τ (y a) ((CV.Q c τ).b ((CV.eQ c τ).symm i))

theorem gM_mulVec (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) (z : (CV.Q c τ).V)
    (a : Fin (D.R.N 0)) : (gM CV c y τ *ᵥ crdQ CV c τ z) a = bcFun CV c τ (y a) z := by
  show ∑ i, gM CV c y τ a i * crdQ CV c τ z i = _
  conv_rhs => rw [← ((CV.Q c τ).b.reindex (CV.eQ c τ)).sum_equivFun z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, Basis.reindex_apply, mul_comm]
  rfl

theorem gM_int (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : ∀ a, y a ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) (τ : D.what₂.Tau) :
    ∀ x ∈ MQ CV c τ, ∀ a, (gM CV c y τ *ᵥ x) a ∈ (1 : Submodule (𝓞 D.what₂.LL) D.what₂.LL) := by
  rintro _ ⟨z, hz, rfl⟩ a
  rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, gM_mulVec]
  exact Submodule.mem_one.2 ⟨⟨_, bcFun_int CV c τ (hy a) hz⟩, rfl⟩

theorem gM_unit (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y)
    (τ : D.what₂.Tau) : IsUnit (gM CV c y τ).det := by
  classical
  have hn : Fintype.card (Fin (D.R.N 0)) = finrank D.host.E (D.sp.X 0).V := by
    rw [Fintype.card_fin, (D.sp.X 0).rank_eq, D.sp.rank0, Ranks.N_zero]
  haveI : Nonempty (Fin (D.R.N 0)) := ⟨⟨0, rank_zero_pos D⟩⟩
  haveI : FiniteDimensional D.host.E (D.sp.X 0).V :=
    Module.finite_of_finrank_pos (by rw [← hn]; exact Fintype.card_pos)
  have hspan := hli.span_eq_top_of_card_eq_finrank hn
  let Φ : (D.sp.X 0).V →ₗ[D.host.E] (Fin (D.R.N 0) → D.host.E) := LinearMap.pi fun a => (D.sp.X 0).hT (y a)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    have h0 : ∀ a, (D.sp.X 0).hT (y a) z = 0 := fun a => congrFun (LinearMap.mem_ker.1 hz) a
    refine (D.sp.X 0).nondeg.2 z fun x => ?_
    have hx : x ∈ Submodule.span D.host.E (Set.range y) := hspan ▸ Submodule.mem_top
    have hx' := (Submodule.span_le (p := LinearMap.ker ((D.sp.X 0).hT.flip z))).2 (by
      rintro _ ⟨a, rfl⟩
      exact LinearMap.mem_ker.2 (by rw [LinearMap.flip_apply]; exact h0 a)) hx
    have := LinearMap.mem_ker.1 hx'
    rwa [LinearMap.flip_apply] at this
  have hfin : finrank D.host.E (D.sp.X 0).V = finrank D.host.E (Fin (D.R.N 0) → D.host.E) := by
    rw [Module.finrank_fin_fun, ← hn, Fintype.card_fin]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
  rw [← Matrix.isUnit_iff_isUnit_det]
  refine Matrix.linearIndependent_rows_iff_isUnit.1 ?_
  rw [Fintype.linearIndependent_iff]
  intro t ht b
  obtain ⟨z, hz⟩ := hsurj (Pi.single b 1)
  have hz' : ∀ a, (D.sp.X 0).hT (y a) z = (Pi.single b (1 : D.host.E) : Fin (D.R.N 0) → D.host.E) a := fun a => congrFun hz a
  have hi : ∀ i, ∑ a, t a * gM CV c y τ a i = 0 := fun i => by
    have := congrFun ht i
    simpa [Finset.sum_apply] using this
  have key : ∑ a, t a * CV.rho τ ((D.sp.X 0).hT (y a) z) = 0 := by
    have e1 : ∀ a, CV.rho τ ((D.sp.X 0).hT (y a) z) = ∑ i, gM CV c y τ a i * crdQ CV c τ (CV.bc c τ z) i := by
      intro a
      rw [← bcFun_bc CV c τ (y a) z, ← gM_mulVec CV c y τ]
      rfl
    simp_rw [e1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hi i, zero_mul]
  simpa [hz', Pi.single_apply] using key

def gG (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y) :
    D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL :=
  fun τ => Matrix.nonsingInvUnit _ (gM_unit CV c y hli τ)

theorem gG_coe (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y)
    (τ : D.what₂.Tau) : ((gG CV c y hli τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) =
      gM CV c y τ := rfl

end G

section Loc

variable {D : D7}

theorem coeff_mem_of_intSpanAt {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n)
    {p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL} (hp : p ∈ IntSpanAt D w lam) (m : (D.what₂.Tau × Fin n × Fin n) →₀ ℕ) :
    AddMonoidAlgebra.coeff p m ∈ intW D.what₂.places w := by
  unfold IntSpanAt at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hr, -, rfl⟩ := hx
    have hten : Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)) =
        MvPolynomial.map (Int.castRingHom D.what₂.LL) (∏ τ, rename (fun v => (τ, v)) (f τ)) := by
      unfold Formalism.MainNotions.flipTwoThree.ten
      rw [map_prod]
      all_goals exact Finset.prod_congr rfl fun τ _ => by rw [MvPolynomial.map_rename]
    rw [MvPolynomial.coeff_smul, hten, MvPolynomial.coeff_map, smul_eq_mul]
    exact (intW D.what₂.places w).mul_mem hr (intCast_mem _ _)
  | zero =>
    rw [MvPolynomial.coeff_zero]
    exact (intW D.what₂.places w).zero_mem
  | add x y _ _ hx hy =>
    rw [MvPolynomial.coeff_add]
    exact (intW D.what₂.places w).add_mem hx hy
  | neg x _ hx =>
    rw [MvPolynomial.coeff_neg]
    exact (intW D.what₂.places w).neg_mem hx

theorem intW_mem_locRing (w : D.what₂.places.Pl) {x : D.what₂.LL} (hx : x ∈ intW D.what₂.places w) : x ∈ locRing (D.plEq w) := by
  show x ∈ localization₂ (D.plEq w).asIdeal (1 : Submodule (𝓞 D.what₂.LL) D.what₂.LL)
  have h1 : (1 : Submodule (𝓞 D.what₂.LL) D.what₂.LL) = latOf (K := D.what₂.LL) (fun _ : Unit => (1 : D.what₂.LL)) := by
    rw [Submodule.one_eq_span]
    unfold latOf
    rw [Set.range_const]
  rw [h1, mem_localization_latticeOf_iff, Set.range_const, Submodule.mem_span_singleton]
  exact ⟨⟨x, hx⟩, by rw [Subring.smul_def, smul_eq_mul, mul_one]⟩

theorem mem_localization_map_equiv {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (P : Ideal (𝓞 K)) [P.IsPrime] (e : V ≃ₗ[K] W) (A : Submodule (𝓞 K) V) (x : V) :
    e x ∈ localization₂ P (A.map ((e : V →ₗ[K] W).restrictScalars (𝓞 K))) ↔ x ∈ localization₂ P A := by
  show (∃ s ∈ P.primeCompl, s • e x ∈ A.map ((e : V →ₗ[K] W).restrictScalars (𝓞 K))) ↔
    ∃ s ∈ P.primeCompl, s • x ∈ A
  have key : ∀ (s : 𝓞 K) (x : V), e (s • x) = s • e x := fun s x =>
    (e : V →ₗ[K] W).map_smul_of_tower s x
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨z, hz, hze⟩ := Submodule.mem_map.mp hx
    refine ⟨s, hs, ?_⟩
    have hzx : z = s • x := e.injective (by rw [key]; exact hze)
    rwa [← hzx]
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, Submodule.mem_map.mpr ⟨s • x, hx, by
      rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, key]⟩⟩

end Loc

section Int

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem colLat_eq_map (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (B : GL (Fin (D.R.N 0)) D.what₂.LL) :
    colLat B = (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) =>
      ∑ i, (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)).map
        ((crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)).restrictScalars (𝓞 D.what₂.LL)) := by
  have hb : ∀ i, crdQ CV c τ ((CV.Q c τ).b ((CV.eQ c τ).symm i)) = Pi.single i 1 := by
    intro i
    unfold crdQ
    rw [← Basis.reindex_apply]
    ext j
    simp [Basis.equivFun_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]
  unfold latOf colLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span _) (congrArg Set.range ?_)
  funext j a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Function.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, map_sum, map_smul, hb]
  simp [Pi.single_apply]

theorem locBasis_of_isBasisAt (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (w : D.what₂.places.Pl) (B : GL (Fin (D.R.N 0)) D.what₂.LL)
    (hB : IsBasisAt (D.plEq w) (MQ CV c τ) B) :
    LocBasis D w (CV.Q c τ) (CV.eQ c τ) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) := by
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mp B.isUnit, ?_⟩
  ext x
  rw [← mem_localization_iff_localizationAtPlace, ← mem_localization_latticeOf_iff D w,
    ← mem_localization_map_equiv (D.plEq w).asIdeal (crdQ CV c τ) (CV.Q c τ).L x,
    ← mem_localization_map_equiv (D.plEq w).asIdeal (crdQ CV c τ)
      (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) =>
        ∑ i, (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) x,
    ← colLat_eq_map CV c τ B]
  change crdQ CV c τ x ∈ localization₂ (D.plEq w).asIdeal (MQ CV c τ) ↔ _
  rw [hB]

end Int

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Int2

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem cf_mem_twId (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V)
    (hy : ∀ a, y a ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) (g : D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL)
    (hg : ∀ τ, ((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) = gM CV c y τ)
    {x : ((D.fm u).lat 0).V} (hx : x ∈ NC CV c) (m : MonI ((D.fm u).lam 0)) :
    cfMap ((D.fm u).lam 0) g (coE CV (hTV0 D u) x c) m ∈ twId ((D.fm u).lam 0) (MQ CV c) := by
  classical
  rw [mem_twId]
  intro w B hB
  set w' := D.plEq.symm w with hw'
  have hw : D.plEq w' = w := D.plEq.apply_symm_apply w
  have hLB : ∀ τ, LocBasis D w' (CV.Q c τ) (CV.eQ c τ) (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) :=
    fun τ => locBasis_of_isBasisAt CV c τ w' (B τ) (by rw [hw]; exact hB τ)
  let γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL := fun c' τ =>
    if c' = c then (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)
    else Classical.choose (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hγ : ∀ c' τ, LocBasis D w' (CV.Q c' τ) (CV.eQ c' τ) (γ c' τ) := by
    intro c' τ
    by_cases h : c' = c
    · simp only [γ, if_pos h]
      rw [h]
      exact hLB τ
    · simp only [γ, if_neg h]
      exact Classical.choose_spec (exists_locBasis w' (CV.Q c' τ) (CV.Q_good c' τ) (CV.eQ c' τ))
  have hxL : x ∈ ((D.fm u).lat 0).L := by
    obtain ⟨x', hx', rfl⟩ := hx
    exact prjC_mem CV c hx'
  have hxW : x ∈ locW D.what₂.places w' ((D.fm u).lat 0).L := Submodule.subset_span hxL
  have hP := (CV.fin w' γ hγ x).1 hxW c
  simp only [γ, if_pos rfl] at hP
  set F : Pol D.what₂.LL D.what₂.Tau (D.R.N 0) := ((coE CV (hTV0 D u) x c : VV D.what₂.LL ((D.fm u).lam 0)) :
    Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) with hF
  have hFco : F = CV.co x c := coE_coe CV (hTV0 D u) x c
  have hinvB : (fun τ => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) =
      fun τ => (((B⁻¹) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) := by
    funext τ
    rw [Pi.inv_apply, Matrix.coe_units_inv]
  rw [← hFco, hinvB, actAll_eq_actP] at hP
  have hF0 : actP ((D.fm u).lam 0) B⁻¹ F ∈ (map (σ := D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) (locRing w).subtype).range := by
    refine mem_range_of_coeff_mem _ fun m' => ?_
    rw [← hw]
    exact intW_mem_locRing w' (coeff_mem_of_intSpanAt w' _ hP m')
  have hU : ∀ τ a b, (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b ∈
      locRing w := by
    intro τ a b
    have hcol : (fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) ∈ localization₂ w.asIdeal (MQ CV c τ) := by
      rw [hB τ]
      exact le_localisation w _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨s, hs, hsx⟩ := hcol
    rw [mem_locRing]
    refine ⟨s, hs, ?_⟩
    have := gM_int CV c y hy τ _ hsx b
    rw [← hg τ, Matrix.mulVec_smul] at this
    have e : (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ a b =
        ((g τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) *ᵥ fun c => (B τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) c a) b := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e]
    exact this
  have hkey := coeff_mem_of_mem_range _ (block_action_integral (locRing w) _ hU hF0) m.1
  have e : Formalism.GradedWeylDivisibility.blockAct D.what₂.LL (fun τ => (((g * B) τ : GL (Fin (D.R.N 0)) D.what₂.LL) :
      Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ) (actP ((D.fm u).lam 0) B⁻¹ F) =
      detTwK ((D.fm u).lam 0) B⁻¹ • trAct g F := by
    show trAct (g * B) (actP ((D.fm u).lam 0) B⁻¹ F) = _
    rw [trAct_mul]
    simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_smul, transpose_action_inv_right]
  rw [e, coeff_smul, smul_eq_mul, mem_locRing] at hkey
  exact hkey

end Int2

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

theorem emb_nonreal {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ) : ∃ a : E, (φ a).im ≠ 0 := by
  by_contra h
  push Not at h
  have hr : NumberField.ComplexEmbedding.IsReal φ :=
    NumberField.ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun x => by
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.mpr (h x))
  exact NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
    (IsTotallyComplex.isComplex (NumberField.InfinitePlace.mk φ))
    (NumberField.InfinitePlace.isReal_mk_iff.mpr hr)

theorem map_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {K : Type} [Field K] [CharZero K] (s : K →+* ℂ)
    {F : Pol K ι n} (hF : F ∈ VV K lam) : MvPolynomial.map s F ∈ VV ℂ lam := by
  obtain ⟨Z, -⟩ := standard_basis_z ι n lam
  rw [← Z.span_F K] at hF
  rw [← Z.span_F ℂ]
  induction hF using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    rw [MvPolynomial.map_map, show s.comp (Int.castRingHom K) = Int.castRingHom ℂ from RingHom.ext_int _ _]
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [map_add]; exact add_mem hp hq
  | smul a p _ hp =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hp

theorem fockN_smul {σ : Type} (d : ℂ) (f : MvPolynomial σ ℂ) : fockN (d • f) = ‖d‖ ^ 2 * fockN f := by
  unfold fockN
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  · rw [MvPolynomial.support_smul_eq hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul, mul_pow, mul_assoc]

theorem nfAll_self_eq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam p p = ((fockN p / extremalFockNormProduct lam : ℝ) : ℂ) := by
  exact nfL_self lam p

end SlopeTestRemainingChoices

section Nrm

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem maj_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) (y z : (D.sp.X 0).V) :
    majAt (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ y) (CV.bc c τ z) = v.embedding (CV.rho τ ((D.sp.X 0).hT y z)) := by
  have := (columnHypotheses D u).tcE
  have hcm : ∀ (φ : D.host.E →+* ℂ) (a : D.host.E), φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1
  set φ : D.host.E →+* ℂ := v.embedding.comp (CV.rho τ) with hφ
  obtain ⟨s1, s2, s3, s4⟩ := isSesq_maj (CV.Q c τ).b (CV.Q c τ).X v
  beta_reduce at s1 s2 s3 s4
  refine sesq_ext (F := fun y z => majAt (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ y) (CV.bc c τ z))
    (G := fun y z => φ ((D.sp.X 0).hT y z)) (σ := φ) (emb_nonreal φ) ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ y z
  · intro x x' y
    show majAt _ _ v (CV.bc c τ (x + x')) _ = _
    rw [map_add (f := _), s1]
  · intro x y y'
    show majAt _ _ v _ (CV.bc c τ (y + y')) = _
    rw [map_add (f := _), s2]
  · intro a x y
    show majAt _ _ v (CV.bc c τ (a • x)) _ = _
    rw [CV.bc_smul, s3]
    rfl
  · intro a x y
    show majAt _ _ v _ (CV.bc c τ (a • y)) = _
    rw [CV.bc_smul, s4]
    rfl
  · intro x x' y
    show φ ((D.sp.X 0).hT (x + x') y) = φ ((D.sp.X 0).hT x y) + φ ((D.sp.X 0).hT x' y)
    rw [map_add (f := _), LinearMap.add_apply, map_add (f := _)]
  · intro x y y'
    show φ ((D.sp.X 0).hT x (y + y')) = φ ((D.sp.X 0).hT x y) + φ ((D.sp.X 0).hT x y')
    rw [map_add (f := _), map_add (f := _)]
  · intro a x y
    show φ ((D.sp.X 0).hT (a • x) y) = starRingEnd ℂ (φ a) * φ ((D.sp.X 0).hT x y)
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul, starRingEnd_apply, hcm]
  · intro a x y
    show φ ((D.sp.X 0).hT x (a • y)) = φ a * φ ((D.sp.X 0).hT x y)
    rw [map_smul, smul_eq_mul, map_mul]
  · intro x
    show majAt _ _ v (CV.bc c τ x) (CV.bc c τ x) = φ ((D.sp.X 0).hT x x)
    have hre := CV.bc_norm c τ v x
    have hreal : (φ ((D.sp.X 0).hT x x)).im = 0 := by
      have e : starRingEnd D.host.E ((D.sp.X 0).hT x x) = (D.sp.X 0).hT x x := (D.sp.X 0).herm.eq x x
      have e2 : starRingEnd ℂ (φ ((D.sp.X 0).hT x x)) = φ ((D.sp.X 0).hT x x) := by
        rw [← hcm, ← starRingEnd_apply, e]
      exact Complex.conj_eq_iff_im.1 e2
    apply Complex.ext
    · exact hre
    · rw [majAt_self, Complex.ofReal_im]
      exact hreal.symm

theorem riesz_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) (y : (D.sp.X 0).V)
    (q : (CV.Q c τ).V) : v.embedding (bcFun CV c τ y q) = majAt (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ y) q := by
  obtain ⟨s1, s2, s3, s4⟩ := isSesq_maj (CV.Q c τ).b (CV.Q c τ).X v
  beta_reduce at s1 s2 s3 s4
  have hq : q ∈ Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i)) :=
    span_bc_frame CV c τ Submodule.mem_top
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨i, rfl⟩ := hq
    rw [bcFun_bc, maj_bc]
  | zero =>
    rw [map_zero, map_zero]
    have := s2 (CV.bc c τ y) 0 0
    rw [add_zero] at this
    linear_combination this
  | add q q' _ _ h1 h2 => rw [map_add (f := _), map_add (f := _), s2, h1, h2]
  | smul a q _ h1 => rw [map_smul, smul_eq_mul, map_mul, s4, h1]

theorem gM_map (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) :
    (gM CV c y τ).map v.embedding =
      Matrix.of (fun a k => star (fcoord (CV.Q c τ).b (CV.Q c τ).X v (CV.bc c τ (y a)) ((CV.eQ c τ).symm k))) *
        Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹ := by
  classical
  ext a j
  simp only [Matrix.map_apply, gM, Matrix.of_apply]
  rw [riesz_bc, Matrix.mul_apply]
  unfold majAt
  refine Fintype.sum_equiv (CV.eQ c τ) _ _ fun i => ?_
  simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  congr 1
  simp [fcoord, vecAt, Matrix.mulVec, dotProduct, Basis.repr_self, Finsupp.single_apply]

theorem invFr_coe (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ) =
      Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹ := rfl

theorem hsN_gM (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (τ : D.what₂.Tau) (v : InfinitePlace D.what₂.LL) :
    hsN (((gM CV c y τ).map v.embedding *
        (((invFr CV v c τ)⁻¹ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ))ᵀ) =
      ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re := by
  have hdet : IsUnit (Matrix.reindex (CV.eQ c τ) (CV.eQ c τ) ((CV.Q c τ).X v)⁻¹).det := by
    rw [← invFr_coe]
    exact Matrix.isUnits_det_units _
  rw [gM_map, Matrix.coe_units_inv, invFr_coe, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  unfold hsN
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← CV.bc_norm c τ v (y a), majAt_self, Complex.ofReal_re]
  unfold normAt cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  refine Fintype.sum_equiv (CV.eQ c τ).symm _ _ fun k => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply, norm_star]

theorem tcAt_mem_VV (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) :
    tcAt CV v c x ∈ VV ℂ ((D.fm u).lam 0) := by
  unfold tcAt
  refine polyAction_mem_VV _ _ (map_mem_VV _ v.embedding ?_)
  rw [← coE_coe CV (hTV0 D u) x c]
  exact (coE CV (hTV0 D u) x c).2

theorem class_norm (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hli : LinearIndependent D.host.E y)
    (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V) :
    normAt (Pi.basisFun D.what₂.LL (MonI ((D.fm u).lam 0))) (fun _ => (monD ((D.fm u).lam 0))⁻¹) v
        (cfMap ((D.fm u).lam 0) (gG CV c y hli) (coE CV (hTV0 D u) x c)) ^ 2 ≤
      ((∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW ((D.fm u).lam 0 τ)) *
          ‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2) *
        normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 := by
  set lam := (D.fm u).lam 0 with hlam
  set g := gG CV c y hli with hg
  set F : Pol D.what₂.LL D.what₂.Tau (D.R.N 0) :=
    ((coE CV (hTV0 D u) x c : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) with hF
  set P := tcAt CV v c x with hP
  set d : ℂ := detTwK lam (invFr CV v c)⁻¹ with hd
  set U : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    ((((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL).map v.embedding) *
      (((invFr CV v c τ)⁻¹ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ))ᵀ with hU
  set G := MvPolynomial.map v.embedding (trAct g F) with hGdef
  set Gp := ∏ τ, (∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re) ^ dW (lam τ) with hGp
  have h1 : normAt (Pi.basisFun D.what₂.LL (MonI lam)) (fun _ => (monD lam)⁻¹) v (cfMap lam g (coE CV (hTV0 D u) x c)) ^ 2 ≤
      fockN G / extremalFockNormProduct lam := by
    rw [monH_norm]
    have e1 : ∑ m, monW lam m * ‖v.embedding (cfMap lam g (coE CV (hTV0 D u) x c) m)‖ ^ 2 =
        (∑ m : MonI lam, ‖AddMonoidAlgebra.coeff G m.1‖ ^ 2 * (mfact m.1 : ℝ)) / extremalFockNormProduct lam := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hGdef, coeff_map, cfMap_apply, monW]
      ring
    have e2 : ∑ m : MonI lam, ‖AddMonoidAlgebra.coeff G m.1‖ ^ 2 * (mfact m.1 : ℝ) ≤ fockN G := by
      have := fockN_sum_le G ((Finset.univ : Finset (MonI lam)).map ⟨fun m : MonI lam => m.1, fun a b h => Subtype.ext h⟩)
      rwa [Finset.sum_map] at this
    rw [e1]
    exact div_le_div_of_nonneg_right e2 (extR_pos lam).le
  have hVt : ∀ τ, (((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ))ᵀ * U τ =
      (((g τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)ᵀ).map v.embedding := by
    intro τ
    simp only [hU]
    rw [← Matrix.transpose_mul, Matrix.coe_units_inv, Matrix.nonsing_inv_mul_cancel_right _ _ (Matrix.isUnits_det_units _),
      Matrix.transpose_map]
  have eP : P = detTwK lam (invFr CV v c) • Formalism.GradedWeylDivisibility.blockAct ℂ
      (fun τ => ((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)ᵀ)
      (MvPolynomial.map v.embedding F) := by
    simp only [hP, tcAt, actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct]
    rfl
  have ecomp : Formalism.GradedWeylDivisibility.blockAct ℂ U (Formalism.GradedWeylDivisibility.blockAct ℂ
      (fun τ => ((invFr CV v c τ : GL (Fin (D.R.N 0)) ℂ) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)ᵀ)
      (MvPolynomial.map v.embedding F)) = G := by
    rw [← AlgHom.comp_apply, blockAct_comp]
    simp only [hVt]
    rw [hGdef]
    unfold trAct
    rw [map_blockAct]
  have hd1 : d * detTwK lam (invFr CV v c) = 1 := by rw [hd, ← detTwK_mul, inv_mul_cancel, detTwK_one]
  have h2 : G = d • Formalism.GradedWeylDivisibility.blockAct ℂ U P := by
    rw [eP, map_smul, ecomp, smul_smul, hd1, one_smul]
  have hPV : P ∈ VV ℂ lam := tcAt_mem_VV CV v c x
  have h3 : fockN (Formalism.GradedWeylDivisibility.blockAct ℂ U P) ≤ (∏ τ, hsN (U τ) ^ dW (lam τ)) * fockN P := by
    refine fockSubNorm D.what₂.Tau (D.R.N 0) U (fun τ => dW (lam τ)) P fun m hm τ => ?_
    have hm' := coefficient_space_support ℂ lam hPV m hm
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => hm' τ s
  have h4 : ∀ τ, hsN (U τ) = ∑ a, (v.embedding (CV.rho τ ((D.sp.X 0).hT (y a) (y a)))).re := fun τ =>
    hsN_gM CV c y τ v
  have h5 : fockN P / extremalFockNormProduct lam ≤ normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 := by
    have e := majorant_lattice_eq_sum CV v x x
    rw [majAt_self] at e
    have e2 : normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 = ∑ c', fockN (tcAt CV v c' x) / extremalFockNormProduct lam := by
      have := congrArg Complex.re e
      rw [Complex.ofReal_re, Complex.re_sum] at this
      rw [this]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [nfAll_self_eq, Complex.ofReal_re]
    rw [e2]
    exact Finset.single_le_sum (f := fun c' => fockN (tcAt CV v c' x) / extremalFockNormProduct lam)
      (fun c' _ => div_nonneg (fockN_nonneg _) (extR_pos _).le) (Finset.mem_univ c)
  have hGn : fockN G ≤ ‖d‖ ^ 2 * (Gp * fockN P) := by
    rw [h2, fockN_smul]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have := h3
    simp only [h4] at this
    exact this
  have hprod : 0 ≤ Gp :=
    Finset.prod_nonneg fun τ _ => pow_nonneg (by rw [← h4 τ]; exact hsN_nonneg _) _
  calc normAt (Pi.basisFun D.what₂.LL (MonI lam)) (fun _ => (monD lam)⁻¹) v (cfMap lam g (coE CV (hTV0 D u) x c)) ^ 2
      ≤ fockN G / extremalFockNormProduct lam := h1
    _ ≤ ‖d‖ ^ 2 * (Gp * fockN P) / extremalFockNormProduct lam := div_le_div_of_nonneg_right hGn (extR_pos lam).le
    _ = (Gp * ‖d‖ ^ 2) * (fockN P / extremalFockNormProduct lam) := by ring
    _ ≤ (Gp * ‖d‖ ^ 2) * normAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x ^ 2 :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg hprod (sq_nonneg _))

end Nrm

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def QFrameDeg (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) c τ,
    (D.R.N 0 : ℝ) * (CV.Q c τ).mu =
      (D.R.N 0 : ℝ) * (latK D.what₂.LL (MQ CV c τ)).mu +
        (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)

section T

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem MQ_lattice (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Submodule.IsLattice D.what₂.LL (MQ CV c τ) := by
  exact Submodule.IsLattice.of_fg _ ((CV.Q_good c τ).2.1.map _)

theorem MQ_fullLattice (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Submodule.IsFullLattice D.what₂.LL (MQ CV c τ) := by
  refine { toIsLattice := MQ_lattice CV c τ, span_eq_top := ?_ }
  unfold MQ
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars]
  rw [show ⇑(crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)) = ⇑(crdQ CV c τ) from rfl]
  rw [← LinearEquiv.coe_coe, Submodule.span_image, (CV.Q_good c τ).2.2, Submodule.map_top]
  exact LinearEquiv.range _

theorem detTwK_inv_ne (c : (D.mem u).C.cls 0) (v : InfinitePlace D.what₂.LL) :
    detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹ ≠ 0 := by
  unfold detTwK
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
  unfold detPow
  exact Units.ne_zero _

theorem det_invFr_inv (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((Matrix.GeneralLinearGroup.det ((invFr CV v c)⁻¹ τ) : ℂˣ) : ℂ) = ((CV.Q c τ).X v).det := by
  simp only [Pi.inv_apply, map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, invFr,
    brpGL]
  show ((Matrix.reindex (CV.eQ c τ) (CV.eQ c τ)) ((CV.Q c τ).X v)⁻¹).det⁻¹ = _
  rw [Matrix.det_reindex_self, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_inv]

theorem log_detTw (c : (D.mem u).C.cls 0) (v : InfinitePlace D.what₂.LL) :
    Real.log (‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2) =
      ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * Real.log (‖((CV.Q c τ).X v).det‖ ^ 2) := by
  unfold detTwK
  simp only [detPow, Units.val_zpow_eq_zpow_val, det_invFr_inv, norm_prod, norm_zpow]
  have hne : ∀ τ, ((CV.Q c τ).X v).det ≠ 0 := fun τ => by
    rw [← det_invFr_inv CV v c τ]
    exact Units.ne_zero _
  rw [← Finset.prod_pow, Real.log_prod]
  · refine Finset.sum_congr rfl fun τ _ => ?_
    rw [show (‖((CV.Q c τ).X v).det‖ ^ ((D.fm u).lam 0 τ).detShift) ^ 2 =
        (‖((CV.Q c τ).X v).det‖ ^ 2) ^ ((D.fm u).lam 0 τ).detShift by rw [sq, sq, mul_zpow], Real.log_zpow]
  · intro τ _
    exact pow_ne_zero _ (zpow_ne_zero _ (norm_ne_zero_iff.mpr (hne τ)))

theorem detShift_eq (τ : D.what₂.Tau) :
    ((((D.fm u).lam 0 τ).detShift : ℤ) : ℝ) = ((lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) := by
  have hn := rank_zero_pos D
  have hk := columnCount_pos D
  unfold DomWeight.detShift
  rw [dite_eq_left hn]
  have := weight_eq_lamCol D u τ ⟨D.R.N 0 - 1, by omega⟩
  rw [this]
  congr 3
  simp [Ranks.N_zero]

theorem classMapT_of (h : QFrameDeg D) : ClassMapT D := by
  intro u CV c y hy
  obtain ⟨hyd, hli, -⟩ := hy
  have := (columnHypotheses D u).tc
  have hn : 0 < D.R.N 0 := rank_zero_pos D
  have hM : ∀ τ, Submodule.IsFullLattice D.what₂.LL (MQ CV c τ) := MQ_fullLattice CV c
  refine ⟨cfMap ((D.fm u).lam 0) (gG CV c y hli) ∘ₗ (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))), twIdeal ((D.fm u).lam 0) (MQ CV c) hM,
    fun v => ‖detTwK ((D.fm u).lam 0) (invFr CV v c)⁻¹‖ ^ 2, ?_, twIdeal_ne_zero _ _ hM, ?_, ?_, ?_, ?_⟩
  · exact injOn_NC CV c _ (cfMap_injective _ _)
  · intro x hx m
    rw [twIdeal_coe]
    exact cf_mem_twId CV c y hyd (gG CV c y hli) (fun τ => gG_coe CV c y hli τ) hx m
  · intro v
    exact pow_pos (norm_pos_iff.2 (detTwK_inv_ne CV c v)) 2
  · intro v x
    exact class_norm CV c y hli v x
  · rw [twisted_ideal_norm_formula D.what₂.LL hn _ _ hM]
    simp_rw [log_detTw CV c]
    have hQ := fun τ => h u CV c τ
    have hslope := fun τ => q_lattice_slope D u CV c τ
    have hk : (D.R.N 0 : ℝ) = (D.R.k : ℝ) := by rw [Ranks.N_zero]
    have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast columnCount_pos D
    have e1 : (1 / (nPl D.what₂.LL : ℝ)) * ∑ v, ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * Real.log (‖((CV.Q c τ).X v).det‖ ^ 2) =
        ∑ τ, (((D.fm u).lam 0 τ).detShift : ℝ) * ((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Finset.mul_sum]
      ring
    rw [e1, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine le_of_eq (Finset.sum_congr rfl fun τ _ => ?_)
    rw [← mul_add, ← hQ τ, hslope τ, hk, detShift_eq]
    field_simp

end T

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Col Formalism.BasicNotions.SkeletonIndexLemmas
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GramSelf

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem gramJ_self_det (A : HLat K) (v : InfinitePlace K) : (gramJ A A.b v).det.re = (‖(A.X v).det‖ ^ 2)⁻¹ := by
  classical
  have h : ∀ i', (A.X v)⁻¹ *ᵥ vecAt A.b v (A.b i') = fun k => (A.X v)⁻¹ k i' := by
    intro i'
    funext k
    simp [vecAt, Matrix.mulVec, dotProduct, Finsupp.single_apply]
  have e : gramJ A A.b v = ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ := by
    ext i j
    simp only [gramJ, Matrix.of_apply, majAt, fcoord, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [h, h]
  have hz : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [show star z * z = ((Complex.normSq z : ℝ) : ℂ) by rw [Complex.normSq_eq_conj_mul_self]; rfl,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [e, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hz, norm_inv, inv_pow]

end GramSelf

section F

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem crd_fam (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)
    (a : Fin (D.R.N 0)) :
    crdQ CV c τ (∑ i, B i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) = famOf (Pi.basisFun D.what₂.LL (Fin (D.R.N 0))) B a := by
  ext j
  simp [crdQ, famOf, Basis.equivFun_apply, Finset.sum_apply, Pi.basisFun_apply,
    Finsupp.single_apply, Pi.single_apply]

theorem latOf_map_crd (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) :
    (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) => ∑ i, B i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)).map
        ((crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)).restrictScalars (𝓞 D.what₂.LL)) =
      latOf (K := D.what₂.LL) (famOf (Pi.basisFun D.what₂.LL (Fin (D.R.N 0))) B) := by
  simp only [latOf, Submodule.map_span, ← Set.range_comp]
  congr 1
  congr 1
  funext a
  exact crd_fam CV c τ B a

theorem q_frame_degree (D : D7) : QFrameDeg D := by
  intro u CV c τ
  classical
  have := (columnHypotheses D u).tc
  have hQ := CV.Q_good c τ
  have hn : 0 < D.R.N 0 := rank_zero_pos D
  haveI : Nonempty (Fin (D.R.N 0)) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (CV.Q c τ).ι := ⟨(CV.eQ c τ).symm ⟨0, hn⟩⟩
  have hfr : Module.finrank D.what₂.LL (CV.Q c τ).V = D.R.N 0 := by
    rw [Module.finrank_eq_card_basis (CV.Q c τ).b, Fintype.card_congr (CV.eQ c τ), Fintype.card_fin]
  choose bK hbK using fun p : FinPl D.what₂.LL => exists_basis_locP (toH p) hQ.2.1 hQ.2.2 hfr
  set g : FinPl D.what₂.LL → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
    fun p => ((CV.Q c τ).b.reindex (CV.eQ c τ)).toMatrix (bK p) with hgdef
  have hg : ∀ p, (g p).det ≠ 0 := fun p => by
    have := ((CV.Q c τ).b.reindex (CV.eQ c τ)).isUnit_det (bK p)
    rw [Basis.det_apply] at this
    exact this.ne_zero
  have hfam : ∀ p, (fun a : Fin (D.R.N 0) => ∑ i, g p i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) = bK p := fun p => by
    funext a
    have := ((CV.Q c τ).b.reindex (CV.eQ c τ)).sum_repr (bK p a)
    simpa [hgdef, Basis.toMatrix_apply, Basis.reindex_apply] using this
  have hloc : ∀ p, localization₂ (toH p).asIdeal (CV.Q c τ).L = localization₂ (toH p).asIdeal
      (latOf (K := D.what₂.LL) fun a : Fin (D.R.N 0) => ∑ i, g p i a • (CV.Q c τ).b ((CV.eQ c τ).symm i)) := fun p => by
    rw [hfam p, hbK p]
  obtain ⟨-, -, hmuQ⟩ := mu_of_frames (CV.Q c τ) hQ (ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc)
  have hML := MQ_lattice CV c τ
  have hspan : Submodule.span D.what₂.LL (MQ CV c τ : Set (Fin (D.R.N 0) → D.what₂.LL)) = ⊤ := by
    unfold MQ
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars]
    rw [show ⇑(crdQ CV c τ : (CV.Q c τ).V →ₗ[D.what₂.LL] (Fin (D.R.N 0) → D.what₂.LL)) = ⇑(crdQ CV c τ) from rfl]
    rw [← LinearEquiv.coe_coe, Submodule.span_image, hQ.2.2, Submodule.map_top]
    exact LinearEquiv.range _
  have hstdGood : (stdHL D.what₂.LL (MQ CV c τ)).Good := ⟨fun _ => by simp, hML.fg, hspan⟩
  let FS : FrameData (stdHL D.what₂.LL (MQ CV c τ)) (Fin (D.R.N 0)) :=
    { e := Pi.basisFun D.what₂.LL (Fin (D.R.N 0))
      Γ := g
      det_ne := hg
      loc := fun p => by
        show localization₂ (toH p).asIdeal (MQ CV c τ) = _
        ext z
        obtain ⟨q, rfl⟩ := (crdQ CV c τ).surjective z
        unfold MQ
        rw [mem_localization_map_equiv, hloc p, ← latOf_map_crd CV c τ (g p), mem_localization_map_equiv] }
  obtain ⟨-, -, hmuS⟩ := mu_of_frames (stdHL D.what₂.LL (MQ CV c τ)) hstdGood FS
  rw [brp_latK_mu D.what₂.LL (MQ CV c τ) hML.fg]
  have hQinf : infPart (fun v => (gramJ (CV.Q c τ) (ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc).e v).det.re) =
      -((1 / (nPl D.what₂.LL : ℝ)) * ∑ v, Real.log (‖((CV.Q c τ).X v).det‖ ^ 2)) := by
    unfold infPart
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    beta_reduce
    rw [show ((ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc).e : (CV.Q c τ).ι → (CV.Q c τ).V) = (CV.Q c τ).b from rfl,
      gramJ_self_det, Real.log_inv]
  have hSinf : infPart (fun v => (gramJ (stdHL D.what₂.LL (MQ CV c τ)) FS.e v).det.re) = 0 := by
    unfold infPart
    rw [Finset.sum_eq_zero fun v _ => ?_, mul_zero]
    beta_reduce
    rw [show (FS.e : Fin (D.R.N 0) → (Fin (D.R.N 0) → D.what₂.LL)) = (stdHL D.what₂.LL (MQ CV c τ)).b from rfl,
      gramJ_self_det]
    simp
  have hfin : finPart (fun p => ((ownFrame (CV.Q c τ) (CV.eQ c τ) g hg hloc).Γ p).det) = finPart (fun p => (FS.Γ p).det) := by
    congr 1
    funext p
    exact Matrix.det_submatrix_equiv_self _ _
  have hcQ : (Fintype.card (CV.Q c τ).ι : ℝ) = (D.R.N 0 : ℝ) := by
    rw [Fintype.card_congr (CV.eQ c τ), Fintype.card_fin]
  rw [hcQ] at hmuQ
  rw [Fintype.card_fin] at hmuS
  rw [hmuQ, hmuS, hQinf, hSinf, hfin]
  ring

theorem class_map_archimedean (D : D7) : ClassMapT D :=
  classMapT_of (q_frame_degree D)

end F

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
