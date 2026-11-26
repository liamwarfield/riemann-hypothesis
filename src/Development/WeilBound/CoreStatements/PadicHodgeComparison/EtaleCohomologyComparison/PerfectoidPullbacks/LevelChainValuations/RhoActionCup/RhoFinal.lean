module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.CupGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.RHofLev
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CrystallineFirstChernLevelCompat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomSGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.LatLink

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomPullRHofGood
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)
  (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
  (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rHN : ∀ n j, N.Hc false n j →ₛₗ[L.lam] HM (QA L N s) none ((l : L.A) ^ n) j)
  (rHM : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

theorem homPull_good_of_nmHM_pull
    (hr : ∀ n j x, nmHM (nmPullA L u hu) l s none n j (rHN n j x) =
      rHM n j (B.pullHc (okToOC l K) (B.schMap u hu) false n j x)) :
    (homPull hL u hu s hQN hQM rHN rHM).Good :=
  { ℓ := rfl
    lam := fun _ => rfl
    ι := fun _ => rfl
    o := fun _ => rfl
    tS := fun n j x => ((Model.pullH u hu false j).comm n x).symm
    r := hr
    red := fun n j z => nmHM_redM _ l s none n j z
    b := nmHO_nmPullB_bMap hL u hu s hQN hQM
    μ := nm_muB (nmPullB L u hu) (Model.genMap_q u hu) 1 s (fun _ => rfl) }

end

theorem homPull_rHof_good {m : ℕ} {L : Lev (per l K) m}
    (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
    (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))
    {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ) (hL : L.Good)
    (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
    (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    (homPull hL u hu s hQN hQM (rHof d hc N s) (rHof d hc M s)).Good :=
  homPull_good_of_nmHM_pull hL u hu s hQN hQM _ _ (rHof_pull d hc u hu s)

end CrystallineSemistableComparison.Pb.Kap
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomGalGood
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomGalGoodRHof
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def galS (M : Model l K) (g : K.fixingSubgroup) (n j : ℕ) : M.Hc false n j →ₛₗ[(per l K).σA g] M.Hc false n j :=
  B.galHc (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K g) (galOC_okToOC _) false n j

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K)

def nmGA : NMor L.γ M.p (κA (OK l K) L.I) L.γ M.p (κA (OK l K) L.I) (L.σA g) :=
  nmK L.γ L.γ M.p M.p (L.σA g) (hL.σ_dp g) (hL.σ_O g) (𝟙 _) (Category.id_comp _)

def nmGB : NMor L.γB M.q (κA K L.IB) L.γB M.q (κA K L.IB) (L.σB g) :=
  nmK L.γB L.γB M.q M.q (L.σB g) (hL.σB_dp g) (hL.σB_K g) (𝟙 _) (Category.id_comp _)

variable (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

def homGal : Hom (chainOf hL M s hQ rH) (chainOf hL M s hQ rH) where
  sΛ := (per l K).σA g
  sA := L.σA g
  sB := L.σB g
  fS n j := galS M g n j
  fZn n j := nmHM (nmGA hL g M) l s none n j
  fZ j := nmHO (nmGA hL g M) l s j
  fW j := nmHO (nmGB hL g M) 1 s j
  fV _ := LinearMap.id

def GalRed : Prop :=
  ∀ n j (x : M.Hc false n j), nmHM (nmGA hL g M) l s none n j (rH n j x) = rH n j (galS M g n j x)

end

section
variable {m : ℕ} {L : Lev (per l K) m}
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))

end

end CrystallineSemistableComparison.Pb.Kap
end
end

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K)

namespace GaloisEquivariantMaps


open LevelPullbackIdentities in
def etaGal (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    (nmS (nmGB hL g M) 1 s).o.G ⋙ (smB M s hL hQ).o.G ⟶ (smB M s hL hQ).o.G ⋙ (nmS (nmGA hL g M) l s).o.G where
  app T := ObjectProperty.homMk (mkH (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (hL.σ_ι g r).symm)
    (DPMorphism.id T.obj.δ).isDPMorphism (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a =>
      (qid _ (fun _ h => h) _).trans (congrArg (fun b => T.obj.y.1.1 (Ideal.Quotient.mk _ b)) (hL.σ_ι g a).symm)))
      ((spec_qid _ (fun _ h => h) _).trans (by
        show ((T.obj.y.1.2 ≫ 𝟙 M.gen) ≫ pullback.fst _ _ : _ ⟶ M.X) = (T.obj.y.1.2 ≫ pullback.fst _ _) ≫ 𝟙 M.X
        simp)))))
  naturality _ _ f := ObjectProperty.hom_ext _ (CrystallineSemistableComparison.Pb.hom_ext rfl)

end GaloisEquivariantMaps

theorem nmHO_nmGB_bMap (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) (j : ℕ) (z : HO (QA L M s) j) :
    nmHO (nmGB hL g M) 1 s j (bMap M s hL hQ j z) = bMap M s hL hQ j (nmHO (nmGA hL g M) l s j z) := by
  have i1 : RingHomCompTriple L.ι (L.σB g) ((L.σB g).comp L.ι) := ⟨rfl⟩
  have i2 : RingHomCompTriple (L.σA g) L.ι ((L.σB g).comp L.ι) := ⟨RingHom.ext fun a => hL.σ_ι g a⟩
  have e₁ := CrystallineSemistableComparison.pull_pull ((L.σB g).comp L.ι) (smB M s hL hQ).o (nmS (nmGB hL g M) 1 s).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull ((L.σB g).comp L.ι) (nmS (nmGA hL g M) l s).o (smB M s hL hQ).o j z
  exact e₁.trans ((CrystallineSemistableComparison.P.prism ((smB M s hL hQ).o.comp (σ'' := (L.σB g).comp L.ι) (nmS (nmGB hL g M) 1 s).o)
    ((nmS (nmGA hL g M) l s).o.comp (σ'' := (L.σB g).comp L.ι) (smB M s hL hQ).o)
    (GaloisEquivariantMaps.etaGal hL g M s hQ) (fun T x => rfl) j z).trans e₂.symm)

variable (s : ℕ) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

theorem homGal_good_of_galRed (hr : GalRed hL g M s rH) : (homGal hL g M s hQ rH).Good :=
  { ℓ := rfl
    lam := hL.σ_lam g
    ι := fun a => (hL.σ_ι g a).symm
    o := hL.σB_K g
    tS := fun n j x => ((M.galH false j (IntermediateField.fixingSubgroupEquiv K g)).comm n x).symm
    r := hr
    red := fun n j z => nmHM_redM _ l s none n j z
    b := nmHO_nmGB_bMap hL g M s hQ
    μ := fun j v => (nm_muB (nmGB hL g M) (Category.id_comp _) 1 s (hL.σB_K g) j v).trans
      (congrArg _ (pullR_id' M.q j v)) }

end

section
variable {m : ℕ} {L : Lev (per l K) m}
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))

theorem galRed_rHof (hL : L.Good) (g : K.fixingSubgroup) (M : Model l K) (s : ℕ) : GalRed hL g M s (rHof d hc M s) := by
  intro n j x
  exact (red_nm (d n) (d n) s (nmGA hL g M) _ _ _ _ _ (hc n) (hc n) _ _ (fun _ _ => (Category.comp_id _).symm)
    (by
      intro y
      obtain ⟨c, rfl⟩ := ((RL.base_acr (PAlg.base l) PAlg.isBase_base).2 n).1 y
      rw [PAlg.galBase_cris, hc, hc]
      exact (congrArg (Ideal.Quotient.mk _) (hL.σ_lam g c)).symm) none j x).symm

end

end CrystallineSemistableComparison.Pb.Kap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorial
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorial
open CrystallineSemistableComparison.Pb.Kap

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.KapRhoHom

private theorem dual_expand {K B : Type} {V : Type*} [Field K] [CommRing B] [AddCommGroup V] [Module K V]
    (o : K →+* B) (f : Module.Dual K V →+ B) (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ)
    {m : ℕ} (bs : Module.Basis (Fin m) K V) (φ : Module.Dual K V) :
    f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem rho_hom :
    ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ']
      [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K)
      (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j)
      (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
        C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  intro Λ A B K Λ' A' B' _ _ _ _ _ _ _ C C' h hC hC' hh j x f hR
  obtain ⟨hs, e, z, hz, hW⟩ := hR
  have htr : ∀ φ : Module.Dual K (C'.V j),
      h.tr j f φ = h.sB (f (Module.Dual.transpose (R := K) (h.fV j) φ)) := fun φ => rfl
  refine ⟨fun k φ => ?_, e, h.fZ j z, fun n => ?_, ?_⟩
  · rw [htr, htr, map_smul, hs, map_mul, hh.o]
  · rw [← hh.red, hz, map_smulₛₗ, hh.r, map_pow, map_natCast, hh.ℓ]
  · intro m bs'
    haveI := hC.fin j
    have bs := Module.finBasis K (C.V j)
    have hE := congrArg (h.fW j) (hW bs)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hh.b, map_smulₛₗ, map_sum, map_pow, map_natCast] at hE
    rw [← hE, hh.ℓ]
    congr 1
    have hexp : ∀ t, h.tr j f (bs'.coord t) =
        ∑ s, h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s))) := by
      intro t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [htr, dual_expand C.o f hs bs, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul, hh.o]
      rfl
    have hμ : ∀ s, C'.μ j (h.fV j (bs s)) =
        ∑ t, C'.o (bs'.coord t (h.fV j (bs s))) • C'.μ j (bs' t) := by
      intro s
      conv_lhs => rw [← bs'.sum_repr (h.fV j (bs s))]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smulₛₗ]
      rfl
    calc ∑ t, h.tr j f (bs'.coord t) • C'.μ j (bs' t)
        = ∑ t, ∑ s, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hexp, Finset.sum_smul]
      _ = ∑ s, ∑ t, (h.sB (f (bs.coord s)) * C'.o (bs'.coord t (h.fV j (bs s)))) • C'.μ j (bs' t) :=
          Finset.sum_comm
      _ = ∑ s, h.fW j (f (bs.coord s) • C.μ j (bs s)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [map_smulₛₗ, hh.μ, hμ, Finset.smul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [mul_smul]

end GlobalTheory.CompanionTheory.KapRhoHom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorialStatement
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_functorial : ∀ {Λ A B K Λ' A' B' : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] [CommRing Λ'] [CommRing A'] [CommRing B'] (C : Chain.{1} Λ A B K) (C' : Chain.{1} Λ' A' B' K) (h : Hom C C'), C.Good → C'.Good → h.Good → ∀ {j : ℕ} (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C'.Rho (fun n => h.fS n j (x n)) (h.tr j f) := by
  first | exact @GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | exact GlobalTheory.CompanionTheory.KapRhoHom.rho_hom | (intros; apply GlobalTheory.CompanionTheory.KapRhoHom.rho_hom <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatible
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem exists_rho {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j) (hx : C.Comp x) :
    ∃ f : Module.Dual K (C.V j) →+ B, C.Rho x f := by
  obtain ⟨e, z, hz⟩ := hC.lift j x hx
  haveI := hC.fin j
  have hunit : IsUnit (C.ℓ : B) := by
    first
    | exact hC.unit
    | simpa using hC.unit.map C.ι
    | simpa using hC.unit.map C.o
    | simpa using (hC.unit.map C.lam).map C.ι
  obtain ⟨u, hu⟩ := hunit
  let w : C.W j := ((u⁻¹ : Bˣ) : B) ^ e • C.b j z
  let bs₀ := Module.finBasis K (C.V j)
  obtain ⟨g, hg, -⟩ := hC.basis j bs₀ w
  let f : Module.Dual K (C.V j) →+ B :=
    { toFun := fun φ => ∑ t, C.o (φ (bs₀ t)) * g t
      map_zero' := by simp
      map_add' := fun φ ψ => by simp [add_mul, Finset.sum_add_distrib] }
  refine ⟨f, fun k φ => ?_, e, z, hz, fun {m} bs => ?_⟩
  · simp [f, Finset.mul_sum, mul_assoc]
  · have key : ∑ s, f (bs.coord s) • C.μ j (bs s) = w := by
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_smul]
      rw [Finset.sum_comm, hg]
      refine Finset.sum_congr rfl fun t _ => ?_
      conv_rhs => rw [← bs.sum_repr (bs₀ t)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [LinearMap.map_smulₛₗ, smul_smul, Module.Basis.coord_apply, mul_comm]
    rw [key, ← hu, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]

end GlobalTheory.CompanionTheory.KapRho
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatibleStatement
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realization_of_compatible : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j), C.Comp x → ∃ f : Module.Dual K (C.V j) →+ B, C.Rho x f := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.exists_rho | exact GlobalTheory.CompanionTheory.KapRho.exists_rho | (intros; apply GlobalTheory.CompanionTheory.KapRho.exists_rho <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProduct
set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem semilinear_eq_sum_coord {K B : Type*} {V : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] (o : K →+* B) (f : Module.Dual K V →+ B)
    (hf : ∀ (k : K) φ, f (k • φ) = o k * f φ) {m : ℕ} (bs : Module.Basis (Fin m) K V)
    (φ : Module.Dual K V) : f φ = ∑ s, f (bs.coord s) * o (φ (bs s)) := by
  have hφ : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [LinearMap.sum_apply, Finsupp.single_apply]
  conv_lhs => rw [hφ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hf, mul_comm]

theorem rho_cup :
    ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K)
      (hC : C.Good) (P : Cup C), P.Good → ∀ {i j : ℕ} (x : ∀ n, C.S n i) (y : ∀ n, C.S n j)
      (f : Module.Dual K (C.V i) →+ B) (g : Module.Dual K (C.V j) →+ B)
      (h : Module.Dual K (C.V (i + j)) →+ B), C.Rho x f → C.Rho y g →
      C.Rho (fun n => P.cS n i j (x n) (y n)) h →
      ∀ {m m' : ℕ} (bs : Module.Basis (Fin m) K (C.V i)) (bs' : Module.Basis (Fin m') K (C.V j))
        (φ : Module.Dual K (C.V (i + j))),
        h φ = ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
          C.o (φ (P.cV i j (bs s) (bs' s'))) := by
  intro Λ A B K _ _ _ _ C hC P hP i j x y f g h hf hg hh m m' bs bs' φ
  obtain ⟨-, e, z, hzr, hzb⟩ := hf
  obtain ⟨-, e', w, hwr, hwb⟩ := hg
  obtain ⟨hh1, e'', u, hur, hub⟩ := hh
  haveI := hC.fin (i + j)
  let b := Module.finBasis K (C.V (i + j))
  have hv : ∀ n, C.red n (i + j) (P.cZ i j z w) =
      ((C.ℓ : A) ^ (e + e')) • C.r n (i + j) (P.cS n i j (x n) (y n)) := by
    intro n
    rw [hP.red, hzr, hwr, hP.r, map_smul, LinearMap.map_smul₂, smul_smul, pow_add, mul_comm]
  have hd : C.b (i + j) (((C.ℓ : A) ^ (e + e')) • u - ((C.ℓ : A) ^ e'') • P.cZ i j z w) = 0 := by
    refine hC.sep _ _ fun n => ?_
    have hu := hur n
    simp only at hu
    rw [map_sub, map_smul, map_smul, hu, hv n, smul_smul, smul_smul, mul_comm, sub_self]
  have key : ((C.ℓ : B) ^ (e + e')) • C.b (i + j) u =
      ((C.ℓ : B) ^ e'') • C.b (i + j) (P.cZ i j z w) := by
    rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, sub_eq_zero] at hd
    simpa only [map_pow, map_natCast] using hd
  let c : Fin (Module.finrank K (C.V (i + j))) → B := fun t =>
    ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') *
      C.o (b.coord t (P.cV i j (bs s) (bs' s')))
  have hμ : ∀ s s', P.cW i j (C.μ i (bs s)) (C.μ j (bs' s')) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) • C.μ (i + j) (b t) := by
    intro s s'
    rw [← hP.μ]
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.coord_apply]
  have hcup : P.cW i j (∑ s, f (bs.coord s) • C.μ i (bs s))
      (∑ s', g (bs'.coord s') • C.μ j (bs' s')) = ∑ t, c t • C.μ (i + j) (b t) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hμ, c,
      Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
    congr 1
    ring
  have hcoef : ∑ t, h (b.coord t) • C.μ (i + j) (b t) = ∑ t, c t • C.μ (i + j) (b t) := by
    have hu : IsUnit ((C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'') :=
      (hC.unit.pow _).mul (hC.unit.pow _)
    refine (hu.smul_left_cancel).1 ?_
    rw [hP.b, ← hub b, ← hzb bs, ← hwb bs', map_smul, LinearMap.map_smul₂, hcup, smul_smul,
      smul_smul, smul_smul] at key
    have hl : (C.ℓ : B) ^ e'' * (C.ℓ : B) ^ e' * (C.ℓ : B) ^ e =
        (C.ℓ : B) ^ (e + e') * (C.ℓ : B) ^ e'' := by ring
    rwa [hl] at key
  have hc : ∀ t, h (b.coord t) = c t := by
    obtain ⟨g₀, -, hg₀⟩ := hC.basis (i + j) b (∑ t, c t • C.μ (i + j) (b t))
    have h1 := hg₀ c rfl
    have h2 := hg₀ (fun t => h (b.coord t)) hcoef.symm
    exact fun t => congrFun (h2.trans h1.symm) t
  have hφ : ∀ s s', C.o (φ (P.cV i j (bs s) (bs' s'))) =
      ∑ t, C.o (b.coord t (P.cV i j (bs s) (bs' s'))) * C.o (φ (b t)) := by
    intro s s'
    conv_lhs => rw [← b.sum_repr (P.cV i j (bs s) (bs' s'))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_mul, Module.Basis.coord_apply]
  refine (semilinear_eq_sum_coord C.o h hh1 b φ).trans ?_
  simp only [hc, c, hφ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun t _ => ?_
  rw [mul_assoc]

end GlobalTheory.CompanionTheory.KapRho
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProductStatement
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_cup_product : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ {i j : ℕ} (x : ∀ n, C.S n i) (y : ∀ n, C.S n j) (f : Module.Dual K (C.V i) →+ B) (g : Module.Dual K (C.V j) →+ B) (h : Module.Dual K (C.V (i + j)) →+ B), C.Rho x f → C.Rho y g → C.Rho (fun n => P.cS n i j (x n) (y n)) h → ∀ {m m' : ℕ} (bs : Module.Basis (Fin m) K (C.V i)) (bs' : Module.Basis (Fin m') K (C.V j)) (φ : Module.Dual K (C.V (i + j))), h φ = ∑ s, ∑ s', f (bs.coord s) * g (bs'.coord s') * C.o (φ (P.cV i j (bs s) (bs' s'))) := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.rho_cup | exact GlobalTheory.CompanionTheory.KapRho.rho_cup | (intros; apply GlobalTheory.CompanionTheory.KapRho.rho_cup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmul
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmul
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapChain

theorem rho_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ}
    (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f →
    C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  intro Λ A B K _ _ _ _ C j c x f hf
  obtain ⟨h1, e, z, h2, h3⟩ := hf
  refine ⟨?_, e, C.lam c • z, ?_, ?_⟩
  · intro k φ
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, h1]
    ring
  · intro n
    rw [map_smul, h2 n, Pi.smul_apply, LinearMap.map_smulₛₗ, smul_comm]
  · intro m bs
    rw [LinearMap.map_smulₛₗ, ← h3 bs]
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_smul]
    rw [← Finset.smul_sum, smul_comm]

end GlobalTheory.CompanionTheory.KapChain
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmulStatement
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_smul : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (c : Λ) (x : ∀ n, C.S n j) (f : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho (c • x) ((AddMonoidHom.mulLeft (C.ι (C.lam c))).comp f) := by
  first | exact @GlobalTheory.CompanionTheory.KapChain.rho_smul | exact GlobalTheory.CompanionTheory.KapChain.rho_smul | (intros; apply GlobalTheory.CompanionTheory.KapChain.rho_smul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClass
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClass
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUnit

theorem rho_one_eval : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  intro Λ A B K _ _ _ _ C hC P hP h hR φ
  obtain ⟨hsem, e, z, hz, hb⟩ := hR
  have hw : C.b 0 z = ((C.ℓ : B) ^ e) • C.μ 0 P.oneV := by
    have h0 : C.b 0 (z - ((C.ℓ : A) ^ e) • P.oneZ) = 0 := hC.sep 0 _ (fun n => by
      rw [map_sub, map_smul, hP.one_r, hz, sub_self])
    rw [map_sub, map_smulₛₗ, hP.one_b, sub_eq_zero] at h0
    rw [h0]
    simp
  haveI := hC.fin 0
  let bs := Module.finBasis K (C.V 0)
  have h1 := hb bs
  rw [hw] at h1
  have h2 : ∑ s, h (bs.coord s) • C.μ 0 (bs s) = C.μ 0 P.oneV := by
    obtain ⟨u, hu⟩ := hC.unit.pow e
    rw [← hu] at h1
    have h1' := congrArg (fun w => ((u⁻¹ : Bˣ) : B) • w) h1
    simpa only [smul_smul, Units.inv_mul, one_smul] using h1'
  have h3 : C.μ 0 P.oneV = ∑ s, C.o (bs.coord s P.oneV) • C.μ 0 (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smulₛₗ]
    rfl
  have h4 : (fun s => h (bs.coord s)) = fun s => C.o (bs.coord s P.oneV) :=
    (hC.basis 0 bs (C.μ 0 P.oneV)).unique h2.symm h3
  have h5 : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [Finset.sum_apply, Module.Basis.coord_apply, Finsupp.single_apply]
  have h6 : φ P.oneV = ∑ s, bs.coord s P.oneV * φ (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h6, map_sum]
  conv_lhs => rw [h5]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hsem, map_mul, mul_comm]
  exact congrArg (· * C.o (φ (bs s))) (congrFun h4 s)

end GlobalTheory.CompanionTheory.KapUnit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClassStatement
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_unit_class : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  first | exact @GlobalTheory.CompanionTheory.KapUnit.rho_one_eval | exact GlobalTheory.CompanionTheory.KapUnit.rho_one_eval | (intros; apply GlobalTheory.CompanionTheory.KapUnit.rho_one_eval <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAdd
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAdd
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem rho_add {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B) :
    C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  rintro ⟨hf, e₁, z₁, hz₁, hb₁⟩ ⟨hg, e₂, z₂, hz₂, hb₂⟩
  refine ⟨fun k φ => by simp only [AddMonoidHom.add_apply, hf, hg, mul_add], e₁ + e₂,
    ((C.ℓ : A) ^ e₂) • z₁ + ((C.ℓ : A) ^ e₁) • z₂, fun n => ?_, fun {m} bs => ?_⟩
  · simp only [map_add (f := _), map_smul, hz₁, hz₂, Pi.add_apply]
    rw [pow_add]
    module
  · simp only [AddMonoidHom.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _),
      LinearMap.map_smulₛₗ, map_pow, map_natCast, ← hb₁ bs, ← hb₂ bs]
    rw [pow_add]
    module

end GlobalTheory.CompanionTheory.KapRho
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAddStatement
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_add : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.rho_add | exact GlobalTheory.CompanionTheory.KapRho.rho_add | (intros; apply GlobalTheory.CompanionTheory.KapRho.rho_add <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnique
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnique
open Module CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUniq

theorem eq_of_unit_smul_combination {K B V M : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup M] [Module B M]
    (o : K →+* B) (μ : V → M) (c : B) (hc : IsUnit c)
    (hind : ∀ (m : ℕ) (bs : Basis (Fin m) K V) (g : Fin m → B),
      ∑ s, g s • μ (bs s) = 0 → ∀ s, g s = 0)
    (f f' : Dual K V →+ B)
    (hf : ∀ (k : K) (φ : Dual K V), f (k • φ) = o k * f φ)
    (hf' : ∀ (k : K) (φ : Dual K V), f' (k • φ) = o k * f' φ)
    (h : ∀ (m : ℕ) (bs : Basis (Fin m) K V),
      c • ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0) :
    f = f' := by
  classical
  let bs := Module.finBasis K V
  have h0 : ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0 := by
    obtain ⟨u, rfl⟩ := hc
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) • x) (h _ bs)
    simpa [smul_smul] using this
  have hco : ∀ s, f (bs.coord s) = f' (bs.coord s) :=
    fun s => sub_eq_zero.mp (hind _ bs _ h0 s)
  have key : ∀ F : Dual K V →+ B, (∀ (k : K) (φ : Dual K V), F (k • φ) = o k * F φ) →
      ∀ φ : Dual K V, F φ = ∑ s, F (bs.coord s) * o (φ (bs s)) := by
    intro F hF φ
    have e : ∑ s, φ (bs s) • bs.coord s = φ := bs.sum_dual_apply_smul_coord φ
    calc F φ = F (∑ s, φ (bs s) • bs.coord s) := by rw [e]
      _ = _ := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_congr rfl fun s _ => by rw [hF, mul_comm]
  ext φ
  rw [key f hf, key f' hf']
  exact Finset.sum_congr rfl fun s _ => by rw [hco]

theorem rho_unique {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j)
    (f f' : Module.Dual K (C.V j) →+ B) : C.Rho x f → C.Rho x f' → f = f' := by
  rintro ⟨hfs, e, z, hz, hzb⟩ ⟨hfs', e', z', hz', hzb'⟩
  haveI := hC.fin j
  have hw : C.b j (((C.ℓ : A) ^ e) • z' - ((C.ℓ : A) ^ e') • z) = 0 := by
    apply hC.sep
    intro n
    rw [map_sub, map_smul, map_smul, hz n, hz' n, smul_smul, smul_smul, mul_comm, sub_self]
  have hb : ∀ (a : A) (y : C.Z j), C.b j (a • y) = C.ι a • C.b j y :=
    fun a y => (C.b j).map_smulₛₗ a y
  refine (eq_of_unit_smul_combination C.o (C.μ j) ((C.ℓ : B) ^ (e + e')) (hC.unit.pow _) ?_
    f' f hfs' hfs ?_).symm
  · intro m bs g hg s
    obtain ⟨g0, _, hu⟩ := hC.basis j bs 0
    have h1 := hu g hg.symm
    have h2 := hu 0 (by simp)
    exact congrFun (h1.trans h2.symm) s
  · intro m bs
    have h := hw
    rw [map_sub, hb, hb, ← hzb bs, ← hzb' bs] at h
    simp only [map_pow, map_natCast, smul_smul] at h
    simp_rw [sub_smul, Finset.sum_sub_distrib, smul_sub]
    rw [← h, pow_add, mul_comm ((C.ℓ : B) ^ e') ((C.ℓ : B) ^ e)]

end GlobalTheory.CompanionTheory.KapUniq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUniqueStatement
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realization_unique : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j) (f f' : Module.Dual K (C.V j) →+ B), C.Rho x f → C.Rho x f' → f = f' := by
  first | exact @GlobalTheory.CompanionTheory.KapUniq.rho_unique | exact GlobalTheory.CompanionTheory.KapUniq.rho_unique | (intros; apply GlobalTheory.CompanionTheory.KapUniq.rho_unique <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.RhoFirstChernFormula
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.CupGenA
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
theorem cup_genA {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)
    (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
    (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j) (hG : (chainOf hL M s hQ rH).Good)
    (hP : (cupOf hL M s hQ rH).Good) {i j : ℕ} (x : ∀ n, M.Hc false n i) (y : ∀ n, M.Hc false n j) (z : ∀ n, M.Hc false n (i + j))
    (f : Module.Dual K (HdR M.q i) →+ L.B) (g : Module.Dual K (HdR M.q j) →+ L.B) (h : Module.Dual K (HdR M.q (i + j)) →+ L.B)
    (hx : (chainOf hL M s hQ rH).Rho x f) (hy : (chainOf hL M s hQ rH).Rho y g) (hz : (chainOf hL M s hQ rH).Rho z h)
    (hc : ∀ n, z n = cupS M n i j (x n) (y n)) {e e' : ℕ} (b : Module.Basis (Fin e) K (HdR M.q i))
    (b' : Module.Basis (Fin e') K (HdR M.q j)) (φ : Module.Dual K (HdR M.q (i + j))) :
    h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K L.B (φ (cupK M.q rfl (b s) (b' s'))) := by
  obtain rfl : z = fun n => cupS M n i j (x n) (y n) := funext hc
  have H : h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K L.B (φ (cupR M i j (b s) (b' s'))) :=
    GlobalTheory.T.realization_cup_product (chainOf hL M s hQ rH) hG (cupOf hL M s hQ rH) hP x y f g h hx hy hz b b' φ
  simp only [cupR_eq] at H
  exact H

end CrystallineSemistableComparison.Pb.Kap
end
end

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap.Mo

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

variable [FiniteDimensional ℚ_[l] K]

theorem chK_good (M : Model l K) (hM : M.Sm) (m : ℕ) :
    ∃ s₁, ∀ s, s₁ ≤ s → (chK S hS hC M m s).Good := by
  obtain ⟨U⟩ := cov_sm_pf M hM
  refine ⟨Finset.univ.sup U.d + (m + 1), fun s hs => ?_⟩
  refine chain_good (hS.lev m) M s hM U (fun α => ?_) (by omega) _ (rHof_tr_gen _ _ M s)
  have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
  omega

theorem rho_mono (M : Model l K) (m : ℕ) {s s' : ℕ} (h : s ≤ s') (hG : (chK S hS hC M m s).Good)
    (hG' : (chK S hS hC M m s').Good) {j : ℕ} (x : ∀ n, M.Hc false n j) (f : Module.Dual K (HdR M.q j) →+ (S.L m).B)
    (hf : (chK S hS hC M m s').Rho x f) : (chK S hS hC M m s).Rho x f := by
  have H := GlobalTheory.T.realization_functorial (chK S hS hC M m s') (chK S hS hC M m s)
    (homS (hS.lev m) M h (qb_le (hS.lev m) M s) (qb_le (hS.lev m) M s')
      (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s'))
    hG' hG (homS_good_of_inclHM _ _ _ _ _ _ _ (rHof_incl_pf S hS hC M m h)) x f hf
  have e : (homS (hS.lev m) M h (qb_le (hS.lev m) M s) (qb_le (hS.lev m) M s')
      (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s')).tr j f = f := by
    ext φ
    rfl
  rw [e] at H
  exact H

theorem rho_uniq_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f f',
    rhoK S hS hC a j m x f → rhoK S hS hC a j m x f' → f = f' := by
  intro M a hM j m x f f' ⟨_, s₀, h⟩ ⟨_, s₀', h'⟩
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  exact GlobalTheory.T.realization_unique (chK S hS hC M m (max s₁ (max s₀ s₀'))) (hg _ (le_max_left _ _)) _ f f'
    (h _ (le_trans (le_max_left _ _) (le_max_right _ _))) (h' _ (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem rho_ex_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x, ∃ f, rhoK S hS hC a j m x f := by
  intro M a hM j m x
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_realization_of_compatible (chK S hS hC M m s₁) (hg s₁ le_rfl) (show (M.HS false j).lim from x).1
    (fun n => (show (M.HS false j).lim from x).2 n)
  refine ⟨f, hM, s₁, fun s hs => ?_⟩
  obtain ⟨g, hgs⟩ := GlobalTheory.T.exists_realization_of_compatible (chK S hS hC M m s) (hg s hs) (show (M.HS false j).lim from x).1
    (fun n => (show (M.HS false j).lim from x).2 n)
  have e : g = f := GlobalTheory.T.realization_unique _ (hg s₁ le_rfl) _ g f (rho_mono S hS hC M m hs (hg s₁ le_rfl) (hg s hs) _ g hgs) hf
  rwa [e] at hgs

theorem rho_add_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x y f g,
    rhoK S hS hC a j m x f → rhoK S hS hC a j m y g → rhoK S hS hC a j m (x + y) (f + g) := by
  intro M a hM j m x y f g ⟨_, s₀, h⟩ ⟨_, s₀', h'⟩
  exact ⟨hM, max s₀ s₀', fun s hs => GlobalTheory.T.realization_add (chK S hS hC M m s) _ _ f g
    (h s (le_trans (le_max_left _ _) hs)) (h' s (le_trans (le_max_right _ _) hs))⟩

theorem rho_smul_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m (c : (per l K).A) x f, rhoK S hS hC a j m x f →
    rhoK S hS hC a j m (c • x) ((AddMonoidHom.mulLeft ((S.L m).ι ((S.L m).lam c))).comp f) := by
  intro M a hM j m c x f ⟨_, s₀, h⟩
  exact ⟨hM, s₀, fun s hs => GlobalTheory.T.realization_smul (chK S hS hC M m s) c _ f (h s hs)⟩

theorem rho_lin'_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f, rhoK S hS hC a j m x f →
    ∀ (k : K) φ, f (k • φ) = algebraMap K (S.L m).B k * f φ := by
  intro M a hM j m x f ⟨_, s₀, h⟩ k φ
  exact (h s₀ le_rfl).1 k φ

theorem rho_fil_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f, rhoK S hS hC a j m x f → ∀ n r : ℕ, n ≤ m →
    (dat Amp).fil a j n x → ∀ φ : Module.Dual K (HdR M.q j), (∀ h ∈ FilR M.q j (r + 1), φ h = 0) →
      f φ ∈ pdP (S.L m).γB (n - r) := by
  intro M a hM j m x f ⟨_, s₀, h⟩ n r hnm hfil φ hφ
  obtain ⟨U⟩ := cov_sm_pf M hM
  have hU : ∀ α, U.d α + (m + 1) ≤ max s₀ (Finset.univ.sup U.d + (m + 1)) := fun α => by
    have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
    omega
  exact fil_lev_pf (hS.lev m) (dOf S hS hC m) (hcOf S hS hC m) M _ hM U hU (by omega) _
    (fun n => (show (M.HS false j).lim from x).2 n) f (h _ (le_max_left _ _)) n r (by omega) hfil φ hφ

theorem rho_firstChern_formula : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ m x f c, rhoK S hS hC a 2 m x f → (dat Amp).c1H a x →
    IsFirstChernDeRham _ (lineK a.1) c → ∀ φ, f φ = algebraMap K (S.L m).B (φ c) := by
  intro M a hM m x f c ⟨_, s₀, h⟩ hx hc φ
  obtain ⟨U⟩ := cov_sm_pf M hM
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  have hU : ∀ α, U.d α + (m + 1) ≤ max (max s₀ s₁) (Finset.univ.sup U.d + (m + 1)) := fun α => by
    have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
    omega
  have H := crystalline_firstChern_level (hS.lev m) (dOf S hS hC m) (hcOf S hS hC m) M _ hM U hU (by omega) a x hx c hc
  have e := GlobalTheory.T.realization_unique (chK S hS hC M m _) (hg _ (by omega)) _ f (evB M c) (h _ (by omega)) H
  rw [e]
  rfl

end CrystallineSemistableComparison.Pb.Kap.Mo
end
end

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap.Mo

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

variable [FiniteDimensional ℚ_[l] K]

theorem lev_good (M : Model l K) (m s : ℕ) : (homLev S hS m M s (qb_le (hS.lev (m + 1)) M s) (qb_le (hS.lev m) M s)
    (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good := by
  exact
    { ℓ := rfl
      lam c := hS.dlam m c
      ι a := hS.dι m a
      o k := hS.dK m k
      tS n j x := rfl
      r n j x := nmHM_nmLevA_rHof_succ S hS hC M m s n j x
      red n j z := nmHM_redM _ l s none n j z
      b j z := nmHO_nmLevB_bMap S hS m M s _ _ j z
      μ j v := (nm_muB (nmLevB S hS m M) (Category.id_comp _) 1 s (hS.dK m) j v).trans (congrArg _ (pullR_id' M.q j v)) }

theorem rho_lev_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f,
    rhoK S hS hC a j (m + 1) x f → rhoK S hS hC a j m x ((S.dB m).toAddMonoidHom.comp f) := by
  intro M a hM j m x f ⟨hM', s₀, hs₀⟩
  refine ⟨hM', ?_⟩
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM (m + 1)
  obtain ⟨s₂, hs₂⟩ := chK_good S hS hC M hM m
  refine ⟨max s₀ (max s₁ s₂), fun s hs => ?_⟩
  have h := GlobalTheory.T.realization_functorial (chK S hS hC M (m + 1) s) (chK S hS hC M m s)
    (homLev S hS m M s (qb_le (hS.lev (m + 1)) M s) (qb_le (hS.lev m) M s)
      (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s))
    (hs₁ s (by omega)) (hs₂ s (by omega)) (lev_good S hS hC M m s)
    (show (M.HS false j).lim from x).1 f (hs₀ s (by omega))
  exact h

theorem rho_act_of (hG : ∀ (M : Model l K) m s g, (homGal (hS.lev m) g M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m (g : K.fixingSubgroup) x f,
    rhoK S hS hC a j m x f → rhoK S hS hC a j m (((dat Amp).H a).act j g x) (((S.L m).σB g).toAddMonoidHom.comp f) := by
  intro M a hM j m g x f ⟨hM', s₀, hs₀⟩
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  refine ⟨hM', max s₀ s₁, fun s hs => ?_⟩
  exact GlobalTheory.T.realization_functorial (chK S hS hC M m s) (chK S hS hC M m s) (homGal (hS.lev m) g M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s))
    (hs₁ s (by omega)) (hs₁ s (by omega)) (hG M m s g) (show (M.HS false j).lim from x).1 f (hs₀ s (by omega))

theorem rho_nat_of (hP : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) m s,
    (homPull (hS.lev m) u hu s (qb_le (hS.lev m) N s) (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) N s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M} {b : (dat Amp).Ch N}
    (μ : (dat Amp).Mo u hu a b), M.Sm → N.Sm → ∀ j m x f f', rhoK S hS hC b j m x f → rhoK S hS hC a j m ((dat Amp).pullH μ j x) f' →
      ∀ φ, f' φ = f (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu)) := by
  intro M N u hu a b μ hM hN j m x f f' ⟨_, s₀, h₀⟩ ⟨_, s₀', h₀'⟩ φ
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  obtain ⟨s₂, hs₂⟩ := chK_good S hS hC N hN m
  obtain ⟨s, e0, e1, e2, e3⟩ : ∃ s, s₀ ≤ s ∧ s₀' ≤ s ∧ s₁ ≤ s ∧ s₂ ≤ s := ⟨s₀ + s₀' + s₁ + s₂, by omega⟩
  have h := GlobalTheory.T.realization_functorial (chK S hS hC N m s) (chK S hS hC M m s) _ (hs₂ s e3) (hs₁ s e2) (hP M N u hu m s)
    (show (N.HS false j).lim from x).1 f (h₀ s e0)
  have e := GlobalTheory.T.realization_unique (chK S hS hC M m s) (hs₁ s e2) _ f' _ (h₀' s e1) h
  rw [e]
  rfl

theorem rho_one_of (hU : ∀ (M : Model l K) m s, (cupOf (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ m x f, rhoK S hS hC a 0 m x f → ((dat Amp).H a).one x →
    ∀ φ, f φ = algebraMap K (S.L m).B (φ (oneK M.q)) := by
  intro M a hM m x f ⟨_, s₀, h₀⟩ hx φ
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  obtain ⟨s, e0, e1⟩ : ∃ s, s₀ ≤ s ∧ s₁ ≤ s := ⟨s₀ + s₁, by omega⟩
  have h := h₀ s e0
  rw [show (show (M.HS false 0).lim from x).1 = (cupOf (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).oneS from
    funext ((one_iff (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) a x).1 hx)] at h
  exact GlobalTheory.T.realization_unit_class (chK S hS hC M m s) (hs₁ s e1) _ (hU M m s) f h φ

theorem rho_cup_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ {i j : ℕ} m x y z f g h,
    rhoK S hS hC a i m x f → rhoK S hS hC a j m y g → rhoK S hS hC a (i + j) m z h → ((dat Amp).H a).cup x y z →
    ∀ {e e' : ℕ} (b : Module.Basis (Fin e) K (HdR M.q i)) (b' : Module.Basis (Fin e') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K (S.L m).B (φ (cupK M.q rfl (b s) (b' s'))) := by
  intro M a hM i j m x y z f g h hx hy hz hc e e' b b' φ
  refine hx.2.elim fun s₀ h₀ => hy.2.elim fun s₁ h₁ => hz.2.elim fun s₂ h₂ => (chK_good S hS hC M hM m).elim fun s₃ h₃ => ?_
  exact cup_genA (hS.lev m) M (s₀ + s₁ + s₂ + s₃) _ _ (h₃ _ (by omega)) (cupOf_rHof_good _ M _ _ _ _) _ _ _ f g h (h₀ _ (by omega))
    (h₁ _ (by omega)) (h₂ _ (by omega))
    ((cup_iff_cS_lim (hS.lev m) M 0 (qb_le (hS.lev m) M 0) (rHof (dOf S hS hC m) (hcOf S hS hC m) M 0) a x y z).1 hc) b b' φ

include hS hC in
theorem rhoSys_ex : Nonempty (RhoSys S Model.Sm (dat Amp) fun a c => IsFirstChernDeRham _ (lineK a.1) c) :=
  ⟨{ ρ := rhoK S hS hC
     ex := rho_ex_pf S hS hC
     uniq := rho_uniq_pf S hS hC
     add := rho_add_pf S hS hC
     smul := rho_smul_pf S hS hC
     lin' := rho_lin'_pf S hS hC
     lev := rho_lev_pf S hS hC
     act := rho_act_of S hS hC fun M m s g => by
       have hL := hS.lev m
       have hRed := galRed_rHof (dOf S hS hC m) (hcOf S hS hC m) hL g M s
       exact
         { ℓ := rfl
           lam c := hL.σ_lam g c
           ι a := (hL.σ_ι g a).symm
           o k := hL.σB_K g k
           tS n j x := ((M.galH false j (IntermediateField.fixingSubgroupEquiv K g)).comm n x).symm
           r n j x := hRed n j x
           red n j z := nmHM_redM _ l s none n j z
           b j z := nmHO_nmGB_bMap hL g M s _ j z
           μ j v := (nm_muB (nmGB hL g M) (Category.id_comp _) 1 s (hL.σB_K g) j v).trans
             (congrArg _ (pullR_id' M.q j v)) }
     nat := rho_nat_of S hS hC fun M N u hu m s => homPull_rHof_good _ _ u hu s _ _ _
     fil := rho_fil_pf S hS hC
     cup := rho_cup_pf S hS hC
     one := rho_one_of S hS hC fun M m s => cupOf_rHof_good _ M s _ _ _
     c1 := rho_firstChern_formula S hS hC }⟩

end CrystallineSemistableComparison.Pb.Kap.Mo
