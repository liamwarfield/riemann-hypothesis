module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RHof
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.ReductionChangeLevel

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.BMapIncl
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

namespace LevelChangeComparison

end LevelChangeComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (m : ℕ) (M : Model l K)

def nmLevA : NMor (S.L (m + 1)).γ M.p (κA (OK l K) (S.L (m + 1)).I) (S.L m).γ M.p (κA (OK l K) (S.L m).I) (S.dA m) :=
  nmK (S.L (m + 1)).γ (S.L m).γ M.p M.p (S.dA m) (hS.ddp m) (hS.dO m) (𝟙 M.X) (Category.id_comp _)

def nmLevB : NMor (S.L (m + 1)).γB M.q (κA K (S.L (m + 1)).IB) (S.L m).γB M.q (κA K (S.L m).IB) (S.dB m) :=
  nmK (S.L (m + 1)).γB (S.L m).γB M.q M.q (S.dB m) (hS.ddpB m) (hS.dK m) (𝟙 M.gen) (Category.id_comp _)

namespace LevelChangeComparison

end LevelChangeComparison

end

theorem bMap_incl {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) {s s' : ℕ} (h : s ≤ s')
    (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
    (hQ' : ∀ T, QB L M s' T → QA L M s' (((nmB M hL).mor 0).obj T)) (j : ℕ) (z : HO (QA L M s') j) :
    (incl (ts_le L.γB M.q 1 h {⊤})).o.pull j (bMap M s' hL hQ' j z) =
      bMap M s hL hQ j ((incl (ts_le L.γ M.p l h {⊤})).o.pull j z) := by
  have e₁ := CrystallineSemistableComparison.pull_pull L.ι (smB M s' hL hQ').o (incl (ts_le L.γB M.q 1 h {⊤})).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull L.ι (incl (ts_le L.γ M.p l h {⊤})).o (smB M s hL hQ).o j z
  exact e₁.trans (Eq.trans rfl e₂.symm)

end CrystallineSemistableComparison.Pb.Kap
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomLevGood
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (m : ℕ) (M : Model l K) (s : ℕ)
  (hQ₁ : ∀ T, QB (S.L (m + 1)) M s T → QA (S.L (m + 1)) M s (((nmB M (hS.lev (m + 1))).mor 0).obj T))
  (hQ₀ : ∀ T, QB (S.L m) M s T → QA (S.L m) M s (((nmB M (hS.lev m)).mor 0).obj T))
  (rH₁ : ∀ n j, M.Hc false n j →ₛₗ[(S.L (m + 1)).lam] HM (QA (S.L (m + 1)) M s) none ((l : (S.L (m + 1)).A) ^ n) j)
  (rH₀ : ∀ n j, M.Hc false n j →ₛₗ[(S.L m).lam] HM (QA (S.L m) M s) none ((l : (S.L m).A) ^ n) j)

def homLev : Hom (chainOf (hS.lev (m + 1)) M s hQ₁ rH₁) (chainOf (hS.lev m) M s hQ₀ rH₀) where
  sΛ := RingHom.id _
  sA := S.dA m
  sB := S.dB m
  fS n j := LinearMap.id
  fZn n j := nmHM (nmLevA S hS m M) l s none n j
  fZ j := nmHO (nmLevA S hS m M) l s j
  fW j := nmHO (nmLevB S hS m M) 1 s j
  fV j := LinearMap.id

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) {s s' : ℕ} (h : s ≤ s')
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (hQ' : ∀ T, QB L M s' T → QA L M s' (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)
  (rH' : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s') none ((l : L.A) ^ n) j)

def inclHM (n j : ℕ) : HM (QA L M s') none ((l : L.A) ^ n) j →ₗ[L.A] HM (QA L M s) none ((l : L.A) ^ n) j :=
  ((incl (ts_le L.γ M.p l h {⊤})).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial)
    (incl_std (ts_le L.γ M.p l h {⊤}) none ((l : L.A) ^ n))).pull j

def homS : Hom (chainOf hL M s' hQ' rH') (chainOf hL M s hQ rH) where
  sΛ := RingHom.id _
  sA := RingHom.id _
  sB := RingHom.id _
  fS n j := LinearMap.id
  fZn n j := inclHM M h n j
  fZ j := (incl (ts_le L.γ M.p l h {⊤})).o.pull j
  fW j := (incl (ts_le L.γB M.q 1 h {⊤})).o.pull j
  fV j := LinearMap.id

end

end CrystallineSemistableComparison.Pb.Kap
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.NmHONmPullBBMap
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomPullGoodRHof
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {R : Per l K} {m : ℕ} (L : Lev R m) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p)

def nmPullA : NMor L.γ N.p (κA (OK l K) L.I) L.γ M.p (κA (OK l K) L.I) (RingHom.id L.A) :=
  nmK L.γ L.γ N.p M.p (RingHom.id L.A) (DPMorphism.id L.γ).isDPMorphism (fun _ => rfl) u hu

def nmPullB : NMor L.γB N.q (κA K L.IB) L.γB M.q (κA K L.IB) (RingHom.id L.B) :=
  nmK L.γB L.γB N.q M.q (RingHom.id L.B) (DPMorphism.id L.γB).isDPMorphism (fun _ => rfl) (Model.genMap u hu)
    (Model.genMap_q u hu)

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)
  (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
  (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (rHN : ∀ n j, N.Hc false n j →ₛₗ[L.lam] HM (QA L N s) none ((l : L.A) ^ n) j)
  (rHM : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)

def homPull : Hom (chainOf hL N s hQN rHN) (chainOf hL M s hQM rHM) where
  sΛ := RingHom.id _
  sA := RingHom.id _
  sB := RingHom.id _
  fS n j := B.pullHc (okToOC l K) (B.schMap u hu) false n j
  fZn n j := nmHM (nmPullA L u hu) l s none n j
  fZ j := nmHO (nmPullA L u hu) l s j
  fW j := nmHO (nmPullB L u hu) 1 s j
  fV j := pullR j (Model.genMap u hu) (Model.genMap_q u hu)

namespace PullbackComparison

end PullbackComparison

end

section
variable {m : ℕ} {L : Lev (per l K) m}
  (d : ∀ n, RedIn (B.DD false (PAlg.base l) n) (B.κb (okToOC l K) false n) L.γ l n)
  (hc : ∀ n (c : Acris l), (d n).ρ ((PAlg.base l).cris n c) = Ideal.Quotient.mk _ (L.lam c))
  {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)

theorem lnMap_id {B : Type} [CommRing B] (k n : ℕ) (y : B ⧸ Ideal.span {(k : B) ^ n}) :
    lnMap (RingHom.id B) k (le_refl n) y = y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem rHof_pull (n j : ℕ) (x : N.Hc false n j) :
    nmHM (nmPullA L u hu) l s none n j (rHof d hc N s n j x) =
      rHof d hc M s n j (B.pullHc (okToOC l K) (B.schMap u hu) false n j x) :=
  (red_nm (d n) (d n) s (nmPullA L u hu) _ _ _ _ _ (hc n) (hc n) _ _ (fun _ _ => rfl) (fun _ => (lnMap_id l n _).symm)
    none j x).symm

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

namespace LevelPullbackIdentities

theorem qid {B : Type} [CommRing B] (J : Ideal B) (h : J ≤ J.comap (RingHom.id B)) (w : B ⧸ J) :
    Ideal.quotientMap J (RingHom.id B) h w = w := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

theorem spec_qid {B : Type} [CommRing B] (J : Ideal B) (h : J ≤ J.comap (RingHom.id B)) {Y : Scheme.{0}}
    (y : Spec (CommRingCat.of (B ⧸ J)) ⟶ Y) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B) h)) ≫ y = y := by
  have e : Ideal.quotientMap J (RingHom.id B) h = RingHom.id _ := RingHom.ext (qid J h)
  rw [e]
  simp

theorem s_one {b : Base} {L : b.Fun} (hι : IsEmpty L.ι) (ht : b.t = 1) (T : Thick L) : T.s = 1 := by
  have h := T.hs
  rw [Finset.prod_of_isEmpty, ht, map_one, mul_one] at h
  exact Units.ext h.symm

def thHom {b : Base} {L : b.Fun} (hι : IsEmpty L.ι) (ht : b.t = 1) {T T' : Thick L} (φ : T.B →+* T'.B)
    (comm : ∀ r, φ (T.i r) = T'.i r) (dp : IsDPMorphism T.δ T'.δ φ) (hle : T.J ≤ T'.J.comap φ)
    (pt : L.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ hle)) T.y = T'.y) : T ⟶ T' where
  φ := φ
  u j := isEmptyElim j
  comm := comm
  dp := dp
  hle := hle
  pt := pt
  hx j := isEmptyElim j
  hs := by rw [s_one hι ht T', s_one hι ht T, map_one, Finset.prod_of_isEmpty, one_mul]
  hv j := isEmptyElim j

end LevelPullbackIdentities

theorem pullR_id' : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : HdR p n),
    pullR n (𝟙 X) (Category.id_comp p) x = x := by
  intro K _ X p n x
  let m' : CH.Mor (O (smFun X p)) (O (smFun X p)) (RingHom.id K) :=
    ⟨(smMor (𝟙 X) (Category.id_comp p)).functor,
      fun _ => { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }, fun _ _ => rfl⟩
  let η : (CH.Mor.id (O (smFun X p))).G ⟶ m'.G :=
    { app := fun T => LevelPullbackIdentities.thHom (L := smFun X p) ⟨fun j => Empty.elim j⟩ rfl (RingHom.id T.B) (fun r => rfl)
        (DPMorphism.id T.δ).isDPMorphism (fun _ h => h)
        (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => LevelPullbackIdentities.qid _ (fun _ h => h) _))
          ((LevelPullbackIdentities.spec_qid _ (fun _ h => h) _).trans (Category.comp_id _).symm)))
      naturality := fun _ _ f => Thick.Hom.ext (RingHom.ext fun _ => rfl) (funext fun j => Empty.elim j) }
  have h1 : (CH.Mor.id (O (smFun X p))).pull n x = x := (CrystallineSemistableComparison.P.pull_comp (CH.Mor.id _) (CH.Mor.id _) n x).2
  have h2 := CrystallineSemistableComparison.P.prism (CH.Mor.id (O (smFun X p))) m' η (fun T x => rfl) n x
  exact h2.symm.trans h1

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (m : ℕ) (M : Model l K)

namespace LevelPullbackIdentities

def etaLev (s : ℕ)
    (hQ₁ : ∀ T, QB (S.L (m + 1)) M s T → QA (S.L (m + 1)) M s (((nmB M (hS.lev (m + 1))).mor 0).obj T))
    (hQ₀ : ∀ T, QB (S.L m) M s T → QA (S.L m) M s (((nmB M (hS.lev m)).mor 0).obj T)) :
    (nmS (nmLevB S hS m M) 1 s).o.G ⋙ (smB M s (hS.lev (m + 1)) hQ₁).o.G ⟶
      (smB M s (hS.lev m) hQ₀).o.G ⋙ (nmS (nmLevA S hS m M) l s).o.G where
  app T := ObjectProperty.homMk (mkH (RingHom.id T.obj.B) (fun r => congrArg T.obj.i (hS.dι m r))
    (DPMorphism.id T.obj.δ).isDPMorphism (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a =>
      (qid _ (fun _ h => h) _).trans (congrArg (fun b => T.obj.y.1.1 (Ideal.Quotient.mk _ b)) (hS.dι m a))))
      ((spec_qid _ (fun _ h => h) _).trans (by
        show ((T.obj.y.1.2 ≫ 𝟙 M.gen) ≫ pullback.fst _ _ : _ ⟶ M.X) = (T.obj.y.1.2 ≫ pullback.fst _ _) ≫ 𝟙 M.X
        simp)))))
  naturality _ _ f := ObjectProperty.hom_ext _ (CrystallineSemistableComparison.Pb.hom_ext rfl)

end LevelPullbackIdentities

theorem nmHO_nmLevB_bMap (s : ℕ)
    (hQ₁ : ∀ T, QB (S.L (m + 1)) M s T → QA (S.L (m + 1)) M s (((nmB M (hS.lev (m + 1))).mor 0).obj T))
    (hQ₀ : ∀ T, QB (S.L m) M s T → QA (S.L m) M s (((nmB M (hS.lev m)).mor 0).obj T)) (j : ℕ) (z : HO (QA (S.L (m + 1)) M s) j) :
    nmHO (nmLevB S hS m M) 1 s j (bMap M s (hS.lev (m + 1)) hQ₁ j z) =
      bMap M s (hS.lev m) hQ₀ j (nmHO (nmLevA S hS m M) l s j z) := by
  have i1 : RingHomCompTriple (S.L (m + 1)).ι (S.dB m) ((S.dB m).comp (S.L (m + 1)).ι) := ⟨rfl⟩
  have i2 : RingHomCompTriple (S.dA m) (S.L m).ι ((S.dB m).comp (S.L (m + 1)).ι) :=
    ⟨RingHom.ext fun a => (hS.dι m a).symm⟩
  have e₁ := CrystallineSemistableComparison.pull_pull ((S.dB m).comp (S.L (m + 1)).ι) (smB M s (hS.lev (m + 1)) hQ₁).o
    (nmS (nmLevB S hS m M) 1 s).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull ((S.dB m).comp (S.L (m + 1)).ι) (nmS (nmLevA S hS m M) l s).o
    (smB M s (hS.lev m) hQ₀).o j z
  exact e₁.trans ((CrystallineSemistableComparison.P.prism ((smB M s (hS.lev (m + 1)) hQ₁).o.comp (σ'' := (S.dB m).comp (S.L (m + 1)).ι) (nmS (nmLevB S hS m M) 1 s).o)
    ((nmS (nmLevA S hS m M) l s).o.comp (σ'' := (S.dB m).comp (S.L (m + 1)).ι) (smB M s (hS.lev m) hQ₀).o)
    (LevelPullbackIdentities.etaLev S hS m M s hQ₁ hQ₀) (fun T x => rfl) j z).trans e₂.symm)

end

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (s : ℕ)
  (hQN : ∀ T, QB L N s T → QA L N s (((nmB N hL).mor 0).obj T))
  (hQM : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))

namespace LevelPullbackIdentities

def etaPull : (nmS (nmPullB L u hu) 1 s).o.G ⋙ (smB N s hL hQN).o.G ⟶
      (smB M s hL hQM).o.G ⋙ (nmS (nmPullA L u hu) l s).o.G where
  app T := ObjectProperty.homMk (mkH (RingHom.id T.obj.B) (fun r => rfl)
    (DPMorphism.id T.obj.δ).isDPMorphism (fun _ h => h)
    (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => qid _ (fun _ h => h) _))
      ((spec_qid _ (fun _ h => h) _).trans (by
        show ((T.obj.y.1.2 ≫ Model.genMap u hu) ≫ pullback.fst _ _ : _ ⟶ N.X) = (T.obj.y.1.2 ≫ pullback.fst _ _) ≫ u
        simp only [Category.assoc, Model.genMap, pullback.lift_fst])))))
  naturality _ _ f := ObjectProperty.hom_ext _ (CrystallineSemistableComparison.Pb.hom_ext rfl)

end LevelPullbackIdentities

theorem nmHO_nmPullB_bMap (j : ℕ) (z : HO (QA L N s) j) :
    nmHO (nmPullB L u hu) 1 s j (bMap N s hL hQN j z) = bMap M s hL hQM j (nmHO (nmPullA L u hu) l s j z) := by
  have i1 : RingHomCompTriple L.ι (RingHom.id L.B) L.ι := ⟨RingHom.ext fun _ => rfl⟩
  have i2 : RingHomCompTriple (RingHom.id L.A) L.ι L.ι := ⟨RingHom.ext fun _ => rfl⟩
  have e₁ := CrystallineSemistableComparison.pull_pull L.ι (smB N s hL hQN).o (nmS (nmPullB L u hu) 1 s).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull L.ι (nmS (nmPullA L u hu) l s).o (smB M s hL hQM).o j z
  exact e₁.trans ((CrystallineSemistableComparison.P.prism ((smB N s hL hQN).o.comp (σ'' := L.ι) (nmS (nmPullB L u hu) 1 s).o)
    ((nmS (nmPullA L u hu) l s).o.comp (σ'' := L.ι) (smB M s hL hQM).o)
    (LevelPullbackIdentities.etaPull hL u hu s hQN hQM) (fun T x => rfl) j z).trans e₂.symm)

end

end CrystallineSemistableComparison.Pb.Kap
end
end
