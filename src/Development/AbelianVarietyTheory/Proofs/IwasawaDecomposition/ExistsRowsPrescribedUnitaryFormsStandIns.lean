module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.MemN GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.DfGen

attribute [local instance] GlobalTheory.Mem.Col2.starE

def RamSp {B : Base} (C : Cols B) (u : B.Word) : Type := (C.mem u).A.Mram

instance {B : Base} (C : Cols B) (u : B.Word) : AddCommGroup (RamSp C u) :=
  inferInstanceAs (AddCommGroup (C.mem u).A.Mram)
instance {B : Base} (C : Cols B) (u : B.Word) : Module ℂ (RamSp C u) :=
  inferInstanceAs (Module ℂ (C.mem u).A.Mram)
instance {B : Base} (C : Cols B) (u : B.Word) : FiniteDimensional ℂ (RamSp C u) :=
  haveI := (C.mem u).A.Mu0_fd
  Submodule.finiteDimensional_of_le (S₁ := (C.mem u).A.Mram) (S₂ := (C.mem u).A.Mu0) inf_le_left

def ramEq {B : Base} (C : Cols B) (u : B.Word) : RamSp C u ≃ₗ[ℂ] (C.mem u).A.Mram := LinearEquiv.refl ℂ _

@[reducible] def core {B : Base} (C : Cols B) (h : SpectralModel.ColsPos C) (u : B.Word) :
    InnerProductSpace.Core ℂ (RamSp C u) where
  inner x y := (C.fm u).ipC 0 (ramEq C u x).1 (ramEq C u y).1
  conj_inner_symm x y := (h u).1 _ (ramEq C u x).2.1 _ (ramEq C u y).2.1
  re_inner_nonneg x := by
    by_cases hx : (ramEq C u x).1 = 0
    · simp [hx, MemberForms.ipC]
    · exact ((h u).2 _ (ramEq C u x).2.1 hx).le
  add_left x y z := by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [MemberForms.ipC, map_smul, Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  definite x hx := by
    by_contra h0
    have h1 : (ramEq C u x).1 ≠ 0 := fun h1 => h0 ((ramEq C u).injective (Subtype.ext (by simpa using h1)))
    have := (h u).2 _ (ramEq C u x).2.1 h1
    rw [show (C.fm u).ipC 0 (ramEq C u x).1 (ramEq C u x).1 = 0 from hx] at this
    simp at this

def stdCongr {a b : ℕ} (h : a = b) : EuclideanSpace ℂ (Fin a) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin b) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr h)

def stdLat (O : Type) [CommRing O] (φ : O →+* ℂ) (a : ℕ) : Rows.OLat O φ (EuclideanSpace ℂ (Fin a)) where
  gen := by classical exact Finset.univ.image (EuclideanSpace.basisFun (Fin a) ℂ).toBasis
  span_top := by
    classical
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact (EuclideanSpace.basisFun (Fin a) ℂ).toBasis.span_eq

theorem subsingleton_std {k : ℕ} (h : k = 0) : Subsingleton (EuclideanSpace ℂ (Fin k)) := by
  subst h
  exact ⟨fun x y => by ext i; exact i.elim0⟩

def sigParB (B : Base) (τ : Tau B.R) (i : ℕ) : ℚ :=
  if h : i < B.R.k - 1 then (B.hc τ).v ⟨i, h⟩
  else if hb : i - (B.R.k - 1) < B.R.m then -(B.hc τ).b ⟨i - (B.R.k - 1), hb⟩ else 0

def eQB (B : Base) (j : ℕ) (τ : Tau B.R) : ℚ :=
  if h : 1 ≤ j ∧ j ≤ B.R.m then (B.hc τ).e ⟨j - 1, by omega⟩ else 0

def aPlusB (B : Base) (j : ℕ) (τ : Tau B.R) (i : ℕ) : ℚ :=
  sigParB B τ i + eQB B j τ - ((B.R.nV : ℚ) - 1 - 2 * (i : ℚ)) / 2 -
    (((B.R.k : ℚ) + j - 1) - ((B.R.m : ℚ) - j)) / 2

def aMinusB (B : Base) (j : ℕ) (τ : Tau B.R) (c : ℕ) : ℚ :=
  (if h : j + c < B.R.m then (B.hc τ).b ⟨j + c, h⟩ else 0) - eQB B j τ - ((B.R.t : ℚ) + 1 + 2 * (c : ℚ)) / 2

theorem eQB_int (B : Base) (j : ℕ) (τ : Tau B.R) : ∃ z : ℤ, eQB B j τ = z := by
  unfold eQB
  split_ifs
  · exact (B.hc τ).e_int _
  · exact ⟨0, by simp⟩

theorem sigParB_int (B : Base) (τ : Tau B.R) (i : ℕ) : ∃ z : ℤ, sigParB B τ i = z := by
  unfold sigParB
  split_ifs
  · exact (B.hc τ).v_int _
  · obtain ⟨z, hz⟩ := (B.hc τ).b_int ⟨i - (B.R.k - 1), by assumption⟩
    exact ⟨-z, by rw [hz]; simp⟩
  · exact ⟨0, by simp⟩

theorem aPlusB_int (B : Base) (j : ℕ) (τ : Tau B.R) (i : ℕ) : ∃ z : ℤ, aPlusB B j τ i = z := by
  obtain ⟨a, ha⟩ := sigParB_int B τ i
  obtain ⟨b, hb⟩ := eQB_int B j τ
  obtain ⟨s, hs⟩ := B.R.t_odd
  refine ⟨a + b - ((B.R.k : ℤ) + j - 1 - 1 - i) - (s + 1), ?_⟩
  unfold aPlusB
  rw [DV.nV_cast, ha, hb, hs]
  push_cast
  ring

theorem aMinusB_int (B : Base) (j : ℕ) (τ : Tau B.R) (c : ℕ) : ∃ z : ℤ, aMinusB B j τ c = z := by
  obtain ⟨b, hb⟩ := eQB_int B j τ
  obtain ⟨s, hs⟩ := B.R.t_odd
  have h1 : ∃ a : ℤ, (if h : j + c < B.R.m then (B.hc τ).b ⟨j + c, h⟩ else 0) = (a : ℚ) := by
    split_ifs
    · exact (B.hc τ).b_int _
    · exact ⟨0, by simp⟩
  obtain ⟨a, ha⟩ := h1
  refine ⟨a - b - (s + 1 + c), ?_⟩
  unfold aMinusB
  rw [ha, hb, hs]
  push_cast
  ring

def kaBigB (B : Base) (j : ℕ) (τ : Tau B.R) (i : Fin (B.R.sigW j).1) : ℤ := (aPlusB_int B j τ i).choose

def kaSmallB (B : Base) (j : ℕ) (τ : Tau B.R) (c : Fin (B.R.sigW j).2) : ℤ := -(aMinusB_int B j τ c).choose

def rowsStd (B : Base) (C : Cols B) (hC : SpectralModel.ColsPos C) (n : C.Tup → ℕ)
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0)))
    (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a)))
    (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a))))
    (mt : B.places.Pl → C.Tup) (hmt : ∀ w, mt (B.places.conj w) = mt w) : RowsRest B C :=
  letI nN : ∀ u, NormedAddCommGroup (RamSp C u) := fun u => (core C hC u).toNormedAddCommGroup
  letI nI : ∀ u, InnerProductSpace ℂ (RamSp C u) := fun u => InnerProductSpace.ofCore (core C hC u).toCore
  { muAt := fun _ => C.mu0
    muAt_conj := fun _ => rfl
    muTw := mt
    muTw_conj := hmt
    muAt_or := fun _ => Or.inl rfl
    EE := EuclideanSpace ℂ (Fin 0)
    Drows := 0
    onb := EuclideanSpace.basisFun (Fin 0) ℂ
    Dall := 0
    delp := 0
    delp_le_one := zero_le_one
    D_eq := by simp
    EE0 := EuclideanSpace ℂ (Fin 0)
    D0 := 0
    onb0 := EuclideanSpace.basisFun (Fin 0) ℂ
    FT := Empty
    ft := fun i => i.elim0
    ft0 := fun i => i.elim0
    Amb := fun a => EuclideanSpace ℂ (Fin (n a))
    Mult := fun a j => EuclideanSpace ℂ (Fin (if j = B.R.m then n a else 0))
    multZero := fun _ => stdCongr (if_neg (by have := B.R.two_le_m; omega))
    multTop := fun _ => stdCongr (if_pos rfl)
    io := fun _ _ => 0
    Mtilde := L
    eOp := fun _ => LinearMap.id
    eOp_idem := fun _ => LinearMap.id_comp _
    eOp_sa := fun _ _ _ => rfl
    Mu := RamSp C
    instMu := nN
    instMui := nI
    perCol := fun u a φ F =>
      haveI := Classical.dec (a = C.mu0)
      if h : a = C.mu0 then (C.mem u).P.PtilCol (ramEq C u φ).1 ((e0 u).symm (h ▸ F))
      else (C.PTw u a).PtilCol (C.e0Tw u a (ramEq C u φ).1) ((eT u a).symm F)
    Bu := fun _ _ _ => 0
    ze := fun _ _ => 1
    rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
    Mj := fun _ => EuclideanSpace ℂ (Fin 0)
    MjLat := fun _ => stdLat _ _ _
    kaBig := kaBigB B
    kaSmall := kaSmallB B
    Mt := fun _ _ => EuclideanSpace ℂ (Fin 0)
    MtLat := fun _ _ => stdLat _ _ _
    MtL := fun _ _ => PUnit
    jMt := fun _ _ => 0
    jMt_basis := fun _ _ b => by
      haveI : IsEmpty (Module.Free.ChooseBasisIndex B.LL PUnit) :=
        ⟨fun i => b.ne_zero i (Subsingleton.elim _ _)⟩
      exact ⟨linearIndependent_empty_type, Subsingleton.elim _ _⟩
    MtLat_sub := fun _ _ x _ => ⟨0, Subsingleton.elim _ _⟩
    eMt := fun _ _ => LinearMap.id
    eMt_idem := fun _ _ => LinearMap.id_comp _
    eMt_sa := fun _ _ _ _ => rfl
    eMt_LL := fun _ _ x => ⟨x, rfl⟩
    thetaP := fun _ _ => 0
    isot := fun _ _ => ⊤
    lamP := fun _ _ _ => 0
    Ij := fun _ _ _ => 0
    jw := fun _ _ _ => 0
    etaJ := fun _ _ => 0
    etaJ_nonneg := fun _ _ => le_rfl
    shaLen := GaloisStage.shaTrue B.host
    shaLen_nonneg := GaloisStage.shaTrue_nonneg B.host
    eMu := ramEq C
    eMt0 := e0
    perCol_base_eq_PtilCol := fun u φ F => dif_pos rfl
    Bu_linL := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    Bu_linR := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    eMtTw := eT
    perCol_tie := fun u a h φ F => dif_neg h
    eMu_isom := fun _ _ _ => rfl }

theorem standIn_rowsStd (B : Base) (C : Cols B) (hC : SpectralModel.ColsPos C) (n : C.Tup → ℕ)
    (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0)))
    (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a)))
    (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a))))
    (mt : B.places.Pl → C.Tup) (hmt : ∀ w, mt (B.places.conj w) = mt w) :
    StandIn (rowsStd B C hC n e0 eT L mt hmt) := by
  exact
    { drows := rfl
      d0 := rfl
      dall := rfl
      delp := rfl
      ft := ⟨fun x => nomatch x⟩
      mult := fun a j hj => subsingleton_std (if_neg hj)
      io := fun _ _ => rfl
      mj := fun _ => subsingleton_std rfl
      mt := fun _ _ => subsingleton_std rfl
      eMt := fun _ _ => rfl
      bu := fun _ _ _ => rfl
      ij := fun _ _ _ => ⟨rfl, rfl⟩
      eta := fun _ _ => rfl
      sha := shaOK_shaTrue B.toPre
      kap := fun V S N G j _ _ τ =>
        ⟨fun i => (aPlusB_int B j τ i).choose_spec.symm,
         fun c => by
           show ((-(aMinusB_int B j τ c).choose : ℤ) : ℚ) = -aMinusB B j τ c
           push_cast
           rw [← (aMinusB_int B j τ c).choose_spec]⟩ }

theorem exists_rowsRest_std : ∀ (B : Base) (C : Cols B) (n : C.Tup → ℕ) (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0))) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a))) (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a)))) (mt : B.places.Pl → C.Tup), (∀ w, mt (B.places.conj w) = mt w) → SpectralModel.ColsPos C → ∃ (W : RowsRest B C) (g : ∀ a, EuclideanSpace ℂ (Fin (n a)) ≃ₗᵢ[ℂ] W.Amb a), StandIn W ∧ (∀ w, W.muAt w = C.mu0) ∧ (∀ w, W.muTw w = mt w) ∧ (∀ u F, W.eMt0 u F = g C.mu0 (e0 u F)) ∧ (∀ u a F, W.eMtTw u a F = g a (eT u a F)) ∧ (∀ a y, g a y ∈ (W.Mtilde a).carrier ↔ y ∈ (L a).carrier) ∧ (∀ a y, g a y ∈ (W.Mtilde a).gen ↔ y ∈ (L a).gen) ∧ (∀ a, W.eOp a = LinearMap.id) ∧ ∀ u a, W.ze u a = 1 := by
  intro B C n e0 eT L mt hmt hC
  exact ⟨rowsStd B C hC n e0 eT L mt hmt, fun a => LinearIsometryEquiv.refl ℂ _,
    standIn_rowsStd B C hC n e0 eT L mt hmt, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl, fun _ _ => rfl⟩

end GlobalTheory.Mem.DfGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandInsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns : ∀ (B : Base) (C : Cols B) (n : C.Tup → ℕ) (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0))) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a))) (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a)))) (mt : B.places.Pl → C.Tup), (∀ w, mt (B.places.conj w) = mt w) → SpectralModel.ColsPos C → ∃ (W : RowsRest B C) (g : ∀ a, EuclideanSpace ℂ (Fin (n a)) ≃ₗᵢ[ℂ] W.Amb a), StandIn W ∧ (∀ w, W.muAt w = C.mu0) ∧ (∀ w, W.muTw w = mt w) ∧ (∀ u F, W.eMt0 u F = g C.mu0 (e0 u F)) ∧ (∀ u a F, W.eMtTw u a F = g a (eT u a F)) ∧ (∀ a y, g a y ∈ (W.Mtilde a).carrier ↔ y ∈ (L a).carrier) ∧ (∀ a y, g a y ∈ (W.Mtilde a).gen ↔ y ∈ (L a).gen) ∧ (∀ a, W.eOp a = LinearMap.id) ∧ ∀ u a, W.ze u a = 1 := by
  first | exact @GlobalTheory.Mem.DfGen.exists_rowsRest_std | exact GlobalTheory.Mem.DfGen.exists_rowsRest_std | (intros; apply GlobalTheory.Mem.DfGen.exists_rowsRest_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsEquiv
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.StepZero

section Gen
open _root_.Formalism.L2.Forms
variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem mem_formsK (S : GStep E K n) (hS : S.Free) (hF : (S.fam emb lam).Ok) (x : S.Cl → VV K lam) : x ∈ S.FormsK emb lam hF := by
  intro c γ
  have hγ : (γ : S.G c.1) = 1 := hS c.1 γ (S.rp c.1 c.2) γ.2
  show (S.rho emb lam c.1) (γ : S.G c.1) (x c) = x c
  rw [hγ, map_one]
  rfl

theorem forms_equiv (S S' : GStep E K n) (hS : S.Free) (hS' : S'.Free) (hF : (S.fam emb lam).Ok) (hF' : (S'.fam emb lam).Ok)
    (e0 : S.Cl ≃ S'.Cl) (hL : ∀ c, S'.Lsh _ (S'.rep (e0 c)) = S.Lsh _ (S.rep c)) :
    ∃ e : (S.hlat emb lam hF).V ≃ₗ[K] (S'.hlat emb lam hF').V,
      (∀ x, x ∈ (S.hlat emb lam hF).L ↔ e x ∈ (S'.hlat emb lam hF').L) ∧
        ∀ x, S'.embF emb σ lam hF' (e x) = fun c => S.embF emb σ lam hF x (e0.symm c) := by
  let f : S.FormsK emb lam hF →ₗ[K] S'.FormsK emb lam hF' :=
    { toFun := fun x => ⟨fun c => x.1 (e0.symm c), mem_formsK emb lam S' hS' hF' _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : S'.FormsK emb lam hF' →ₗ[K] S.FormsK emb lam hF :=
    { toFun := fun y => ⟨fun c => y.1 (e0 c), mem_formsK emb lam S hS hF _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, ?_, ?_⟩
  · ext y c
    simp [f, g]
  · ext x c
    simp [f, g]
  · intro x
    constructor
    · intro hx c
      have h1 := hx (e0.symm c)
      have h2 := hL (e0.symm c)
      rw [Equiv.apply_symm_apply] at h2
      show x.1 (e0.symm c) ∈ delAtr emb lam (S'.Lsh c.1 (S'.rep c))
      rw [h2]
      exact h1
    · intro hx c
      have h1 : x.1 (e0.symm (e0 c)) ∈ delAtr emb lam (S'.Lsh (e0 c).1 (S'.rep (e0 c))) := hx (e0 c)
      rw [hL c, Equiv.symm_apply_apply] at h1
      exact h1
  · intro x
    rfl
end Gen

attribute [local instance] GlobalTheory.Mem.Col2.starE


set_option maxHeartbeats 1600000 in
theorem law0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ l : I.Laws, I.Law0 l := by
  intro B X I hI l u a
  obtain ⟨e, he1, he2⟩ := forms_equiv B.fields.emb B.embLL (lamT (B.hcW u) 0) (I.stp u I.mu0 0) (I.stp u a 0)
    (l.lev u I.mu0).free0 (l.lev u a).free0 ((l.fmL u I.mu0).fam 0) ((l.fmL u a).fam 0) (I.eCls0 l u a)
    (fun c => by
      have h := (GlobalTheory.T.cl0_bijective_and_deco_eq I hI u a (l.idx0 a).some).2 c
      show ((I.stp u a 0).rep (I.cl0 u a (l.idx0 a).some c)).1.1.deco.1.Lsh = ((I.stp u I.mu0 0).rep c).1.1.deco.1.Lsh
      rw [h])
  exact ⟨e, he1, fun x => he2 x⟩

end GlobalTheory.Mem.Col2.StepZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory

theorem ambSpace_map_eq_sum {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} (A : HLat K)
    {W : Type} [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W) (x : A.V) :
    j x = ∑ i, σ (A.b.repr x i) • j (A.b i) := by
  conv_lhs => rw [← A.b.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]

private lemma exists_linearEquiv_euclidean_norm_eq_mulVec {ι W : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup W]
    [Module ℂ W] (bW : Module.Basis ι ℂ W) (N : Matrix ι ι ℂ) (hN : IsUnit N.det) :
    ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)),
      ∀ w, ‖g w‖ = Real.sqrt (∑ i, ‖(N.mulVec (bW.equivFun w)) i‖ ^ 2) := by
  letI := Matrix.invertibleOfIsUnitDet N hN
  let e₂ : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) := Matrix.toLinearEquiv' N this
  let e₃ : (ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ ι := (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm
  let e₄ : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι)
  refine ⟨Fintype.card ι, bW.equivFun.trans (e₂.trans (e₃.trans e₄.toLinearEquiv)), fun w => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
  rfl

theorem exists_equiv_normAt_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A : HLat K) (W : Type) [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W), (∀ v, IsUnit (A.X v).det) → LinearIndependent ℂ (fun i => j (A.b i)) → Submodule.span ℂ (Set.range fun i => j (A.b i)) = ⊤ → ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)), ∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖g (j x)‖ := by
  intro K _ _ _ σ A W _ _ j hX hli hsp
  let bW : Module.Basis A.ι ℂ W := Module.Basis.mk hli (by rw [hsp])
  have hc : ∀ x, bW.equivFun (j x) = fun i => σ (A.b.repr x i) := by
    intro x
    have hx : j x = bW.equivFun.symm (fun i => σ (A.b.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply, ambSpace_map_eq_sum]
      simp [bW, Module.Basis.mk_apply]
    rw [hx, LinearEquiv.apply_symm_apply]
  have hU : IsUnit ((A.X (InfinitePlace.mk σ))⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (hX _)
  have hv : ∀ x, Formalism.HermitianLatticesTheory.vecAt A.b (InfinitePlace.mk σ) x =
      fun i => (InfinitePlace.mk σ).embedding (A.b.repr x i) := fun x => rfl
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (A.X (InfinitePlace.mk σ))⁻¹ hU
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
  · have hU' : IsUnit (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det := by
      have e : (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)).det =
          starRingEnd ℂ ((A.X (InfinitePlace.mk σ))⁻¹).det := (RingHom.map_det _ _).symm
      rw [e]
      exact hU.map _
    obtain ⟨n, g, hg⟩ := exists_linearEquiv_euclidean_norm_eq_mulVec bW (((A.X (InfinitePlace.mk σ))⁻¹).map (starRingEnd ℂ)) hU'
    refine ⟨n, g, fun x => ?_⟩
    rw [hg, hc]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, hv, h]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← Complex.norm_conj]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_hermitianFrameNorm_at_complexPlace : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A : HLat K) (W : Type) [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W), (∀ v, IsUnit (A.X v).det) → LinearIndependent ℂ (fun i => j (A.b i)) → Submodule.span ℂ (Set.range fun i => j (A.b i)) = ⊤ → ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)), ∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖g (j x)‖ := by
  first | exact @GlobalTheory.exists_equiv_normAt_eq_norm | exact GlobalTheory.exists_equiv_normAt_eq_norm | (intros; apply GlobalTheory.exists_equiv_normAt_eq_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClasses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HermTransport

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open scoped TensorProduct

theorem reGL_refl_apply' {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  ext a b
  simp [reGL]

theorem reGL_refl_hom' {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_refl_apply' R g

omit [StarRing E] in
theorem reL_refl' {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x
  simp [reL, reV]

theorem classTie_of_reindex (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) {σ : E →ₐ[F] E}
    (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ a b, J a b = S.gram (Fin.cast h.symm a) (Fin.cast h.symm b))
    {U' : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))} {Lb' : Submodule (𝓞 E) (Fin n → E)}
    {cl cl' : Type} (e : cl' ≃ cl) {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) S.V)
    (y : cl → UPts σ J (Formalism.L2.Herm.Af F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) :
      ClassSet ((ratPts σ J (Formalism.L2.Herm.Af F)).subgroupOf (UPts σ J (Formalism.L2.Herm.Af F)))
        (U'.subgroupOf (UPts σ J (Formalism.L2.Herm.Af F))))))
    (y_lat : ∀ c (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      x ∈ Formalism.L2.Herm.hatL (F := F) (reL h (Formalism.L2.Herm.crdLat S (lat c))) ↔
        ((y c).1⁻¹).1 *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Lb')
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J)
    (stabI_inj : ∀ c, Function.Injective (stabI c))
    (stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (Formalism.L2.Herm.Af F)) γ.1 ∈ U'.map (MulAut.conj (y c).1).toMonoidHom)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) (U : Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (hLb : Lb' = reL h Lb) (hU : U' = U.map (reGL h _).toMonoidHom) :
    ∃ C : Formalism.L2.Herm.ClassTie hc S Lb U (fun c' => stab (e c')) (fun c' => lat (e c')),
      (∀ c', (y (e c')).1 = reGL h _ (C.y c').1) ∧ ∀ c' s, (stabI (e c') s).1 = reGL h _ (C.stabI c' s).1 := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := by
    ext a b
    simpa using hJ a b
  subst hLb
  subst hU
  have hU0 : U.map (reGL (rfl : S.rank = S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)).toMonoidHom = U := by
    rw [reGL_refl_hom', Subgroup.map_id]
  rw [hU0] at y_bij stabI_range
  simp only [reL_refl'] at y_lat
  refine ⟨⟨fun c' => y (e c'), y_bij.comp e.bijective, fun c' x => y_lat (e c') x, fun c' => stabI (e c'),
    fun c' => stabI_inj (e c'), fun c' γ => stabI_range (e c') γ⟩,
    fun c' => (reGL_refl_apply' _ _).symm, fun c' s => (reGL_refl_apply' _ _).symm⟩

end Gen

theorem latCrd_eq_reL (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    latCrd D i hi L = reL (rankN D i hi) (Formalism.L2.Herm.crdLat (D.sp.X i) L) := by
  ext x
  simp [latCrd, reL, Formalism.L2.Herm.crdLat, reV, Formalism.L2.Herm.crd]

theorem classTie_of_chart : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  intro D i hi T bad cl cl' e stab _ lat K T' f' L hLb hU
  exact classTie_of_reindex D.sp.cm (D.sp.X i) (rankN D i hi) rfl (fun a b => rfl) e lat K.y K.y_bij
    (fun c x => by rw [← latCrd_eq_reL]; exact K.y_lat c x) K.stabI K.stabI_inj K.stabI_range L.Lb L.U hLb hU

end GlobalTheory.HermTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClassesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianClassCondition_of_chartClasses : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  first | exact @GlobalTheory.HermTransport.classTie_of_chart | exact GlobalTheory.HermTransport.classTie_of_chart | (intros; apply GlobalTheory.HermTransport.classTie_of_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReLev0
noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}

abbrev recOf (Z : Later B C) : D7 := assemble B C Z.W Z.V Z.S Z.N Z.G

variable {Z : Later B C} (Z' : Later B C)


set_option maxHeartbeats 4000000 in
def atTTRe {u : B.Word} (A : AtTTied (D := recOf Z) u) : AtTTied (D := recOf Z') u := { A with }


set_option maxHeartbeats 4000000 in
def clsRe {u : B.Word} {i : ℕ} {hi : i ≤ B.R.m} (K : ClsTied (D := recOf Z) u i hi) : ClsTied (D := recOf Z') u i hi := { K with }


set_option maxHeartbeats 4000000 in
def valRe {u : B.Word} {eV : (C.mem u).A.vT ≃ PlT (recOf Z) u} {i : ℕ} {hi : i ≤ B.R.m} {K : ClsTied (D := recOf Z) u i hi}
    (W : ValTied (D := recOf Z) u eV i hi K) : ValTied (D := recOf Z') u eV i hi (clsRe Z' K) := { W with }


set_option maxHeartbeats 4000000 in
def lvRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {i : ℕ} {hi : i ≤ B.R.m} (P : LvTied (D := recOf Z) u A i hi) :
    LvTied (D := recOf Z') u (atTTRe Z' A) i hi := { P with }


set_option maxHeartbeats 4000000 in
def clsPRe {u : B.Word} (K : ClsPTied (D := recOf Z) u) : ClsPTied (D := recOf Z') u := { K with }


set_option maxHeartbeats 4000000 in
def valPRe {u : B.Word} {K : ClsPTied (D := recOf Z) u} (W : ValPTied (D := recOf Z) u K) :
    ValPTied (D := recOf Z') u (clsPRe Z' K) := { W with }


set_option maxHeartbeats 4000000 in
def tilRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {K : ClsPTied (D := recOf Z) u} {P : LvTied (D := recOf Z) u A B.R.m le_rfl}
    (Tl : TilTied (D := recOf Z) u A K P) : TilTied (D := recOf Z') u (atTTRe Z' A) (clsPRe Z' K) (lvRe Z' P) := { Tl with }


set_option maxHeartbeats 4000000 in
def tilAdRe {u : B.Word} {A : AtTTied (D := recOf Z) u} {K : ClsPTied (D := recOf Z) u} {P : LvTied (D := recOf Z) u A B.R.m le_rfl}
    {Tl : TilTied (D := recOf Z) u A K P} {Km : ClsTied (D := recOf Z) u B.R.m le_rfl} (Ta : TilAd (D := recOf Z) Tl Km) :
    TilAd (D := recOf Z') (tilRe Z' Tl) (clsRe Z' Km) := { Ta with }


set_option maxHeartbeats 4000000 in
def chartRe {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {i : ℕ} {hi : i ≤ B.R.m} {cl : Type}
    {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    (K : LevelChart (recOf Z) T bad i hi stab lat) : LevelChart (recOf Z') T bad i hi stab lat := { K with }


set_option maxHeartbeats 4000000 in
def lvGRe {u : B.Word} {T : ℕ} {res : ∀ v : (C.mem u).A.vT, 𝓞 B.host.E →+* (C.mem u).A.Fv v} {i : ℕ} {hi : i ≤ B.R.m}
    {lat : (C.mem u).C.cls i → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    (L : LevelCompatibleLattices (D := recOf Z) (u := u) (C.fm u) T res i hi lat) : LevelCompatibleLattices (D := recOf Z') (u := u) (C.fm u) T res i hi lat := { L with }


set_option maxHeartbeats 16000000 in
def formsRe {u : B.Word} {Ch : ℕ → Type} {chOf : ∀ i, (C.mem u).C.cls i → Ch i} (T : FormsTiedSym (recOf Z) u Ch chOf) :
    FormsTiedSym (recOf Z') u Ch chOf :=
  { T with
    atT := atTTRe Z' T.atT
    cls := fun i hi h => clsRe Z' (T.cls i hi h)
    val := fun i hi h => valRe Z' (T.val i hi h)
    lv := fun i hi => lvRe Z' (T.lv i hi)
    ch := fun i h1 h2 β => chartRe Z' (T.ch i h1 h2 β)
    valC := fun i h1 h2 => { T.valC i h1 h2 with }
    dilC := fun i h1 h2 => { T.dilC i h1 h2 with }
    lvC := fun i h1 h2 => lvGRe Z' (T.lvC i h1 h2)
    clsP := clsPRe Z' T.clsP
    valP := valPRe Z' T.valP
    til := tilRe Z' T.til
    tilAd := tilAdRe Z' T.tilAd }


set_option maxHeartbeats 4000000 in
def hermChRe (H : Formalism.L2.Herm.HermColsCh (recOf Z)) : Formalism.L2.Herm.HermColsCh (recOf Z') := { H with }


set_option maxHeartbeats 4000000 in
def atTRe {u : B.Word}
    {e : (C.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 B.host.F) // (((C.mem u).A.T : ℕ) : 𝓞 B.host.F) ∈ v.asIdeal}}
    {eF : ∀ v : (C.mem u).A.vT, (C.mem u).A.Fv v ≃+* (𝓞 B.host.F ⧸ (e v).1.asIdeal)} (A : Formalism.L2.Herm.AtT (recOf Z) u e eF) :
    Formalism.L2.Herm.AtT (recOf Z') u e eF := { A with }


set_option maxHeartbeats 4000000 in
def hermRe (H : Formalism.L2.Herm.ColsHermS (recOf Z)) : Formalism.L2.Herm.ColsHermS (recOf Z') :=
  { H with
    base := hermChRe Z' H.base
    atT := fun u => atTRe Z' (H.atT u)
    ad := { H.ad with } }


set_option maxHeartbeats 16000000 in
def colsRe (T : ColsTiedSym (recOf Z)) : ColsTiedSym (recOf Z') :=
  { T with
    herm := hermRe Z' T.herm
    forms := fun u => formsRe Z' (T.forms u)
    gl_const := T.gl_const }

end GlobalTheory.Mem.Top.ColOwe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapHypOfNodes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNodeGapGeRankPow
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top Filter

namespace GlobalTheory.Mem.Top.NodeGap

theorem rank_le {s : Scale} {R : Ranks} (h : RankVal s R) (hx : 4 ≤ s.x) : (R.r : ℝ) ≤ s.x ^ 6 := by
  have h1 : (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps) := h.2.2.1.2
  have h2 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ 5 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; push_cast; linarith)
  have h3 : R.r ≤ 2 * R.k := by have := R.m_add_three_le_k; unfold Ranks.r; omega
  have h4 : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast h3
  have h5 : (0 : ℝ) < s.x ^ 5 := by positivity
  calc (R.r : ℝ) ≤ 4 * s.x ^ 5 := by linarith
    _ ≤ s.x * s.x ^ 5 := by gcongr
    _ = s.x ^ 6 := by ring

theorem le_m {s : Scale} {R : Ranks} (h : RankVal s R) {M : ℕ} (hx : (M : ℝ) ^ 4 ≤ s.x) : M ≤ R.m := by
  have h1 : Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) := h.2.1.1
  have hx0 : 0 < s.x := by linarith [s.one_lt_alt]
  have h2 : (M : ℝ) ^ 2 ≤ s.x * s.delta1 := by
    have e : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
      unfold Scale.delta1
      rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
    have h3 : s.x ^ ((1 : ℝ) / 2) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; linarith)
    rw [e]
    refine le_trans ?_ h3
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by rw [← pow_mul]; exact hx)
  have h4 : (M : ℝ) ≤ R.m := (Real.le_sqrt_of_sq_le h2).trans h1
  exact_mod_cast h4

theorem b_eq (K : Ctx) (u : K.P.Word) (τ : Tau K.P.R) :
    ∃ b1 : ℤ, ∀ j : Fin K.P.R.m, (K.P.hcW u τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h0v K.s K.ch : ℚ) ∧
      (K.P.hcW u τ).e j = (K.P.hcW u τ).b j + (h0v K.s K.ch : ℚ) / 2 := by
  obtain ⟨b1, h, -⟩ := (K.ok.hc u).2.2.1
  exact ⟨b1 τ, h τ⟩

theorem eventually_nodeGap_ge_rank_pow (A : ℝ) (N M : ℕ) : Ev fun K => M ≤ K.P.R.m ∧ A * (K.P.R.r : ℝ) ^ N ≤ (h0v K.s K.ch : ℝ) := by
  refine ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨6 * N + 1, fun ch hch =>
    ⟨max (max 4 A) ((M : ℝ) ^ 4), fun K _ _ h3 _ hx => ?_⟩⟩⟩⟩⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx4, hxA⟩, hxM⟩ := hx
  refine ⟨le_m K.ok.rank hxM, ?_⟩
  have h1 := rank_le K.ok.rank hx4
  have h2 : K.s.x ^ (6 * N + 1) ≤ K.s.x ^ K.ch := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le K.s.one_lt_alt.le (by rw [h3]; push_cast; exact hch)
  have h5 : K.s.x ^ K.ch ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.le_ceil _
  have h6 : (0 : ℝ) ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.cast_nonneg _
  calc A * (K.P.R.r : ℝ) ^ N ≤ K.s.x * (K.s.x ^ 6) ^ N := by gcongr
    _ = K.s.x ^ (6 * N + 1) := by ring
    _ ≤ (h0v K.s K.ch : ℝ) := by unfold h0v; push_cast; linarith

theorem ev_nodes (A : ℝ) (N M : ℕ) : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → M ≤ X.toD7.R.m ∧
    ∃ h : ℕ, A * (X.toD7.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin X.toD7.R.m,
      (X.toD7.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (X.toD7.hc τ).e j = (X.toD7.hc τ).b j + (h : ℚ) / 2 := by
  obtain ⟨a, ha, hp⟩ := eventually_nodeGap_ge_rank_pow A N M
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K0, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K0, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  refine ⟨a3, fun K h1 h2 h3 h4 hx X hO => ?_⟩
  obtain ⟨g1, g2⟩ := ha3 K h1 h2 h3 h4 hx
  have key : ∀ B : Pre, K.Over B → M ≤ B.R.m ∧
      ∃ h : ℕ, A * (B.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin B.R.m,
        (B.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (B.hc τ).e j = (B.hc τ).b j + (h : ℚ) / 2 := by
    rintro B ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩
    exact ⟨g1, _, g2, fun τ => b_eq K K.P.u₀ τ⟩
  exact key _ hO

end GlobalTheory.Mem.Top.NodeGap
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.Mem.Top.NodeGap

theorem gapHyp_of_nodes (D : D7) (hm : 1801 ≤ D.R.m) (h : ℕ) (hh : 16 * (D.R.r : ℝ) ^ 19 ≤ (h : ℝ))
    (hb : ∀ τ, ∃ b1 : ℤ, ∀ j : Fin D.R.m, (D.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ)) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  refine ⟨?_, ?_⟩
  · have h1 := D.R.m_add_three_le_k
    show 1801 ≤ D.R.k + D.R.m - 1
    omega
  · intro τ j hj
    obtain ⟨b1, hb1⟩ := hb τ
    rw [hb1 ⟨j.1 + 1, hj⟩, hb1 j]
    have h2 : 16 * D.R.r ^ 19 ≤ h := by exact_mod_cast hh
    have h3 : (16 * (D.R.r : ℚ) ^ 19) ≤ (h : ℚ) := by exact_mod_cast h2
    push_cast
    linarith

private theorem ev_mono_of_forall_imp {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  unfold Ev at hp ⊢
  obtain ⟨w, hw, H⟩ := hp
  refine ⟨w, hw, fun eps C8 a b c d => ?_⟩
  obtain ⟨K0, H1⟩ := H eps C8 a b c d
  refine ⟨K0, fun C e f g => ?_⟩
  obtain ⟨c1, H2⟩ := H1 C e f g
  refine ⟨c1, fun cD hc => ?_⟩
  obtain ⟨c2, H3⟩ := H2 cD hc
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H4⟩ := H3 ch hch
  exact ⟨x0, fun K k1 k2 k3 k4 k5 => h K (H4 K k1 k2 k3 k4 k5)⟩

theorem ev_gapHyp : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → Formalism.L2.SG.ConcreteSettingExists.GapHyp X.toD7 := by
  refine ev_mono_of_forall_imp ?_ (ev_nodes 16 19 1801)
  intro K hK X hX
  obtain ⟨hm, h, hh, hb⟩ := hK X hX
  exact gapHyp_of_nodes X.toD7 hm h hh fun τ => (hb τ).imp fun b1 hb1 j => (hb1 j).1

end GlobalTheory.Mem.Top.NodeGap
end
