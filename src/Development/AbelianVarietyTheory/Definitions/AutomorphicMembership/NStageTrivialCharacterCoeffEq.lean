module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure LocStage where
  loc : LocTheory
  locA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (loc l)
  locT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (loc l) (locA l)

structure NStage (B : Base) (C : Cols B) (W : RowsRest B C) extends LocStage where
  nd : NData B.R B.host W.what₂
  ntw : NTw B.R B.host W.what₂ B.LL0 nd
  naut : NAut nd
  nbc : NBC naut
  nexp : NExp B.R B.host W.what₂ B.LL0 nd ntw
  ntypes : NTypes naut
  nStage_trivialCharacter_compat : ntypes.IdempotentMatchesAction
  nStage_trivialCharacter_coeff_eq : ∀ g : G0g nd, B.embLL ((nexp.eLL0 g : ↥B.LL0) : B.LL) = ntypes.e0.coeff g
  nth : NTh B.R B.host W.what₂ B.LL0 nd ntw nexp
  nbr : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 B.host.E)), w ∈ Formalism.BasicNotions.placesOver B.host.E (nd.l i) →
    Formalism.BasicNotions.LocBridge (nd.l i) B.host.E nd.Om (ReciprocityTheory.Gal.Dec (F := B.host.E) (nd.plOm.1 w)) (nd.O i)
  nbr_ind : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver B.host.E (nd.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(nbr i w hw).j x‖ ≤ 1
  self_good : ∀ (i : nd.Loc) (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver B.host.E (nd.l i)),
    Formalism.BasicNotions.Loc.GoodCoef B.host.condN (nbr i w hw).LL
  ntwbr : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 B.host.E)), w ∈ Formalism.BasicNotions.placesOver B.host.E (ntw.l i) →
    Formalism.BasicNotions.LocBridge (ntw.l i) B.host.E nd.Om (ReciprocityTheory.Gal.Dec (F := B.host.E) (nd.plOm.1 w)) (ntw.O0 i)
  ntwbr_ind : ∀ (i : ntw.Tw) (w : HeightOneSpectrum (𝓞 B.host.E)) (hw : w ∈ Formalism.BasicNotions.placesOver B.host.E (ntw.l i))
    (x : nd.Om), x ∈ nd.plOm.1 w ↔ ‖(ntwbr i w hw).j x‖ ≤ 1
  loc_tie : Formalism.MainNotions.N.LocTie nd naut loc nbr
  bc_tie : Formalism.MainNotions.N.BcTie nd naut ntypes
  rbar_tie : Formalism.MainNotions.N.RbarTie nd naut ntypes
  mtpar_tie : Formalism.MainNotions.N.MtParTie nd naut ntypes
  Z_tie : ∀ i x, x ∈ nd.Z i ↔ x ∈ Formalism.MainNotions.N.ZN nd naut i
  Zgood_tie : ∀ i x, x ∈ nd.Zgood i ↔ x ∈ Formalism.MainNotions.N.ZgoodN nd naut i
  etaJ_tie : ∀ j w, 1 ≤ j → j ≤ B.R.m → W.etaJ j w = ∑ i ∈ nd.locs j w, nd.etaLoc i

end GlobalTheory.Mem

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NuInRange
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure DivStage (B : Base) (C : Cols B) (W : RowsRest B C) where
  div : DivData B.LL B.Word
  div_good : (∀ v, IsUnit (div.RR.X v).det) ∧ ∀ u v, IsUnit ((div.Nu u).X v).det
  jEE : div.RR.V →ₛₗ[B.embLL] W.EE
  jEE_basis : LinearIndependent ℂ (fun i => jEE (div.RR.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jEE (div.RR.b i))) = ⊤
  jN : ∀ u, (div.Nu u).V →ₛₗ[B.embLL] W.Mu u
  jN_basis : ∀ u, LinearIndependent ℂ (fun i => jN u ((div.Nu u).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jN u ((div.Nu u).b i))) = ⊤
  Dall_eq : div.Dall = W.Dall
  delP_eq : div.delP = W.delp
  nuIn : ∀ u, (div.Nu u).V →ₗ[B.LL] ((C.fm u).lat 0).V
  nuIn_inj : ∀ u, Function.Injective (nuIn u)
  nuIn_range : ∀ u, LinearMap.range (nuIn u) = (C.fm u).ramSub
  nuIn_jN : ∀ u (x : (div.Nu u).V),
    ((W.eMu u (jN u x) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) = (C.fm u).emb 0 (nuIn u x)
  nuIn_norm : ∀ u v (x : (div.Nu u).V), Formalism.HermitianLatticesTheory.normAt (div.Nu u).b (div.Nu u).X v x =
    Formalism.HermitianLatticesTheory.normAt ((C.fm u).lat 0).b ((C.fm u).lat 0).X v (nuIn u x)
  jEE_norm : ∀ x : div.RR.V,
    Formalism.HermitianLatticesTheory.normAt div.RR.b div.RR.X (InfinitePlace.mk B.embLL) x = ‖jEE x‖

end GlobalTheory.Mem

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SCuIsom
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure SStage (B : Base) (C : Cols B) (W : RowsRest B C) where
  dsig : (Tau B.R) → ℝ
  dsig_pos : ∀ ρ, 0 < dsig ρ
  s : Formalism.MainNotions.S.Draft.SData B.R B.host.F B.host.E B.toPre.conjF B.Word (Tau B.R) B.hcW
  s_split : ∀ p, (s.atP p).split.isSome ↔
    Formalism.MainNotions.S.Loc.resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  s_HH : Module.finrank ℂ s.HH = W.Dall
  s_Cu : ∀ u, s.Cu u ≃ₗ[ℂ] (C.mem u).A.Mu0
  s_PlF : s.PlF ≃ HeightOneSpectrum (𝓞 B.host.F)
  s_Cu_isom : ∀ u (x y : s.Cu u), inner ℂ x y =
    (C.fm u).ipC 0 ((s_Cu u x : (C.mem u).A.Mu0) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
      ((s_Cu u y : (C.mem u).A.Mu0) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
  sEE : W.EE →ₗᵢ⋆[ℂ] s.HH

end GlobalTheory.Mem

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ModelLamPDef
noncomputable section

namespace GlobalTheory.Mem.RowsRestModel

open Formalism.BasicNotions NumberField

variable {B : Base}

abbrev Eu (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

structure Fits (C : Cols B) (d : C.Tup → ℕ) : Prop where
  mt0 : ∀ u, Nonempty ((C.mem u).P.Mt ≃ₗ[ℂ] Eu (d C.mu0))
  mtTw : ∀ u μ, Nonempty ((C.PTw u μ).Mt ≃ₗ[ℂ] Eu (d μ))
  herm : ∀ u (x y : (C.mem u).A.Mram), starRingEnd ℂ ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y
  pos : ∀ u (x : (C.mem u).A.Mram), 0 ≤ ((C.fm u).ipC 0 x x).re
  defn : ∀ u (x : (C.mem u).A.Mram), (C.fm u).ipC 0 x x = 0 → x = 0

def MuT (C : Cols B) (u : B.Word) : Type := (C.mem u).A.Mram

instance (C : Cols B) (u : B.Word) : AddCommGroup (MuT C u) := inferInstanceAs (AddCommGroup (C.mem u).A.Mram)
instance (C : Cols B) (u : B.Word) : Module ℂ (MuT C u) := inferInstanceAs (Module ℂ (C.mem u).A.Mram)
instance (C : Cols B) (u : B.Word) : FiniteDimensional ℂ (MuT C u) :=
  haveI := (C.mem u).A.Mu0_fd
  (Submodule.finiteDimensional_of_le (inf_le_left : (C.mem u).A.Mram ≤ (C.mem u).A.Mu0) :
    FiniteDimensional ℂ (C.mem u).A.Mram)

@[reducible] def core {C : Cols B} {d : C.Tup → ℕ} (h : Fits C d) (u : B.Word) : InnerProductSpace.Core ℂ (MuT C u) where
  inner x y := (C.fm u).ipC 0 (Subtype.val x) (Subtype.val y)
  conj_inner_symm x y := h.herm u x y
  re_inner_nonneg x := h.pos u x
  add_left x y z := by
    show (C.fm u).ipC 0 (x.1 + y.1) z.1 = (C.fm u).ipC 0 x.1 z.1 + (C.fm u).ipC 0 y.1 z.1
    simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left x y r := by
    show (C.fm u).ipC 0 (r • x.1) y.1 = starRingEnd ℂ r * (C.fm u).ipC 0 x.1 y.1
    simp only [MemberForms.ipC, Pi.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  definite x hx := h.defn u x hx

def stdOLat (O : Type) [CommRing O] (φ : O →+* ℂ) (n : ℕ) : Rows.OLat O φ (Eu n) where
  gen := by classical exact Finset.univ.image (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  span_top := by
    classical
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact Module.Basis.span_eq _

def stdJ {L : Type} [Field L] (σ : L →+* ℂ) (n : ℕ) : (Fin n → L) →ₛₗ[σ] Eu n where
  toFun x := WithLp.toLp 2 (fun i => σ (x i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

theorem stdJ_single {L : Type} [Field L] (σ : L →+* ℂ) (n : ℕ) (i : Fin n) :
    stdJ σ n (Pi.single i 1) = (EuclideanSpace.basisFun (Fin n) ℂ).toBasis i := by
  ext k
  by_cases h : k = i
  · subst h; simp [stdJ]
  · simp [stdJ, h, Pi.single_eq_of_ne h]

theorem stdJ_basis {L : Type} [Field L] (σ : L →+* ℂ) (n : ℕ) {κ : Type} (b : Module.Basis κ L (Fin n → L)) :
    LinearIndependent ℂ (fun i => stdJ σ n (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => stdJ σ n (b i))) = ⊤ := by
  constructor
  · letI : Algebra L ℂ := σ.toAlgebra
    have h : LinearIndependent ℂ (fun i => algebraMap L ℂ ∘ b i) :=
      linearIndependent_algebraMap_comp_iff.2 b.linearIndependent
    exact h.map' (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
  · have h : ∀ x, stdJ σ n x ∈ Submodule.span ℂ (Set.range (fun i => stdJ σ n (b i))) := by
      intro x
      have hx : x ∈ Submodule.span L (Set.range b) := by rw [b.span_eq]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
    rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← stdJ_single σ]
    exact h _

def trunc (a b : ℕ) : Eu a →ₗ[ℂ] Eu b :=
  Matrix.toEuclideanLin (Matrix.of fun (i : Fin b) (k : Fin a) => if (i : ℕ) = k then (1 : ℂ) else 0)

theorem chain_lin {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (j : ℕ) :
    IsLinearMap ℂ (Formalism.ThetaLiftIndependence.chainOpM C.wt C.Kmap j) := by
  induction j with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ j ih =>
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · show C.Klin j _ = C.Klin j _ + C.Klin j _
      rw [ih.map_add (f := _), map_add (f := _)]
    · show C.Klin j _ = c • C.Klin j _
      rw [ih.map_smul, map_smul]

def mdim (n e : ℕ) : ℕ → ℕ
  | 0 => n
  | _ + 1 => e

theorem mdim_m (R : Ranks) (n e : ℕ) : mdim n e R.m = e := by
  have := R.two_le_m
  obtain ⟨k, hk⟩ : ∃ k, R.m = k + 1 := ⟨R.m - 1, by omega⟩
  rw [hk]; rfl

def model {C : Cols B} {d : C.Tup → ℕ} (h : Fits C d) (n n₀ a : ℕ) : RowsRest B C where
  muAt _ := C.mu0
  muAt_conj _ := rfl
  muTw _ := C.muStar
  muTw_conj _ := rfl
  muAt_or _ := Or.inl rfl
  EE := Eu n
  Drows := n
  onb := EuclideanSpace.basisFun (Fin n) ℂ
  Dall := 2 * n
  delp := 1 / 2
  delp_le_one := by norm_num
  D_eq := by push_cast; ring
  EE0 := Eu n₀
  D0 := n₀
  onb0 := EuclideanSpace.basisFun (Fin n₀) ℂ
  FT := Unit
  ft _ := ()
  ft0 _ := ()
  Amb μ := Eu (d μ)
  Mult μ j := Eu (mdim n (d μ) j)
  multZero _ := LinearIsometryEquiv.refl ℂ (Eu n)
  multTop μ := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (mdim_m B.R n (d μ)))
  io μ j := trunc _ _
  Mtilde μ := stdOLat _ _ _
  eOp _ := LinearMap.id
  eOp_idem _ := rfl
  eOp_sa _ := fun _ _ => rfl
  Mu u := MuT C u
  instMu u := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (core h u)
  instMui u := InnerProductSpace.ofCore (core h u).toCore
  instMuf u := inferInstanceAs (FiniteDimensional ℂ (MuT C u))
  perCol u μ φ F := by
    classical
    exact if hμ : μ = C.mu0 then (C.mem u).P.PtilCol φ.1 ((h.mt0 u).some.symm (hμ ▸ F))
      else (C.PTw u μ).PtilCol (C.e0Tw u μ φ.1) ((h.mtTw u μ).some.symm F)
  Bu u φ F := (C.mem u).P.PtilCol φ.1 ((h.mt0 u).some.symm (trunc n (d C.mu0) F))
  ze _ _ := 1
  rowsRest_wordColumnUnit_baseTuple _ := rfl
  Mj _ := Eu a
  MjLat _ := stdOLat _ _ _
  kaBig _ _ _ := 1
  kaSmall _ _ _ := -1
  Mt _ _ := Eu a
  MtLat _ _ := stdOLat _ _ _
  MtL _ _ := Fin a → B.LL
  jMt _ _ := stdJ B.embLL a
  jMt_basis _ _ b := stdJ_basis _ _ b
  MtLat_sub _ _ x hx := by
    classical
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨_, stdJ_single _ _ i⟩
  eMt _ _ := LinearMap.id
  eMt_idem _ _ := rfl
  eMt_sa _ _ := fun _ _ => rfl
  eMt_LL _ _ x := ⟨x, rfl⟩
  thetaP _ _ := LinearMap.id
  isot _ _ := ⊤
  lamP _ _ _ := 1
  Ij _ _ _ := 0
  jw _ _ _ := 0
  etaJ _ _ := 0
  etaJ_nonneg _ _ := le_rfl
  shaLen _ _ := 1
  shaLen_nonneg _ _ := zero_le_one
  eMu u := LinearEquiv.refl ℂ (C.mem u).A.Mram
  eMt0 u := (h.mt0 u).some
  perCol_base_eq_PtilCol u φ F := by
    rw [dite_eq_left rfl]; rfl
  Bu_linL u F := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · show (C.mem u).P.Ptil (Formalism.ThetaLiftIndependence.chainOpM (C.mem u).C.wt (C.mem u).C.Kmap B.R.m (x.1 + y.1)) _ = _
      rw [(chain_lin _ _).map_add (f := _)]
      simp [PeriodMap.Ptil, PeriodMap.PtilCol, ColumnChain.col]
    · show (C.mem u).P.Ptil (Formalism.ThetaLiftIndependence.chainOpM (C.mem u).C.wt (C.mem u).C.Kmap B.R.m (c • x.1)) _ = _
      rw [(chain_lin _ _).map_smul]
      simp [PeriodMap.Ptil, PeriodMap.PtilCol, ColumnChain.col]
  Bu_linR u φ := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩ <;> simp [PeriodMap.Ptil, PeriodMap.PtilCol]
  eMtTw u μ := (h.mtTw u μ).some
  perCol_tie u μ hμ φ F := by
    rw [dite_eq_right hμ]; rfl
  eMu_isom _ _ _ := rfl



end GlobalTheory.Mem.RowsRestModel

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WithTrue
noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory.Mem

def GJStage.withTrue {B : Base} {C : Cols B} (G : GJStage B C) : GJStage B C :=
  letI := B.host.cmStar
  { G with
    vol := fun W => Vol.trueVol B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    vol_pos := fun W => Vol.trueVol_pos B.sp.cm (fun g : Tau B.R => B.host.emb g.1) G.cd W
    gx := Per.trueGx B.host B.embLL B.embE (Equiv.refl _) }

end GlobalTheory.Mem
end
end
