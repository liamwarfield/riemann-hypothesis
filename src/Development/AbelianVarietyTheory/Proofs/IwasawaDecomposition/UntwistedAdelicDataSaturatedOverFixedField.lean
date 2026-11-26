module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedCoefficientFieldInComplex
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

def SeedW (K : Ctx) (P : Pre) (f : Fr P) (F F₀ : IntermediateField ℚ ℂ) (px : PreX P) (S : Set ℕ) (L : IntermediateField ℚ ℂ) :
    Prop :=
  ∃ (B₀ : Base) (f₀ : Fr B₀.toPre) (T₀ : TwDat B₀) (w₀ : ColW B₀ f₀ T₀) (Z₀ : w₀.Lt) (hX₀ : B₀.fields.Ok) (Wt₀ : Set B₀.places.Pl)
    (z₀ : Dat (w₀.st Z₀) w₀.I hX₀ T₀ Wt₀), B₀.toPre = P ∧ HEq f₀ f ∧ B₀.KsC = F ∧ B₀.fixedCoefficientFieldInComplex = F₀ ∧ HEq w₀.px px ∧
      Pinned K B₀ f₀ T₀ w₀ ∧ GrpTrue Z₀.N f₀ ∧ GrpAt (w₀.st Z₀) w₀.I ∧ Fine z₀ ∧ HoldsL z₀.R z₀.F ∧
      (∀ v ∈ z₀.W1 (fun _ _ => 0), B₀.places.resChar v ∈ S) ∧ B₀.LLC ≤ L

theorem SeedW.mono {K : Ctx} {P : Pre} {f : Fr P} {F F₀ : IntermediateField ℚ ℂ} {px : PreX P} {S S' : Set ℕ}
    {L L' : IntermediateField ℚ ℂ} (h : SeedW K P f F F₀ px S L) (hS : S ⊆ S') (hL : L ≤ L') : SeedW K P f F F₀ px S' L' := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun v hv => hS (a11 v hv), a12.trans hL⟩

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteNonzeroIndexPlacesReferenceTuple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Resize

variable {B : Base}

@[reducible] def preX {P : Pre} (X Y : PreX P) : PreX P := { X with a := Y.a, T_gt := Y.T_gt, a_gt := Y.a_gt, spread_le := Y.spread_le }

theorem preX_eq {P : Pre} {X Y : PreX P} (h : X.piG = Y.piG) (h' : X.piT = Y.piT) : preX X Y = Y := by
  cases X; cases Y; cases h; cases h'; rfl

@[reducible] def colIn {X : PreX B.toPre} (I : ColIn B X) (Y : PreX B.toPre) : ColIn B (preX X Y) :=
  @ColIn.mk B (preX X Y) I.C I.Ch I.sel I.S I.ι I.finι I.tup I.tup_inj I.mu0 I.muStar I.muStar' I.trueColumn_tuple_trivial_eq_one I.xi I.cst I.idx I.J


set_option maxHeartbeats 2000000 in
theorem laws {X : PreX B.toPre} (I : ColIn B X) (Y : PreX B.toPre) (l : TC.Laws I) : TC.Laws (colIn I Y) :=
  ⟨l.pr, l.ch, l.lev, l.per, l.ovr, l.atL, l.fmL, l.xi0, l.idx0, l.bij0, l.lat⟩

variable {f : Top.Fr B.toPre} {T : TwDat B}


set_option maxHeartbeats 4000000 in
@[reducible] def colW (w : ColW B f T) (Y : PreX B.toPre) : ColW B f T where
  px := preX w.px Y
  I := colIn w.I Y
  ok := ⟨w.ok.spaces, w.ok.ch_ok, w.ok.ch_tied, w.ok.weil, w.ok.pibar, w.ok.sel_ok, w.ok.T_mem, w.ok.g_mem, w.ok.ram_mem, w.ok.xi_reads,
    w.ok.xi_star, w.ok.xi_star', w.ok.sharp, w.ok.idx_ok, w.ok.amb_ok, w.ok.duStar⟩
  C_eq := w.C_eq
  S_eq := w.S_eq
  xi_range := w.xi_range
  pins := ⟨w.pins.iX, w.pins.cof⟩
  l := laws w.I Y w.l
  l0 := w.l0
  δ := w.δ
  exact := w.exact
  fld := w.fld
  val := w.val


set_option maxHeartbeats 4000000 in
@[reducible] def dat (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt) :
    R3.Dat (w.st Z) (colIn w.I Y) hX T Wt :=
  @R3.Dat.mk (w.st Z) (preX w.px Y) (colIn w.I Y) hX T Wt z.Xg z.tr z.core z.alg z.alg_eq z.R z.cG z.geo z.pins
    ⟨z.lev.is, z.lev.C, z.lev.xiH, z.lev.Pg, z.lev.Q, z.lev.beta⟩ z.idG z.good z.mu z.fieldValues_mem_fixedField z.Ks_le


set_option maxHeartbeats 4000000 in
theorem pinned {K : Ctx} (w : ColW B f T) (Y : PreX B.toPre) (h : Pinned K B f T w) : Pinned K B f T (colW w Y) := by
  obtain ⟨p⟩ := h
  exact ⟨⟨p.isTw, p.jets, p.hX, p.above, p.half, p.d3b, p.selectedPlacesAgree, p.vals, p.roots⟩⟩


set_option maxHeartbeats 4000000 in
theorem grpAt (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (h : GrpAt (w.st Z) w.I) : GrpAt (w.st Z) (colIn w.I Y) :=
  ⟨h.pl, h.idem, h.cen⟩


set_option maxHeartbeats 4000000 in
theorem fine (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (h : Fine z) : Fine (w := colW w Y) (Z := Z) (dat w Y Z hX Wt z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h.1 :))
  · exact (by with_unfolding_all exact (h.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.1 :))
  · exact (by with_unfolding_all exact (h.2.2.2 :))


set_option maxHeartbeats 4000000 in
theorem holdsL (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (h : HoldsL z.R z.F) : HoldsL (dat w Y Z hX Wt z).R (dat w Y Z hX Wt z).F := (by with_unfolding_all exact (h :))


set_option maxHeartbeats 4000000 in
theorem nonzeroIndexPlaces_adelicDataResized_eq (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) : (dat w Y Z hX Wt z).W1 (fun _ _ => 0) = z.W1 (fun _ _ => 0) := rfl


set_option maxHeartbeats 4000000 in
theorem seedW {K : Ctx} {P : Pre} {f : Top.Fr P} {F F₀ : IntermediateField ℚ ℂ} {X Y : PreX P} {S : Set ℕ}
    {L : IntermediateField ℚ ℂ} (h : SeedW K P f F F₀ X S L) (hG : X.piG = Y.piG) (hT : X.piT = Y.piT) : SeedW K P f F F₀ Y S L := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  subst a1
  have e : w₀.px = X := eq_of_heq a5
  subst e
  refine ⟨B₀, f₀, T₀, colW w₀ Y, Z₀, hX₀, Wt₀, dat w₀ Y Z₀ hX₀ Wt₀ z₀, rfl, a2, a3, a4, heq_of_eq (preX_eq hG hT),
    pinned w₀ Y a6, a7, grpAt w₀ Y Z₀ a8, fine w₀ Y Z₀ hX₀ Wt₀ z₀ a9, holdsL w₀ Y Z₀ hX₀ Wt₀ z₀ a10, ?_, a12⟩
  intro v hv
  exact a11 v ((nonzeroIndexPlaces_adelicDataResized_eq w₀ Y Z₀ hX₀ Wt₀ z₀).le hv)

theorem finite_norm_eq {R : Ranks} (H : Formalism.BasicNotions.Host R) (n : ℕ) :
    {x : 𝓞 H.E | (x : H.E) * H.conj (x : H.E) = (n : H.E)}.Finite := by
  have hF := NumberField.Embeddings.finite_of_norm_le H.E ℂ (n + 1 : ℝ)
  refine (hF.preimage (f := fun x : 𝓞 H.E => (x : H.E)) RingOfIntegers.coe_injective.injOn).subset ?_
  intro x hx
  refine ⟨x.isIntegral_coe, fun φ => ?_⟩
  have h1 : φ (H.conj (x : H.E)) = starRingEnd ℂ (φ (x : H.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
  have h2 := congrArg φ hx
  rw [map_mul, h1, map_natCast, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖φ (x : H.E)‖ ^ 2 = (n : ℝ) := by exact_mod_cast h2
  have h4 := norm_nonneg (φ (x : H.E))
  show ‖φ (x : H.E)‖ ≤ (n + 1 : ℝ)
  nlinarith

theorem finite_gens (P : Pre) : (Set.range fun X : PreX P => (X.piG, X.piT)).Finite := by
  have h1 := Set.Finite.pi' fun i : Fin 2 => finite_norm_eq P.host (P.host.g i)
  have h2 := Set.Finite.pi' fun u : P.Word => finite_norm_eq P.host (P.T u)
  refine (h1.prod h2).subset ?_
  rintro _ ⟨X, rfl⟩
  exact ⟨fun i => X.piG_norm i, fun u => X.piT_norm u⟩

theorem exists_gens_LLC (B : Base) : ∃ S₂ : Finset ℂ, (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧
    B.LLC ≤ IntermediateField.adjoin ℚ (S₂ : Set ℂ) := by
  classical
  let b := Module.finBasis ℚ B.LL
  refine ⟨Finset.univ.image fun i => B.embLL (b i), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom B.embLL.toRatAlgHom
  · intro z hz
    obtain ⟨x, rfl⟩ := B.mem_LLC.1 hz
    have e : B.embLL x = ∑ i, (b.repr x i) • B.embLL (b i) := by
      conv_lhs => rw [← b.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact map_rat_smul B.embLL _ _
    rw [e]
    refine sum_mem fun i _ => IntermediateField.smul_mem _ (IntermediateField.subset_adjoin _ _ ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)


set_option maxHeartbeats 1000000 in
theorem finite_nonzeroIndexPlaces_referenceTuple (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (hH : HoldsL z.R z.F) : (z.W1 fun _ _ => 0).Finite := by
  have hok := hH.ok.ok2
  have hIw : ∀ j, {w' | (R3.s0Of z.R z.F).Iw j (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0}.Finite :=
    fun j => GlobalTheory.Mem.NonzeroPlacesOverPrimes.idx_finite_of_fg _ _ _ (hH.mLat j).fg
      (Formalism.L2.DIV.BlockDat.Tl_lat hok.conj (hok.lifts j _) hok.irr).fg
  have hjw : ∀ j, {w' | Formalism.DivisionValues.jw (((R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0
      (R3.zsOf z.R z.F)).HT j (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0) w'
      (((R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (R3.zsOf z.R z.F)).Tl j
        (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0) ≠ 0}.Finite :=
    fun j => GlobalTheory.Mem.NonzeroPlacesOverPrimes.jw_finite_of_lat _ (Formalism.L2.DIV.BlockDat.HZ_det hok.conj (hok.lifts j _) hok.irr) _
      (Formalism.L2.DIV.BlockDat.Tl_full hok.conj (hok.lifts j _) hok.irr)
  have hF := Set.finite_iUnion fun j => (hIw j).union (hjw j)
  refine ((hF.preimage (w.st Z).toD7.plEq.injective.injOn).union
    ((hF.preimage GlobalTheory.Mem.NonzeroPlacesOverPrimes.conjPl_injective.injOn).preimage (w.st Z).toD7.plEq.injective.injOn)).subset ?_
  rintro v ⟨j, w', hw', h | h | h⟩
  · rcases hw' with rfl | rfl
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Or.inl h⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Or.inl h⟩)
  · rcases hw' with rfl | rfl
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Or.inr h⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Or.inr h⟩)
  · exact absurd rfl h

theorem seedW_bound {K : Ctx} {P : Pre} {f : Top.Fr P} {F F₀ : IntermediateField ℚ ℂ} {X : PreX P}
    (h : SeedW K P f F F₀ X Set.univ ⊤) : ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧
      SeedW K P f F F₀ X (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -, -⟩ := h
  obtain ⟨S₂, hS₂, hL⟩ := exists_gens_LLC B₀
  have hfin := (finite_nonzeroIndexPlaces_referenceTuple w₀ Z₀ hX₀ Wt₀ z₀ a10).image B₀.places.resChar
  refine ⟨hfin.toFinset, S₂, hS₂, B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun v hv => ?_, hL⟩
  rw [Set.Finite.coe_toFinset]
  exact ⟨v, hv, rfl⟩

end GlobalTheory.Mem.R3.Rw.Resize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharMemF0Primes
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.NonzeroPlacesOverPrimes

theorem resChar_symm_conjPl (D : Formalism.BasicNotions.D7) (v : D.what₂.places.Pl) :
    D.what₂.places.resChar (D.plEq.symm (Formalism.DivisionValues.conjPl (D.plEq v))) = D.what₂.places.resChar v := by
  refine Formalism.MainNotions.Inhab.eq_resChar_of_mem D _ _ (D.what₂.places.resChar_prime v) ?_
  rw [Equiv.apply_symm_apply]
  show _ ∈ Ideal.map _ _
  have h := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.what₂.LL) (Formalism.MainNotions.Inhab.resChar_mem D v)
  rwa [map_natCast] at h

theorem resChar_mem_f0Primes : ∀ (K : Ctx) (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt), ∀ v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K K.s (w.D Z)), B.places.resChar v ∈ GlobalTheory.Mem.NonzeroPlacesOverPrimes.forcedContentSupportPrimes K B.toPre := by
  intro K B f T w Z v hv
  obtain ⟨j, y, hy, hne⟩ := hv
  have key : (w.D Z).what₂.places.resChar ((w.D Z).plEq.symm y) = B.places.resChar v := by
    rcases hy with h | h
    · rw [h]; exact congrArg (w.D Z).what₂.places.resChar ((w.D Z).plEq.symm_apply_apply v)
    · rw [h]; exact resChar_symm_conjPl (w.D Z) v
  unfold F0K FK at hne
  rw [key] at hne
  show B.places.resChar v ∈ ({(w.D Z).host.g 0, (w.D Z).host.g 1, (w.D Z).host.d} ∪
    Finset.range (⌊K.s.X'' (w.D Z).R.n⌋₊ + 1) : Finset ℕ)
  split_ifs at hne with h1 h2 h3
  · obtain ⟨i, hi⟩ := h1
    rw [hi]
    fin_cases i <;> simp
  · refine Finset.mem_union_left _ ?_
    unfold Host.cls primeClass at h2
    split_ifs at h2 with e1 e2 e3 <;> first | simp [e3] | exact absurd h2 (by decide)
  · exact Finset.mem_union_right _ (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h3.2)))
  · exact absurd rfl hne

end GlobalTheory.Mem.NonzeroPlacesOverPrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBelowOfRange
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Untw

theorem exists_below_of_range (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃ v : D.what₂.places.Pl, Below D D' v v' := by
  first
  | exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | exact _root_.GlobalTheory.PrimeBelow.exists_below
  | (apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeBelow.exists_below <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeBelow.exists_below ..)

theorem resChar_of_below {D D' : D7} {v : D.what₂.places.Pl} {v' : D'.what₂.places.Pl} (hB : Below D D' v v') :
    D'.what₂.places.resChar v' = D.what₂.places.resChar v := by
  refine GlobalTheory.LvT.Inh.resChar_eq_of_mem_plEq D' v' (D.what₂.places.resChar_prime v) ((hB _ _ ?_).1 (GlobalTheory.LvT.Inh.resChar_mem_plEq D v))
  simp only [map_natCast]

end GlobalTheory.Mem.R3.Rw.Untw

namespace GlobalTheory.Mem.R3.Rw

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformNormalisedAdelicSeeds
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformNormalisedAdelicSeeds
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Resize

theorem seeds_uniform_exists : ∀ (K : Ctx) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P) (F : IntermediateField ℚ ℂ),
    ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ px : PreX P,
      (∃ F₀, SeedW K P f F F₀ px Set.univ ⊤) →
        ∃ F₀, SeedW K P f F F₀ px (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  classical
  intro K P f F
  have key : ∀ c : (Fin 2 → 𝓞 P.host.E) × (P.Word → 𝓞 P.host.E), ∃ (S : Finset ℕ) (S₂ : Finset ℂ),
      (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ Y : PreX P, (Y.piG, Y.piT) = c → (∃ F₀, SeedW K P f F F₀ Y Set.univ ⊤) →
        ∃ F₀, SeedW K P f F F₀ Y (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
    intro c
    by_cases hc : ∃ (X : PreX P) (F₀ : IntermediateField ℚ ℂ), (X.piG, X.piT) = c ∧ SeedW K P f F F₀ X Set.univ ⊤
    · obtain ⟨X, F₀, hX, hs⟩ := hc
      obtain ⟨S, S₂, hS₂, hb⟩ := seedW_bound hs
      refine ⟨S, S₂, hS₂, fun Y hY _ => ⟨F₀, ?_⟩⟩
      have e := hX.trans hY.symm
      exact seedW hb (congrArg Prod.fst e) (congrArg Prod.snd e)
    · exact ⟨∅, ∅, by simp, fun Y hY ⟨F₀, hs⟩ => absurd ⟨Y, F₀, hY, hs⟩ hc⟩
  choose S S₂ hS₂ hS using key
  have hfin := finite_gens P
  refine ⟨hfin.toFinset.biUnion S, hfin.toFinset.biUnion S₂, ?_, fun Y hs => ?_⟩
  · intro z hz
    obtain ⟨c, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS₂ c z hz
  · have hm : (Y.piG, Y.piT) ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨Y, rfl⟩
    obtain ⟨F₀, h⟩ := hS _ Y rfl hs
    refine ⟨F₀, h.mono ?_ (IntermediateField.adjoin.mono _ _ _ ?_)⟩
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)
    · intro p hp
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨_, hm, hp⟩)

end GlobalTheory.Mem.R3.Rw.Resize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformNormalisedAdelicSeedsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniform_normalisedAdelicSeeds : ∀ (K : Ctx) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P) (F : IntermediateField ℚ ℂ), ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ px : PreX P, (∃ F₀, SeedW K P f F F₀ px Set.univ ⊤) → ∃ F₀, SeedW K P f F F₀ px (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.Resize.seeds_uniform_exists | exact GlobalTheory.Mem.R3.Rw.Resize.seeds_uniform_exists | (intros; apply GlobalTheory.Mem.R3.Rw.Resize.seeds_uniform_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharEqOfOverOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.SatForced

theorem resChar_eq_of_overOne (D : D7) {v v' : D.what₂.places.Pl} (h : GlobalTheory.TwistChoice.OverOne D v v') :
    D.what₂.places.resChar v = D.what₂.places.resChar v' := by
  have hp := D.what₂.places.resChar_prime v
  have h1 := GlobalTheory.TwistChoice.val_resChar_pos D v
  have h2 := (h ((D.what₂.places.resChar v : ℕ) : 𝓞 ↥D.LL0)).1 (by simpa using h1)
  exact GlobalTheory.TwistChoice.eq_resChar_of_pos D v' hp (by simpa using h2)

theorem mem_W1F_of_overOne : ∀ (K : Ctx) (D : D7) (v v' : D.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D v v' →
    v ∈ placesWithNonzeroContentOrConj D (F0K K.s D) → v' ∈ placesWithNonzeroContentOrConj D (F0K K.s D) := by
  intro K D v v' h hv
  obtain ⟨j, y, hy, hne⟩ := hv
  have key : D.what₂.places.resChar (D.plEq.symm y) = D.what₂.places.resChar v := by
    rcases hy with e | e
    · rw [e, Equiv.symm_apply_apply]
    · rw [e]; exact GlobalTheory.Mem.NonzeroPlacesOverPrimes.resChar_symm_conjPl D v
  refine ⟨j, D.plEq v', Or.inl rfl, ?_⟩
  have e2 : F0K K.s D (D.plEq v') j = F0K K.s D y j := by
    unfold F0K
    rw [key, Equiv.symm_apply_apply, resChar_eq_of_overOne D h]
  rw [e2]; exact hne

end GlobalTheory.Mem.SatForced
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverFixedFieldSameCoefficientPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverFixedFieldSameCoefficientPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.Top.Bl

theorem below_of_overOne : ∀ (D D' : D7), (∀ x : D.what₂.LL, ∃ y ∈ D'.LL0, D'.what₂.embLL y = D.what₂.embLL x) → ∀ (v : D.what₂.places.Pl) (v₁ v₂ : D'.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D' v₁ v₂ → Below D D' v v₁ → Below D D' v v₂ := by
  intro D D' hsub v v₁ v₂ h12 hb x x' hxx'
  rw [hb x x' hxx']
  obtain ⟨y, hy, hye⟩ := hsub (x : D.what₂.LL)
  have hyx : y = (x' : D'.what₂.LL) := D'.what₂.embLL.injective (hye.trans hxx')
  have hint : IsIntegral ℤ (⟨(x' : D'.what₂.LL), hyx ▸ hy⟩ : ↥D'.LL0) :=
    (isIntegral_algebraMap_iff ).1 (RingOfIntegers.isIntegral_coe x')
  let z : 𝓞 ↥D'.LL0 := ⟨⟨(x' : D'.what₂.LL), hyx ▸ hy⟩, hint⟩
  have hz : algebraMap (𝓞 ↥D'.LL0) (𝓞 D'.what₂.LL) z = x' := by
    apply RingOfIntegers.ext
    rfl
  rw [← hz, ← GlobalTheory.TwistChoice.val_pos_iff_mem, ← GlobalTheory.TwistChoice.val_pos_iff_mem]
  exact h12 z

end GlobalTheory.Mem.Top.Bl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverFixedFieldSameCoefficientPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placesOverFixedField_same_coefficient_place : ∀ (D D' : D7), (∀ x : D.what₂.LL, ∃ y ∈ D'.LL0, D'.what₂.embLL y = D.what₂.embLL x) → ∀ (v : D.what₂.places.Pl) (v₁ v₂ : D'.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D' v₁ v₂ → Below D D' v v₁ → Below D D' v v₂ := by
  first | exact @GlobalTheory.Mem.Top.Bl.below_of_overOne | exact GlobalTheory.Mem.Top.Bl.below_of_overOne | (intros; apply GlobalTheory.Mem.Top.Bl.below_of_overOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedAdelicDataSaturatedOverFixedField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.UntwSat

theorem stepW_seed_fixed : StepW Pinned fun K B f T _ =>
    (↑(NonzeroPlacesOverPrimes.forcedContentSupportPrimes K B.toPre) : Set ℕ) ⊆ ↑T.pl ∧ ∀ px : PreX B.toPre,
      (∃ F₀, SeedW K B.toPre f B.KsC F₀ px Set.univ ⊤) → ∃ F₀, SeedW K B.toPre f B.KsC F₀ px ↑T.pl B.fixedCoefficientFieldInComplex := by
  refine evG_all fun K => ?_
  choose S S₁ hS using GlobalTheory.T.exists_uniform_normalisedAdelicSeeds K
  refine ⟨fun P f F => S₁ P f F, fun P f F _ => S P f F ∪ NonzeroPlacesOverPrimes.forcedContentSupportPrimes K P, fun _ _ _ _ _ => ∅,
    fun _ _ _ _ _ => ∅, fun P f F => (hS P f F).1, by simp, ?_⟩
  intro B f T _ hHas hP _ _ _ _ w _
  refine ⟨fun p hp => hP (Finset.mem_union_right _ hp), fun px hs => ?_⟩
  obtain ⟨F₀, h⟩ := (hS _ _ _).2 px hs
  refine ⟨F₀, h.mono ?_ ?_⟩
  · intro p hp
    exact hP (Finset.mem_union_left _ hp)
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact hHas.1 z hz

theorem isBaseEnlargementFixedCoefField_of_same_fields {B₀ B : Base} (hP : B₀.toPre = B.toPre) (hKs : B₀.KsC = B.KsC) (hLL : B₀.LLC ≤ B.fixedCoefficientFieldInComplex) : Enl0 B₀ B := by
  refine ⟨hP.symm, ?_, ?_, ?_⟩
  · have := congrArg (fun F : IntermediateField ℚ ℂ => (F : Set ℂ)) hKs
    simp only [Base.KsC, IntermediateField.coe_map] at this
    exact this.symm
  · rintro _ ⟨x, -, rfl⟩
    exact (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  · rintro _ ⟨x, rfl⟩
    exact (B.mem_LLC).1 (B.fixedField_le_coefficientField (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩)))

theorem dat_saturated_of_untw : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 →
    StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok)
      (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧
        DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧
        (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧
        ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  intro hG hDS hHL hDE
  have hP : StepW Pinned Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have hHLw : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
      HoldsL z.R z.F := hHL
  refine (((((hP.and hDS).and hHLw).and hDE).and GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep).and stepW_seed_fixed).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨⟨⟨⟨⟨pin⟩, hDS'⟩, hHL'⟩, hDE'⟩, G, hG2⟩, hf0, hsd⟩ := H
  intro hT
  obtain ⟨Z, rfl, hGT, hGA, hKap⟩ := exists_lt_grpTrue hG w hO pin.hX G
  have hVol := (hG2 Z.W Z.V Z.S Z.N).1
  obtain ⟨z₁, hF₁⟩ := hDS' Z pin.hX hGT hGA hVol
  have hL₁ := hHL' Z pin.hX _ z₁ hGT hGA hF₁.1 hF₁.2.1
  have hs : SeedW K B.toPre f B.KsC B.fixedCoefficientFieldInComplex w.px Set.univ ⊤ :=
    ⟨B, f, T, w, Z, pin.hX, _, z₁, rfl, HEq.rfl, rfl, rfl, HEq.rfl, ⟨pin⟩, hGT, hGA, hF₁, hL₁, fun _ _ => trivial, le_top⟩
  obtain ⟨F₀, B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, hB₀, hf₀, hKs, -, hpx, hpin₀, hGT₀, hGA₀, hFine₀, hHL₀, hW₀, hLL⟩ :=
    hsd w.px ⟨_, hs⟩
  have hE : Enl0 B₀ B := isBaseEnlargementFixedCoefField_of_same_fields hB₀ hKs hLL
  obtain ⟨z', hFine', hExt⟩ := hDE' B₀ f₀ T₀ w₀ hE hf₀.symm hpin₀ hpx.symm Z₀ hX₀ Wt₀ z₀ hGT₀ hGA₀ hFine₀ hHL₀ Z pin.hX hGT hGA hVol
  have hsub : ∀ x : (w₀.D Z₀).what₂.LL, ∃ y ∈ (w.D Z).LL0, (w.D Z).what₂.embLL y = (w₀.D Z₀).what₂.embLL x :=
    fun x => (B.mem_LL0C).1 (hLL ((B₀.mem_LLC).2 ⟨x, rfl⟩))
  refine ⟨Z, pin.hX, z', hG2, hGT, hGA, hKap, hFine', ?_, ?_, ?_⟩
  · intro v' hv'
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').1 hv' with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v'
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v' hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').2 (Or.inl h))
      have hr : B.places.resChar v' = B₀.places.resChar v := Untw.resChar_of_below hB
      have hm : B₀.places.resChar v ∈ (T.pl : Set ℕ) := hW₀ v hv
      rw [hr]
      exact hm
    · exact hf0 (NonzeroPlacesOverPrimes.resChar_mem_f0Primes K B f T w Z v' h)
  · intro v _
    have e := congrArg (fun T' : TwDat B => T'.psi v) hT
    exact e.trans rfl
  · intro v₁ v₂ hov hv₁
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).1 hv₁ with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v₁
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v₁ hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₁).2 (Or.inl h))
      have hB₂ := GlobalTheory.T.placesOverFixedField_same_coefficient_place (w₀.D Z₀) (w.D Z) hsub v v₁ v₂ hov hB
      have hv₂ := (hExt.W1 v v₂ hB₂).1 hv
      rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).1 hv₂ with h₂ | h₂
      · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inl h₂)
      · obtain ⟨j, y, -, hne⟩ := h₂
        exact absurd rfl hne
    · exact (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v₂).2 (Or.inr (GlobalTheory.Mem.SatForced.mem_W1F_of_overOne K (w.D Z) v₁ v₂ hov h))

end GlobalTheory.Mem.R3.Rw.UntwSat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedAdelicDataSaturatedOverFixedFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untwisted_adelic_data_saturated_over_fixed_field : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt0 → StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → ∃ (Z : w.Lt) (hX : B.fields.Ok) (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) ∧ Fine z ∧ (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) ∧ (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) ∧ ∀ v v', GlobalTheory.TwistChoice.OverOne (w.D Z) v v' → v ∈ z.W1 (F0K K.s (w.D Z)) → v' ∈ z.W1 (F0K K.s (w.D Z)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | exact GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw | (intros; apply GlobalTheory.Mem.R3.Rw.UntwSat.dat_saturated_of_untw <;> assumption)
end
