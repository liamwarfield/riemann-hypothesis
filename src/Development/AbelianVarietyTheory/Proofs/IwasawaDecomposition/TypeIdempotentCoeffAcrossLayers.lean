module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaOfOfIsCharLab
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlaceParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZOfCoeffMem
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepMemCyclotomicAdjoin
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepMemCyclotomicAdjoin
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem trace_mem_adjoin_of_pow_eq_one (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (N : ℕ) (hN : 0 < N) (hf : f ^ N = 1) :
    LinearMap.trace ℂ V f ∈
      IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine multiset_sum_mem _ ?_
  intro μ hμ
  have hroot : f.charpoly.IsRoot μ := (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hroot).exists_hasEigenvector
  have h1 := hv.pow_apply N
  rw [hf] at h1
  have h2 : μ ^ N = 1 := by
    have h3 : (μ ^ N - 1) • v = 0 := by
      rw [sub_smul, ← h1]; simp
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv.2
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp N hN.ne').eq_pow_of_pow_eq_one h2
  rw [← hi]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ _) i

theorem isChar_mem_adjoin_exp :
    ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ →
      ∀ x, χ x ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  intro G _ _ χ N hN hd hχ x
  obtain ⟨V, hV⟩ := hχ
  rw [← hV x]
  refine trace_mem_adjoin_of_pow_eq_one V (V.ρ x) N hN ?_
  obtain ⟨k, rfl⟩ := hd
  rw [← map_pow, pow_mul, pow_card_eq_one', one_pow, map_one]

end GlobalTheory.GLm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepMemCyclotomicAdjoinStatement
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOfFDRep_mem_cyclotomic_adjoin : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ → ∀ x, χ x ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  first | exact @GlobalTheory.GLm.isChar_mem_adjoin_exp | exact GlobalTheory.GLm.isChar_mem_adjoin_exp | (intros; apply GlobalTheory.GLm.isChar_mem_adjoin_exp <;> assumption)
end
end

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem zOf_coeff_mem {G : Type} [Group G] [Fintype G] (K : IntermediateField ℚ ℂ) (χ : G → ℂ)
    (h : ∀ x, χ x ∈ K) (y : G) : (zOf χ).coeff y ∈ K := by
  unfold zOf
  refine Finset.sum_induction _ (fun a : MonoidAlgebra ℂ G => a.coeff y ∈ K) ?_ ?_ ?_
  · intro a b ha hb
    have := K.add_mem ha hb
    simpa using this
  · simp
  · intro x _
    have h1 : χ 1 / (Fintype.card G : ℂ) * χ x⁻¹ ∈ K :=
      K.mul_mem (K.div_mem (h 1) (natCast_mem K _)) (h _)
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs
    · exact h1
    · exact K.zero_mem

theorem isSer_eSerC (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (hg : 5 ≤ g) (hG : Green) (r N : ℕ) (hN : 0 < N)
    (hd : Nat.card (GL (Fin r) (ZMod g)) ∣ N) : GlobalTheory.MemN.IsSer r g N (eSerC L r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws g L hg hG r
  refine ⟨h1, h2, h3, ?_, h5, ?_⟩
  · intro f
    refine ⟨fun h0 hf => GlobalTheory.T.harishChandraSeriesCentralIdempotent_ne_zero g L hG r f hf.1 hf.2.1 hf.2.2 h0, h4 f⟩
  · intro f x
    unfold eSerC
    refine finsum_mem_induction (fun a : MonoidAlgebra ℂ (Gn g r) => a.coeff x ∈
      IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))}) ?_ ?_ ?_
    · simp
    · intro a b ha hb
      have := add_mem ha hb
      simpa using this
    · intro χ hχ
      obtain ⟨⟨V, _, hV⟩, _⟩ := hχ
      exact zOf_coeff_mem _ χ (GlobalTheory.T.isCharacterOfFDRep_mem_cyclotomic_adjoin (Gn g r) χ N hN hd ⟨V, hV⟩) x

end GlobalTheory.GLm
end

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.Mem.TypePl NumberField IsDedekindDomain Polynomial

section Types

variable {R : Ranks} {H : Host R}

local instance factType (H : Host R) (k : Fin 2) : Fact (H.g k).Prime := ⟨H.g_prime k⟩

def omLab (W : Omg H) (k : Fin 2) : (ZMod (H.g k))ˣ := charLab (labDat (H.g k)) (W.om k)

theorem orderOf_omLab (W : Omg H) (k : Fin 2) : orderOf (omLab W k) = H.g k - 1 := orderOf_charLab _ (W.gen k)

theorem isCharLab_omLab (W : Omg H) (k : Fin 2) : IsCharLab (labDat (H.g k)) (W.om k) (omLab W k) :=
  isCharLab_charLab _ _

structure TypesTrue {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : NTypes A) (P : PiBar H) (W : Omg H) : Prop where
  pl : ∀ k v, P.Div k (A.plGw k v)
  teich : ∀ k, T.teichC k = (labDat (H.g k)).teich
  chi : ∀ k v j, N.chiT k v j = omLab W k ^ (2 * (j.1 + 1))
  ser : ∀ k p, T.eSer k p = eSerC (labDat (H.g k)) R.r p

variable {what₂ rows' : Rows.Data R} {N : NData R H what₂} {N' : NData R H rows'}

def plF (A : NAut N) (k : Fin 2) : N.PlG k ≃ placesOver H.F (H.g k) :=
  Equiv.ofBijective _ (below_bijective (H.g_prime k) (N.g_split k) (N.card_PlG k) (A.plGw k) (A.plGw_over k)
    (A.plGw_inj k) (A.plGw_nconj k))

theorem plF_apply (A : NAut N) (k : Fin 2) (v : N.PlG k) :
    (plF A k v : HeightOneSpectrum (𝓞 H.F)) = (A.plGw k v).under (𝓞 H.F) := rfl

def plEquiv (A : NAut N) (A' : NAut N') (k : Fin 2) : N.PlG k ≃ N'.PlG k := (plF A k).trans (plF A' k).symm

def grpEquiv (A : NAut N) (A' : NAut N') : G0g N ≃* G0g N' where
  toFun g kv := g ⟨kv.1, (plEquiv A A' kv.1).symm kv.2⟩
  invFun g kv := g ⟨kv.1, plEquiv A A' kv.1 kv.2⟩
  left_inv g := funext fun kv => by
    show g ⟨kv.1, (plEquiv A A' kv.1).symm (plEquiv A A' kv.1 kv.2)⟩ = g ⟨kv.1, kv.2⟩
    rw [Equiv.symm_apply_apply]
  right_inv g := funext fun kv => by
    show g ⟨kv.1, plEquiv A A' kv.1 ((plEquiv A A' kv.1).symm kv.2)⟩ = g ⟨kv.1, kv.2⟩
    rw [Equiv.apply_symm_apply]
  map_mul' _ _ := rfl

theorem grpEquiv_apply (A : NAut N) (A' : NAut N') (g : G0g N) (k : Fin 2) (v : N'.PlG k) :
    grpEquiv A A' g ⟨k, v⟩ = g ⟨k, (plEquiv A A' k).symm v⟩ := rfl

theorem grpEquiv_apply' (A : NAut N) (A' : NAut N') (g : G0g N) (k : Fin 2) (v : N.PlG k) :
    grpEquiv A A' g ⟨k, plEquiv A A' k v⟩ = g ⟨k, v⟩ := by
  rw [grpEquiv_apply, Equiv.symm_apply_apply]

namespace TypesTrue

variable {A : NAut N} {A' : NAut N'} {T : NTypes A} {T' : NTypes A'} {P : PiBar H} {W : Omg H}

theorem plGw_eq (h : TypesTrue T P W) (k : Fin 2) (v : N.PlG k) :
    A.plGw k v = above P (N.g_split k) (plF A k v) :=
  (existsUnique_div P (N.g_split k) (plF A k v)).unique ⟨h.pl k v, rfl⟩ ⟨above_div _ _ _, above_under _ _ _⟩

theorem plGw_plEquiv (h : TypesTrue T P W) (h' : TypesTrue T' P W) (k : Fin 2) (v : N.PlG k) :
    A'.plGw k (plEquiv A A' k v) = A.plGw k v := by
  rw [h'.plGw_eq, h.plGw_eq, plEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem isCharLab (h : TypesTrue T P W) (k : Fin 2) (v : N.PlG k) (j : Fin R.m) :
    IsCharLab (labDat (H.g k)) (W.om k ^ (2 * (j.1 + 1))) (N.chiT k v j) := by
  rw [h.chi]
  exact isCharLab_pow _ _ _

theorem chiT_gen (h : TypesTrue T P W) (k : Fin 2) (v : N.PlG k) :
    ∃ w : (ZMod (H.g k))ˣ, orderOf w = H.g k - 1 ∧ ∀ j : Fin R.m, N.chiT k v j = w ^ (2 * (j.1 + 1)) :=
  ⟨omLab W k, orderOf_omLab W k, h.chi k v⟩

theorem goodTuple_comp (h : TypesTrue T P W) (h' : TypesTrue T' P W) (e : ∀ k, N.PlG k ≃ N'.PlG k)
    {f : ∀ k, N'.PlG k → (ZMod (H.g k))[X]} (hf : T'.goodTuple f) : T.goodTuple fun k v => f k (e k v) := by
  intro k
  have e1 : N.chiT k = fun v => N'.chiT k (e k v) := by
    funext v j
    rw [h.chi, h'.chi]
  have h1 := TypesInhab.isGood_comp (e k) (hf k).1
  have h2 := TypesInhab.isGood_comp (e k) (hf k).2
  rw [e1]
  exact ⟨h1, h2⟩

theorem goodTuple_iff (h : TypesTrue T P W) (h' : TypesTrue T' P W) (e : ∀ k, N.PlG k ≃ N'.PlG k)
    (f : ∀ k, N'.PlG k → (ZMod (H.g k))[X]) : (T.goodTuple fun k v => f k (e k v)) ↔ T'.goodTuple f :=
  ⟨fun hf => by simpa using h'.goodTuple_comp h (fun k => (e k).symm) hf, h.goodTuple_comp h' e⟩

theorem typeIdempotent_coeff_across_layers (h : TypesTrue T P W) (h' : TypesTrue T' P W) (g : G0g N) :
    T'.e0.coeff (grpEquiv A A' g) = T.e0.coeff g := by
  classical
  let e := plEquiv A A'
  let E : (∀ kv : (Σ k : Fin 2, N'.PlG k), (Fin R.r → ZMod (H.g kv.1))) ≃
      (∀ kv : (Σ k : Fin 2, N.PlG k), (Fin R.r → ZMod (H.g kv.1))) :=
    { toFun := fun a kv => a ⟨kv.1, e kv.1 kv.2⟩
      invFun := fun a kv => a ⟨kv.1, (e kv.1).symm kv.2⟩
      left_inv := fun a => funext fun kv => by
        show a ⟨kv.1, e kv.1 ((e kv.1).symm kv.2)⟩ = a ⟨kv.1, kv.2⟩
        rw [Equiv.apply_symm_apply]
      right_inv := fun a => funext fun kv => by
        show a ⟨kv.1, (e kv.1).symm (e kv.1 kv.2)⟩ = a ⟨kv.1, kv.2⟩
        rw [Equiv.symm_apply_apply] }
  simp only [NTypes.e0, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
  rw [← finsum_comp_equiv E]
  refine finsum_congr fun a => ?_
  refine if_congr (h.goodTuple_iff h' e fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)).symm ?_ rfl
  symm
  refine Fintype.prod_equiv (Equiv.sigmaCongrRight e) _ _ fun kv => ?_
  rw [h.ser, h'.ser]
  exact congrArg _ (grpEquiv_apply' A A' g kv.1 kv.2).symm

end TypesTrue

end Types

section Build

variable {R : Ranks} {H : Host R} {what₂ rows' : Rows.Data R} {N : NData R H what₂} {N' : NData R H rows'}
  {A : NAut N} {A' : NAut N'}

attribute [local instance] factType

theorem five_le_type (H : Host R) {k : Fin 2} (hc : H.g k % (H.QS * H.q * H.d) = 1) : 5 ≤ H.g k := by
  have h2 := (H.g_prime k).two_le
  have h4 : H.g k % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd (H.g k) (show 4 ∣ H.QS * H.q * H.d from ((((pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans H.tower_dvd).mul_right _).mul_right _)), hc]
  omega


set_option synthInstance.maxHeartbeats 400000 in
def retype [IsEmpty N.Loc] (T : NTypes A) (hl : ∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p)
    (hi : ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p) (L : ∀ k, LabelDatum (H.g k))
    (ω : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] ℂ) : NTypes A :=
  { T with
    teichC := fun k => (L k).teich
    teichC_inj := fun k => (L k).teich_inj
    inertiaCharpoly_type := fun k v p _ => by
      rw [hi, hl, GaloisStage.rootsBar_unip, Multiset.map_replicate, Multiset.prod_replicate, map_one, C_1]
    chiT_tg := fun i => isEmptyElim i
    cenAmb := fun _ => (Algebra.ofId ℂ _).comp ω
    cenMt := fun _ _ => (Algebra.ofId ℂ _).comp ω }

end Build

section PiLocalization₂

attribute [local instance] factType

def GrpTrue {B : Base} {C : Cols B} {W : RowsRest B C} (N : NStage B C W) (f : Fr B.toPre) : Prop :=
  TypesTrue N.ntypes f.P f.W

namespace GrpTrue

variable {B : Base} {C C' : Cols B} {W : RowsRest B C} {W' : RowsRest B C'} {N : NStage B C W} {N' : NStage B C' W'}
  {f : Fr B.toPre}

theorem typeIdempotent_coeff_across_layers (h : GrpTrue N f) (h' : GrpTrue N' f) (g : G0g N.nd) :
    N'.ntypes.e0.coeff (grpEquiv N.naut N'.naut g) = N.ntypes.e0.coeff g :=
  TypesTrue.typeIdempotent_coeff_across_layers h h' g

theorem eSerTie (h : GrpTrue N f) (V : DivStage B C W) (S : SStage B C W) (G : GJStage B C) :
    ESerTie (assemble B C W V S N G) :=
  fun k => ⟨labDat (B.host.g k), (h.teich k).symm, h.ser k⟩

end GrpTrue

def trueLayer (B : Base) (C : Cols B) (W : RowsRest B C) (Om : Omg B.host)
    (ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E (AlgebraicClosure B.host.E) p)
    (h : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → W.shaLen p e = (n : ℚ)) : NData B.R B.host W.what₂ :=
  let nd := emptyLayer B C W (fun k _ j => omLab Om k ^ (2 * (j.1 + 1))) ldat h
  have hc : ∀ k, Nat.card (placesOver B.host.F (B.host.g k)) = B.R.f :=
    fun k => card_placesOver (B.host.g_prime k) (nd.g_split k)
  { nd with
    PlG := fun k => placesOver B.host.F (B.host.g k)
    finPlG := fun k => Nat.card_pos_iff.1 ((hc k).symm ▸ GaloisStage.f_pos B.R) |>.2 |> @Fintype.ofFinite _
    card_PlG := fun k => (@Nat.card_eq_fintype_card _ (_)).symm.trans (hc k)
    lab := fun _ _ _ => (X - 1) ^ B.R.r
    lab_monic := fun _ _ _ => GaloisStage.monic_unip _
    chiT := fun k _ j => omLab Om k ^ (2 * (j.1 + 1)) }

theorem exists_nStage_grpTrue (hG : GlobalTheory.Published.GreenCuspidal) (B : Base) (C : Cols B) (W : RowsRest B C)
    (hsha : ShaOK B.toPre W.shaLen) (heta : ∀ j w, 1 ≤ j → j ≤ B.R.m → W.etaJ j w = 0) (hOp : ∀ μ, W.eOp μ = 0)
    (hMt : ∀ μ j, W.eMt μ j = 0) (f : Fr B.toPre) :
    ∃ N : NStage B C W, IsEmpty N.nd.Loc ∧ IsEmpty N.ntw.Tw ∧ GrpTrue N f ∧
      (N.nd.PlG = fun k => ↥(placesOver B.host.F (B.host.g k))) ∧
      ∃ ω : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N.nd)) →ₐ[ℂ] ℂ,
        (∀ μ z, N.ntypes.cenAmb μ z = algebraMap ℂ _ (ω z)) ∧ ∀ μ j z, N.ntypes.cenMt μ j z = algebraMap ℂ _ (ω z) := by
  obtain ⟨ldat, hsha⟩ := hsha
  obtain ⟨L⟩ := locStage_inhabited
  let nd := trueLayer B C W f.W ldat hsha
  have hE : IsEmpty nd.Loc := ⟨Empty.elim⟩
  let A : NAut nd := GaloisStage.nAut nd (fun k v => above f.P (nd.g_split k) v)
    (fun k v => div_over f.P (above_div _ _ v)) (fun k => above_injective f.P (nd.g_split k))
    (fun k v v' => not_isConjPl f.P (nd.g_split k) (above_div _ _ v) (above_div _ _ v'))
  have hl : ∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  have hi : ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  choose tg htg using fun (k : Fin 2) (v : nd.PlG k) =>
    GlobalTheory.TameInertiaGen.exists_tameGenAt B.host.E nd.Om (A.plGw k v) (nd.plOm.1 (A.plGw k v)) (nd.plOm.2 _)
  have he : ∀ k, IsSer B.R.r (B.host.g k) B.toPre.restRowsFiniteGroupCard (eSerC (labDat (B.host.g k)) B.R.r) := fun k =>
    GlobalTheory.GLm.isSer_eSerC _ _ (five_le_type B.host (B.g_cond k)) hG _ _ B.toPre.restRowsFiniteGroupCard_pos
      ((dvd_pow_self _ (GaloisStage.f_pos B.R).ne').trans
        (Finset.dvd_prod_of_mem (fun k : Fin 2 => (Nat.card (GL (Fin B.R.r) (ZMod (B.host.g k)))) ^ B.R.f)
          (Finset.mem_univ k)))
  obtain ⟨T₀, hT₀⟩ : ∃ T : NTypes A, T.eSer = fun k => eSerC (labDat (B.host.g k)) B.R.r :=
    ⟨TypesInhab.types0 hl hi B.g_cond B.BB_disj tg htg _ he, rfl⟩
  have he₀ : ∀ k, IsSer B.R.r (B.host.g k) B.toPre.restRowsFiniteGroupCard (T₀.eSer k) := fun k => by rw [hT₀]; exact he k
  obtain ⟨hc, hm⟩ := TypesInhab.goodTupleIdempotent_central_and_action T₀ fun k p hp h0 => ((he₀ k).zero p).1 h0 hp
  obtain ⟨t, ht, -, ht0⟩ := hm (fun _ _ => (X - 1) ^ B.R.r) fun k _ =>
    ⟨(GaloisStage.monic_unip _).1, (GaloisStage.monic_unip _).2, GaloisStage.unip_coeff_zero _ _⟩
  obtain ⟨ω, h0⟩ := TypesInhab.exists_char ⟨T₀.e0, hc⟩ ht (ht0 (TypesInhab.not_good_unip T₀))
  let T : NTypes A := retype T₀ hl hi (fun k => labDat (B.host.g k)) ω
  have hTe : T.e0 = T₀.e0 := rfl
  have htie : T.IdempotentMatchesAction := by
    refine ⟨fun μ => ?_, fun μ j => ?_⟩
    · rw [hTe, NTypes.onAmb, dite_eq_left hc]
      change W.eOp μ = algebraMap ℂ _ (ω _)
      rw [h0, map_zero, hOp]
    · rw [hTe, NTypes.onMt, dite_eq_left hc]
      change W.eMt μ j = algebraMap ℂ _ (ω _)
      rw [h0, map_zero, hMt]
  have hy : ∀ x, ∃ y : ↥B.LL0, B.embLL (y : B.LL) = T.e0.coeff x := fun x => by
    obtain ⟨y, hy, hy'⟩ := TypesInhab.goodTupleIdempotent_coeff_mem_subring T₀ _
      (fun k p x => TypesInhab.adjoin_le B _ ((he₀ k).rat p x)) x
    exact ⟨⟨y, hy⟩, hy'⟩
  choose e hee using hy
  let tw := GaloisStage.nTw B.LL0 nd
  have hT : IsEmpty tw.Tw := ⟨Empty.elim⟩
  obtain ⟨Y, hY, ⟨th⟩⟩ := exists_nexp_nth_of_isEmpty B C W nd tw hT e
  exact ⟨{
    toLocStage := L
    nd := nd
    ntw := tw
    naut := A
    nbc := GaloisStage.nBC A
    nexp := Y
    ntypes := T
    nStage_trivialCharacter_compat := htie
    nStage_trivialCharacter_coeff_eq := fun g => by rw [hY]; exact hee g
    nth := th
    nbr := fun i => hE.elim i
    nbr_ind := fun i => hE.elim i
    self_good := fun i => hE.elim i
    ntwbr := fun i => hT.elim i
    ntwbr_ind := fun i => hT.elim i
    loc_tie := fun i => hE.elim i
    bc_tie := fun i => hE.elim i
    rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i
    Z_tie := fun i => hE.elim i
    Zgood_tie := fun i => hE.elim i
    etaJ_tie := fun j w h1 h2 => (heta j w h1 h2).trans (Finset.sum_eq_zero fun i _ => hE.elim i).symm },
    hE, hT, ⟨fun k v => above_div f.P (nd.g_split k) v, fun _ => rfl, fun _ _ _ => rfl,
      fun k p => congrFun (congrFun hT₀ k) p⟩, rfl, ω, fun _ _ => rfl, fun _ _ _ => rfl⟩

end PiLocalization₂

end GlobalTheory.Mem.Top

end
