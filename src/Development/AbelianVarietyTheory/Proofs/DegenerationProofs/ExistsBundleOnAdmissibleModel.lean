module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NsmulEqZeroOfCast
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSpanRowsOfForallValuationRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem mem_span_rows_iff_vecMul_inv {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {c : Matrix J J Ω} (hc : c.det ≠ 0) (v : J → Ω) :
    v ∈ Submodule.span S (Set.range c) ↔ ∀ j, Matrix.vecMul v c⁻¹ j ∈ S := by
  have hu : IsUnit c.det := isUnit_iff_ne_zero.2 hc
  have key : ∀ a : J → S, ∑ i, a i • c i = Matrix.vecMul (fun i => (a i : Ω)) c := fun a => by
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun S (v := fun i => c i)).trans ?_
  constructor
  · rintro ⟨a, rfl⟩ j
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    exact (a j).2
  · intro h
    refine ⟨fun j => ⟨_, h j⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul v c⁻¹) c = v
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
  {J : Type} [Fintype J] [DecidableEq J]

theorem mem_span_rows_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {c : Matrix J J Ω} (hc : c.det ≠ 0) (x : M.Z) (v : J → Ω)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) → v ∈ Submodule.span (M.O ξ) (Set.range c)) :
    v ∈ Submodule.span (M.O x) (Set.range c) :=
  (mem_span_rows_iff_vecMul_inv _ hc v).2 fun j => M.mem_O_of_forall_valuationRing hn x _ fun ξ hξ hv =>
    (mem_span_rows_iff_vecMul_inv _ hc v).1 (h ξ hξ hv) j

theorem span_rows_eq_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {b c : Matrix J J Ω} (hb : b.det ≠ 0) (hc : c.det ≠ 0) (x : M.Z)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range b) = Submodule.span (M.O ξ) (Set.range c)) :
    Submodule.span (M.O x) (Set.range b) = Submodule.span (M.O x) (Set.range c) :=
  le_antisymm
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hc x v fun ξ hξ hr =>
      (h ξ hξ hr).le (Submodule.subset_span hv))
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hb x v fun ξ hξ hr =>
      (h ξ hξ hr).ge (Submodule.subset_span hv))

end RatModel

theorem exists_lat_of_height_le_one :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
      [JacobsonSpace M.Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (J : Type) [Fintype J] [DecidableEq J]
      (b : M.Z → Matrix J J Ω) (D : ∀ ξ : M.Z, Submodule (M.O ξ) (J → Ω)), (∀ z, (b z).det ≠ 0) →
      (∀ z, IsClosed ({z} : Set M.Z) → ∃ W : M.Z.Opens, z ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
        Submodule.span (M.O ξ) (Set.range (b z)) = D ξ) →
      ∃ EE : M.Lat J, (∀ z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) (Set.range (b z))) ∧
        ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
          (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
          ∀ x ∈ W, EE.E x = Submodule.span (M.O x) (Set.range c) := by
  intro o Ω _ _ _ M _ _ hn J _ _ b D hb h
  have hx : ∀ x : M.Z, ∃ (z : M.Z) (W : M.Z.Opens), x ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range (b z)) = D ξ := fun x => by
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set M.Z))
      ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    obtain ⟨W, hzW, hW⟩ := h z hzc
    exact ⟨z, W, (specializes_iff_mem_closure.2 hz).mem_open W.isOpen hzW, hW⟩
  choose g U hU hg using hx
  have main : ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
      (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
      ∀ x ∈ W, Submodule.span (M.O x) (Set.range (b (g x))) = Submodule.span (M.O x) (Set.range c) :=
    fun W c hc hW x hx => M.span_rows_eq_of_forall_valuationRing hn (hb _) hc x fun ξ hξ hr =>
      (hg x ξ (hξ.mem_open (U x).isOpen (hU x)) hr).trans (hW ξ (hξ.mem_open W.isOpen hx) hr)
  refine ⟨⟨fun x => Submodule.span (M.O x) (Set.range (b (g x))), fun x => ⟨U x, b (g x), hU x, hb _,
    main _ _ (hb _) fun ξ hξ hr => (hg x ξ hξ hr).symm⟩⟩, fun z hz => ?_, main⟩
  obtain ⟨W, hzW, hW⟩ := h z hz
  exact main W _ (hb z) (fun ξ hξ hr => (hW ξ hξ hr).symm) z hzW

end GlobalTheory.ZH
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.WeightBundle

theorem sum_pow_neg_val {o G : Type} [CommRing o] [IsDomain o] [AddCommGroup G] [Fintype G] {N : ℕ} [NeZero N]
    {w : o} (hw : IsPrimitiveRoot w N) (f : G →+ ZMod N) :
    ∑ a, w ^ (-(f a)).val = if f = 0 then (Fintype.card G : o) else 0 := by
  split_ifs with hf
  · simp [hf]
  · have h := AddChar.sum_eq_zero_of_ne_one
      (ψ := (AddChar.zmodChar N hw.pow_eq_one).compAddMonoidHom (-f)) (by
        intro h
        refine hf (AddMonoidHom.ext fun a => ?_)
        have h1 := DFunLike.congr_fun h a
        rw [AddChar.compAddMonoidHom_apply, AddChar.zmodChar_apply, AddChar.one_apply,
          hw.pow_eq_one_iff_dvd] at h1
        have h2 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
        simpa using h2)
    simpa [AddChar.zmodChar_apply] using h

theorem nsmul_eq_zero_of_cast {r N : ℕ} [NeZero (r * N)] (x : ZMod (r * N))
    (h : ZMod.castHom (dvd_mul_left N r) (ZMod N) x = 0) : r • x = 0 := by
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at h
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact Nat.mul_dvd_mul_left r h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

instance neZero_N : NeZero S.N := ⟨by have := S.N_ge; omega⟩

instance neZero_rN : NeZero (S.r * S.N) :=
  ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (NeZero.ne _)⟩

instance finite_hom (T : AddSubgroup S.Gam) : Finite (T →+ ZMod S.N) :=
  Finite.of_injective _ DFunLike.coe_injective

theorem isPrimitiveRoot_root : IsPrimitiveRoot S.ζN S.N :=
  S.prim.pow (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _))) (by ring)

theorem sum_proj [IsDomain o] (T : AddSubgroup S.Gam) (hT : S.IsoFree T) [Fintype (T →+ ZMod S.N)] :
    ∑ c, S.proj T c = 1 := by
  obtain ⟨d, ⟨e⟩⟩ := hT.2
  have hw := isPrimitiveRoot_root S
  have hu : IsUnit (Nat.card T : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have key : ∀ t : T, ∑ c : T →+ ZMod S.N, S.ζN ^ (-(c t)).val • S.ρ t =
      (∑ c : T →+ ZMod S.N, S.ζN ^ (-(c t)).val) • (1 : Matrix S.J S.J o) := by
    intro t
    rw [← Finset.sum_smul]
    have h := sum_pow_neg_val hw (AddMonoidHom.eval t : (T →+ ZMod S.N) →+ ZMod S.N)
    simp only [AddMonoidHom.eval_apply_apply] at h
    split_ifs at h with h0
    · rw [S.ρ_one]
      have : S.r • e t = 0 := funext fun i => nsmul_eq_zero_of_cast _ (DFunLike.congr_fun h0
        ((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp
          ((Pi.evalAddMonoidHom _ i).comp e.toAddMonoidHom)))
      rw [← map_nsmul, map_eq_zero_iff e e.injective] at this
      exact congrArg Subtype.val this
    · rw [h, zero_smul, zero_smul]
  simp only [ThetaSys.proj, finsum_eq_sum_of_fintype]
  rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_congr rfl fun t _ => key t, ← Finset.sum_smul,
    Finset.sum_comm, Finset.sum_congr rfl fun c _ => sum_pow_neg_val hw c, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [← Nat.card_eq_fintype_card, smul_smul, Ring.inverse_mul_cancel _ hu, one_smul]

variable (M : RatModel o Ω)

abbrev gens (z : M.Z) : Set (S.J → Ω) :=
  {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧
    x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}

theorem FF_mem (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k) : S.FF T c k ∈ S.R := by
  rw [ThetaSys.FF, finsum_eq_sum_of_fintype]
  exact sum_mem fun t _ => mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem span_gens_eq [IsDomain o] {U₀ : M.Z.Opens} (hA : S.admitted M U₀) (z : M.Z) (hT : S.IsoFree (S.TT M z))
    (hF : ∀ c, S.FF (S.TT M z) c ≠ 0) {ξ : M.Z} (hξ : ξ ∈ U₀) :
    Submodule.span (M.O ξ) (gens S M z) =
      Submodule.span (M.O ξ) (Set.range fun i => Pi.single i (1 : Ω)) := by
  have hO : M.ringOn U₀ ≤ M.O ξ := RatModel.ringOn_le_O hξ
  have hR : S.R ≤ M.O ξ := hA.1.le.trans hO
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, k, x₀, i, hk, -, rfl⟩
    refine (RatModel.Lat.mem_const_iff M).2 fun j => ?_
    rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (hR (S.th_mem _)) (hO (hA.1.FF_unit _ _ _ hT hk.1))) (Subalgebra.algebraMap_mem _ _)
  · rintro _ ⟨i, rfl⟩
    obtain ⟨x₀, hx⟩ := hA.1.div z
    have := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
    have e : (Pi.single i (1 : Ω) : S.J → Ω) =
        ∑ c : S.TT M z →+ ZMod S.N, fun j => algebraMap o Ω (S.proj _ c j i) := by
      ext j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_apply, ← map_sum, ← Matrix.sum_apply, sum_proj S _ hT]
      simp [Matrix.one_apply, Pi.single_apply]
    show (Pi.single i (1 : Ω) : S.J → Ω) ∈ Submodule.span (M.O ξ) (gens S M z)
    rw [e]
    refine sum_mem fun c _ => ?_
    obtain ⟨k, hk⟩ := hA.2 _ c hT (hF c) z
    have hm : S.FF _ c k * (S.th x₀)⁻¹ ∈ M.O ξ := mul_mem (hR (FF_mem S _ _ _)) (hO (hA.1.th_unit _ hx.1))
    have e2 : (fun j => algebraMap o Ω (S.proj _ c j i)) = (⟨_, hm⟩ : M.O ξ) •
        fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i) := by
      ext j
      have h1 := hx.1
      have h2 := hk.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      field_simp
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, k, x₀, i, hk, hx, rfl⟩)

theorem exists_lat : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ → JacobsonSpace M.Z → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z ξ : M.Z, IsClosed ({z} : Set M.Z) → ξ ⤳ z → ValuationRing (M.O ξ) → Submodule.span (M.O ξ) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O ξ) {v | ∃ (c : S.TT M ξ →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M ξ) c) k ξ ∧ x₀ ∈ S.supI M ξ ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → (∀ z : M.Z, ∃ (b : Matrix S.J S.J Ω) (W : M.Z.Opens), z ∈ W ∧ b.det ≠ 0 ∧ ∀ x ∈ W, Submodule.span (M.O x) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O x) (Set.range b)) → ∃ EE : M.Lat S.J, (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) ∧ ∀ z ∈ U₀, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω)) := by
  intro o Ω _ _ _ hb S M U₀ hA hJ h0 hF hht hloc
  have := hb.ded
  choose b W hW hb0 hbW using hloc
  have hn := hA.1.normal
  obtain ⟨EE, h1, h2⟩ := GlobalTheory.ZH.exists_lat_of_height_le_one o Ω M hn S.J b
    (fun ξ => Submodule.span (M.O ξ) (gens S M ξ)) hb0 (by
      intro z hz
      have hfin := (GlobalTheory.ZH.normalModel_height_le_one o Ω M hn z).2.2 U₀ hA.1.ne
      have hfin' : {ξ : M.Z | (ξ ∉ U₀ ∧ ValuationRing (M.O ξ)) ∧ ¬ ξ ⤳ z}.Finite :=
        hfin.subset fun _ h => h.1
      have hcl : IsClosed (⋃ ξ ∈ {ξ : M.Z | (ξ ∉ U₀ ∧ ValuationRing (M.O ξ)) ∧ ¬ ξ ⤳ z}, closure {ξ}) :=
        hfin'.isClosed_biUnion fun _ _ => isClosed_closure
      refine ⟨W z ⊓ ⟨_, hcl.isOpen_compl⟩, ⟨hW z, ?_⟩, ?_⟩
      · intro h
        obtain ⟨ξ, hξ, h⟩ := Set.mem_iUnion₂.1 h
        exact hξ.2 (specializes_iff_mem_closure.2 h)
      · rintro ξ ⟨hξW, hξ⟩ hv
        rw [← hbW z ξ hξW]
        by_cases hU : ξ ∈ U₀
        · exact (span_gens_eq S M hA z (h0.1 z).1 (hF z) hU).trans
            (span_gens_eq S M hA ξ (h0.1 ξ).1 (hF ξ) hU).symm
        · refine hht z ξ hz ?_ hv
          by_contra hs
          exact hξ (Set.mem_iUnion₂.2 ⟨ξ, ⟨⟨hU, hv⟩, hs⟩, subset_closure rfl⟩))
  refine ⟨EE, fun z hz => (h1 z hz).trans (hbW z z (hW z)).symm, ?_⟩
  refine h2 U₀ (Matrix.of fun i => Pi.single i 1) ?_
    fun ξ hξ _ => span_gens_eq S M hA ξ (h0.1 ξ).1 (hF ξ) hξ
  have : (Matrix.of fun i => Pi.single i 1 : Matrix S.J S.J Ω) = 1 := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_one]
  exact one_ne_zero

end GlobalTheory.ZH.WeightBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanLatticeEqOfValuationRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem span_lattice_eq_of_valuationRing :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → S.FF _ c k / S.FF _ c' k' ∈ M.O ξ) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → IsDomain (M.O ξ) → ValuationRing (M.O ξ) → IsNoetherianRing (M.O ξ) → S.FF _ c' k' / S.FF _ c k ∈ M.O ξ) → (∀ z ξ : M.Z, IsClosed ({z} : Set M.Z) → ξ ⤳ z → ValuationRing (M.O ξ) → Submodule.span (M.O ξ) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O ξ) {v | ∃ (c : S.TT M ξ →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M ξ) c) k ξ ∧ x₀ ∈ S.supI M ξ ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  intro o Ω _ _ _ hA S M U₀ hAdm h0 hne hge hle z ξ hz hs hval
  haveI : IsDomain o := hA.inj.isDomain
  haveI := hA.ded
  have hnoeth : IsNoetherianRing (M.O ξ) := (normalModel_height_le_one o Ω M hAdm.1.normal ξ).2.1
  have hT := (h0.1 z).1
  have hT' := (h0.1 ξ).1
  have hsup := h0.2.1 ξ z hs
  have h : S.TT M ξ ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  haveI := FreeNear.finite_char S (S.TT M z)
  haveI := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
  have hmul := (FreeNear.proj_orthogonal S _ hT).1
  have hsum : ∀ c' : S.TT M ξ →+ ZMod S.N, S.proj _ c' =
      ∑ c ∈ Finset.univ.filter fun c : S.TT M z →+ ZMod S.N => c.comp (AddSubgroup.inclusion h) = c',
        S.proj _ c := fun c' => by
    rw [(GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.2 _ _ h hT hT' c', ← finsum_mem_coe_finset]
    simp
  have hcomp : ∀ (c : S.TT M z →+ ZMod S.N) (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ),
      c ⟨t, h₁⟩ = c.comp (AddSubgroup.inclusion h) ⟨t, h₂⟩ := fun _ _ _ _ => rfl
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, k, x₀, i, hk, hx, rfl⟩
    obtain ⟨k', hk'⟩ := hAdm.2 _ (c.comp (AddSubgroup.inclusion h)) hT' (hne ξ _) ξ
    have hu := hle z ξ c _ k k' hz hs (hcomp c) hk hk' inferInstance hval hnoeth
    have hp : S.proj _ (c.comp (AddSubgroup.inclusion h)) * S.proj _ c = S.proj _ c := by
      rw [hsum, Finset.sum_mul, Finset.sum_eq_single c]
      · rw [hmul, if_pos rfl]
      · intro b _ hb
        rw [hmul, if_neg hb]
      · simp
    have e : (fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)) =
        ∑ l, ((⟨_, hu⟩ : M.O ξ) * algebraMap o (M.O ξ) (S.proj _ c l i)) •
          fun j => S.th x₀ / S.FF _ (c.comp (AddSubgroup.inclusion h)) k' *
            algebraMap o Ω (S.proj _ (c.comp (AddSubgroup.inclusion h)) j l) := by
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← hp, Matrix.mul_apply, map_sum, Finset.mul_sum]
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      have h1 := hk.1
      have h2 := hk'.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, MulMemClass.coe_mul,
        Subalgebra.coe_algebraMap, map_mul]
      field_simp
    rw [SetLike.mem_coe, e]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, k', x₀, l, hk', hsup hx, rfl⟩)
  · rintro _ ⟨c', k', x', i, hk', hx', rfl⟩
    obtain ⟨x₀, hx₀⟩ := hAdm.1.div z
    choose k hk using fun c : S.TT M z →+ ZMod S.N => hAdm.2 _ c hT (hne z c) z
    have e : (fun j => S.th x' / S.FF _ c' k' * algebraMap o Ω (S.proj _ c' j i)) =
        ∑ c ∈ Finset.univ.filter fun c : S.TT M z →+ ZMod S.N => c.comp (AddSubgroup.inclusion h) = c',
          fun j => S.th x' / S.FF _ c' k' * algebraMap o Ω (S.proj _ c j i) := by
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_apply, hsum, Matrix.sum_apply, map_sum, Finset.mul_sum]
    rw [SetLike.mem_coe, e]
    refine Submodule.sum_mem _ fun c hc => ?_
    obtain rfl := (Finset.mem_filter.1 hc).2
    have hu := mul_mem ((hsup hx₀).2 x') (hge z ξ c _ (k c) k' hz hs (hcomp c) (hk c) hk')
    have e' : (fun j => S.th x' / S.FF _ (c.comp (AddSubgroup.inclusion h)) k' * algebraMap o Ω (S.proj _ c j i)) =
        (⟨_, hu⟩ : M.O ξ) • fun j => S.th x₀ / S.FF _ c (k c) * algebraMap o Ω (S.proj _ c j i) := by
      funext j
      have h1 := (hk c).1
      have h2 := hk'.1
      have h3 := hx₀.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      field_simp
    rw [e']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, k c, x₀, i, hk c, hx₀, rfl⟩)

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsEEOfSpanWeightSpaces
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem ThetaSys.FF_mem_ring (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem RatModel.span_val_span {M : RatModel o Ω} {J : Type} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z}
    {z : M.Z} (h : y (cPt p) = z) (w : Sp (PadicAlgCl p)) (G : Set (J → Ω))
    (hG : ∀ v ∈ G, ∀ j, v j ∈ M.O ((gPt p ≫ y) w)) :
    Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (Submodule.span (M.O z) G)) =
      Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' G) := by
  have hs : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨v, hv, rfl⟩
  suffices H : (∀ j, v j ∈ M.O ((gPt p ≫ y) w)) ∧ (fun j => M.val (gPt p ≫ y) (v j)) ∈
      Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' G) from H.2
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨hG v hv, Submodule.subset_span ⟨v, hv, rfl⟩⟩
  | zero =>
    refine ⟨fun j => zero_mem _, ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((0 : J → Ω) j)) = 0 := funext fun j => RatModel.val_zero _
    rw [this]
    exact zero_mem _
  | add u v _ _ hu hv =>
    refine ⟨fun j => add_mem (hu.1 j) (hv.1 j), ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((u + v) j)) =
        (fun j => M.val (gPt p ≫ y) (u j)) + fun j => M.val (gPt p ≫ y) (v j) :=
      funext fun j => RatModel.val_add hs (hu.1 j) (hv.1 j)
    rw [this]
    exact add_mem hu.2 hv.2
  | smul a v _ hv =>
    have ha : (a : Ω) ∈ M.O ((gPt p ≫ y) w) := RatModel.O_le_of_specializes (RatModel.gPt_specializes h w) a.2
    refine ⟨fun j => mul_mem ha (hv.1 j), ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((a • v) j)) =
        (⟨M.val (gPt p ≫ y) a, (mem_OO_iff _).2 (RatModel.norm_val_le_one h a.2)⟩ : OO p) •
          fun j => M.val (gPt p ≫ y) (v j) :=
      funext fun j => RatModel.val_mul hs ha (hv.1 j)
    rw [this]
    exact Submodule.smul_mem _ _ hv.2

theorem RatModel.val_div_mul {M : RatModel o Ω} {K : Type} [Field K] {y : Sp K ⟶ M.Z} {z : M.Z}
    (h : ∀ w, y w ⤳ z) {a b c : Ω} (ha : a ∈ M.O z) (hb : b ∈ M.O z) (hb0 : b ≠ 0) (hb' : b⁻¹ ∈ M.O z)
    (hc : c ∈ M.O z) : M.val y (a / b * c) = M.val y a / M.val y b * M.val y c := by
  have h1 : M.val y b⁻¹ = (M.val y b)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← RatModel.val_mul h hb hb', mul_inv_cancel₀ hb0, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul h (mul_mem ha hb') hc, RatModel.val_mul h ha hb', h1, div_eq_mul_inv]

theorem ThetaSys.span_val_eq_testLattice (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens)
    (hA : S.admitted M U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}
    (τ : S.Test p y₀) (hC : M.Cen U₀ z y) (hAt : S.At M y y₀)
    (hI : ∀ x ∈ S.supI M z, ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ)
    (T : AddSubgroup S.Gam) (hT : T = S.perp τ.yy.ker) (hF : ∀ c : T →+ ZMod S.N, S.FF T c ≠ 0)
    (hα : ∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c)
    (hv : ∀ (c : T →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF T c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) →
      (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) →
      ‖M.val (gPt p ≫ y) (S.FF T c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) :
    Submodule.span (OO p) ((fun (v : S.J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (Submodule.span (M.O z)
      {v | ∃ (c : T →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF T c) k z ∧ x₀ ∈ S.supI M z ∧
        v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)})) = τ.E := by
  subst hT
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hC.2 ⟨w, rfl⟩
  have hs : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hR : S.R ≤ M.O ((gPt p ≫ y) w) := hA.1.le.trans (RatModel.ringOn_le_O hw)
  have hinv : ∀ c k, M.Div (S.FF (S.perp τ.yy.ker) c) k z → (S.FF _ c k)⁻¹ ∈ M.O ((gPt p ≫ y) w) :=
    fun c k hk => RatModel.ringOn_le_O hw (hA.1.FF_unit _ c k τ.isoFree hk.1)
  have hval : ∀ c k x₀ i, M.Div (S.FF (S.perp τ.yy.ker) c) k z →
      (fun j => M.val (gPt p ≫ y) (S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i))) =
      fun j => M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ c k) *
        y₀ (algebraMap o S.R (S.proj _ c j i)) := by
    intro c k x₀ i hk
    funext j
    rw [RatModel.val_div_mul hs (hR (S.th_mem _)) (hR (S.FF_mem_ring _ _ _)) hk.1 (hinv c k hk)
      (Subalgebra.algebraMap_mem _ _), hAt]
    rfl
  have hnorm : ∀ α k x₀, M.Div (S.FF (S.perp τ.yy.ker) (τ.wt α)) k z → x₀ ∈ S.supI M z →
      (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) →
      ‖M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k)‖ = Real.exp (τ.q α / S.N) := by
    intro α k x₀ hk hx hm
    rw [norm_div, hI x₀ hx, hv _ k α hk hm fun _ _ _ => rfl, Real.exp_neg]
    have := τ.δ_pos.ne'
    have := (Real.exp_pos (τ.q α / S.N)).ne'
    field_simp
  rw [RatModel.span_val_span hC.1 w]
  · refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨_, ⟨c, k, x₀, i, hk, hx, rfl⟩, rfl⟩
      obtain ⟨α, hm, rfl⟩ := hα c
      exact ⟨α, _, i, hm, (hnorm α k x₀ hk hx hm).le, hval _ k x₀ i hk⟩
    · rintro _ ⟨α, l, i, hm, hl, rfl⟩
      obtain ⟨k, hk⟩ := hA.2 _ (τ.wt α) τ.isoFree (hF _) z
      obtain ⟨x₀, hx⟩ := hA.1.div z
      have hn := hnorm α k x₀ hk hx hm
      have hv' := hval _ k x₀ i hk
      generalize M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k) = l₀ at hn hv'
      have hpos : 0 < ‖l₀‖ := hn ▸ Real.exp_pos _
      have h0 : l₀ ≠ 0 := norm_pos_iff.1 hpos
      have hq : l / l₀ ∈ OO p := by
        rw [mem_OO_iff, norm_div, div_le_one hpos, hn]
        exact hl
      have : (fun j => l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i))) =
          (⟨l / l₀, hq⟩ : OO p) • fun j => l₀ * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) := by
        funext j
        show _ = l / l₀ * (l₀ * _)
        rw [← _root_.mul_assoc, div_mul_cancel₀ _ h0]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, k, x₀, i, hk, hx, rfl⟩, hv'⟩)
  · rintro _ ⟨c, k, x₀, i, hk, -, rfl⟩ j
    rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (hR (S.th_mem _)) (hinv c k hk)) (Subalgebra.algebraMap_mem _ _)

theorem isEE_of_span_weightSpaces : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → (∀ z ∈ U₀, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω))) → S.IsEE M U₀ EE := by
  intro o Ω _ _ _ hb S M U₀ EE hA h0 _ hF hα hv hE hU
  refine ⟨hU, fun z p _ y y₀ τ hC hAt => ?_⟩
  rw [hE z (hC.1 ▸ isClosed_singleton_cPt y)]
  obtain ⟨hI, hH⟩ := h0 z p y y₀ τ hC hAt
  exact S.span_val_eq_testLattice M U₀ hA τ hC hAt (fun x hx => (hI x).1 hx) _ (congrArg S.perp hH) (hF z)
    (hα p y₀ τ).1 (hv z p y y₀ τ hC hAt)

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FFDivFFMemOOfValuationRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
open Module

namespace GlobalTheory.ZH

theorem div_mem_of_forall_pow_succ_div_pow_mem :
    ∀ (Ω : Type) [Field Ω] (O : Subring Ω) [ValuationRing O] [IsNoetherianRing O],
      (∀ x : Ω, x ∈ O ∨ x⁻¹ ∈ O) → ∀ f f' : Ω, f ≠ 0 → f' ≠ 0 →
        (∀ j : ℕ, 1 ≤ j → f' ^ (j + 1) / f ^ j ∈ O) → f' / f ∈ O := by
  intro Ω _ O _ _ hO f f' hf hf' h
  by_contra hn
  have hg : f / f' ∈ O := by
    rcases hO (f' / f) with h1 | h1
    · exact absurd h1 hn
    · simpa using h1
  set g : O := ⟨f / f', hg⟩ with hgdef
  have hI : Ideal.span {g} ≠ ⊤ := by
    intro htop
    obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_top.mp htop).exists_right_inv
    have hu' : f / f' * (u : Ω) = 1 := congrArg Subtype.val hu
    have : (u : Ω) = f' / f := by
      field_simp at hu' ⊢
      linear_combination hu'
    exact hn (this ▸ u.2)
  have hK := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  have hmem : (⟨f' ^ (1 + 1) / f ^ 1, h 1 le_rfl⟩ : O) ∈ ⨅ n : ℕ, Ideal.span {g} ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨⟨f' ^ (n + 1 + 1) / f ^ (n + 1), h (n + 1) (by omega)⟩, Subtype.ext ?_⟩
    simp only [hgdef, Subring.coe_mul, SubmonoidClass.coe_pow, div_pow]
    field_simp
    ring
  rw [hK, Ideal.mem_bot] at hmem
  have h0 : f' ^ (1 + 1) / f ^ 1 = 0 := congrArg Subtype.val hmem
  exact div_ne_zero (pow_ne_zero _ hf') (pow_ne_zero _ hf) h0

end GlobalTheory.ZH
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.FF_div_FF_mem_O_of_valuationRing :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → ∀ x₀ ∈ S.supI M z, ∀ j : ℕ, 1 ≤ j → ∃ C : ℕ, (S.FF _ c' k' / S.th x₀) ^ (j + 1) * (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ^ C / (S.FF _ c k / S.th x₀) ^ j ∈ M.O z) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → IsDomain (M.O ξ) → ValuationRing (M.O ξ) → IsNoetherianRing (M.O ξ) → S.FF _ c' k' / S.FF _ c k ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ hO _ H z ξ c c' k k' hz hs hc hk hk' _ hv hn
  obtain ⟨x₀, hx₀⟩ := hO.div z
  have hx₀' : M.Div S.th x₀ ξ := hx₀.of_specializes hs
  have h0 : S.th x₀ ≠ 0 := hx₀.1
  have hP : (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ≠ 0 ∧ (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀)⁻¹ ∈ M.O ξ := by
    refine finprod_mem_induction (fun u : Ω => u ≠ 0 ∧ u⁻¹ ∈ M.O ξ) ⟨one_ne_zero, by simp⟩ ?_ ?_
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨mul_ne_zero ha hb, by rw [mul_inv]; exact mul_mem ha' hb'⟩
    · intro x hx
      have hx' : M.Div S.th x ξ := hx
      exact ⟨div_ne_zero hx'.1 h0, by rw [inv_div]; exact hx'.2 x₀⟩
  have hval : ∀ x : Ω, x ∈ (M.O ξ).toSubring ∨ x⁻¹ ∈ (M.O ξ).toSubring := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger (M.O ξ) x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Or.inl (hy ▸ y.2)
    · exact Or.inr (hy ▸ y.2)
  haveI : ValuationRing (M.O ξ).toSubring := hv
  haveI : IsNoetherianRing (M.O ξ).toSubring := hn
  have key := div_mem_of_forall_pow_succ_div_pow_mem Ω (M.O ξ).toSubring hval
    (S.FF _ c k / S.th x₀) (S.FF _ c' k' / S.th x₀) (div_ne_zero hk.1 h0) (div_ne_zero hk'.1 h0) (by
      intro j hj
      obtain ⟨C, hC⟩ := H z ξ c c' k k' hz hs hc hk hk' x₀ hx₀ j hj
      have h1 := mul_mem (RatModel.O_le_of_specializes hs hC) (pow_mem hP.2 C)
      have hP1 := hP.1
      generalize (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) = P at h1 hP1
      rw [div_mul_eq_mul_div, _root_.mul_assoc, ← _root_.mul_pow, mul_inv_cancel₀ hP1, _root_.one_pow, _root_.mul_one] at h1
      exact h1)
  rw [div_div_div_cancel_right₀ h0] at key
  exact key

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ComparisonFunctionRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsReducedCombination
open Module

namespace GlobalTheory

namespace LatticeIneq

variable {X : Type} [AddCommGroup X]

theorem weighted_add_le (q : QuadraticMap ℤ X ℝ) (hq : ∀ x, 0 ≤ q x) (j : ℕ) (a b : X) :
    (j : ℝ) * q (a + b) ≤ (j + 1) * q a + j * (j + 1) * q b := by
  have h1 : q (a + b) = q a + q b + QuadraticMap.polar q a b := by
    simp [QuadraticMap.polar]
  have h2 : q (a + (-(j : ℤ)) • b) = q a + q ((-(j : ℤ)) • b)
      + QuadraticMap.polar q a ((-(j : ℤ)) • b) := by
    simp only [QuadraticMap.polar]; ring
  rw [QuadraticMap.polar_smul_right, QuadraticMap.map_smul] at h2
  have h3 := hq (a + (-(j : ℤ)) • b)
  rw [h2] at h3
  simp only [zsmul_eq_mul] at h3
  push_cast at h3
  rw [h1]
  nlinarith

theorem map_sum_le (q : QuadraticMap ℤ X ℝ) (hq : ∀ x, 0 ≤ q x) {I : Type} (s : Finset I)
    (v : I → X) : q (∑ x ∈ s, v x) ≤ s.card * ∑ x ∈ s, q (v x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have hpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
      have h := weighted_add_le q hq s.card (∑ x ∈ s, v x) (v i)
      rw [add_comm (v i)]
      push_cast
      refine le_of_mul_le_mul_left ?_ hpos
      have h2 := mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ (s.card : ℝ) + 1)
      nlinarith

theorem exists_int_combination {I : Type} [Fintype I] (N : ℕ) (yy w : I → X)
    (hw : ∀ x, ∃ μ, w x = yy x + N • μ) (z : X)
    (hz : z ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ)) :
    ∃ (k : I → ℤ) (μ : X), z + N • μ = ∑ x, k x • w x := by
  classical
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    rcases hy with ⟨i, rfl⟩ | ⟨μ, rfl⟩
    · obtain ⟨μ, hμ⟩ := hw i
      refine ⟨Pi.single i 1, μ, ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [hμ]
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · simp
    · exact ⟨0, -μ, by simp⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, μ, h⟩ := ha
    obtain ⟨k', μ', h'⟩ := hb
    refine ⟨k + k', μ + μ', ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← h, ← h', smul_add]
    abel
  | neg a _ ha =>
    obtain ⟨k, μ, h⟩ := ha
    refine ⟨-k, -μ, ?_⟩
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, ← h, smul_neg]
    abel

theorem exists_reduced_combination {I : Type} [Fintype I] (N : ℕ) (hN : 1 ≤ N) (yy w : I → X)
    (hw : ∀ x, ∃ μ, w x = yy x + N • μ) (z : X)
    (hz : z ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ)) :
    ∃ (k : I → ℤ) (μ : X), (∀ x, 0 ≤ k x ∧ k x ≤ N) ∧ z + N • μ = ∑ x, k x • w x := by
  obtain ⟨k, μ, h⟩ := exists_int_combination N yy w hw z hz
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  refine ⟨fun x => k x % N, μ - ∑ x, (k x / N) • w x,
    fun x => ⟨Int.emod_nonneg _ hN'.ne', (Int.emod_lt_of_pos _ hN').le⟩, ?_⟩
  rw [smul_sub, ← add_sub_assoc, h, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← natCast_zsmul, smul_smul, ← sub_smul]
  simp only [Int.emod_def]

end LatticeIneq


open LatticeIneq in
theorem lattice_inequality :
    ∀ (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ), (∀ x, 0 ≤ q x) → ∀ (I : Type) [Fintype I] (N N' j : ℕ), 1 ≤ N → N ∣ N' → 1 ≤ j → ∀ (yy w : I → X) (vth : I → ℝ) (αs c : X) (vf' : ℝ), (∀ x, ∃ μ, w x = yy x + N' • μ) → (∀ x, q (w x) ≤ (N' : ℝ) ^ 2 * vth x) → q αs ≤ N * vf' → c - αs ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ) → ∃ μ : X, j * (q (c + N • μ) / N) ≤ (j + 1) * vf' + (j * (j + 1) * Fintype.card I * N * N' ^ 2 : ℕ) * ∑ x, vth x := by
  intro X _ q hq I _ N N' j hN hNN' _ yy w vth αs c vf' hw hwq hα hc
  obtain ⟨m, rfl⟩ := hNN'
  have hw' : ∀ x, ∃ μ, w x = yy x + N • μ := fun x => by
    obtain ⟨μ, hμ⟩ := hw x
    exact ⟨m • μ, by rw [hμ, mul_smul]⟩
  obtain ⟨k, μ, hk, h⟩ := LatticeIneq.exists_reduced_combination N hN yy w hw' _ hc
  refine ⟨μ, ?_⟩
  have hc' : c + N • μ = αs + ∑ x, k x • w x := by rw [← h]; abel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := LatticeIneq.weighted_add_le q hq j αs (∑ x, k x • w x)
  have h2 := LatticeIneq.map_sum_le q hq Finset.univ (fun x => k x • w x)
  have h3 : ∑ x, q (k x • w x) ≤ (N : ℝ) ^ 2 * ((N * m : ℕ) : ℝ) ^ 2 * ∑ x, vth x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    have a0 : (0 : ℝ) ≤ k x := by exact_mod_cast (hk x).1
    have a1 : (k x : ℝ) ≤ N := by exact_mod_cast (hk x).2
    have a2 : ((k x * k x : ℤ) : ℝ) ≤ (N : ℝ) ^ 2 := by push_cast; nlinarith
    calc _ ≤ (N : ℝ) ^ 2 * q (w x) := mul_le_mul_of_nonneg_right a2 (hq _)
      _ ≤ (N : ℝ) ^ 2 * (((N * m : ℕ) : ℝ) ^ 2 * vth x) :=
        mul_le_mul_of_nonneg_left (hwq x) (by positivity)
      _ = _ := by ring
  rw [Finset.card_univ] at h2
  have h4 := h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (j : ℝ) * (j + 1))
  have h6 := mul_le_mul_of_nonneg_left hα (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)
  rw [hc', ← mul_div_assoc, div_le_iff₀ hNpos]
  push_cast at h5 ⊢
  linarith

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH
namespace Regular

theorem nonneg_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (h : Filter.Tendsto q Filter.cofinite Filter.atTop) (x : X) : 0 ≤ q x := by
  by_contra hx
  push_neg at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hfin : {v | ¬ (0 : ℝ) ≤ q v}.Finite := Filter.eventually_cofinite.1 (h.eventually_ge_atTop 0)
  have hinj : Function.Injective fun n : ℕ => ((n : ℤ) + 1) • x := by
    intro a b hab
    have := smul_left_injective ℤ hx0 hab
    omega
  refine Set.infinite_of_injective_forall_mem hinj (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_le, QuadraticMap.map_smul, zsmul_eq_mul]
  refine mul_neg_of_pos_of_neg ?_ hx
  positivity

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem FF_mem (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _) (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem perp_anti (S : ThetaSys o Ω) {H H' : AddSubgroup S.Gam} (h : H ≤ H') : S.perp H' ≤ S.perp H :=
  fun _ ha x hx => ha x (h hx)

variable {M : RatModel o Ω} {K : Type} [Field K] {y : Sp K ⟶ M.Z} {z : M.Z}

theorem val_pow (h : ∀ w, y w ⤳ z) {a : Ω} (ha : a ∈ M.O z) (n : ℕ) : M.val y (a ^ n) = M.val y a ^ n :=
  map_pow (RatModel.valHomOf y z h) ⟨a, ha⟩ n

theorem val_prod (h : ∀ w, y w ⤳ z) {I : Type} (s : Finset I) {a : I → Ω} (ha : ∀ i, a i ∈ M.O z) :
    M.val y (∏ i ∈ s, a i) = ∏ i ∈ s, M.val y (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [RatModel.val_one]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    rw [RatModel.val_mul h (ha i) (prod_mem fun j _ => ha j), ih]

theorem val_ne_zero (h : ∀ w, y w ⤳ z) {a : Ω} (h0 : a ≠ 0) (ha : a ∈ M.O z) (ha' : a⁻¹ ∈ M.O z) :
    M.val y a ≠ 0 := by
  have := RatModel.val_mul h ha ha'
  rw [mul_inv_cancel₀ h0, RatModel.val_one] at this
  exact left_ne_zero_of_mul_eq_one this.symm

theorem val_div (h : ∀ w, y w ⤳ z) {a b : Ω} (ha : a ∈ M.O z) (hb : b ∈ M.O z) (hb' : b⁻¹ ∈ M.O z) :
    M.val y (a / b) = M.val y a / M.val y b := by
  by_cases h0 : b = 0
  · simp [h0, RatModel.val_zero]
  have := RatModel.val_mul h hb hb'
  rw [mul_inv_cancel₀ h0, RatModel.val_one] at this
  rw [div_eq_mul_inv, RatModel.val_mul h ha hb', div_eq_mul_inv, eq_inv_of_mul_eq_one_right this.symm]

theorem ratio_le_one {I : Type} [Fintype I] {δ a a' f' : ℝ} {t v : I → ℝ} (hδ : 0 < δ) (hf0 : 0 ≤ f')
    (hf : f' ≤ δ * Real.exp (-a')) (ht0 : ∀ x, 0 ≤ t x) (ht : ∀ x, t x ≤ δ * Real.exp (-(v x))) {j C : ℕ}
    (h : j * a ≤ (j + 1) * a' + C * ∑ x, v x) :
    (f' / δ) ^ (j + 1) * (∏ x, t x / δ) ^ C / (δ * Real.exp (-a) / δ) ^ j ≤ 1 := by
  rw [mul_div_cancel_left₀ _ hδ.ne', div_le_one (by positivity)]
  have h1 : f' / δ ≤ Real.exp (-a') := by rwa [div_le_iff₀' hδ]
  have h2 : ∏ x, t x / δ ≤ Real.exp (-∑ x, v x) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun x _ => div_nonneg (ht0 x) hδ.le) fun x _ => ?_
    rw [div_le_iff₀' hδ]
    exact ht x
  have h3 : 0 ≤ ∏ x, t x / δ := Finset.prod_nonneg fun x _ => div_nonneg (ht0 x) hδ.le
  calc _ ≤ Real.exp (-a') ^ (j + 1) * Real.exp (-∑ x, v x) ^ C := by gcongr
    _ ≤ _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      push_cast
      linarith

end Regular


open Regular in
theorem comparison_function_regular : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → ∀ x₀ ∈ S.supI M z, ∀ j : ℕ, 1 ≤ j → ∃ C : ℕ, (S.FF _ c' k' / S.th x₀) ^ (j + 1) * (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ^ C / (S.FF _ c k / S.th x₀) ^ j ∈ M.O z) := by
  intro o Ω _ _ _ _ S M U₀ hO hLL hT h0 hI h01 h11 h12 z ξ c c' k k' hz hξ hcc hk hk' x₀ hx₀ j hj
  have hN : 1 ≤ S.N := le_trans one_le_two S.N_ge
  have hr := S.r_pos
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  haveI : Fintype (S.supI M ξ) := Fintype.ofFinite _
  refine ⟨j * (j + 1) * Fintype.card (S.supI M ξ) * S.N * (S.r * S.N) ^ 2, ?_⟩
  rw [← finprod_set_coe_eq_finprod_mem, finprod_eq_prod_of_fintype]
  have hth : ∀ x, S.th x ∈ M.ringOn U₀ := fun x => hO.le (S.th_mem x)
  have hx0 : (S.th x₀)⁻¹ ∈ M.ringOn U₀ := hO.th_unit _ hx₀.1
  have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (FF_mem S _ c k)
  have hf' : S.FF _ c' k' ∈ M.ringOn U₀ := hO.le (FF_mem S _ c' k')
  have hfi : (S.FF _ c k)⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c k (hI.1 z).1 hk.1
  have e1 : S.FF _ c' k' / S.th x₀ ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]; exact mul_mem hf' hx0
  have e2 : ∀ x, S.th x / S.th x₀ ∈ M.ringOn U₀ := fun x => by
    rw [div_eq_mul_inv]; exact mul_mem (hth x) hx0
  have e3 : S.FF _ c k / S.th x₀ ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]; exact mul_mem hf hx0
  have e4 : ((S.FF _ c k / S.th x₀) ^ j)⁻¹ ∈ M.ringOn U₀ := by
    rw [← inv_pow, inv_div, div_eq_mul_inv]; exact pow_mem (mul_mem (hth _) hfi) j
  have e5 : ∏ x : S.supI M ξ, S.th x / S.th x₀ ∈ M.ringOn U₀ := prod_mem fun x _ => e2 x
  refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ fun p _ y hy => ?_
  · rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (pow_mem e1 _) (pow_mem e5 _)) e4
  obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT z p y hy
  obtain ⟨hsup, hH⟩ := h0 z p y y₀ τ hy hAt
  set w₀ := (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw₀
  have hs : ∀ w, (gPt p ≫ y) w ⤳ w₀ :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hle : M.ringOn U₀ ≤ M.O w₀ := RatModel.ringOn_le_O (hy.2 ⟨_, rfl⟩)
  have hTz : S.TT M z = S.perp τ.yy.ker := by rw [ThetaSys.TT, hH]
  have hTT : S.TT M ξ ≤ S.TT M z := perp_anti S (AddSubgroup.closure_mono (hI.2.1 ξ z hξ))
  have hTξ : S.TT M ξ ≤ S.perp τ.yy.ker := hTT.trans hTz.le
  obtain ⟨α, hα, hwα⟩ := (h01 p y₀ τ).1 (c.comp (AddSubgroup.inclusion hTz.ge))
  have hcα : ∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩ :=
    fun t h₁ h₂ => by rw [hwα]; rfl
  have hvf := h12 z p y y₀ τ hy hAt c k α hk hα hcα
  obtain ⟨β, -, hcβ, hvf'⟩ := (h11 p y₀ τ hint _ c' k' (FF_mem S _ c' k') (hI.1 ξ).1).2 hTξ
  rw [hAt] at hvf'
  have hex : ∀ x : S.Gam, ∃ w : τ.X, τ.yy x = QuotientAddGroup.mk w ∧ (x ∈ S.supI M ξ →
      ‖M.val (gPt p ≫ y) (S.th x)‖ ≤ τ.δ * Real.exp (-(τ.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) := by
    intro x
    by_cases hx : x ∈ S.supI M ξ
    · obtain ⟨w, h1, h2⟩ := τ.tx x (by
        rw [hAt]
        exact val_ne_zero hs hx.1 (hle (hth x)) (hle (hO.th_unit x hx.1)))
      rw [hAt] at h2
      exact ⟨w, h1, fun _ => h2⟩
    · obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (τ.yy x)
      exact ⟨w, hw.symm, fun h => absurd h hx⟩
  choose w hw hwv using hex
  have hmem := ((h01 p y₀ τ).2 _ (hI.1 ξ).1 hTξ w hw (S.supI M ξ) (hI.1 ξ).2.symm (α - β)).1
    (fun t h₂ h₁ => by
      rw [map_sub, AddMonoidHom.sub_apply, ← hcβ t h₁ h₂, ← hcα t (hTT h₁) h₂, hcc t (hTT h₁) h₁, sub_self])
  rw [Set.image_eq_range] at hmem
  have hNpos : (0 : ℝ) < S.N := by exact_mod_cast hN
  have hN'pos : (0 : ℝ) < ((S.r * S.N : ℕ) : ℝ) := by exact_mod_cast NeZero.pos _
  obtain ⟨v₁, hv₁⟩ := lattice_inequality τ.X τ.q (nonneg_of_tendsto τ.q τ.pos) (S.supI M ξ) S.N (S.r * S.N) j hN
    (dvd_mul_left _ _) hj (fun x => w x) (fun x => w x) (fun x => τ.q (w x) / ((S.r * S.N : ℕ) : ℝ) ^ 2) β α
    (τ.q β / S.N) (fun x => ⟨0, by simp⟩) (fun x => by rw [mul_div_cancel₀ _ (by positivity)])
    (by rw [mul_div_cancel₀ _ hNpos.ne']) hmem
  have hfin := le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hα v₁) hNpos.le)
    (Nat.cast_nonneg j)) hv₁
  have := ratio_le_one τ.δ_pos (norm_nonneg _) hvf' (fun x : S.supI M ξ => norm_nonneg _)
    (fun x => hwv x x.2) hfin
  rw [val_div hs (hle (mul_mem (pow_mem e1 _) (pow_mem e5 _))) (hle (pow_mem e3 _)) (hle e4),
    RatModel.val_mul hs (hle (pow_mem e1 _)) (hle (pow_mem e5 _)), val_pow hs (hle e1), val_pow hs (hle e5),
    val_pow hs (hle e3), val_prod hs _ (fun x : S.supI M ξ => hle (e2 x)),
    val_div hs (hle hf') (hle (hth _)) (hle hx0), val_div hs (hle hf) (hle (hth _)) (hle hx0)]
  simp only [fun x => val_div hs (hle (hth x)) (hle (hth _)) (hle hx0), norm_div, norm_mul, norm_pow, norm_prod]
  rw [(hsup x₀).1 hx₀, hvf]
  exact this

end GlobalTheory.ZH
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem exists_isEE_of_adm : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.HasTests → S.admitted M U₀ → ∃ EE : M.Lat S.J, S.IsEE M U₀ EE ∧ (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  intro o Ω _ _ _ hb S M U₀ hT hA
  have hO : S.Over₀ M U₀ := hA.1
  haveI := hb.ft
  haveI := hb.char
  have hll := @GlobalTheory.ZH.classical_points_and_local_regularity o Ω _ _ _ _ _ M U₀ hO.normal
  have hte := @GlobalTheory.ZH.exists_at_test_of_cen o Ω _ _ _ _ S M U₀ hT hO
  have hwt := @GlobalTheory.ZH.test_weights o Ω _ _ _ _ S
  have h0a := @GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω _ _ _ _ S M U₀ hO
  have h0b := @GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a
  have h11 := @GlobalTheory.thetaSys_norm_FF_le_exp o Ω _ _ _ _ S hwt
  have h12 := @GlobalTheory.norm_val_FF_eq_of_div o Ω _ _ _ _ S M U₀ hO h0a h11 hte
  have hne := @GlobalTheory.ZH.FF_TT_ne_zero o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt
  have h2g := @GlobalTheory.ZH.comparison_function_regular o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2ge := @GlobalTheory.ZH.FirstIneq.ff_div_ff_mem_of_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2le := @GlobalTheory.ZH.ThetaSys.FF_div_FF_mem_O_of_valuationRing o Ω _ _ _ _ S M U₀ hO h0b h2g
  have h3h := @GlobalTheory.ZH.span_lattice_eq_of_valuationRing o Ω _ _ _ _ S M U₀ hA h0b hne h2ge h2le
  have h3b := @GlobalTheory.ZH.exists_basis_lattice_near o Ω _ _ _ _ S M U₀ hA h0b hne
  obtain ⟨EE, hE₁, hE₂⟩ := @GlobalTheory.ZH.WeightBundle.exists_lat o Ω _ _ _ _ S M U₀ hA hll.2 h0b hne h3h h3b
  exact ⟨EE, @GlobalTheory.ZH.isEE_of_span_weightSpaces o Ω _ _ _ _ S M U₀ EE hA h0a h0b hne hwt h12 hE₁ hE₂, hE₁⟩

end GlobalTheory.ZH
