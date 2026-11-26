module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriContraction

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralMultipleBoundedPlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralMultipleBoundedPlaces
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV.Den

variable {F : Type} [Field F] [NumberField F]

theorem exists_pow_mul_le_one (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v)
    (ha : Valued.v a < 1) (K : Set (Fv F v)) (hK : IsCompact K) :
    ∃ m : ℕ, ∀ s ∈ K, Valued.v (a ^ m * s) ≤ 1 := by
  have h1 : IsOpen {s : Fv F v | Valued.v s < 1} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    have hy' : Valued.v (y - x) < 1 := by simpa using hy
    have h := Valuation.map_add_lt Valued.v hy' hx
    simpa using h
  have h2 : Tendsto (fun m : ℕ => a ^ m) atTop (𝓝 0) := Valued.tendsto_zero_pow_of_v_lt_one ha
  have hUo : ∀ m : ℕ, IsOpen {s : Fv F v | Valued.v (a ^ m * s) < 1} := fun m =>
    (continuous_const.mul continuous_id).isOpen_preimage _ h1
  have hcover : ∀ s : Fv F v, ∃ m : ℕ, Valued.v (a ^ m * s) < 1 := by
    intro s
    have h0 : Tendsto (fun m : ℕ => a ^ m * s) atTop (𝓝 0) := by
      simpa using h2.mul_const s
    have hn : {y : Fv F v | Valued.v y < 1} ∈ 𝓝 (0 : Fv F v) := h1.mem_nhds (by simp)
    exact (h0.eventually hn).exists
  have hmono : Monotone fun m : ℕ => {s : Fv F v | Valued.v (a ^ m * s) < 1} := by
    intro m m' hmm' s hs
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmm'
    show Valued.v (a ^ (m + d) * s) < 1
    rw [show a ^ (m + d) * s = a ^ d * (a ^ m * s) by ring, Valuation.map_mul, map_pow]
    calc Valued.v a ^ d * Valued.v (a ^ m * s) ≤ 1 * Valued.v (a ^ m * s) := by
          gcongr
          exact pow_le_one₀ zero_le ha.le
      _ = Valued.v (a ^ m * s) := one_mul _
      _ < 1 := hs
  obtain ⟨m, hm⟩ := hK.elim_directed_cover (fun m : ℕ => {s : Fv F v | Valued.v (a ^ m * s) < 1}) hUo
    (fun s _ => Set.mem_iUnion.mpr (hcover s)) hmono.directed_le
  exact ⟨m, fun s hs => le_of_lt (hm hs)⟩

theorem exists_nat_lt_one (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, 0 < p ∧ v.valuation F (p : F) < 1 := by
  refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩
  have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  have h : (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) : F) = ((Ideal.absNorm v.asIdeal : ℕ) : F) := by simp
  rw [← h]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hm

theorem val_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : v.valuation F (n : F) ≤ 1 := by
  have h : ((n : 𝓞 F) : F) = (n : F) := by simp
  rw [← h]
  exact HeightOneSpectrum.valuation_le_one v _

end GlobalTheory.CompanionTheory.Mass.MeanV.Den

theorem GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator :
    ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ T, IsCompact (K v)) → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ IntOut T, (∀ v ∈ T, algebraMap F (Fv F v) x ∈ K v) → ∃ y : 𝓞 F, (y : F) = (N : F) * x := by
  intro F _ _ T K hK
  have h3 : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F), Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
    intro v x
    show Valued.v ((x : v.adicCompletion F)) = v.valuation F x
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have h4 : ∀ x : F, (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1) → ∃ y : 𝓞 F, (y : F) = x := by
    intro x hx
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) (x := x) (h := hx)
    exact ⟨y, hy⟩
  have hpl : ∀ (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ), v.valuation F ((n : F) ^ k) ≤ 1 := by
    intro v n k
    rw [← Nat.cast_pow]
    exact Den.val_nat_le_one v _
  choose p hp0 hp1 using fun v : HeightOneSpectrum (𝓞 F) => Den.exists_nat_lt_one v
  have hm : ∀ v ∈ T, ∃ m : ℕ, ∀ s ∈ K v, Valued.v (algebraMap F (Fv F v) (p v : F) ^ m * s) ≤ 1 :=
    fun v hv => Den.exists_pow_mul_le_one v _ (by rw [h3]; exact hp1 v) (K v) (hK v hv)
  choose! m hm using hm
  refine ⟨∏ v ∈ T, p v ^ m v, Finset.prod_pos fun v _ => pow_pos (hp0 v) _, ?_⟩
  intro x hx hxK
  apply h4
  intro w
  push_cast
  rw [map_mul]
  by_cases hw : w ∈ T
  · rw [← Finset.mul_prod_erase T (fun v => (p v : F) ^ m v) hw, map_mul, map_prod]
    have hrest : ∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v) ≤ 1 :=
      Finset.prod_le_one' fun v _ => hpl w (p v) (m v)
    have hmain : w.valuation F ((p w : F) ^ m w) * w.valuation F x ≤ 1 := by
      have h := hm w hw _ (hxK w hw)
      rw [← map_pow, ← map_mul, h3, map_mul] at h
      exact h
    calc w.valuation F ((p w : F) ^ m w) * (∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v)) *
          w.valuation F x
        = (∏ v ∈ T.erase w, w.valuation F ((p v : F) ^ m v)) *
            (w.valuation F ((p w : F) ^ m w) * w.valuation F x) := by ac_rfl
      _ ≤ 1 * 1 := mul_le_mul' hrest hmain
      _ = 1 := one_mul 1
  · have hxw : w.valuation F x ≤ 1 := by
      have h : Valued.v (algebraMap F (Fv F w) x) ≤ 1 := hx w hw
      rwa [h3] at h
    have hN : w.valuation F (∏ v ∈ T, (p v : F) ^ m v) ≤ 1 := by
      rw [map_prod]
      exact Finset.prod_le_one' fun v _ => hpl w (p v) (m v)
    calc w.valuation F (∏ v ∈ T, (p v : F) ^ m v) * w.valuation F x ≤ 1 * 1 := mul_le_mul' hN hxw
      _ = 1 := one_mul 1
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralMultipleBoundedPlacesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_multiple_bounded_places : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (K : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), (∀ v ∈ T, IsCompact (K v)) → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ IntOut T, (∀ v ∈ T, algebraMap F (Fv F v) x ∈ K v) → ∃ y : 𝓞 F, (y : F) = (N : F) * x := by
  exact @GlobalTheory.CompanionTheory.Mass.MeanV.exists_common_denominator
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCochainExtendOfSurjective
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeRepExact

universe v u

section Gen

variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {A : D ⥤ CommAlgCat.{0} R} (a b : IdF A)

def Rp {j : ℕ} (y : CH.Cn (sq a b) j) (z : CH.Cn (CH.modF A) j) : Prop :=
  ∀ s, (show sqM a b _ from y s).1 = Ideal.Quotient.mk (b.S _) (show A.obj _ from z s)

variable {a b}

theorem sqMap_val {T T' : D} (φ : T ⟶ T') (w : sqM a b T) (x : A.obj T) (h : w.1 = Ideal.Quotient.mk (b.S T) x) :
    (sqMap a b φ w).1 = Ideal.Quotient.mk (b.S T') ((A.map φ).hom x) := by
  obtain ⟨w, hw⟩ := w
  obtain rfl : w = _ := h
  rfl

theorem Rp.d {j : ℕ} {y : CH.Cn (sq a b) j} {z : CH.Cn (CH.modF A) j} (h : Rp a b y z) :
    Rp a b (CH.d _ j y) (CH.d _ j z) := by
  intro s
  change (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • sqMap a b (toLast i s) (y (face i s)) : sqM a b _).1 =
    Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (z (face i s)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  change (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s) (y (face i s))).1 = _
  rw [sqMap_val _ _ _ (h (face i s))]

theorem Rp.sub {j : ℕ} {y y' : CH.Cn (sq a b) j} {z z' : CH.Cn (CH.modF A) j} (h : Rp a b y z) (h' : Rp a b y' z') :
    Rp a b (y - y') (z - z') := by
  intro s
  change (show sqM a b _ from y s).1 - (show sqM a b _ from y' s).1 =
    Ideal.Quotient.mk _ ((show A.obj _ from z s) - (show A.obj _ from z' s))
  rw [map_sub, h s, h' s]

theorem Rp.unique {j : ℕ} {y y' : CH.Cn (sq a b) j} {z : CH.Cn (CH.modF A) j} (h : Rp a b y z) (h' : Rp a b y' z) :
    y = y' :=
  funext fun s => Subtype.ext ((h s).trans (h' s).symm)

theorem Rp.mem {j : ℕ} {z : CH.Cn (CH.modF A) j} (h : Rp a b 0 z) (s) : z s ∈ b.S _ :=
  (Ideal.Quotient.eq_zero_iff_mem (a := (show A.obj _ from z s)) (I := b.S _)).1 (h s).symm

theorem Rp.zero {j : ℕ} {z : CH.Cn (CH.modF A) j} (h : ∀ s, z s ∈ b.S _) : Rp a b 0 z := fun s =>
  ((Ideal.Quotient.eq_zero_iff_mem (a := (show A.obj _ from z s)) (I := b.S _)).2 (h s)).symm

theorem exists_rp {j : ℕ} (z : CH.Cn (CH.modF A) j) (hz : ∀ s, z s ∈ a.S _) : ∃ y, Rp a b y z :=
  ⟨fun s => sqMk a b (show A.obj _ from z s) (hz s), fun _ => rfl⟩

theorem exists_lift {j : ℕ} (y : CH.Cn (sq a b) j) : ∃ z : CH.Cn (CH.modF A) j, (∀ s, z s ∈ a.S _) ∧ Rp a b y z := by
  have key : ∀ s : ComposableArrows D j, ∃ x : A.obj (s.obj (Fin.last j)), x ∈ a.S _ ∧
      (show sqM a b _ from y s).1 = Ideal.Quotient.mk (b.S _) x := fun s => by
    obtain ⟨x, hx, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from y s).2
    exact ⟨x, hx, e.symm⟩
  choose z hz hr using key
  exact ⟨z, hz, hr⟩

theorem exists_of_mem_B {n : ℕ} {w : CH.Cn (sq a b) n} {z : CH.Cn (CH.modF A) n} (hr : Rp a b w z)
    (hw : w ∈ (CH.cx (sq a b)).B n) : ∃ e : CH.Cn (CH.modF A) n, (∀ s, e s ∈ b.S _) ∧ CH.d _ n z = CH.d _ n e := by
  cases n with
  | zero =>
    have h0 : w = 0 := hw
    subst h0
    exact ⟨z, hr.mem, rfl⟩
  | succ n =>
    obtain ⟨t, rfl⟩ := hw
    obtain ⟨g, -, hg⟩ := exists_lift t
    have h0 : Rp a b 0 (z - CH.d _ n g) := by
      have := hr.sub hg.d
      rwa [sub_self] at this
    refine ⟨_, h0.mem, ?_⟩
    rw [map_sub, CH.d_d, sub_zero]

end Gen

section Cls

variable {R : Type} [CommRing R]

theorem sub_mem_B (K : Cx.{u} R) {n : ℕ} {x y : K.X n} (hx : K.d n x = 0) (hy : K.d n y = 0) (e : K.cls x hx = K.cls y hy) :
    x - y ∈ K.B n :=
  (Submodule.Quotient.eq ((K.B n).submoduleOf (K.Z n))).1 e

theorem cls_eq_of_sub_mem (K : Cx.{u} R) {n : ℕ} {x y : K.X n} (hx : K.d n x = 0) (hy : K.d n y = 0) (h : x - y ∈ K.B n) :
    K.cls x hx = K.cls y hy :=
  (Submodule.Quotient.eq ((K.B n).submoduleOf (K.Z n))).2 h

end Cls

section Res

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {A : C ⥤ CommAlgCat.{0} R}

theorem Rp.res (a b : IdF A) {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} {y : CH.Cn (sq (a.res U.ι) (b.res U.ι)) j}
    {z : CH.Cn (CH.modF (U.ι ⋙ A)) j} (hr : Rp _ _ y z) :
    Rp (a.res V.ι) (b.res V.ι) ((resU (sq a b) h).pullC j y) ((resU (CH.modF A) h).pullC j z) := fun s =>
  hr (s ⋙ ObjectProperty.ιOfLE h)

end Res

theorem exact_lift : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {U V : ObjectProperty C} (h : V ≤ U) (n : ℕ),
    Function.Surjective ((resU (gr Fil n) h).pull n) →
    ∀ (f : CH.Cn (CH.modF (V.ι ⋙ Φ.A)) n), (∀ σ, f σ ∈ (Fil n).S _) → (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) →
    ∃ f' : CH.Cn (CH.modF (U.ι ⋙ Φ.A)) n, (∀ σ, f' σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f' σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
      ∀ (x : HU (gr Fil ((n : ℤ) + 1)) V (n + 1)) (x' : HU (gr Fil ((n : ℤ) + 1)) U (n + 1)),
        Rep ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι) (CH.d _ n f) x →
        Rep ((Fil ((n : ℤ) + 1)).res U.ι) ((Fil ((n : ℤ) + 1 + 1)).res U.ι) (CH.d _ n f') x' →
        x = (resU (gr Fil ((n : ℤ) + 1)) h).pull (n + 1) x' := by
  intro R _ C _ Φ Fil hF U V h n hs f hf hdf
  obtain ⟨y, hy⟩ := exists_rp (a := (Fil n).res V.ι) (b := (Fil ((n : ℤ) + 1)).res V.ι) f hf
  have hdy : CH.d _ n y = 0 := hy.d.unique (Rp.zero hdf)
  obtain ⟨c', hc'⟩ := hs ((CH.cx (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι))).cls y hdy)
  obtain ⟨⟨y', hy'⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c'
  obtain ⟨f', hf'a, hf'⟩ := exists_lift (a := (Fil n).res U.ι) (b := (Fil ((n : ℤ) + 1)).res U.ι)
    (show CH.Cn (sq ((Fil n).res U.ι) ((Fil ((n : ℤ) + 1)).res U.ι)) n from y')
  have hdy' : CH.d (sq ((Fil n).res U.ι) ((Fil ((n : ℤ) + 1)).res U.ι)) n y' = 0 := hy'
  have hz : CH.d (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι)) n ((resU (gr Fil n) h).pullC n y') = 0 :=
    ((resU (gr Fil n) h).hom.mapZ n ⟨y', hy'⟩).2
  have hB := sub_mem_B (CH.cx (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι)))
    (x := (resU (gr Fil n) h).pullC n y') (y := y) hz hdy hc'
  refine ⟨f', hf'a, ?_, ?_⟩
  · have := hf'.d
    rw [hdy'] at this
    exact this.mem
  · rintro x x' ⟨u, hu, rfl, hur⟩ ⟨u', hu', rfl, hur'⟩
    have hur1 : Rp _ _ u (CH.d _ n f) := hur
    have hur2 : Rp _ _ u' (CH.d _ n f') := hur'
    have hw := (Rp.res (Fil n) (Fil ((n : ℤ) + 1)) h hf').sub hy
    obtain ⟨e, he, hde⟩ := exists_of_mem_B hw hB
    obtain ⟨t, ht⟩ := exists_rp (a := (Fil ((n : ℤ) + 1)).res V.ι) (b := (Fil ((n : ℤ) + 1 + 1)).res V.ι) e he
    have h1 := (Rp.res (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) h hur2).sub hur1
    have e1 : (resU (CH.modF Φ.A) h).pullC (n + 1) (CH.d (CH.modF (U.ι ⋙ Φ.A)) n f') =
        CH.d (CH.modF (V.ι ⋙ Φ.A)) n ((resU (CH.modF Φ.A) h).pullC n f') :=
      ((resU (CH.modF Φ.A) h).d_pullC n f').symm
    rw [e1, ← map_sub, hde] at h1
    have h2 := h1.unique ht.d
    have hz' : CH.d (sq ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι)) (n + 1)
        ((resU (gr Fil ((n : ℤ) + 1)) h).pullC (n + 1) u') = 0 :=
      ((resU (gr Fil ((n : ℤ) + 1)) h).hom.mapZ (n + 1) ⟨u', hu'⟩).2
    exact (cls_eq_of_sub_mem (CH.cx (sq ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι)))
      (x := (resU (gr Fil ((n : ℤ) + 1)) h).pullC (n + 1) u') (y := u) hz' hu ⟨t, h2.symm⟩).symm

end GlobalTheory.CompanionTheory.ConeRepExact
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmpPutSucc
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open GlobalTheory.CatH (face toLast)
universe w w' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.ReesDown

section
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {F : D ⥤ ModuleCat.{w} R} (Ψ : Flt F)

def ev (r : ℕ) (T : D) : Ψ.Pr T →+ F.obj T where
  toFun x := (x r).1
  map_zero' := rfl
  map_add' _ _ := rfl

def cmp (r j : ℕ) (f : Cn Ψ.rees j) : Cn F j := fun s => ev Ψ r _ (f s)

def cmpS (r j : ℕ) (f : Cn Ψ.rees j) : Cn (Ψ.S r).fn j := fun s => (show Ψ.Pr _ from f s) r

def put (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : Cn Ψ.rees j := fun s =>
  show Ψ.Pr _ from fun r => match r with
    | 0 => ⟨z s, by rw [h0]; trivial⟩
    | _ + 1 => 0

theorem cmp_d (r j : ℕ) (f : Cn Ψ.rees j) : cmp Ψ r (j + 1) (d Ψ.rees j f) = d F j (cmp Ψ r j f) := by
  funext s
  refine (map_sum (ev Ψ r _) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_zsmul]
  rfl

theorem cmp_zero (r j : ℕ) : cmp Ψ r j 0 = 0 := rfl

theorem cmp_sub (r j : ℕ) (f g : Cn Ψ.rees j) : cmp Ψ r j (f - g) = cmp Ψ r j f - cmp Ψ r j g := rfl

theorem cmp_put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : cmp Ψ 0 j (put Ψ h0 j z) = z := rfl

theorem cmp_put_succ (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (r j : ℕ) (z : Cn F j) : cmp Ψ (r + 1) j (put Ψ h0 j z) = 0 := rfl

theorem cochain_ext {j : ℕ} {f g : Cn Ψ.rees j} (h : ∀ r, cmp Ψ r j f = cmp Ψ r j g) : f = g := by
  funext s
  refine funext fun r => Subtype.ext ?_
  exact congrFun (h r) s

theorem put_d (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    d Ψ.rees j (put Ψ h0 j z) = put Ψ h0 (j + 1) (d F j z) := by
  refine cochain_ext Ψ fun r => ?_
  rw [cmp_d]
  cases r with
  | zero => rfl
  | succ r =>
    rw [cmp_put_succ, cmp_put_succ, map_zero]

theorem put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) : put Ψ h0 j 0 = 0 := by
  refine cochain_ext Ψ fun r => ?_
  cases r <;> rfl

theorem cmp_X (j r : ℕ) (f : Cn Ψ.rees j) : cmp Ψ (r + 1) j ((X : ℤ[X]) • f) = Ψ.μ • cmp Ψ r j f := by
  funext s
  exact Ψ.X_smul_succ _ (f s) r

theorem cmp_X_pow (j k : ℕ) (f : Cn Ψ.rees j) : cmp Ψ k j ((X : ℤ[X]) ^ k • f) = Ψ.μ ^ k • cmp Ψ 0 j f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, cmp_X, ih, pow_succ', mul_smul]

theorem cmp_mem_B (r j : ℕ) (a : Cn Ψ.rees j) (h : a ∈ (cx Ψ.rees).B j) : cmp Ψ r j a ∈ (cx F).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨cmp Ψ r j e, (cmp_d Ψ r j e).symm⟩

theorem put_mem_B (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (a : Cn F j) (h : a ∈ (cx F).B j) :
    put Ψ h0 j a ∈ (cx Ψ.rees).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this, put_zero]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨put Ψ h0 j e, put_d Ψ h0 j e⟩

theorem d_cmpS (r j : ℕ) (f : Cn Ψ.rees j) (hf : d Ψ.rees j f = 0) : d (Ψ.S r).fn j (cmpS Ψ r j f) = 0 := by
  funext s
  refine Subtype.ext ?_
  have h1 := congrFun ((Ψ.S r).inc.d_pullC j (cmpS Ψ r j f)) s
  have h2 : d F j (cmp Ψ r j f) = 0 := by rw [← cmp_d, hf, cmp_zero]
  exact h1.symm.trans (congrFun h2 s)

end

end GlobalTheory.CompanionTheory.ReesDown

namespace GlobalTheory.CompanionTheory.ReesDown

theorem put_pull {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (h0 : ∀ T, (Φ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    (Mor.restrict Φ.rees G).pullC j (put Φ h0 j z) =
      put (Φ.comap G) (fun T => h0 (G.obj T)) j ((Mor.restrict F G).pullC j z) := by
  refine cochain_ext (Φ.comap G) fun r => ?_
  cases r <;> rfl

theorem main : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n N : ℕ), (∀ T, (Φ.S 0).S T = ⊤) → RI ((X : ℤ[X]) ^ N) n Φ.rees G → ∀ j ≤ n, InjUpTo (Φ.μ ^ N) ((Mor.restrict F G).pull j) ∧ ∀ y, ∃ x ∈ (Φ.S N).img j, (Mor.restrict F G).pull j x = Φ.μ ^ N • y := by
  intro R _ C _ C' _ F Φ G n N h0 hRI j hj
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  have h0' : ∀ T, ((Φ.comap G).S 0).S T = ⊤ := fun T => h0 (G.obj T)
  have hpd : ∀ (z : Cn F j), d F j z = 0 → d (G ⋙ F) j ((Mor.restrict F G).pullC j z) = 0 := fun z hz => by
    rw [Mor.d_pullC, hz, map_zero]
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := (P.cls_surj (cx F) j).1 x
    have h2 : (Mor.restrict F G).pullC j z ∈ (cx (G ⋙ F)).B j := by
      have h1 := P.mapH_cls (Mor.restrict F G).hom j z hz (hpd z hz)
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.1 _ _).1 (h1.symm.trans hx)
    have hZ : d Φ.rees j (put Φ h0 j z) = 0 := by
      rw [put_d, hz]; exact put_zero Φ h0 _
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j (put Φ h0 j z)) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have h3 : (Mor.restrict Φ.rees G).pull j ((cx Φ.rees).cls _ hZ) = 0 := by
      refine (P.mapH_cls (Mor.restrict Φ.rees G).hom j _ hZ hZ').trans ?_
      refine ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.1 _ _).2 ?_
      have key : ∀ a : (cx (G ⋙ Φ.rees)).X j, a = put (Φ.comap G) h0' j ((Mor.restrict F G).pullC j z) →
          a ∈ (cx (G ⋙ Φ.rees)).B j := by
        intro a ha
        subst ha
        exact put_mem_B (Φ.comap G) h0' j _ h2
      exact key _ (put_pull Φ G h0 j z)
    have hXZ : d Φ.rees j ((X : ℤ[X]) ^ N • put Φ h0 j z) = 0 := by
      rw [map_smul, hZ, smul_zero]
    have h4 := hU.1 _ h3
    rw [← (P.cls_surj (cx Φ.rees) j).2.2.2.2 _ _ hZ hXZ] at h4
    have h5 := cmp_mem_B Φ N j _ (((P.cls_surj (cx Φ.rees) j).2.1 _ hXZ).1 h4)
    rw [cmp_X_pow, cmp_put_zero] at h5
    have hμ : d F j (Φ.μ ^ N • z) = 0 := by rw [map_smul, hz, smul_zero]
    rw [← (P.cls_surj (cx F) j).2.2.2.2 _ _ hz hμ]
    exact ((P.cls_surj (cx F) j).2.1 _ hμ).2 h5
  · obtain ⟨w, hw, rfl⟩ := (P.cls_surj (cx (G ⋙ F)) j).1 y
    have hW : d (G ⋙ Φ.rees) j (put (Φ.comap G) h0' j w) = 0 := by
      refine (put_d (Φ.comap G) h0' j w).trans ?_
      rw [hw]; exact put_zero (Φ.comap G) h0' _
    obtain ⟨x', hx'⟩ := hU.2 ((cx (G ⋙ Φ.rees)).cls (show (cx (G ⋙ Φ.rees)).X j from put (Φ.comap G) h0' j w) hW)
    obtain ⟨Z, hZ, rfl⟩ := (P.cls_surj (cx Φ.rees) j).1 x'
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j Z) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have hXW : d (G ⋙ Φ.rees) j ((X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) = 0 := by
      rw [map_smul, hW, smul_zero]
    have hx2 := (P.mapH_cls (Mor.restrict Φ.rees G).hom j Z hZ hZ').symm.trans hx'
    rw [← (P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.2.2 _ _ hW hXW] at hx2
    have hB := ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.1 _ _ hZ' hXW).1 hx2
    have hc : (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w ∈ (cx (G ⋙ F)).B j := by
      have h := cmp_mem_B (Φ.comap G) N j _ hB
      have e : ∀ A : Cn (Φ.comap G).rees j, A = (Mor.restrict Φ.rees G).pullC j Z →
          cmp (Φ.comap G) N j (A - (X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) =
            (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w := by
        intro A hA
        rw [cmp_sub, cmp_X_pow, cmp_put_zero, hA]
        rfl
      exact (e _ rfl) ▸ h
    have hz0 : d F j (cmp Φ N j Z) = 0 := by rw [← cmp_d, hZ, cmp_zero]
    have hμ : d (G ⋙ F) j (Φ.μ ^ N • w) = 0 := by rw [map_smul, hw, smul_zero]
    refine ⟨(cx F).cls _ hz0, ⟨(cx (Φ.S N).fn).cls _ (d_cmpS Φ N j Z hZ), ?_⟩, ?_⟩
    · exact P.mapH_cls (Φ.S N).inc.hom j _ _ hz0
    · refine (P.mapH_cls (Mor.restrict F G).hom j _ hz0 (hpd _ hz0)).trans ?_
      rw [← (P.cls_surj (cx (G ⋙ F)) j).2.2.2.2 _ _ hw hμ]
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.2.1 _ _ _ hμ).2 hc

end GlobalTheory.CompanionTheory.ReesDown
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorSandwichApprox
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorSandwichApprox
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

variable {F : Type} [Field F] [NumberField F]

def ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Set (Fv F v) :=
  {y | Valued.v y ≤ WithZero.exp (-(n : ℤ))}

theorem isClopen_ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : IsClopen (ballV v n) := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-(n : ℤ)))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : ballV v n = {y : Fv F v | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [ballV, Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isClopen_closedBall _ (by simp [hc0])

theorem ballV_subset (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ballV v n ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
  intro y hy
  have h1 : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 : Valued.v y ≤ 1 := le_trans (show Valued.v y ≤ _ from hy) h1
  exact h2

theorem antitone_ballV (v : HeightOneSpectrum (𝓞 F)) : Antitone (ballV (F := F) v) := by
  intro m n hmn y hy
  show Valued.v y ≤ _
  refine le_trans (show Valued.v y ≤ _ from hy) ?_
  rw [WithZero.exp_le_exp]
  omega

theorem iInter_ballV (v : HeightOneSpectrum (𝓞 F)) : ⋂ n, ballV (F := F) v n = {0} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hy
    have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h1 := h (-(Valued.v y).log + 1).toNat
    have h2 : Valued.v y ≤ WithZero.exp (-(((-(Valued.v y).log + 1).toNat : ℕ) : ℤ)) := h1
    conv_lhs at h2 => rw [← WithZero.exp_log hv0]
    rw [WithZero.exp_le_exp] at h2
    have := Int.self_le_toNat (-(Valued.v y).log + 1)
    omega
  · rintro rfl n
    simp [ballV]

theorem nhdsNE_Fv (v : HeightOneSpectrum (𝓞 F)) : (𝓝[≠] (0 : Fv F v)).NeBot := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

theorem tendsto_real_ballV {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam) :
    Tendsto (fun n => lam.real (ballV v n)) atTop (𝓝 0) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  have hfin : ∀ n, lam (ballV v n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono (ballV_subset v n))
  have h := tendsto_measure_iInter_atTop (μ := lam) (s := ballV v)
    (fun n => (isClopen_ballV v n).isOpen.measurableSet.nullMeasurableSet) (antitone_ballV v) ⟨0, hfin 0⟩
  rw [iInter_ballV, measure_singleton] at h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Measure.real, Function.comp_def] using h2

theorem exists_sandwich : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by
  intro F _ _ v lam C g hstd hg0 hg η hη
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  obtain ⟨hcont, hout, hint, -, hone⟩ := hg
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + |C| := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hgK : ∀ s, s ≠ 0 → g s ≤ K := by
    intro s hs
    by_cases hO : s ∈ v.adicCompletionIntegers F
    · have h1 := hint s hO hs
      have h2 : C / (Ideal.absNorm v.asIdeal : ℝ) ≤ |C| :=
        (div_le_self (abs_nonneg C) hq |>.trans' (div_le_div_of_nonneg_right (le_abs_self C) (by linarith)))
      have h3 := (abs_le.1 h1).2
      rw [hKdef]; linarith
    · rw [hout s hO]; exact hK0.le
  have hgi : Integrable g lam := by
    by_contra h
    rw [integral_undef h] at hone
    norm_num at hone
  have hnz : ∀ᵐ s ∂lam, s ≠ 0 := by
    have : ({0}ᶜ : Set (Fv F v)) ∈ ae lam := compl_mem_ae_iff.2 (measure_singleton 0)
    exact this
  have hlim : Tendsto (fun n => K * lam.real (ballV v n)) atTop (𝓝 0) := by
    simpa using (tendsto_real_ballV hstd).const_mul K
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  obtain ⟨B, hB⟩ : ∃ B, B = ballV v n := ⟨_, rfl⟩
  rw [← hB] at hn
  have hBc : IsClopen B := hB ▸ isClopen_ballV v n
  have hBO : B ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := hB ▸ ballV_subset v n
  have h0B : (0 : Fv F v) ∈ B := by rw [hB]; simp [ballV]
  have hBm : MeasurableSet B := hBc.isOpen.measurableSet
  have hBfin : lam B ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono hBO)
  have hcomp : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Formalism.L2.S.S7.AdeleLC.isCompact_integers v
  have hψm : Continuous (Bᶜ.indicator g) := by
    refine continuous_indicator ?_ ?_
    · intro a ha
      rw [hBc.compl.frontier_eq] at ha
      exact absurd ha (Set.notMem_empty a)
    · rw [hBc.compl.isClosed.closure_eq]
      refine hcont.mono ?_
      intro s hs h0
      exact hs (by rw [Set.mem_singleton_iff.1 h0]; exact h0B)
  have hψb : Continuous (B.indicator fun _ => K) :=
    by
    refine continuous_indicator ?_ continuous_const.continuousOn
    intro a ha
    rw [hBc.frontier_eq] at ha
    exact absurd ha (Set.notMem_empty a)
  have hIm : ∫ s, Bᶜ.indicator g s ∂lam = ∫ s in Bᶜ, g s ∂lam := integral_indicator hBm.compl
  have hsplit : ∫ s in B, g s ∂lam + ∫ s in Bᶜ, g s ∂lam = 1 := by
    rw [integral_add_compl hBm hgi, hone]
  have hpos : 0 ≤ ∫ s in B, g s ∂lam := setIntegral_nonneg hBm fun s _ => hg0 s
  have hconst : ∫ s in B, K ∂lam = K * lam.real B := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hup : ∫ s in B, g s ∂lam ≤ K * lam.real B := by
    rw [← hconst]
    refine integral_mono_ae hgi.integrableOn (integrableOn_const hBfin) ?_
    exact ae_restrict_of_ae (hnz.mono fun s hs => hgK s hs)
  have hi1 : Integrable (Bᶜ.indicator g) lam := hgi.indicator hBm.compl
  have hi2 : Integrable (B.indicator fun _ => K) lam :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
  have hIp : ∫ s, (Bᶜ.indicator g s + B.indicator (fun _ => K) s) ∂lam =
      ∫ s in Bᶜ, g s ∂lam + K * lam.real B := by
    rw [integral_add hi1 hi2, hIm, integral_indicator hBm, hconst]
  refine ⟨Bᶜ.indicator g, fun s => Bᶜ.indicator g s + B.indicator (fun _ => K) s, hψm, ?_,
    hψm.add hψb, ?_, fun s => Set.indicator_nonneg (fun s _ => hg0 s) s, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    simp [Set.indicator, hout s hs]
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    have hsB : s ∉ B := fun h => hs (hBO h)
    simp [hsB, hout s hs]
  · intro s hs
    by_cases hsB : s ∈ B
    · simp only [Set.indicator, Set.mem_compl_iff, hsB, not_true_eq_false, if_false, if_true, zero_add]
      exact ⟨hg0 s, hgK s hs⟩
    · simp [Set.indicator, hsB]
  · rw [hIm]; linarith
  · rw [hIp]; linarith

end GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorSandwichApproxStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_sandwich_approx : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by
  exact @GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich.exists_sandwich
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructure
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOutNeZero
open GlobalTheory.SplitFlip

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeAdj

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_out_ne_zero (K : Subgroup G) (hKo : IsOpen (K : Set G)) {φ : G → ℂ} (hφ : HasCompactSupport φ) :
    {q : G ⧸ K | φ q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' tsupport φ) :=
    hφ.isCompact.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset fun q hq => ?_
  exact ⟨q.out, subset_tsupport φ hq, QuotientGroup.out_eq' q⟩

variable [MeasurableSpace G] [BorelSpace G]

theorem measure_coset (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (q : G ⧸ K) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) = μ (K : Set G) := by
  have e : (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q} = (fun h => q.out⁻¹ * h) ⁻¹' (K : Set G) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  rw [e, measure_preimage_mul]

theorem integral_eq_sum (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {φ : G → ℂ} (hφ : HasCompactSupport φ)
    (hr : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) :
    ∫ g, φ g ∂μ = μ.real (K : Set G) • ∑ᶠ q : G ⧸ K, φ q.out := by
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hF := finite_out_ne_zero K hKo hφ
  set S : Finset (G ⧸ K) := hF.toFinset with hS
  have hmeas : ∀ q : G ⧸ K, MeasurableSet ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}) := fun q =>
    ((isOpen_discrete ({q} : Set (G ⧸ K))).preimage QuotientGroup.continuous_mk).measurableSet
  have hout : ∀ g : G, φ ((g : G ⧸ K)).out = φ g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hr g k k.2]
  have hsum : φ = fun g => ∑ q ∈ S, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g := by
    funext g
    have : ∀ q : G ⧸ K, ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out) g =
        if (g : G ⧸ K) = q then φ q.out else 0 := fun q => by
      simp [Set.indicator_apply]
    simp only [this, Finset.sum_ite_eq]
    split_ifs with h
    · exact (hout g).symm
    · have : φ ((g : G ⧸ K)).out = 0 := by
        by_contra h0
        exact h (hF.mem_toFinset.2 h0)
      rw [← hout g, this]
  have hint : ∀ q ∈ S, Integrable (((QuotientGroup.mk : G → G ⧸ K) ⁻¹' {q}).indicator (fun _ => φ q.out)) μ := by
    intro q _
    refine (integrable_indicator_iff (hmeas q)).2 (integrableOn_const ?_)
    rw [measure_coset]
    exact hfin
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun q hq => hF.mem_toFinset.2 hq)]
  conv_lhs => rw [hsum]
  rw [MeasureTheory.integral_finsetSum S hint, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hmeas q)]
  simp only [Measure.real, measure_coset]

theorem adjoint_of_inv (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (e : G → ℂ) (he : HasCompactSupport e)
    (hbi : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, e (k₁ * g * k₂) = e g)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (v w : V) (hv : ∀ k ∈ K, ρ k v = v) (hw : ∀ k ∈ K, ρ k w = w) :
    B (∑ᶠ q : G ⧸ K, e q.out • ρ q.out v) w =
      B v (∑ᶠ q : G ⧸ K, starRingEnd ℂ (e q.out⁻¹) • ρ q.out w) := by
  have hfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hpos : μ.real (K : Set G) ≠ 0 :=
    (ENNReal.toReal_pos (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne' hfin).ne'
  set φ₁ : G → ℂ := fun g => e g * B (ρ g v) w with hφ₁
  set φ₂ : G → ℂ := fun g => e g⁻¹ * B v (ρ g w) with hφ₂
  have hinv : ∀ g, φ₂ g = φ₁ g⁻¹ := fun g => by
    have h := hB g (ρ g⁻¹ v) w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    simp only [hφ₁, hφ₂, h]
  have he' : HasCompactSupport (fun g : G => e g⁻¹) := he.comp_homeomorph (Homeomorph.inv G)
  have hc₁ : HasCompactSupport φ₁ := he.mul_right
  have hc₂ : HasCompactSupport φ₂ := he'.mul_right
  have hr₁ : ∀ g, ∀ k ∈ K, φ₁ (g * k) = φ₁ g := fun g k hk => by
    have h1 : e (g * k) = e g := by simpa using hbi 1 K.one_mem k hk g
    simp only [hφ₁, h1, map_mul, Module.End.mul_apply, hv k hk]
  have hr₂ : ∀ g, ∀ k ∈ K, φ₂ (g * k) = φ₂ g := fun g k hk => by
    have h1 : e (g * k)⁻¹ = e g⁻¹ := by
      rw [mul_inv_rev]
      simpa using hbi k⁻¹ (K.inv_mem hk) 1 K.one_mem g⁻¹
    simp only [hφ₂, h1, map_mul, Module.End.mul_apply, hw k hk]
  have hs₁ : (Function.support fun q : G ⧸ K => e q.out • ρ q.out v).Finite :=
    (finite_out_ne_zero K hKo he).subset fun q hq h0 => hq (by simp [show e q.out = 0 from h0])
  have hs₂ : (Function.support fun q : G ⧸ K => starRingEnd ℂ (e q.out⁻¹) • ρ q.out w).Finite :=
    (finite_out_ne_zero K hKo he').subset fun q hq h0 => hq (by simp [show e q.out⁻¹ = 0 from h0])
  have l₁ : B (∑ᶠ q : G ⧸ K, e q.out • ρ q.out v) w = ∑ᶠ q : G ⧸ K, φ₁ q.out := by
    have := AddMonoidHom.map_finsum (AddMonoidHom.mk' (fun x => B x w) (by simp)) hs₁
    simpa [hφ₁] using this
  have l₂ : B v (∑ᶠ q : G ⧸ K, starRingEnd ℂ (e q.out⁻¹) • ρ q.out w) = ∑ᶠ q : G ⧸ K, φ₂ q.out := by
    have := AddMonoidHom.map_finsum (AddMonoidHom.mk' (fun x => B v x) (by simp)) hs₂
    simpa [hφ₂] using this
  have hI : ∫ g, φ₂ g ∂μ = ∫ g, φ₁ g ∂μ := by
    simp only [hinv]
    exact integral_inv_eq_self φ₁ μ
  rw [integral_eq_sum μ K hKo hfin hc₁ hr₁, integral_eq_sum μ K hKo hfin hc₂ hr₂] at hI
  rw [l₁, l₂]
  exact (smul_right_injective ℂ hpos hI).symm

end Abstract

section GeneralLinearIntegers

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isInvInvariant [MeasurableSpace F] [BorelSpace F] (μ : Measure (GL ι F)) [μ.IsHaarMeasure]
    (K : Subgroup (GL ι F)) (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) :
    μ.IsInvInvariant := by
  refine ⟨?_⟩
  have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have hne : μ (K : Set (GL ι F)) ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hnt : μ (K : Set (GL ι F)) ≠ ⊤ := hKc.measure_lt_top.ne
  have h2 := congrArg (fun m : Measure (GL ι F) => m (K : Set (GL ι F))) hc
  open scoped Pointwise in
  have hKi : (K : Set (GL ι F))⁻¹ = K := inv_coe_set
  simp only [Measure.inv_apply, hKi, Measure.coe_nnreal_smul_apply] at h2
  have h3 : ((Measure.haarScalarFactor μ.inv μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
  have h4 : Measure.haarScalarFactor μ.inv μ = 1 := by exact_mod_cast h3
  rw [hc, h4, one_smul]

end GeneralLinearIntegers

theorem hk_adjoint : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e →
    IsHk K (hstar e) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
      (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∀ v ∈ fixed ρ K, ∀ w ∈ fixed ρ K,
      B (hk ρ K e v) w = B v (hk ρ K (hstar e) w) := by
  intro F _ _ _ _ ι _ _ K e he
  obtain ⟨hKo, hKc, hc, hbi⟩ := he
  refine ⟨⟨hKo, hKc, ?_, ?_⟩, ?_⟩
  · have h1 : HasCompactSupport (fun g : GL ι F => e g⁻¹) := hc.comp_homeomorph (Homeomorph.inv _)
    exact h1.comp_left (g := starRingEnd ℂ) (map_zero _)
  · intro k₁ h₁ k₂ h₂ g
    show starRingEnd ℂ (e (k₁ * g * k₂)⁻¹) = starRingEnd ℂ (e g⁻¹)
    rw [show (k₁ * g * k₂)⁻¹ = k₂⁻¹ * g⁻¹ * k₁⁻¹ by group, hbi _ (K.inv_mem h₂) _ (K.inv_mem h₁)]
  · intro V _ _ ρ B hB v hv w hw
    borelize F
    haveI := isInvInvariant (Measure.haar : Measure (GL ι F)) K hKo hKc
    exact adjoint_of_inv Measure.haar K hKo hKc e hc hbi ρ B hB v w
      (fun k hk => by simpa using hv ⟨k, hk⟩) (fun k hk => by simpa using hw ⟨k, hk⟩)

end GlobalTheory.CompanionTheory.HeckeAdj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructure
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeAlg

theorem hk_alg : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  intro F _ _ _ _ ι _ _
  unfold HkAlg
  intro K e₁ e₂ h₁ h₂
  obtain ⟨hstar₁, hadj⟩ := GlobalTheory.CompanionTheory.HeckeAdj.hk_adjoint F ι K e₁ h₁
  refine ⟨GlobalTheory.CompanionTheory.HeckeMul.isHk_hconv h₁ h₂, hstar₁, ?_⟩
  intro V _ _ ρ v hv
  exact ⟨(GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e₁ h₁ V ρ v hv).1,
    GlobalTheory.CompanionTheory.HeckeMul.hk_hconv h₁ h₂ ρ hv,
    fun B hB w hw => hadj V ρ B hB v hv w hw⟩

end GlobalTheory.CompanionTheory.HeckeAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeAlgebraStructureStatement
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_algebra_structure : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  exact @GlobalTheory.CompanionTheory.HeckeAlg.hk_alg
end
end
