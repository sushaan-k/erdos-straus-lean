import ErdosStraus.Basic
import ErdosStraus.Family.Events
import ErdosStraus.Estimates.ReciprocalPrimes
import ErdosStraus.Family.Scales
import ErdosStraus.Estimates.RoughSums
import ErdosStraus.Family.SmallDivisors

/-!
# Proposition 6.6: the total event weight

The weight `μ_b = ∑_{i ∈ I_b} 1/q_i` satisfies `μ_b ≍ (log X)³`, uniformly in reduced `b`.
Grouping the members by `j = (e, d₋, d₊)` gives `|μ_b - 𝒫_X 𝓜_b| ≤ 𝒢`, where `𝓜_b` is the
weight (21) and `𝒢 = ∑_j (1/d₊) max_{(a,q)=1} |G_q(a)|` with `q = m rad(e)`; Lemma 3.8
bounds `𝒢` by a constant. The sum `V(e, d₋)` is `≍ log X / log z` by Lemma 3.4, and
Lemma 6.5 then gives `𝓜_b ≍ (log X)³`.
-/

/-! ## The error term (Lemma 3.8) -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family
open scoped BigOperators

theorem PrePrimeMem.rho_le_HScale
    {m : ℕ} {P : Params} {X : ℝ} {Pz b : ℕ} {j : FamilyPrePrimeIndex}
    (h : PrePrimeMem m P X Pz b j) : (j.E.rho : ℝ) ≤ HScale P X := by
  have hs : (1 : ℝ) ≤ j.E.s := by exact_mod_cast h.s_pos
  have hsp : (0 : ℝ) < j.E.s := zero_lt_one.trans_le hs
  have hprod := (le_div_iff₀ (sq_pos_of_pos hsp)).mp h.r_le
  have hsq : (j.E.s : ℝ) ≤ (j.E.s : ℝ) ^ 2 := by nlinarith
  have hh := (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg j.E.r)).trans hprod
  simpa only [ExactDivisor.rho, Nat.cast_mul] using hh

/-- The error `𝒢 = ∑_j (1/d₊) max_{(a,q)=1} |G_q(a)|`, `q = m rad(e)`, over the triples
`j = (e, d₋, d₊)` of `I_b`. -/
noncomputable def prePrimeError (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) : ℝ :=
  ∑ j ∈ prePrimeFinset m P X (Estimates.roughModulus X) b,
    ((1 : ℝ) / j.dplus) * Estimates.reducedClassPrimeErrorMax P X (m * j.E.rho)

/-- A triple `(e, d₋, d₊)` is determined by `q = m rad(e) ≤ X^ν`, a divisor `s ∣ q`,
`d₋ ≤ U` and `d₊ ≤ Y`. Hence `𝒢 ≤ ⌊U⌋ H_{⌊Y⌋} ∑_{q ≤ X^ν} τ(q) max_{(a,q)=1} |G_q(a)|`. -/
theorem prePrimeError_le_weightedBV
    (m : ℕ) (hm : 0 < m) (P : Params) {ν : ℝ} (hθν : P.θ < ν) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      prePrimeError m P X b ≤
        ((⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)) *
          Estimates.weightedBVSum P X 1 ν := by
  obtain ⟨Xm, hXm⟩ := fixedNat_le_rpow_eventually_threshold m (sub_pos.mpr hθν)
  refine ⟨Xm, ?_⟩
  intro X hX hX1 b
  let J := prePrimeFinset m P X (Estimates.roughModulus X) b
  let Q := Finset.Icc (1 : ℕ) ⌊X ^ ν⌋₊
  let T : Finset (Sigma (fun _ : ℕ => ℕ × ℕ × ℕ)) :=
    Q.sigma (fun q => q.divisors.product
      ((Finset.Icc (1 : ℕ) ⌊UScale X⌋₊).product (Finset.Icc (1 : ℕ) ⌊YScale P X⌋₊)))
  let code : FamilyPrePrimeIndex → Sigma (fun _ : ℕ => ℕ × ℕ × ℕ) :=
    fun j => ⟨m * j.E.rho, j.E.s, j.dminus, j.dplus⟩
  let w : Sigma (fun _ : ℕ => ℕ × ℕ × ℕ) → ℝ :=
    fun k => ((1 : ℝ) / k.2.2.2) * Estimates.reducedClassPrimeErrorMax P X k.1
  have hdata : ∀ j ∈ J, PrePrimeMem m P X (Estimates.roughModulus X) b j :=
    fun j hj => (mem_prePrimeFinset_iff m P X _ b j (zero_lt_one.trans hX1)).mp hj
  have hmap : J.image code ⊆ T := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have h := hdata j hj
    have hρ : 0 < j.E.rho := Nat.pos_of_ne_zero j.E.rho_squarefree.ne_zero
    have hq : ((m * j.E.rho : ℕ) : ℝ) ≤ X ^ ν := by
      push_cast
      calc
        (m : ℝ) * (j.E.rho : ℝ) ≤ X ^ (ν - P.θ) * X ^ P.θ :=
          mul_le_mul (hXm X hX) h.rho_le_HScale
            (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hX1.le) _)
        _ = X ^ ν := by rw [← Real.rpow_add (zero_lt_one.trans hX1)]; congr 1; ring
    have hdp : (j.dplus : ℝ) ≤ YScale P X := by
      exact (show (j.dplus : ℝ) ≤ (j.dminus : ℝ) * j.dplus by
        exact_mod_cast Nat.le_mul_of_pos_left j.dplus h.dminus_pos).trans h.dd_le_Y
    have hsdiv : j.E.s ∣ m * j.E.rho :=
      (show j.E.s ∣ j.E.rho from dvd_mul_left _ _).trans (dvd_mul_left _ _)
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hm hρ, Nat.le_floor hq⟩,
      Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hsdiv, (Nat.mul_pos hm hρ).ne'⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h.dminus_pos, Nat.le_floor h.dminus_le_U⟩,
          Finset.mem_Icc.mpr ⟨h.dplus_pos, Nat.le_floor hdp⟩⟩⟩⟩
  have hinj : Set.InjOn code (J : Set FamilyPrePrimeIndex) := by
    intro j hj k hk heq
    have hq : m * j.E.rho = m * k.E.rho := congrArg Sigma.fst heq
    have htail : (j.E.s, j.dminus, j.dplus) = (k.E.s, k.dminus, k.dplus) := by
      simpa only [code, Sigma.mk.inj_iff, heq_eq_eq] using congrArg Sigma.snd heq
    have hs : j.E.s = k.E.s := congrArg Prod.fst htail
    have hdm : j.dminus = k.dminus := congrArg (fun x => x.2.1) htail
    have hdp : j.dplus = k.dplus := congrArg (fun x => x.2.2) htail
    have hρ : j.E.rho = k.E.rho := Nat.eq_of_mul_eq_mul_left hm hq
    have hrs : j.E.r * j.E.s = k.E.r * j.E.s := by
      simpa only [ExactDivisor.rho, hs] using hρ
    have hr : j.E.r = k.E.r :=
      Nat.eq_of_mul_eq_mul_right (hdata j hj).s_pos hrs
    cases j with
    | mk Ej dj pj =>
      cases k with
      | mk Ek dk pk =>
        cases Ej
        cases Ek
        simp_all
  have hbound : prePrimeError m P X b ≤ ∑ k ∈ T, w k := by
    unfold prePrimeError
    change (∑ j ∈ J, w (code j)) ≤ _
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hmap (fun k _ _ =>
      mul_nonneg (by positivity) (Estimates.reducedClassPrimeErrorMax_nonneg _ _ _))
  have hsum : (∑ k ∈ T, w k) =
      ((⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)) *
        Estimates.weightedBVSum P X 1 ν := by
    unfold T w Estimates.weightedBVSum
    rw [Finset.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hp : (∑ x ∈ q.divisors.product
        ((Finset.Icc (1 : ℕ) ⌊UScale X⌋₊).product (Finset.Icc (1 : ℕ) ⌊YScale P X⌋₊)),
        ((1 : ℝ) / x.2.2) * Estimates.reducedClassPrimeErrorMax P X q) =
        ∑ _s ∈ q.divisors, ∑ _d ∈ Finset.Icc (1 : ℕ) ⌊UScale X⌋₊,
          ∑ t ∈ Finset.Icc (1 : ℕ) ⌊YScale P X⌋₊,
            ((1 : ℝ) / t) * Estimates.reducedClassPrimeErrorMax P X q := by
      apply (Finset.sum_product _ _ _).trans
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_product _ _ _
    rw [hp]
    simp_rw [← Finset.sum_mul]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, Real.rpow_one]
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Estimates.tau]
    ring_nf
  exact hbound.trans_eq hsum

/-- `𝒢 = O(1)` uniformly in `b`: the weighted sum of Lemma 3.8 is `≪ (log X)^{-12}`,
and `⌊U⌋ H_{⌊Y⌋} ≪ (log X)^9`. -/
theorem prePrimeError_eventually_bounded (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      prePrimeError m P X b ≤ C := by
  let ν : ℝ := (P.θ + P.β / 2) / 2
  have hνpos : 0 < ν := by dsimp [ν]; linarith [P.θ_pos, P.β_pos]
  have hθν : P.θ < ν := by dsimp [ν]; linarith [P.two_θ_lt_β]
  have hνhalf : ν < P.β / 2 := by dsimp [ν]; linarith [P.two_θ_lt_β]
  obtain ⟨K, XBV, hK, hBVbound⟩ := PrimeEstimates.reciprocalBV_weighted
    P ν 12 1 hνpos hνhalf (by norm_num) (by norm_num)
  obtain ⟨XE, herror⟩ := prePrimeError_le_weightedBV m hm P hθν
  refine ⟨(1 + P.σ) * K, max (max XBV XE) (Real.exp 1),
    mul_pos (by linarith [P.σ_pos]) hK, ?_⟩
  intro X hX hXgt b
  have hXBV : XBV ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXE : XE ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXexp : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hlog : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (zero_lt_one.trans hXgt)]
    exact hXexp
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog
  let W := Estimates.weightedBVSum P X 1 ν
  let A : ℝ := (⌊UScale X⌋₊ : ℝ) * (harmonic ⌊YScale P X⌋₊ : ℝ)
  have hW : 0 ≤ W := Estimates.weightedBVSum_nonneg P X 1 ν
  have hσ : 0 ≤ 1 + P.σ := by linarith [P.σ_pos]
  have hWbound : W ≤ K * (Real.log X) ^ (-(12 : ℝ)) := by
    calc
      W = |W| := (abs_of_nonneg hW).symm
      _ ≤ K * (Real.log X) ^ (-(12 : ℝ)) := hBVbound X hXBV
  have hcut : A ≤ (1 + P.σ) * (Real.log X) ^ 9 :=
    prePrimeErrorCutoffs_le_log_pow_nine P X hXexp
  have hpowprod : (Real.log X) ^ 9 * (Real.log X) ^ (-(12 : ℝ)) =
      (Real.log X) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hlogpos]
    norm_num
  have hnegpow : (Real.log X) ^ (-(3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
  calc
    prePrimeError m P X b ≤ A * W := herror X hXE hXgt b
    _ ≤ ((1 + P.σ) * (Real.log X) ^ 9) * W :=
      mul_le_mul_of_nonneg_right hcut hW
    _ ≤ ((1 + P.σ) * (Real.log X) ^ 9) *
        (K * (Real.log X) ^ (-(12 : ℝ))) :=
      mul_le_mul_of_nonneg_left hWbound (mul_nonneg hσ (by positivity))
    _ = ((1 + P.σ) * K) * (Real.log X) ^ (-(3 : ℝ)) := by
      rw [← hpowprod]
      ring
    _ ≤ (1 + P.σ) * K := by
      exact mul_le_of_le_one_right (mul_nonneg hσ hK.le) hnegpow

end ErdosStraus.FixedNumeratorFamily

/-! ## The rough factor `V(e, d₋)` -/

namespace ErdosStraus.FixedNumeratorFamily

open scoped BigOperators

/-- The squarefree `d₊ ≤ Y/d` with `(d₊, P(z)) = (d₊, m ρ) = 1`. -/
noncomputable def numeratorDplusRange
    (m : ℕ) (P : Params) (X : ℝ) (d ρ : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊YScale P X / (d : ℝ)⌋₊).filter (fun t =>
    Squarefree t ∧ Nat.Coprime t (Estimates.roughModulus X) ∧ Nat.Coprime t (m * ρ))

/-- The sum `V(e, d₋) = ∑ 1/d₊` over `numeratorDplusRange`, with `d = d₋` and
`ρ = rad(e)`. -/
noncomputable def numeratorDplusReciprocal
    (m : ℕ) (P : Params) (X : ℝ) (d ρ : ℕ) : ℝ :=
  ∑ t ∈ numeratorDplusRange m P X d ρ, (1 : ℝ) / t

theorem roughInitial_le_numeratorDplusReciprocal
    (m : ℕ) (P : Params) (X : ℝ) (d ρ : ℕ) (hm : 0 < m) (hρ : 0 < ρ)
    (hd : 0 < d) (hdU : (d : ℝ) ≤ UScale X) (hX : 1 < X)
    (hscale : UScale X * X ^ (P.σ / 2) ≤ YScale P X) :
    Estimates.roughInitial X (m * ρ) (P.σ / 2) ≤
      numeratorDplusReciprocal m P X d ρ := by
  classical
  unfold Estimates.roughInitial numeratorDplusReciprocal
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨htI, htSq, htP, htM⟩ := Finset.mem_filter.mp ht
    have htpos : 0 < t := (Finset.mem_Icc.mp htI).1
    have htUpper : (t : ℝ) ≤ X ^ (P.σ / 2) :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp htI).2).trans
        (Nat.floor_le (Real.rpow_nonneg (zero_lt_one.trans hX).le _))
    have hdt : (d : ℝ) * t ≤ YScale P X :=
      (mul_le_mul hdU htUpper (Nat.cast_nonneg _) (by unfold UScale; positivity)).trans hscale
    have htCap : t ≤ ⌊YScale P X / (d : ℝ)⌋₊ := by
      apply Nat.le_floor
      apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
      nlinarith only [hdt]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨htpos, htCap⟩, htSq, htP, ?_⟩
    rwa [Estimates.auxiliaryModulus_eq_self_of_pos (Nat.mul_pos hm hρ)] at htM
  · intro t _ _
    positivity

/-- Lower half of `V(e, d₋) ≍ log X / log z`, by Lemma 3.4, uniformly in `d₋ ≤ U` and
`rad(e) ≤ H`. -/
theorem numeratorDplusReciprocal_lower (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X →
      ∀ d ρ : ℕ, 0 < d → 0 < ρ → (d : ℝ) ≤ UScale X → (ρ : ℝ) ≤ HScale P X →
        c * (Real.log X / Real.log (zScale X)) ≤ numeratorDplusReciprocal m P X d ρ := by
  obtain ⟨c, _C, Xrough, hc, _hC, hrough⟩ := RoughReciprocal.roughInitial_two_sided
    (P.σ / 2) (P.θ + 1) (by linarith [P.σ_pos])
  obtain ⟨Xscale, hscale⟩ := familyPrePrime_initial_scale_eventually P
  refine ⟨c, max (max Xrough Xscale) (m : ℝ), hc, ?_⟩
  intro X hX hX1 d ρ hd hρ hdU hρH
  have hXp : 0 < X := zero_lt_one.trans hX1
  have hXm : (m : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hM : ((m * ρ : ℕ) : ℝ) ≤ X ^ (P.θ + 1) := by
    rw [Nat.cast_mul, Real.rpow_add hXp, Real.rpow_one, mul_comm (X ^ P.θ)]
    exact mul_le_mul hXm hρH (Nat.cast_nonneg _) (le_of_lt hXp)
  obtain ⟨_, _, _, _, hr, _, _⟩ := hrough X
    ((le_max_left _ _).trans ((le_max_left _ _).trans hX)) (m * ρ) hM
  exact hr.trans (roughInitial_le_numeratorDplusReciprocal m P X d ρ hm hρ hd hdU hX1
    (hscale X ((le_max_right _ _).trans ((le_max_left _ _).trans hX)) hX1))

end ErdosStraus.FixedNumeratorFamily

/-! ## Lower bound for `𝓜_b` -/

namespace ErdosStraus.FixedNumeratorFamily

open Classical Family
open scoped BigOperators

/-- The type of tuples `((s, d₋), (r, d₊))`. -/
abbrev StructuralTuple := Sigma fun _sd : ℕ × ℕ => Sigma fun _r : ℕ => ℕ

/-- The tuples `((s, d₋), (r, d₊))` with `(s, d₋)` a small pair, `r` in the progression of
Lemma 6.1 determined by `b`, and `d₊` in `numeratorDplusRange`. -/
noncomputable def structuralTuples (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) :
    Finset StructuralTuple :=
  (numeratorSmallPairs m P X).sigma (fun sd =>
    (numeratorRRange m P X sd.2 (numeratorBaseResidueTotal m b sd.2 sd.1) sd.1).sigma
      (fun r => numeratorDplusRange m P X sd.2 (r * sd.1)))

/-- The triple `(e, d₋, d₊)`, `e = r s²`, of a tuple `((s, d₋), (r, d₊))`. -/
noncomputable def structuralTupleIndex (m : ℕ) (P : Params) (X : ℝ) (b : ℕ)
    (t : { t // t ∈ structuralTuples m P X b }) : FamilyPrePrimeIndex := by
  refine ⟨⟨t.val.2.1, t.val.1.1, ?_, ?_, ?_⟩, t.val.1.2, t.val.2.2⟩
  · exact (Finset.mem_filter.mp (Finset.mem_sigma.mp
      (Finset.mem_sigma.mp t.property).2).1).2.1
  · exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp (Finset.mem_sigma.mp t.property).1).1).2.1
  · exact (Nat.coprime_mul_iff_right.mp (Finset.mem_filter.mp
      (Finset.mem_sigma.mp (Finset.mem_sigma.mp t.property).2).1).2.2.1).1

theorem structuralTupleIndex_mem (m : ℕ) (P : Params) (X : ℝ) (b : ℕ)
    (hX : 0 < X) (hb : Nat.Coprime b (Estimates.roughModulus X))
    (t : { t // t ∈ structuralTuples m P X b }) :
    PrePrimeMem m P X (Estimates.roughModulus X) b (structuralTupleIndex m P X b t) := by
  let s := t.val.1.1
  let d := t.val.1.2
  let r := t.val.2.1
  let dp := t.val.2.2
  obtain ⟨hsd, hrp⟩ := Finset.mem_sigma.mp t.property
  obtain ⟨hr, hdp⟩ := Finset.mem_sigma.mp hrp
  obtain ⟨hsd0, hsm, hdm⟩ := Finset.mem_filter.mp hsd
  obtain ⟨hbox, hsSq, hdP, hdOdd, hds⟩ := Finset.mem_filter.mp hsd0
  obtain ⟨hsI, hdI⟩ := Finset.mem_product.mp hbox
  obtain ⟨hspos, hsmax⟩ := Finset.mem_Icc.mp hsI
  obtain ⟨hdpos, hdmax⟩ := Finset.mem_Icc.mp hdI
  obtain ⟨hrW, hrSq, hrC, hrcong⟩ := Finset.mem_filter.mp hr
  obtain ⟨hrI, hrgt⟩ := Finset.mem_filter.mp hrW
  obtain ⟨hdpI, hdpSq, hdpP, hdpM⟩ := Finset.mem_filter.mp hdp
  obtain ⟨hdppos, hdpmax⟩ := Finset.mem_Icc.mp hdpI
  have hbd := hb.coprime_dvd_right hdP
  have hcoef : Nat.Coprime (m * s ^ 2) d := Nat.coprime_mul_iff_left.mpr
    ⟨hdm.symm, (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) s d).mpr hds.symm⟩
  have hres : numeratorBaseResidueTotal m b d s =
      numeratorBaseResidue m b d s hbd hcoef := by
    rw [numeratorBaseResidueTotal, dif_pos ⟨hbd, hcoef⟩]
  have hrc : r ≡ numeratorBaseResidue m b d s hbd hcoef [MOD d] := by
    simpa only [← hres, Estimates.congMod, Nat.ModEq] using hrcong
  have hbase : d ∣ b + m * r * s ^ 2 := by
    apply Nat.modEq_zero_iff_dvd.mp
    exact ((hrc.mul_left m).mul_right (s ^ 2) |>.add_left b).trans
      (Nat.modEq_zero_iff_dvd.mpr (numeratorBaseResidue_sat m b d s hdpos hbd hcoef))
  have hrd : Nat.Coprime r d := by
    have ha := numeratorBaseResidue_coprime m b d s hbd hcoef
    apply Nat.coprime_of_dvd
    intro p hp hpr hpd
    have hpa : p ∣ numeratorBaseResidue m b d s hbd hcoef :=
      Nat.modEq_zero_iff_dvd.mp
        ((hrc.of_dvd hpd).symm.trans (Nat.modEq_zero_iff_dvd.mpr hpr))
    have hp1 : p ∣ 1 := by rw [← ha.gcd_eq_one]; exact Nat.dvd_gcd hpa hpd
    exact hp.not_dvd_one hp1
  have hdmrho : Nat.Coprime d (m * (r * s)) :=
    Nat.coprime_mul_iff_right.mpr
      ⟨hdm, Nat.coprime_mul_iff_right.mpr ⟨hrd.symm, hds⟩⟩
  have hrm : Nat.Coprime (r * s) m :=
    Nat.coprime_mul_iff_left.mpr ⟨(Nat.coprime_mul_iff_right.mp hrC).2, hsm⟩
  have hddY : (d : ℝ) * dp ≤ YScale P X := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hdpY : (dp : ℝ) ≤ YScale P X / d :=
      (Nat.cast_le.mpr hdpmax).trans (Nat.floor_le (by
        apply div_nonneg (Real.rpow_nonneg hX.le _) hdR.le))
    nlinarith [(le_div_iff₀ hdR).mp hdpY]
  exact
    { s_pos := hspos,
      s_le_S := (Nat.cast_le.mpr hsmax).trans (Nat.floor_le (Real.rpow_nonneg hX.le _)),
      r_gt := hrgt,
      r_le := (Nat.cast_le.mpr (Finset.mem_Icc.mp hrI).2).trans
        (Nat.floor_le (div_nonneg (Real.rpow_nonneg hX.le _) (sq_nonneg _))),
      dminus_pos := hdpos,
      dminus_le_U := (Nat.cast_le.mpr hdmax).trans (Nat.floor_le (by unfold UScale; positivity)),
      dminus_dvd_Pz := hdP,
      dminus_squarefree := (Estimates.roughModulus_squarefree X).squarefree_of_dvd hdP,
      dminus_odd := hdOdd,
      base_cong := by simpa [structuralTupleIndex, FamilyPrePrimeIndex.withPrime,
        ExactDivisor.e, s, d, r, Nat.mul_assoc] using Nat.modEq_zero_iff_dvd.mpr hbase,
      dplus_pos := hdppos, dplus_squarefree := hdpSq,
      dd_le_Y := hddY, dplus_coprime_Pz := hdpP,
      rho_coprime_m := hrm,
      dd_coprime_mrho := Nat.coprime_mul_iff_left.mpr ⟨hdmrho, hdpM⟩ }

/-- The weight `𝓜_b = ∑_j (1/d₊)/φ(m rad(e))` of (21), over the triples `j = (e, d₋, d₊)`. -/
noncomputable def prePrimeStructuralMass (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) : ℝ :=
  ∑ j ∈ prePrimeFinset m P X (Estimates.roughModulus X) b,
    ((1 : ℝ) / j.dplus) / Nat.totient (m * j.E.rho)

/-- The nested sum `∑_{(s, d₋)} ∑_r V(e, d₋)/φ(m s r)`, `e = r s²`. -/
noncomputable def selectedStructuralMass (m : ℕ) (P : Params) (X : ℝ) (b : ℕ) : ℝ :=
  ∑ sd ∈ numeratorSmallPairs m P X,
    ∑ r ∈ numeratorRRange m P X sd.2 (numeratorBaseResidueTotal m b sd.2 sd.1) sd.1,
      (1 / (Nat.totient (m * sd.1 * r) : ℝ)) *
        numeratorDplusReciprocal m P X sd.2 (r * sd.1)

theorem selectedStructuralMass_le_prePrimeStructuralMass (m : ℕ) (P : Params)
    (X : ℝ) (b : ℕ) (hX : 0 < X) (hb : Nat.Coprime b (Estimates.roughModulus X)) :
    selectedStructuralMass m P X b ≤ prePrimeStructuralMass m P X b := by
  let T := structuralTuples m P X b
  let F := structuralTupleIndex m P X b
  let w : FamilyPrePrimeIndex → ℝ := fun j =>
    ((1 : ℝ) / j.dplus) / Nat.totient (m * j.E.rho)
  have hF_inj : Function.Injective F := by
    intro a b hab
    have hr := congrArg (fun j : FamilyPrePrimeIndex => j.E.r) hab
    have hs := congrArg (fun j : FamilyPrePrimeIndex => j.E.s) hab
    have hd := congrArg (fun j : FamilyPrePrimeIndex => j.dminus) hab
    have hp := congrArg (fun j : FamilyPrePrimeIndex => j.dplus) hab
    apply Subtype.ext
    apply Sigma.ext
    · exact Prod.ext hs hd
    · apply heq_of_eq
      exact Sigma.ext hr (heq_of_eq hp)
  have hsub : T.attach.image F ⊆ prePrimeFinset m P X (Estimates.roughModulus X) b := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    exact (mem_prePrimeFinset_iff _ _ _ _ _ _ hX).mpr
      (structuralTupleIndex_mem m P X b hX hb t)
  have hsum : selectedStructuralMass m P X b = ∑ t ∈ T.attach, w (F t) := by
    unfold selectedStructuralMass numeratorDplusReciprocal
    simp_rw [Finset.mul_sum]
    change _ = ∑ t ∈ T.attach,
      ((1 : ℝ) / t.val.2.2) / Nat.totient (m * (t.val.2.1 * t.val.1.1))
    rw [Finset.sum_attach T (fun t : StructuralTuple =>
      ((1 : ℝ) / t.2.2) / Nat.totient (m * (t.2.1 * t.1.1)))]
    dsimp [T, structuralTuples]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro sd hsd
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro dp hdp
    rw [show m * sd.1 * r = m * (r * sd.1) by ring]
    ring
  rw [hsum]
  calc
    _ = ∑ j ∈ T.attach.image F, w j := (Finset.sum_image
      (fun a _ b _ h => hF_inj h)).symm
    _ ≤ ∑ j ∈ prePrimeFinset m P X (Estimates.roughModulus X) b, w j := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by dsimp [w]; positivity)

/-- Bounding `V(e, d₋)` below termwise: the nested sum is `≫ (log X / log z) Σ_b`. -/
theorem selectedStructuralMass_ge_rough_smallMass (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      c * (Real.log X / Real.log (zScale X)) * numeratorSmallCertificateMass m P X b ≤
        selectedStructuralMass m P X b := by
  obtain ⟨c, X₀, hc, hrough⟩ := numeratorDplusReciprocal_lower m hm P
  refine ⟨c, X₀, hc, ?_⟩
  intro X hX hXgt b
  unfold numeratorSmallCertificateMass selectedStructuralMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  rintro ⟨s, d⟩ hsd
  unfold numeratorPhiAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  obtain ⟨hsd0, hsm, hdm⟩ := Finset.mem_filter.mp hsd
  obtain ⟨hbox, hsSq, hdP, hdOdd, hds⟩ := Finset.mem_filter.mp hsd0
  obtain ⟨hsI, hdI⟩ := Finset.mem_product.mp hbox
  obtain ⟨hspos, hsmax⟩ := Finset.mem_Icc.mp hsI
  obtain ⟨hdpos, hdmax⟩ := Finset.mem_Icc.mp hdI
  have hdU : (d : ℝ) ≤ UScale X :=
    (Nat.cast_le.mpr hdmax).trans (Nat.floor_le (by unfold UScale; positivity))
  obtain ⟨hrW, hrSq, hrC, hrcong⟩ := Finset.mem_filter.mp hr
  obtain ⟨hrI, hrgt⟩ := Finset.mem_filter.mp hrW
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hspos
  have hsp : (0 : ℝ) < s := zero_lt_one.trans_le hsR
  have hrUpper : (r : ℝ) ≤ HScale P X / (s : ℝ) ^ 2 :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hrI).2).trans
      (Nat.floor_le (div_nonneg (Real.rpow_nonneg (zero_lt_one.trans hXgt).le _)
        (sq_nonneg _)))
  have hrho : ((r * s : ℕ) : ℝ) ≤ HScale P X := by
    have hprod := (le_div_iff₀ (sq_pos_of_pos hsp)).mp hrUpper
    have hsSqR : (s : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
    simpa only [Nat.cast_mul] using
      (mul_le_mul_of_nonneg_left hsSqR (Nat.cast_nonneg r)).trans hprod
  have hrhopos : 0 < r * s :=
    Nat.mul_pos (Nat.pos_of_ne_zero hrSq.ne_zero) hspos
  have h := hrough X hX hXgt d (r * s) hdpos hrhopos hdU hrho
  calc
    c * (Real.log X / Real.log (zScale X)) * (1 / (Nat.totient (m * s * r) : ℝ)) =
        (1 / (Nat.totient (m * s * r) : ℝ)) *
          (c * (Real.log X / Real.log (zScale X))) := mul_comm _ _
    _ ≤ (1 / (Nat.totient (m * s * r) : ℝ)) *
        numeratorDplusReciprocal m P X d (r * s) :=
      mul_le_mul_of_nonneg_left h (by positivity)

/-- `𝓜_b ≫ (log X)³`, uniformly in reduced `b`. -/
theorem prePrimeStructuralMass_lower (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      c * (Real.log X) ^ 3 ≤ prePrimeStructuralMass m P X b := by
  obtain ⟨cr, Xr, hcr, hr⟩ := selectedStructuralMass_ge_rough_smallMass m hm P
  obtain ⟨cs, Xs, hcs, hs⟩ := numeratorSmallCertificateMass_lower m hm P
  refine ⟨cr * cs * P.η, max (max Xr Xs) (Real.exp 2),
    mul_pos (mul_pos hcr hcs) P.η_pos, ?_⟩
  intro X hX hXgt b hb
  have hXp : 0 < X := zero_lt_one.trans hXgt
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hXgt.le
  have hlogZ : 0 < Real.log (zScale X) :=
    Estimates.log_zScale_pos_of_exp_two_le ((le_max_right _ _).trans hX)
  have hsmall := hs X ((le_max_right _ _).trans ((le_max_left _ _).trans hX)) hXgt b hb
  have hstruct := hr X ((le_max_left _ _).trans ((le_max_left _ _).trans hX)) hXgt b
  calc
    (cr * cs * P.η) * (Real.log X) ^ 3 =
        (cr * (Real.log X / Real.log (zScale X))) *
          (cs * Real.log X * Real.log (SScale P X) * Real.log (zScale X)) := by
      rw [log_SScale P hXp]
      field_simp [hlogZ.ne']
    _ ≤ (cr * (Real.log X / Real.log (zScale X))) *
        numeratorSmallCertificateMass m P X b :=
      mul_le_mul_of_nonneg_left hsmall (mul_nonneg hcr.le (div_nonneg hlogX hlogZ.le))
    _ ≤ selectedStructuralMass m P X b := hstruct
    _ ≤ prePrimeStructuralMass m P X b :=
      selectedStructuralMass_le_prePrimeStructuralMass m P X b hXp hb

/-! ## Comparison of `μ_b` with `𝒫_X 𝓜_b` -/

/-- The residue `-(d₋ d₊)⁻¹ mod m rad(e)`, and `1` if `d₋ d₊` is not invertible. -/
noncomputable def prePrimeResidueTotal (m : ℕ) (j : FamilyPrePrimeIndex) : ℕ :=
  if h : Nat.Coprime (j.dminus * j.dplus) (m * j.E.rho) then prePrimeResidue m j h else 1

/-- The large primes of a triple `j`, and `∅` if `d₋ d₊` is not invertible modulo
`m rad(e)`. -/
noncomputable def prePrimePrimeValuesTotal (m : ℕ) (P : Params) (X : ℝ)
    (j : FamilyPrePrimeIndex) : Finset ℕ :=
  if h : Nat.Coprime (j.dminus * j.dplus) (m * j.E.rho) then
    prePrimePrimeValues m P X j h else ∅

/-- The pairs `(j, p)` of a triple `j = (e, d₋, d₊)` and one of its large primes. -/
noncomputable def prePrimePairs (m : ℕ) (P : Params) (X : ℝ) (Pz b : ℕ) :
    Finset (Sigma fun _j : FamilyPrePrimeIndex => ℕ) :=
  (prePrimeFinset m P X Pz b).sigma (prePrimePrimeValuesTotal m P X)

theorem prePrimePairs_image_eq_indexFinset (m : ℕ) (hm : 0 < m) (P : Params)
    (X : ℝ) (Pz b : ℕ) (hX : 0 < X) :
    (prePrimePairs m P X Pz b).image familyPrePrimePairToIndex =
      indexFinset m P X Pz b := by
  ext i
  constructor
  · intro hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hj, hp⟩ := Finset.mem_sigma.mp ht
    have hpre := (mem_prePrimeFinset_iff m P X Pz b t.1 hX).mp hj
    unfold prePrimePrimeValuesTotal at hp
    rw [dif_pos hpre.dd_coprime_mrho] at hp
    exact (mem_indexFinset_iff m P X Pz b _ hX).mpr
      ((withPrime_static_iff m hm P X Pz b hX t.1 hpre t.2).mpr hp)
  · intro hi
    have h := (mem_indexFinset_iff m P X Pz b i hX).mp hi
    let j : FamilyPrePrimeIndex := ⟨i.E, i.dminus, i.dplus⟩
    have hj : PrePrimeMem m P X Pz b j :=
      { s_pos := h.s_pos, s_le_S := h.s_le_S, r_gt := h.r_gt, r_le := h.r_le,
        dminus_pos := h.dminus_pos, dminus_le_U := h.dminus_le_U,
        dminus_dvd_Pz := h.dminus_dvd_Pz, dminus_squarefree := h.dminus_squarefree,
        dminus_odd := h.dminus_odd, base_cong := h.base_cong,
        dplus_pos := h.dplus_pos, dplus_squarefree := h.dplus_squarefree,
        dd_le_Y := h.dd_le_Y, dplus_coprime_Pz := h.dplus_coprime_Pz,
        rho_coprime_m := h.rho_coprime_m, dd_coprime_mrho := h.dd_coprime_mrho }
    have hjI := (mem_prePrimeFinset_iff m P X Pz b j hX).mpr hj
    have hp : i.p ∈ prePrimePrimeValuesTotal m P X j := by
      rw [prePrimePrimeValuesTotal, dif_pos hj.dd_coprime_mrho]
      apply (withPrime_static_iff m hm P X Pz b hX j hj i.p).mp
      simpa only [j, FamilyPrePrimeIndex.withPrime] using h
    exact Finset.mem_image.mpr ⟨⟨j, i.p⟩, Finset.mem_sigma.mpr ⟨hjI, hp⟩,
      by simp only [familyPrePrimePairToIndex, FamilyPrePrimeIndex.withPrime, j]⟩

/-- `μ_b = ∑_j (1/d₊) ∑_p 1/p`, the inner sum over the large primes of `j = (e, d₋, d₊)`. -/
theorem indexMass_eq_prePrimeFibers (m : ℕ) (hm : 0 < m) (P : Params)
    (X : ℝ) (Pz b : ℕ) (hX : 0 < X) :
    (∑ i ∈ indexFinset m P X Pz b, (1 : ℝ) / i.q) =
      ∑ j ∈ prePrimeFinset m P X Pz b,
        ((1 : ℝ) / j.dplus) * Estimates.btRecip P X (m * j.E.rho) (prePrimeResidueTotal m j) := by
  rw [← prePrimePairs_image_eq_indexFinset m hm P X Pz b hX,
    Finset.sum_image (fun a _ b _ h => familyPrePrimePairToIndex_injective h)]
  unfold prePrimePairs
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  have hpre := (mem_prePrimeFinset_iff m P X Pz b j hX).mp hj
  rw [prePrimeResidueTotal, dif_pos hpre.dd_coprime_mrho]
  unfold prePrimePrimeValuesTotal
  rw [dif_pos hpre.dd_coprime_mrho]
  change (∑ p ∈ prePrimePrimeValues m P X j hpre.dd_coprime_mrho,
    (1 : ℝ) / (j.dplus * p : ℕ)) = _
  unfold Estimates.btRecip prePrimePrimeValues
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => by push_cast; ring)

/-- `μ_b ≥ 𝒫_X 𝓜_b - 𝒢`. -/
theorem indexMass_ge_main_sub_error (m : ℕ) (hm : 0 < m) (P : Params)
    (X : ℝ) (b : ℕ) (hX : 0 < X) :
    prePrimeStructuralMass m P X b * Estimates.btRecip P X 1 0 -
      (∑ j ∈ prePrimeFinset m P X (Estimates.roughModulus X) b,
        ((1 : ℝ) / j.dplus) * Estimates.reducedClassPrimeErrorMax P X (m * j.E.rho)) ≤
      ∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q := by
  rw [indexMass_eq_prePrimeFibers m hm P X _ b hX]
  unfold prePrimeStructuralMass
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hpre := (mem_prePrimeFinset_iff m P X (Estimates.roughModulus X) b j hX).mp hj
  have hres : prePrimeResidueTotal m j = prePrimeResidue m j hpre.dd_coprime_mrho := by
    rw [prePrimeResidueTotal, dif_pos hpre.dd_coprime_mrho]
  have hcop : Nat.Coprime (prePrimeResidueTotal m j) (m * j.E.rho) := by
    rw [hres]
    exact prePrimeResidue_coprime _ _ _
  have hpos : 0 < m * j.E.rho :=
    Nat.mul_pos hm (Nat.pos_of_ne_zero j.E.rho_squarefree.ne_zero)
  have herr := Estimates.reducedClassPrimeError_le_max_of_coprime
    (P := P) (X := X) hpos hcop
  have hneg := (neg_le_neg herr).trans (neg_abs_le _)
  have hpoint :
      (1 / (Nat.totient (m * j.E.rho) : ℝ)) * Estimates.btRecip P X 1 0 -
        Estimates.reducedClassPrimeErrorMax P X (m * j.E.rho) ≤
      Estimates.btRecip P X (m * j.E.rho) (prePrimeResidueTotal m j) := by
    linarith
  convert mul_le_mul_of_nonneg_left hpoint (show 0 ≤ (1 : ℝ) / j.dplus by positivity)
    using 1
  ring

/-- `|μ_b - 𝒫_X 𝓜_b| ≤ 𝒢`. -/
theorem indexMass_abs_sub_main (m : ℕ) (hm : 0 < m) (P : Params)
    (X : ℝ) (b : ℕ) (hX : 0 < X) :
    |(∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q) -
      prePrimeStructuralMass m P X b * Estimates.btRecip P X 1 0| ≤
      prePrimeError m P X b := by
  rw [indexMass_eq_prePrimeFibers m hm P X _ b hX]
  unfold prePrimeStructuralMass prePrimeError
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hpre := (mem_prePrimeFinset_iff m P X (Estimates.roughModulus X) b j hX).mp hj
  have hres : prePrimeResidueTotal m j = prePrimeResidue m j hpre.dd_coprime_mrho := by
    rw [prePrimeResidueTotal, dif_pos hpre.dd_coprime_mrho]
  have hcop : Nat.Coprime (prePrimeResidueTotal m j) (m * j.E.rho) := by
    rw [hres]
    exact prePrimeResidue_coprime _ _ _
  have hpos : 0 < m * j.E.rho :=
    Nat.mul_pos hm (Nat.pos_of_ne_zero j.E.rho_squarefree.ne_zero)
  have herr := Estimates.reducedClassPrimeError_le_max_of_coprime
    (P := P) (X := X) hpos hcop
  have heq :
      ((1 : ℝ) / j.dplus) * Estimates.btRecip P X (m * j.E.rho) (prePrimeResidueTotal m j) -
        ((1 : ℝ) / j.dplus) / (Nat.totient (m * j.E.rho) : ℝ) *
          Estimates.btRecip P X 1 0 =
      ((1 : ℝ) / j.dplus) *
        (Estimates.btRecip P X (m * j.E.rho) (prePrimeResidueTotal m j) -
          (1 / (Nat.totient (m * j.E.rho) : ℝ)) * Estimates.btRecip P X 1 0) := by ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / j.dplus)]
  exact mul_le_mul_of_nonneg_left herr (by positivity)

/-- `μ_b/𝓜_b = 𝒫_X + o(1)`, uniformly in reduced `b`. -/
theorem indexMass_relative_error (m : ℕ) (hm : 0 < m) (P : Params)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      |(∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q) /
          prePrimeStructuralMass m P X b - Estimates.btRecip P X 1 0| ≤ ε := by
  obtain ⟨c, XM, hc, hM⟩ := prePrimeStructuralMass_lower m hm P
  obtain ⟨C, XE, hC, hE⟩ := prePrimeError_eventually_bounded m hm P
  refine ⟨max (max XM XE) (Real.exp (max 1 (C / (c * ε)))), ?_⟩
  intro X hX hX1 b hb
  have hXM : XM ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXE : XE ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hXp : 0 < X := zero_lt_one.trans hX1
  have hlog : max 1 (C / (c * ε)) ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXp).mpr ((le_max_right _ _).trans hX)
  have hlog1 : 1 ≤ Real.log X := (le_max_left _ _).trans hlog
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog1
  have hcube : Real.log X ≤ (Real.log X) ^ 3 := by
    have hsq : 1 ≤ (Real.log X) ^ 2 := one_le_pow₀ hlog1
    nlinarith
  have hmain := hM X hXM hX1 b hb
  have hMp : 0 < prePrimeStructuralMass m P X b :=
    lt_of_lt_of_le (mul_pos hc (pow_pos hlogpos _)) hmain
  have hsmall : C ≤ ε * prePrimeStructuralMass m P X b := by
    have hratio : C / (c * ε) ≤ Real.log X := (le_max_right _ _).trans hlog
    have hlinear : C ≤ c * ε * Real.log X := by
      simpa only [mul_comm] using (div_le_iff₀ (mul_pos hc hε)).mp hratio
    have hscaled := mul_le_mul_of_nonneg_left hcube (mul_nonneg hc.le hε.le)
    have hmass := mul_le_mul_of_nonneg_left hmain hε.le
    nlinarith
  have hbound := (indexMass_abs_sub_main m hm P X b hXp).trans
    ((hE X hXE hX1 b).trans hsmall)
  let W : ℝ := ∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q
  let M := prePrimeStructuralMass m P X b
  have hMn : M ≠ 0 := hMp.ne'
  change |W / M - Estimates.btRecip P X 1 0| ≤ ε
  have heq : W / M - Estimates.btRecip P X 1 0 =
      (W - M * Estimates.btRecip P X 1 0) / M := by field_simp
  rw [heq, abs_div, abs_of_pos hMp]
  exact (div_le_iff₀ hMp).mpr hbound

/-- `μ_b/𝓜_b = log((1 - σ)/β) + o(1)`, uniformly in reduced `b`. -/
theorem indexMass_ratio (m : ℕ) (hm : 0 < m) (P : Params)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      |(∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q) /
          prePrimeStructuralMass m P X b - Real.log ((1 - P.σ) / P.β)| ≤ ε := by
  obtain ⟨XM, hM⟩ := indexMass_relative_error m hm P (ε / 2) (half_pos hε)
  obtain ⟨XP, hP⟩ := PrimeEstimates.Mertens.primeRecipWindow_limit P (ε / 2) (half_pos hε)
  refine ⟨max (max XM XP) 2, ?_⟩
  intro X hX b hb
  have hXM : XM ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hXP : XP ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hX1 : 1 < X := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hX)
  have hmass := hM X hXM hX1 b hb
  have hprime := hP X hXP
  rw [← Estimates.btRecip_mod_one_eq_primeRecipWindow (a := 0)] at hprime
  exact (abs_sub_le _ (Estimates.btRecip P X 1 0) _).trans (by linarith)

/-! ## Lower bound for `μ_b` -/

/-- Lower half of Proposition 6.6: `μ_b ≫ (log X)³`, uniformly in reduced `b`. The main
term `𝒫_X 𝓜_b` is `≫ (log X)³` and the error `𝒢` is `O(1)`. -/
theorem indexMass_lower (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → 1 < X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      c * (Real.log X) ^ 3 ≤
        ∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q := by
  obtain ⟨cs, Xs, hcs, hs⟩ := prePrimeStructuralMass_lower m hm P
  obtain ⟨cp, Xp, hcp, hp⟩ :=
    PrimeEstimates.primeRecipWindow_mertens_lower P
  obtain ⟨C, XE, hC, hE⟩ := prePrimeError_eventually_bounded m hm P
  let c := cs * cp / 2
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, max (max (max Xs Xp) XE) (Real.exp (max 1 (C / c))), hc, ?_⟩
  intro X hX hXgt b hb
  have hXp : 0 < X := zero_lt_one.trans hXgt
  have hXs : Xs ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hX))
  have hXprime : Xp ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hX))
  have hXE : XE ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hlog : max 1 (C / c) ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXp).mpr ((le_max_right _ _).trans hX)
  have hlog1 : 1 ≤ Real.log X := (le_max_left _ _).trans hlog
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog1
  have hcube : Real.log X ≤ (Real.log X) ^ 3 := by
    have hsq : 1 ≤ (Real.log X) ^ 2 := one_le_pow₀ hlog1
    calc
      Real.log X ≤ Real.log X * (Real.log X) ^ 2 :=
        le_mul_of_one_le_right hlogpos.le hsq
      _ = (Real.log X) ^ 3 := by ring
  have hClog : C ≤ c * (Real.log X) ^ 3 := by
    have hratio : C / c ≤ Real.log X := (le_max_right _ _).trans hlog
    have hClinear : C ≤ c * Real.log X := by
      nlinarith [(div_le_iff₀ hc).mp hratio]
    exact hClinear.trans (mul_le_mul_of_nonneg_left hcube hc.le)
  have hmass : 0 ≤ prePrimeStructuralMass m P X b :=
    Finset.sum_nonneg (fun j _ => by positivity)
  have hmain : 2 * c * (Real.log X) ^ 3 ≤
      prePrimeStructuralMass m P X b * Estimates.btRecip P X 1 0 := by
    calc
      2 * c * (Real.log X) ^ 3 = (cs * (Real.log X) ^ 3) * cp := by dsimp [c]; ring
      _ ≤ prePrimeStructuralMass m P X b * cp :=
        mul_le_mul_of_nonneg_right (hs X hXs hXgt b hb) hcp.le
      _ ≤ prePrimeStructuralMass m P X b * Estimates.btRecip P X 1 0 :=
        mul_le_mul_of_nonneg_left (hp X hXprime) hmass
  have herr := (hE X hXE hXgt b).trans hClog
  have htransfer := indexMass_ge_main_sub_error m hm P X b hXp
  change prePrimeStructuralMass m P X b * Estimates.btRecip P X 1 0 -
    prePrimeError m P X b ≤ _ at htransfer
  linarith

/-! ## Upper bound for `𝓜_b` -/

/-- Upper half of `V(e, d₋) ≍ log X / log z`, uniformly in `d₋` and `rad(e)`. -/
theorem numeratorDplusReciprocal_upper (m : ℕ) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ d ρ : ℕ,
      numeratorDplusReciprocal m P X d ρ ≤ C * (Real.log X / Real.log (zScale X)) := by
  obtain ⟨_, C, X₀, _, hC, h⟩ := RoughReciprocal.roughInitial_two_sided P.σ 0 P.σ_pos
  refine ⟨C, max X₀ 1, hC, ?_⟩
  intro X hX d ρ
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  obtain ⟨_, _, _, _, _, hup, _⟩ := h X ((le_max_left _ _).trans hX) 1 (by simp)
  refine le_trans ?_ hup
  unfold numeratorDplusReciprocal numeratorDplusRange Estimates.roughInitial
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨htI, htSq, htP, _⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht1, htmax⟩ := Finset.mem_Icc.mp htI
    have hY : 0 ≤ YScale P X := Real.rpow_nonneg hXp.le _
    have hYd : YScale P X / (d : ℝ) ≤ X ^ P.σ := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simpa [YScale] using hY
      · exact div_le_self hY (by exact_mod_cast hd)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ht1, htmax.trans
      (Nat.floor_le_floor hYd)⟩, htSq, htP, ?_⟩
    simp [Estimates.auxiliaryModulus]
  · intro t _ _
    positivity

/-- `𝓜_b` is the nested sum (21) over small divisors `d₋`, divisors `e = r s²` with
`b ≡ -m e (mod d₋)`, and rough cofactors `d₊`. -/
theorem prePrimeStructuralMass_eq_selected (m : ℕ) (P : Params) (X : ℝ) (b : ℕ)
    (hX : 0 < X) (hb : Nat.Coprime b (Estimates.roughModulus X)) :
    prePrimeStructuralMass m P X b = selectedStructuralMass m P X b := by
  refine le_antisymm ?_ (selectedStructuralMass_le_prePrimeStructuralMass m P X b hX hb)
  let J := prePrimeFinset m P X (Estimates.roughModulus X) b
  let T := structuralTuples m P X b
  let g : FamilyPrePrimeIndex → StructuralTuple :=
    fun j => ⟨(j.E.s, j.dminus), ⟨j.E.r, j.dplus⟩⟩
  let w : StructuralTuple → ℝ :=
    fun t => ((1 : ℝ) / t.2.2) / Nat.totient (m * (t.2.1 * t.1.1))
  have hsel : selectedStructuralMass m P X b = ∑ t ∈ T, w t := by
    unfold selectedStructuralMass numeratorDplusReciprocal
    simp only [T, structuralTuples]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro sd _
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro dp _
    simp only [w]
    rw [show m * sd.1 * r = m * (r * sd.1) by ring]
    ring
  have hinj : Set.InjOn g (J : Set FamilyPrePrimeIndex) := by
    intro j _ k _ h
    simp only [g, Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq] at h
    obtain ⟨⟨hs, hd⟩, hr, hp⟩ := h
    cases j with
    | mk Ej dj pj =>
      cases k with
      | mk Ek dk pk =>
        cases Ej
        cases Ek
        simp_all
  have hmap : ∀ j ∈ J, g j ∈ T := by
    intro j hj
    have h := (mem_prePrimeFinset_iff m P X _ b j hX).mp hj
    have hsS : 0 ≤ SScale P X := Real.rpow_nonneg hX.le _
    have hds : Nat.Coprime j.dminus j.E.s :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _)
        (Nat.Coprime.coprime_dvd_right (dvd_mul_left j.E.s (m * j.E.r))
          (by simpa [ExactDivisor.rho, Nat.mul_assoc] using h.dd_coprime_mrho))
    have hdm : Nat.Coprime j.dminus m :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _)
        (Nat.Coprime.coprime_dvd_right (dvd_mul_right m _) h.dd_coprime_mrho)
    have hsm : Nat.Coprime j.E.s m :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) h.rho_coprime_m
    have hrm : Nat.Coprime j.E.r m :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) h.rho_coprime_m
    have hbd : Nat.Coprime b j.dminus := hb.coprime_dvd_right h.dminus_dvd_Pz
    have hcoef : Nat.Coprime (m * j.E.s ^ 2) j.dminus := Nat.coprime_mul_iff_left.mpr
      ⟨hdm.symm, (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) _ _).mpr hds.symm⟩
    have hbase : j.dminus ∣ b + m * j.E.r * j.E.s ^ 2 := by
      have := Nat.modEq_zero_iff_dvd.mp h.base_cong
      simpa [ExactDivisor.e, Nat.mul_assoc] using this
    have hcong := (numeratorBaseResidueTotal_cong_iff m b j.dminus j.E.s j.E.r
      h.dminus_pos hbd hcoef).mpr hbase
    have hdR : (0 : ℝ) < j.dminus := by exact_mod_cast h.dminus_pos
    have hdpY : (j.dplus : ℝ) ≤ YScale P X / j.dminus := by
      rw [le_div_iff₀ hdR]
      nlinarith [h.dd_le_Y]
    have hrpos : 0 < j.E.r := Nat.pos_of_ne_zero j.E.r_squarefree.ne_zero
    refine Finset.mem_sigma.mpr ⟨?_, Finset.mem_sigma.mpr ⟨?_, ?_⟩⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, j.E.s_squarefree,
        h.dminus_dvd_Pz, h.dminus_odd, hds⟩, hsm, hdm⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨h.s_pos, Nat.le_floor h.s_le_S⟩,
          Finset.mem_Icc.mpr ⟨h.dminus_pos, Nat.le_floor h.dminus_le_U⟩⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hrpos, Nat.le_floor ?_⟩, ?_⟩, j.E.r_squarefree,
        Nat.coprime_mul_iff_right.mpr ⟨j.E.coprime_rs, hrm⟩, hcong⟩
      · simpa [phiProgressionU1] using h.r_le
      · simpa [phiProgressionU0] using h.r_gt
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h.dplus_pos, Nat.le_floor hdpY⟩,
        h.dplus_squarefree, h.dplus_coprime_Pz, ?_⟩
      exact Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) h.dd_coprime_mrho
  have hsub : J.image g ⊆ T := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact hmap j hj
  calc
    prePrimeStructuralMass m P X b = ∑ j ∈ J, w (g j) := rfl
    _ = ∑ t ∈ J.image g, w t := (Finset.sum_image hinj).symm
    _ ≤ ∑ t ∈ T, w t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => by positivity)
    _ = _ := hsel.symm

/-- Bounding `V(e, d₋)` termwise: `𝓜_b ≪ (log X / log z) Σ_b`. -/
theorem selectedStructuralMass_le_rough_smallMass (m : ℕ) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ b : ℕ,
      selectedStructuralMass m P X b ≤
        C * (Real.log X / Real.log (zScale X)) * numeratorSmallCertificateMass m P X b := by
  obtain ⟨C, X₀, hC, hV⟩ := numeratorDplusReciprocal_upper m P
  refine ⟨C, X₀, hC, ?_⟩
  intro X hX b
  unfold selectedStructuralMass numeratorSmallCertificateMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro sd _
  unfold numeratorPhiAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  calc
    (1 / (Nat.totient (m * sd.1 * r) : ℝ)) * numeratorDplusReciprocal m P X sd.2 (r * sd.1) ≤
        (1 / (Nat.totient (m * sd.1 * r) : ℝ)) * (C * (Real.log X / Real.log (zScale X))) :=
      mul_le_mul_of_nonneg_left (hV X hX _ _) (by positivity)
    _ = _ := by ring

/-- `𝓜_b ≍ (log X / log z) Σ_b`, uniformly in reduced `b`, where `Σ_b` is the sum of
Lemma 6.5. -/
theorem prePrimeStructuralMass_comparable_saturation (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      c * (Real.log X / Real.log (zScale X)) * saturationMass m P X b ≤
          prePrimeStructuralMass m P X b ∧
        prePrimeStructuralMass m P X b ≤
          C * (Real.log X / Real.log (zScale X)) * saturationMass m P X b := by
  obtain ⟨c, Xl, hc, hl⟩ := selectedStructuralMass_ge_rough_smallMass m hm P
  obtain ⟨C, Xu, hC, hu⟩ := selectedStructuralMass_le_rough_smallMass m P
  refine ⟨c, C, max (max Xl Xu) 2, hc, hC, ?_⟩
  intro X hX b hb
  have hX1 : 1 < X := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hX)
  have hXp : 0 < X := zero_lt_one.trans hX1
  rw [saturationMass_eq_certificate m P X b hb,
    prePrimeStructuralMass_eq_selected m P X b hXp hb]
  exact ⟨hl X ((le_max_left _ _).trans ((le_max_left _ _).trans hX)) hX1 b,
    hu X ((le_max_right _ _).trans ((le_max_left _ _).trans hX)) b⟩

/-- `𝓜_b ≪ (log X)³`, uniformly in reduced `b`. -/
theorem prePrimeStructuralMass_upper (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      prePrimeStructuralMass m P X b ≤ C * (Real.log X) ^ 3 := by
  obtain ⟨_, C, X₁, _, hC, hcmp⟩ := prePrimeStructuralMass_comparable_saturation m hm P
  obtain ⟨_, CS, XS, _, hCS, hS⟩ := saturationMass_two_sided m hm P
  refine ⟨C * CS, max (max X₁ XS) (Real.exp 2), mul_pos hC hCS, ?_⟩
  intro X hX b hb
  have hXe : Real.exp 2 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le hXe
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1.le
  have hlogz : 0 < Real.log (zScale X) := Estimates.log_zScale_pos_of_exp_two_le hXe
  have hM := (hcmp X ((le_max_left _ _).trans ((le_max_left _ _).trans hX)) b hb).2
  have hSb := (hS X ((le_max_right _ _).trans ((le_max_left _ _).trans hX)) b hb).2
  calc
    prePrimeStructuralMass m P X b ≤
        C * (Real.log X / Real.log (zScale X)) * saturationMass m P X b := hM
    _ ≤ C * (Real.log X / Real.log (zScale X)) *
        (CS * (Real.log X) ^ 2 * Real.log (zScale X)) :=
      mul_le_mul_of_nonneg_left hSb (mul_nonneg hC.le (div_nonneg hlogX hlogz.le))
    _ = C * CS * (Real.log X) ^ 3 := by field_simp

/-! ## Upper bound for `μ_b` -/

/-- `μ_b = (𝒫_X + o(1)) 𝓜_b`, uniformly in reduced `b`. -/
theorem indexMass_window_comparison (m : ℕ) (hm : 0 < m) (P : Params)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ b : ℕ, Nat.Coprime b (Estimates.roughModulus X) →
      (Estimates.btRecip P X 1 0 - ε) * prePrimeStructuralMass m P X b ≤
          ∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q ∧
        (∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q) ≤
          (Estimates.btRecip P X 1 0 + ε) * prePrimeStructuralMass m P X b := by
  obtain ⟨XR, hR⟩ := indexMass_relative_error m hm P ε hε
  obtain ⟨c, XM, hc, hM⟩ := prePrimeStructuralMass_lower m hm P
  refine ⟨max (max XR XM) 2, ?_⟩
  intro X hX b hb
  have hX1 : 1 < X := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hX)
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hMb := hM X ((le_max_right _ _).trans ((le_max_left _ _).trans hX)) hX1 b hb
  have hMpos : 0 < prePrimeStructuralMass m P X b :=
    (mul_pos hc (pow_pos hlogX 3)).trans_le hMb
  have hrel := abs_le.mp (hR X ((le_max_left _ _).trans ((le_max_left _ _).trans hX)) hX1 b hb)
  constructor
  · have h := hrel.1
    have h' : Estimates.btRecip P X 1 0 - ε ≤
        (∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q) /
          prePrimeStructuralMass m P X b := by linarith
    exact (le_div_iff₀ hMpos).mp h'
  · have h := hrel.2
    have h' : (∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q) /
          prePrimeStructuralMass m P X b ≤ Estimates.btRecip P X 1 0 + ε := by linarith
    exact (div_le_iff₀ hMpos).mp h'

/-- Upper half of Proposition 6.6: `μ_b ≤ (𝒫_X + o(1)) 𝓜_b ≪ (log X)³`, uniformly in
reduced `b`. -/
theorem indexMass_upper (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      (∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q) ≤
        C * (Real.log X) ^ 3 := by
  obtain ⟨XW, hW⟩ := indexMass_window_comparison m hm P 1 one_pos
  obtain ⟨XP, hP⟩ := PrimeEstimates.Mertens.primeRecipWindow_limit P 1 one_pos
  obtain ⟨CM, XM, hCM, hM⟩ := prePrimeStructuralMass_upper m hm P
  have hratio : 1 < (1 - P.σ) / P.β :=
    (one_lt_div P.β_pos).mpr P.β_lt_one_sub_σ
  have hL : 0 < Real.log ((1 - P.σ) / P.β) := Real.log_pos hratio
  refine ⟨(Real.log ((1 - P.σ) / P.β) + 2) * CM, max (max XW XP) XM,
    mul_pos (by linarith) hCM, ?_⟩
  intro X hX b hb
  have hw := (hW X ((le_max_left _ _).trans ((le_max_left _ _).trans hX)) b hb).2
  have hp := hP X ((le_max_right _ _).trans ((le_max_left _ _).trans hX))
  rw [← Estimates.btRecip_mod_one_eq_primeRecipWindow (a := 0)] at hp
  have hPX : Estimates.btRecip P X 1 0 + 1 ≤ Real.log ((1 - P.σ) / P.β) + 2 := by
    linarith [(abs_le.mp hp).2]
  have hPX0 : 0 ≤ Estimates.btRecip P X 1 0 + 1 := by
    have : 0 ≤ Estimates.btRecip P X 1 0 := by
      unfold Estimates.btRecip
      exact Finset.sum_nonneg (fun p _ => by positivity)
    linarith
  have hMb := hM X ((le_max_right _ _).trans hX) b hb
  have hMnn : 0 ≤ prePrimeStructuralMass m P X b :=
    Finset.sum_nonneg (fun j _ => by positivity)
  calc
    _ ≤ (Estimates.btRecip P X 1 0 + 1) * prePrimeStructuralMass m P X b := hw
    _ ≤ (Real.log ((1 - P.σ) / P.β) + 2) * (CM * Real.log X ^ 3) :=
      mul_le_mul hPX hMb hMnn (by linarith)
    _ = _ := by ring

/-- Proposition 6.6: `μ_b ≍ (log X)³`, uniformly in reduced `b`. -/
theorem indexMass_two_sided (m : ℕ) (hm : 0 < m) (P : Params) :
    ∃ c C X₀ : ℝ, 0 < c ∧ 0 < C ∧ ∀ X : ℝ, X₀ ≤ X → ∀ b : ℕ,
      Nat.Coprime b (Estimates.roughModulus X) →
      c * (Real.log X) ^ 3 ≤
          ∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q ∧
        (∑ i ∈ indexFinset m P X (Estimates.roughModulus X) b, (1 : ℝ) / i.q) ≤
          C * (Real.log X) ^ 3 := by
  obtain ⟨c, Xl, hc, hl⟩ := indexMass_lower m hm P
  obtain ⟨C, Xu, hC, hu⟩ := indexMass_upper m hm P
  refine ⟨c, C, max (max Xl Xu) 2, hc, hC, ?_⟩
  intro X hX b hb
  have hX1 : 1 < X := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hX)
  exact ⟨hl X ((le_max_left _ _).trans ((le_max_left _ _).trans hX)) hX1 b hb,
    hu X ((le_max_right _ _).trans ((le_max_left _ _).trans hX)) b hb⟩

end ErdosStraus.FixedNumeratorFamily
