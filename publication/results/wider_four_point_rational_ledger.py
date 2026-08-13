#!/usr/bin/env python3
"""Exact rational ledger for the wider-window four-point route.

This file checks only terminal rational arithmetic.  It performs no floating
point evaluation, root search, interval grid, or numerical optimization.  The
analytic obligations that remain are stated in ``WIDER_FOUR_POINT_ROUTE.md``.
"""

from fractions import Fraction as Q
from pathlib import Path
import re
import sys


def require(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)


def render() -> str:
    rho = Q(1, 8)
    localization_threshold = Q(1815107, 989072150)
    cos_lower = Q(12359, 12800)
    negative_sine_loss = Q(129, 1280)

    # On |e-epsilon_n| <= 1/8, the exact derivative lower bound is
    # ((3n-1/16) C - 129/1280).  The local denominator is bounded by
    # (44n/7+21/40)^2 and 2 cos(theta) >= 3/2.
    slope_denominators = {
        1: Q(930982144, 82354251),
        2: Q(3442403584, 169559355),
        3: Q(2513265408, 85588153),
        4: Q(13223160064, 343969563),
        5: Q(20492495104, 431174667),
        6: Q(9782600448, 172793257),
    }
    local_slopes = {}
    for n, denominator in slope_denominators.items():
        derivative_lower = (Q(3 * n) - Q(1, 16)) * cos_lower - negative_sine_loss
        local_x_upper = Q(44 * n, 7) + Q(21, 40)
        slope = Q(3, 2) * derivative_lower / local_x_upper**2
        require(slope == Q(1) / denominator, f"exact local slope n={n}")
        local_slopes[n] = slope

    # Positive root intervals n=1,...,5, outside the radius rho.
    positive_outside = []
    for n in range(1, 6):
        derivative_lower = (Q(3 * n) - Q(1, 16)) * cos_lower - negative_sine_loss
        full_denominator = Q(22 * (2 * n + 1), 7) ** 2
        bound = Q(3, 2) * derivative_lower * rho / full_denominator
        require(bound > localization_threshold, f"positive outside n={n}")
        positive_outside.append(bound)

    # Alternating zero-free intervals ending at 2m*pi for m<=5.
    zero_free = []
    for m in range(1, 6):
        full_denominator = Q(44 * m, 7) ** 2
        bound = Q(3, 2) * Q(592688, 490449) / full_denominator
        require(bound >= localization_threshold, f"zero-free m={m}")
        zero_free.append(bound)

    # The last interval [11*pi,12*pi] is split at e=-rho.  Farther left,
    # x |sin(e/2)| >= 33/17.  In the short terminal segment, integrate the
    # n=6 derivative lower bound over rho.
    last_denominator = Q(264, 7) ** 2
    last_far = Q(3, 2) * Q(33, 17) / last_denominator
    derivative_six = (Q(18) - Q(1, 16)) * cos_lower - negative_sine_loss
    last_short = Q(3, 2) * derivative_six * rho / last_denominator
    require(last_far > localization_threshold, "last zero-free far part")
    require(last_short > localization_threshold, "last zero-free short part")

    # Exact lower test for epsilon_2.  The sine/cosine rational estimate gives
    # tan(11/120) <= u/(1-u^2/2), while pi < 22/7.
    eps_two_test = Q(11, 60)
    u = eps_two_test / 2
    root_test_upper = (Q(88, 7) + eps_two_test) * u / (1 - u**2 / 2)
    require(root_test_upper < Q(6, 5), "epsilon_2 > 11/60 test")

    # Exact upper test for epsilon_6.  Use pi > 157/50, tan(1/30) > 1/30,
    # and kappa <= 49/40.  Strict monotonicity of the root equation then gives
    # epsilon_6 < 1/15.
    eps_six_upper = Q(1, 15)
    root_six_test_lower = (Q(12) * Q(157, 50) + eps_six_upper) * Q(1, 30)
    require(root_six_test_lower == Q(2831, 2250), "epsilon_6 test identity")
    require(root_six_test_lower > Q(49, 40), "epsilon_6 < 1/15 test")

    # Weighted Cauchy with local slopes 1/d_n.  This loop mirrors the Lean
    # Fin 6^3 budget theorem exactly: all additive rows use 11/60 because
    # 2*epsilon_3-epsilon_6 > 1/4-1/15 = 11/60, while nonadditive rows use 1.
    full_rows = []
    delta_wide = Q(
        2810232522752,
        834437357315980975,
    )
    for i in range(1, 7):
        for j in range(1, 7):
            for k in range(1, 7):
                if i + j == k:
                    separation = eps_two_test
                else:
                    separation = Q(1)
                denominator = (
                    slope_denominators[i] ** 2
                    + slope_denominators[j] ** 2
                    + slope_denominators[k] ** 2
                )
                bound = separation**2 / denominator
                require(bound >= delta_wide, f"root triple {(i, j, k)}")
                full_rows.append(((i, j, k), bound))
    require(len(full_rows) == 216, "all Fin 6^3 root triples covered")

    # Energy below delta_wide makes each correlation smaller than the exact
    # weakest refined zero-free exclusion threshold 1815107/989072150.
    require(delta_wide < localization_threshold**2, "localization activation")

    endpoint_gap = Q(102239, 592688)
    exact_gain = delta_wide * endpoint_gap**2 / 8
    public_eta = Q(1, 79828975)
    require(public_eta == exact_gain, "public eta equals selected exact gain")
    require(public_eta > Q(1, 233423794), "strict improvement over three-point eta")

    endpoint_supremum = localization_threshold**2 * endpoint_gap**2 / 8
    require(
        endpoint_supremum == Q(25097204303521, 2003484094270714880000),
        "endpoint activation supremum identity",
    )
    require(public_eta < endpoint_supremum, "public eta below strict supremum")
    require(
        endpoint_supremum <= Q(1, 79828974),
        "next unit fraction excluded by method ceiling",
    )

    weakest_local = min(local_slopes.values())
    weakest_positive = min(positive_outside)
    weakest_zero_free = min(zero_free)
    require(
        weakest_zero_free == localization_threshold,
        "threshold equals exact weakest zero-free exclusion",
    )
    weakest_budget = min(bound for _, bound in full_rows)
    weighted_budget_ceiling = Q(
        9755468468368320337833317374859207102505001,
        1623000197669009639771565694101668583197612441600,
    )
    require(
        weakest_budget == weighted_budget_ceiling,
        "exact refined weighted-budget ceiling",
    )
    require(
        [triple for triple, bound in full_rows if bound == weakest_budget]
        == [(1, 5, 6), (5, 1, 6)],
        "refined weighted-budget minimizers",
    )
    require(delta_wide < weakest_budget, "selected delta below every budget")

    # Bind the exact arithmetic to the integrated Lean source rather than
    # certifying an unrelated copy of the constants.
    lean_root = (
        Path(__file__).parent
        / "sources"
        / "zeta-23-lean"
        / "Zeta23"
        / "StrictImprovement"
    )
    arithmetic_source = (lean_root / "WiderRootArithmetic.lean").read_text(
        encoding="utf-8"
    )
    constant_source = (lean_root / "WiderFourPointConstant.lean").read_text(
        encoding="utf-8"
    )
    endpoint_source = (lean_root / "ZetaWiderEndpointPassage.lean").read_text(
        encoding="utf-8"
    )
    ceiling_source = (lean_root / "WiderFixedInterfaceCeiling.lean").read_text(
        encoding="utf-8"
    )
    root_source = (lean_root.parent / "../Zeta23.lean").resolve().read_text(
        encoding="utf-8"
    )

    denominator_match = re.search(
        r"def widerSlopeDenominator : Fin 6 → ℝ :=\s*!\[(.*?)\]\s*\n\s*lemma",
        arithmetic_source,
        flags=re.DOTALL,
    )
    require(denominator_match is not None, "parse Lean slope denominators")
    denominator_pairs = [
        Q(int(a), int(b))
        for a, b in re.findall(r"(\d+)\s*/\s*(\d+)", denominator_match.group(1))
    ]
    require(
        denominator_pairs == [slope_denominators[n] for n in range(1, 7)],
        "Lean slope denominators equal exact ledger values",
    )

    delta_match = re.search(
        r"def widerDeltaLower : ℝ :=\s*(\d+)\s*/\s*(\d+)",
        constant_source,
    )
    eta_match = re.search(
        r"def widerEtaLower : ℝ :=\s*(\d+)\s*/\s*(\d+)",
        constant_source,
    )
    require(delta_match is not None, "parse Lean widerDeltaLower")
    require(eta_match is not None, "parse Lean widerEtaLower")
    require(
        Q(int(delta_match.group(1)), int(delta_match.group(2))) == delta_wide,
        "Lean widerDeltaLower equals selected endpoint-optimized value",
    )
    require(
        Q(int(eta_match.group(1)), int(eta_match.group(2))) == public_eta,
        "Lean widerEtaLower equals public unit fraction",
    )
    require(
        "+ (1 : ℝ) / 79828975 - outer" in endpoint_source,
        "public endpoint theorem uses optimized unit fraction",
    )
    threshold_match = re.search(
        r"def widerCorrelationThreshold : ℝ :=\s*(\d+)\s*/\s*(\d+)",
        arithmetic_source,
    )
    budget_ceiling_match = re.search(
        r"def widerWeightedBudgetCeiling : ℝ :=\s*(\d+)\s*/\s*(\d+)",
        constant_source,
    )
    require(threshold_match is not None, "parse Lean localization threshold")
    require(budget_ceiling_match is not None, "parse Lean budget ceiling")
    require(
        Q(int(threshold_match.group(1)), int(threshold_match.group(2)))
        == localization_threshold,
        "Lean localization threshold equals ledger value",
    )
    require(
        Q(int(budget_ceiling_match.group(1)), int(budget_ceiling_match.group(2)))
        == weighted_budget_ceiling,
        "Lean weighted budget ceiling equals ledger minimum",
    )
    require(
        re.search(
            r"def widerFixedDeltaCeiling : ℝ :=\s*widerWeightedBudgetCeiling",
            ceiling_source,
        )
        is not None,
        "ceiling theorem is bound to weighted budget ceiling",
    )
    require(
        "import Zeta23.StrictImprovement.ZetaWiderEndpointPassage" in root_source
        and "import Zeta23.StrictImprovement.WiderFixedInterfaceCeiling"
        in root_source,
        "root imports optimized endpoint and ceiling",
    )

    lines = [
        "WIDER_FOUR_POINT_RATIONAL_LEDGER PASS",
        f"radius={rho.numerator}/{rho.denominator}",
        f"localization_threshold={localization_threshold.numerator}/{localization_threshold.denominator}",
        f"weakest_local_slope={weakest_local.numerator}/{weakest_local.denominator}",
        f"weakest_positive_outside={weakest_positive.numerator}/{weakest_positive.denominator}",
        f"weakest_zero_free_m1_m5={weakest_zero_free.numerator}/{weakest_zero_free.denominator}",
        f"last_zero_free_far={last_far.numerator}/{last_far.denominator}",
        f"last_zero_free_short={last_short.numerator}/{last_short.denominator}",
        f"epsilon_two_test_upper={root_test_upper.numerator}/{root_test_upper.denominator}",
        f"epsilon_two_lower={eps_two_test.numerator}/{eps_two_test.denominator}",
        f"epsilon_six_test_lower={root_six_test_lower.numerator}/{root_six_test_lower.denominator}",
        f"epsilon_six_upper={eps_six_upper.numerator}/{eps_six_upper.denominator}",
        "root_triples_checked=216",
        f"weakest_budget_energy={weakest_budget.numerator}/{weakest_budget.denominator}",
        f"delta_1_6_candidate={delta_wide.numerator}/{delta_wide.denominator}",
        f"activation_slack={(localization_threshold**2-delta_wide).numerator}/{(localization_threshold**2-delta_wide).denominator}",
        f"endpoint_gap={endpoint_gap.numerator}/{endpoint_gap.denominator}",
        f"public_eta={public_eta.numerator}/{public_eta.denominator}",
        f"endpoint_activation_supremum={endpoint_supremum.numerator}/{endpoint_supremum.denominator}",
        "best_strict_unit_eta=1/79828975",
        "next_unit_eta_excluded=1/79828974",
        "lean_source_bindings=threshold,denominators,budget_ceiling,delta,eta,endpoint,ceiling,root",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    output = render()
    if len(sys.argv) == 2 and sys.argv[1] == "--verify-frozen-output":
        frozen = Path(__file__).with_name(
            "wider_four_point_rational_ledger_output.txt"
        ).read_text(encoding="utf-8")
        require(output == frozen, "frozen output mismatch")
        print(output, end="")
        return
    if len(sys.argv) != 1:
        raise SystemExit(
            "usage: wider_four_point_rational_ledger.py [--verify-frozen-output]"
        )
    print(output, end="")


if __name__ == "__main__":
    main()
