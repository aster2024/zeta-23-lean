#!/usr/bin/env python3
"""Exact ceilings for the refined width-six four-point interface.

The computation is entirely rational.  It uses the pre-rounding slope lower
bounds already present in the width-six localization argument, the frozen
refined separation-floor rule, radius 1/8, localization threshold
1815107/989072150, and
endpoint-gap lower bound.  It proves both the weighted-budget ceiling and the
strict localization/endpoint supremum.  It does not claim a ceiling for other
radii, stronger analytic estimates, larger blocks, or the exact transcendental
endpoint gap.
"""

from fractions import Fraction as Q
from pathlib import Path
import sys


def require(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)


def rational_string(x: Q) -> str:
    return f"{x.numerator}/{x.denominator}"


def render() -> str:
    radius = Q(1, 8)
    localization_threshold = Q(1815107, 989072150)
    cos_lower = Q(12359, 12800)
    negative_sine_loss = Q(129, 1280)
    endpoint_gap = Q(102239, 592688)

    # These are the exact, pre-rounding rational slope lower bounds from
    # (3/2) * derivativeLower(n) / (44n/7 + 21/40)^2.
    slopes = {}
    for n in range(1, 7):
        derivative_lower = (
            (Q(3 * n) - Q(1, 16)) * cos_lower - negative_sine_loss
        )
        local_x_upper = Q(44 * n, 7) + Q(21, 40)
        slopes[n] = Q(3, 2) * derivative_lower / local_x_upper**2
        require(slopes[n] > 0, f"positive exact slope n={n}")

    expected_slopes = {
        1: Q(82354251, 930982144),
        2: Q(169559355, 3442403584),
        3: Q(85588153, 2513265408),
        4: Q(343969563, 13223160064),
        5: Q(431174667, 20492495104),
        6: Q(172793257, 9782600448),
    }
    require(slopes == expected_slopes, "closed-form slope identities")

    denominators = {n: Q(1) / slopes[n] for n in slopes}
    rows = []
    for i in range(1, 7):
        for j in range(1, 7):
            for k in range(1, 7):
                if i + j == k:
                    separation = Q(11, 60)
                else:
                    separation = Q(1)
                budget = separation**2 / (
                    denominators[i] ** 2
                    + denominators[j] ** 2
                    + denominators[k] ** 2
                )
                rows.append(((i, j, k), budget))
    require(len(rows) == 216, "all ordered Fin 6 cubed rows covered")

    delta_ceiling = Q(
        9755468468368320337833317374859207102505001,
        1623000197669009639771565694101668583197612441600,
    )
    weakest = min(budget for _, budget in rows)
    minimizers = [index for index, budget in rows if budget == weakest]
    require(weakest == delta_ceiling, "exact minimum budget")
    require(minimizers == [(1, 5, 6), (5, 1, 6)], "ceiling witnesses")
    require(
        delta_ceiling
        == Q(11, 60) ** 2
        / (
            denominators[1] ** 2
            + denominators[5] ** 2
            + denominators[6] ** 2
        ),
        "special-row identity",
    )
    require(
        localization_threshold**2 < delta_ceiling,
        "localization is the active ceiling",
    )

    # The special row is also the upper-bound witness: any common lower budget
    # valid for every one of the 216 rows is at most its value.
    for _, budget in rows:
        require(delta_ceiling <= budget, "ceiling lower-bounds every row")

    activation_supremum = localization_threshold**2
    endpoint_gain_ceiling = activation_supremum * endpoint_gap**2 / 8
    expected_gain = Q(25097204303521, 2003484094270714880000)
    require(endpoint_gain_ceiling == expected_gain, "endpoint supremum identity")
    best_unit_eta = Q(1, 79828975)
    next_unit_eta = Q(1, 79828974)
    require(best_unit_eta < endpoint_gain_ceiling, "best strict unit is valid")
    require(endpoint_gain_ceiling <= next_unit_eta, "next unit is impossible")

    selected_delta = Q(2810232522752, 834437357315980975)
    require(selected_delta < activation_supremum, "selected delta activates")
    require(
        selected_delta * endpoint_gap**2 / 8 == best_unit_eta,
        "selected delta realizes best strict unit",
    )
    previous_delta = Q(702558130688, 211561101386624593)
    previous_eta = Q(1, 80958532)
    require(previous_delta < selected_delta, "previous delta below selected delta")
    require(previous_eta < best_unit_eta, "previous eta below selected eta")

    budget_above_activation = delta_ceiling - activation_supremum
    selected_activation_slack = activation_supremum - selected_delta
    valid_cross_slack = (
        79828975 * endpoint_gain_ceiling.numerator
        - endpoint_gain_ceiling.denominator
    )
    invalid_cross_slack = (
        endpoint_gain_ceiling.denominator
        - 79828974 * endpoint_gain_ceiling.numerator
    )

    lines = [
        "WIDER_FIXED_INTERFACE_CEILING_LEDGER PASS",
        "scope=refined_radius_slopes_separation_localization_weighted_cauchy_endpoint_gap",
        "root_triples_checked=216",
        "weighted_budget_minimizers=1,5,6;5,1,6",
        f"slope_3={rational_string(slopes[3])}",
        f"slope_6={rational_string(slopes[6])}",
        f"weighted_budget_ceiling={rational_string(delta_ceiling)}",
        f"activation_supremum={rational_string(activation_supremum)}",
        f"budget_above_activation={rational_string(budget_above_activation)}",
        f"selected_delta={rational_string(selected_delta)}",
        f"selected_activation_slack={rational_string(selected_activation_slack)}",
        f"previous_delta={rational_string(previous_delta)}",
        f"previous_delta_fraction_of_selected={rational_string(previous_delta / selected_delta)}",
        f"endpoint_gap={rational_string(endpoint_gap)}",
        f"endpoint_activation_supremum={rational_string(endpoint_gain_ceiling)}",
        f"best_unit_eta={rational_string(best_unit_eta)}",
        f"next_unit_eta={rational_string(next_unit_eta)}",
        f"best_unit_strict_cross_slack={valid_cross_slack}",
        f"next_unit_invalid_cross_slack={invalid_cross_slack}",
        f"previous_eta={rational_string(previous_eta)}",
        f"previous_eta_fraction_of_selected={rational_string(previous_eta / best_unit_eta)}",
    ]
    return "\n".join(lines) + "\n"


def main() -> None:
    output = render()
    if len(sys.argv) == 2 and sys.argv[1] == "--verify-frozen-output":
        frozen = Path(__file__).with_name(
            "wider_fixed_interface_ceiling_ledger_output.txt"
        ).read_text(encoding="utf-8")
        require(output == frozen, "frozen output mismatch")
        print(output, end="")
        return
    if len(sys.argv) != 1:
        raise SystemExit(
            "usage: wider_fixed_interface_ceiling_ledger.py "
            "[--verify-frozen-output]"
        )
    print(output, end="")


if __name__ == "__main__":
    main()
