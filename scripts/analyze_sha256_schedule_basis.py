#!/usr/bin/env python3
"""Verify the exact GF(2) schedule-basis claims in the SHA-256 row note."""

from __future__ import annotations

from functools import reduce


WIDTH = 32


def popcount(value: int) -> int:
    return bin(value).count("1")


def small_sigma_rows(kind: int) -> list[int]:
    rows = []
    for output_bit in range(WIDTH):
        if kind == 0:
            sources = [(output_bit + 7) % WIDTH,
                       (output_bit + 18) % WIDTH]
            if output_bit + 3 < WIDTH:
                sources.append(output_bit + 3)
        elif kind == 1:
            sources = [(output_bit + 17) % WIDTH,
                       (output_bit + 19) % WIDTH]
            if output_bit + 10 < WIDTH:
                sources.append(output_bit + 10)
        else:
            raise ValueError("small-sigma index must be zero or one")
        rows.append(sum(1 << source for source in sources))
    return rows


def inverse(rows: list[int]) -> tuple[int, list[int] | None]:
    augmented = [rows[i] | (1 << (WIDTH + i)) for i in range(WIDTH)]
    rank = 0
    for column in range(WIDTH):
        pivot = next((i for i in range(rank, WIDTH)
                      if augmented[i] >> column & 1), None)
        if pivot is None:
            continue
        augmented[rank], augmented[pivot] = augmented[pivot], augmented[rank]
        for i in range(WIDTH):
            if i != rank and augmented[i] >> column & 1:
                augmented[i] ^= augmented[rank]
        rank += 1
    if rank != WIDTH:
        return rank, None
    return rank, [row >> WIDTH for row in augmented]


def compose(left: list[int], right: list[int]) -> list[int]:
    return [
        reduce(int.__xor__,
               (right[j] for j in range(WIDTH) if row >> j & 1), 0)
        for row in left
    ]


def main() -> None:
    sigma0 = small_sigma_rows(0)
    sigma1 = small_sigma_rows(1)
    word = [1 << i for i in range(WIDTH)]
    assert len(set(word + sigma0 + sigma1)) == 96

    for name, basis, other in (
        ("sigma0", sigma0, sigma1),
        ("sigma1", sigma1, sigma0),
    ):
        rank, basis_inverse = inverse(basis)
        assert rank == WIDTH and basis_inverse is not None
        other_in_basis = compose(other, basis_inverse)
        inverse_weights = [popcount(row) for row in basis_inverse]
        other_weights = [popcount(row) for row in other_in_basis]
        assert len(set(basis_inverse)) == WIDTH
        assert len(set(other_in_basis)) == WIDTH
        assert not set(basis_inverse) & set(other_in_basis)
        print(
            f"{name}: rank={rank}; inverse total/min/max="
            f"{sum(inverse_weights)}/{min(inverse_weights)}/{max(inverse_weights)}; "
            f"other total/min/max="
            f"{sum(other_weights)}/{min(other_weights)}/{max(other_weights)}; "
            "derived distinct=64; overlap=0"
        )
    print("word + sigma0 + sigma1 distinct characters: 96")


if __name__ == "__main__":
    main()
