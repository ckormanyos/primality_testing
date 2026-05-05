#include <boost/multiprecision/cpp_int.hpp>

#include <algorithm>
#include <array>
#include <chrono>
#include <iomanip>
#include <iostream>
#include <random>
#include <string>
#include <vector>
#include <utility>

// #define TEST_USE_SOLOVAY_STRASSEN
// #define TEST_USE_SYSTEM_ENTROPY

using big_int_type =
    boost::multiprecision::number<boost::multiprecision::cpp_int_backend<>, boost::multiprecision::et_off>;

// =============================================================================
// Random number generation using OS entropy (std::random_device)
// =============================================================================

namespace rnd_gens {

std::mt19937_64 gen1(42);
std::ranlux48 gen2(123);

} // rnd_gens

big_int_type generate_random_bits(int bit_length) {
    // Generate a random odd integer of exact bit length using OS entropy.
#if defined(TEST_USE_SYSTEM_ENTROPY)
    std::random_device rd{};
    rnd_gens::gen1.seed(rd());
#endif
    std::uniform_int_distribution<uint64_t> dist(0, UINT64_MAX);

    big_int_type n = 0;
    int remaining = bit_length;
    while (remaining > 0) {
        int chunk = std::min(remaining, 64);
        uint64_t bits = dist(rnd_gens::gen1);
        if (chunk < 64) {
            bits &= ((uint64_t(1) << chunk) - 1);
        }
        n <<= chunk;
        n |= bits;
        remaining -= chunk;
    }

    // Set MSB to guarantee exact bit length
    big_int_type msb = big_int_type(1) << (bit_length - 1);
    n |= msb;
    // Set LSB to guarantee odd
    n |= 1;

    return n;
}

big_int_type random_below(const big_int_type& upper) {
    // Generate a random integer in [0, upper)
#if defined(TEST_USE_SYSTEM_ENTROPY)
    std::random_device rd{};
    rnd_gens::gen2.seed(rd());
#endif
    std::uniform_int_distribution<uint64_t> dist(0, UINT64_MAX);

    int bits_needed = static_cast<int>(msb(upper) + 1);
    big_int_type result{0};

    int remaining = bits_needed;
    while (remaining > 0) {
        int chunk = std::min(remaining, 64);
        uint64_t bits = dist(rnd_gens::gen2);
        if (chunk < 64) {
            bits &= ((uint64_t(1) << chunk) - 1);
        }
        result <<= chunk;
        result |= bits;
        remaining -= chunk;
    }

    return result % upper;
}

// =============================================================================
// Jacobi Symbol
// =============================================================================

int jacobi_symbol(big_int_type a, big_int_type n) {
    // Compute the Jacobi symbol (a/n) using the iterative algorithm.

    // n must be a positive odd integer.
    if ((n <= 0) || ((static_cast<unsigned>(n) % 2U) == 0)) {
        return 0;
    }

    a = a % n;

    if (a < 0) {
        a += n;
    }

    int result = 1;

    while ((static_cast<unsigned>(a) != 0U) && (a != 0)) {
        // Remove factors of 2 from a
        while ((static_cast<unsigned>(a) % 2U) == 0U) {
            a /= 2;
            int n_mod8 = static_cast<int>(n % 8);
            if (n_mod8 == 3 || n_mod8 == 5) {
                result = -result;
            }
        }

        // Apply quadratic reciprocity (swap a and n)
        std::swap(a, n);

        if (a % 4 == 3 && n % 4 == 3) {
            result = -result;
        }

        a = a % n;
    }

    return (n == 1) ? result : 0;
}

#if defined(TEST_USE_SOLOVAY_STRASSEN)
// =============================================================================
// Solovay-Strassen Primality Test
// =============================================================================

bool solovay_strassen(const big_int_type& n, int k = 50) {
    // List of small primes.
    constexpr std::array<unsigned, std::size_t{32U}> small_primes = {
          3U,   5U,   7U,  11U,  13U,  17U,  19U,  23U,
         29U,  31U,  37U,  41U,  43U,  47U,  53U,  59U,
         61U,  67U,  71U,  73U,  79U,  83U,  89U,  97U,
        101U, 103U, 107U, 109U, 113U, 127U, 131U, 137U
    };

    bool is_small_prime_divisible = std::any_of(
        small_primes.cbegin(), small_primes.cend(),
        [&n](int p) { return ((n % p) == 0U) && (n != p); }
    );

    if (is_small_prime_divisible) {
        return false;
    }

    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if ((static_cast<unsigned>(n) % 2U) == 0U) return false;

    for (int i = 0; i < k; ++i) {
        // Choose random witness from [2, n-2]
        big_int_type a = random_below(n - 3) + 2;

        // Compute Jacobi symbol (a/n)
        int jac = jacobi_symbol(a, n);

        // If jacobi is 0, then gcd(a, n) != 1, so n is composite
        if (jac == 0) return false;

        big_int_type jacobi_mod = (jac == -1) ? (n - 1) : big_int_type(jac);

        // Compute a^((n-1)/2) mod n
        big_int_type euler = powm(a, (n - 1) / 2, n);

        // Euler's criterion: for primes, these must be equal
        if (euler != jacobi_mod) return false;
    }

    return true;
}

#else

auto lsb_position(std::uint64_t x) -> unsigned {
    unsigned pos{};

    while (static_cast<unsigned>(x & UINT64_C(1)) == 0U) {
        x >>= 1U;
        ++pos;
    }

    return pos;
}

auto miller_rabin(const big_int_type& np, const int trials) -> bool {
    // Perform the Miller-Rabin primality test on the prime candidate np.
    // This subroutine returns true if the prime candidate is prime within
    // the limits of Miller-Rabin testing for the given input of trials.
    // In this reduced implementation, we ignore small primes.

    // List of small primes.
    constexpr std::array<unsigned, std::size_t{32U}> small_primes = {
          3U,   5U,   7U,  11U,  13U,  17U,  19U,  23U,
         29U,  31U,  37U,  41U,  43U,  47U,  53U,  59U,
         61U,  67U,  71U,  73U,  79U,  83U,  89U,  97U,
        101U, 103U, 107U, 109U, 113U, 127U, 131U, 137U
    };

    bool is_small_prime_divisible = std::any_of(
        small_primes.cbegin(), small_primes.cend(),
        [&np](int p) { return ((np % p) == 0U) && (np != p); }
    );

    if (is_small_prime_divisible) {
        return false;
    }

    const big_int_type nm1{np - static_cast<unsigned>(UINT8_C(1))};

    auto local_functor_isone{[](const big_int_type& t1) { return ((static_cast<unsigned>(t1) == 1U) && (t1 == 1U)); }};

    {
        // Perform a single Fermat test which will exclude many non-prime candidates.
        // If this fails, np is definitely composite. If it passes, np might still
        // be composite (Carmichael numbers are the classic troublemakers).
        // But this simple test weeds out many non-prime candidates. The value
        // 228 is not a correctness requirement. Rather, it is just a performance
        // tradeoff in this interpretation of Miller-Rabin primality testing.

        const big_int_type fn{powm(big_int_type(228U), nm1, np)};

        if (!local_functor_isone(fn)) {
            return false;
        }
    }

    const unsigned k{lsb_position(static_cast<std::uint64_t>(nm1))};

    const big_int_type q{nm1 >> k};

    // Assume the test will pass, even though it usually does not pass.
    bool result_candidate_is_prime{true};

    const big_int_type nm2{np - 2};

    // We will now run the trials.
    for (int trial{0}; ((trial < trials) && result_candidate_is_prime); ++trial) {
        big_int_type next_rnd{random_below(nm2)};

        big_int_type y{powm(next_rnd, q, np)};

        for (auto j = std::size_t{UINT8_C(0)}; ((j < static_cast<std::size_t>(k)) && result_candidate_is_prime); ++j) {
            if (y == nm1) {
                // This trial passes and the candidate is very probably
                // prime within the limits of Miller-Rabin.

                break;
            }

            if (local_functor_isone(y)) {
                // Failure and the candidate is not prime, but only
                // if this is not the first step.

                if (j != std::size_t{UINT8_C(0)}) {
                    result_candidate_is_prime = false;
                }

                break;
            }

            // Compute y = y^2 mod np.
            y = (y * y) % np;

            // If we reach the final iteration without hitting nm1,
            // then the candidate is not prime.

            if (static_cast<unsigned>(j + std::size_t{UINT8_C(1)}) == k) {
                result_candidate_is_prime = false;
            }
        }
    }

    return result_candidate_is_prime;
}

#endif

// =============================================================================
// Prime Generation
// =============================================================================

std::pair<big_int_type, int> generate_prime(int bit_length) {
    int attempts{};

    big_int_type found_candidate{};

    bool found {false};



    while (!found) {
        big_int_type candidate{generate_random_bits(bit_length)};
        ++attempts;

#if defined(TEST_USE_SOLOVAY_STRASSEN)
        constexpr int rounds{50};
        if (solovay_strassen(candidate, rounds)) {
#else
        constexpr int rounds{25};
        if (miller_rabin(candidate, rounds)) {
#endif
            found_candidate = candidate;
            found = true;
        }
    }

    return {found_candidate, attempts};
}

// =============================================================================
// Verification Helpers
// =============================================================================

void verify_known_prime(const big_int_type& p) {
#if defined(TEST_USE_SOLOVAY_STRASSEN)
    bool result = solovay_strassen(p);
#else
    bool result = miller_rabin(p, 25);
#endif

    std::cout << "  Result: " << (result ? "PRIME (probably)" : "COMPOSITE") << "\n";
}

void verify_known_composite(const big_int_type& n) {
#if defined(TEST_USE_SOLOVAY_STRASSEN)
    bool result = solovay_strassen(n);
#else
    bool result = miller_rabin(n, 25);
#endif
    std::cout << "  Result: " << (result ? "PRIME (probably)" : "COMPOSITE") << "\n";
}

int bit_length(const big_int_type& n) {
    if (n == 0) return 0;
    return static_cast<int>(msb(n)) + 1;
}

// =============================================================================
// Main
// =============================================================================

int main() {
    using clock = std::chrono::high_resolution_clock;

    std::cout << std::string(70, '=') << "\n";
    std::cout << "  PRIMALITY TEST - BigInteger (512+ bits)\n";
    std::cout << "  Entropy source: std::random_device (optional)\n";
    std::cout << std::string(70, '=') << "\n";

    // --- Test 1: Verify with known small primes ---
    std::cout << "\n[1] Verifying known primes...\n";
    struct NamedValue { std::string name; big_int_type value; };
    std::vector<NamedValue> known_primes = {
        {"Mersenne prime M_61", (big_int_type(1) << 61) - 1},
        {"Mersenne prime M_89", (big_int_type(1) << 89) - 1},
        {"Mersenne prime M_127", (big_int_type(1) << 127) - 1},
    };
    for (const auto& [name, p] : known_primes) {
        std::cout << "  Testing " << name << " (" << bit_length(p) << " bits):\n";
        verify_known_prime(p);
    }

    // --- Test 2: Verify composites are rejected ---
    std::cout << "\n[2] Verifying known composites are rejected...\n";
    std::vector<NamedValue> composites = {
        {"Carmichael number", 561},
        {"Large composite (2^512 - 1)", (big_int_type(1) << 512) - 1},
        {"Product of two primes", ((big_int_type(1) << 61) - 1) * ((big_int_type(1) << 89) - 1)},
    };
    for (const auto& [name, c] : composites) {
        std::cout << "  Testing " << name << " (" << bit_length(c) << " bits):\n";
        verify_known_composite(c);
    }

    // --- Test 3: Generate 512-bit prime ---
    std::cout << "\n[3] Generating a 512-bit prime number...\n";
    auto start = clock::now();
    auto [prime_512, attempts_512] = generate_prime(512);
    double elapsed_512 = std::chrono::duration<double>(clock::now() - start).count();
    std::cout << "  Bit length: " << bit_length(prime_512) << "\n";
    std::cout << "  Attempts:   " << attempts_512 << "\n";
    std::cout << "  Time:       " << std::fixed << std::setprecision(3) << elapsed_512 << " seconds\n";
    std::cout << "  Prime (dec):\n    " << prime_512 << "\n";

    // --- Test 4: Generate 1024-bit prime ---
    std::cout << "\n[4] Generating a 1024-bit prime number...\n";
    start = clock::now();
    auto [prime_1024, attempts_1024] = generate_prime(1024);
    double elapsed_1024 = std::chrono::duration<double>(clock::now() - start).count();
    std::cout << "  Bit length: " << bit_length(prime_1024) << "\n";
    std::cout << "  Attempts:   " << attempts_1024 << "\n";
    std::cout << "  Time:       " << std::fixed << std::setprecision(3) << elapsed_1024 << " seconds\n";
    std::cout << "  Prime (dec):\n    " << prime_1024 << "\n";

    // --- Test 5: Generate 2048-bit prime ---
    std::cout << "\n[5] Generating a 2048-bit prime number...\n";
    start = clock::now();
    auto [prime_2048, attempts_2048] = generate_prime(2048);
    double elapsed_2048 = std::chrono::duration<double>(clock::now() - start).count();
    std::cout << "  Bit length: " << bit_length(prime_2048) << "\n";
    std::cout << "  Attempts:   " << attempts_2048 << "\n";
    std::cout << "  Time:       " << std::fixed << std::setprecision(3) << elapsed_2048 << " seconds\n";
    std::cout << "  Prime (dec):\n    " << prime_2048 << "\n";

#if defined(TEST_USE_SOLOVAY_STRASSEN)
    constexpr int rounds_extra{100};
#else
    constexpr int rounds_extra{50};
#endif
    // --- Test 6: Cross-verify generated primes ---
    std::cout << "\n[6] Cross-verification: re-testing generated primes (" << rounds_extra << " rounds)...\n";
    std::vector<std::pair<std::string, big_int_type>> generated = {
        {"512-bit", prime_512}, {"1024-bit", prime_1024}, {"2048-bit", prime_2048}
    };
    for (const auto& [label, p] : generated) {
#if defined(TEST_USE_SOLOVAY_STRASSEN)
        bool result = solovay_strassen(p, rounds_extra);
#else
        bool result = miller_rabin(p, rounds_extra);
#endif
        std::cout << "  " << label << " prime re-test (" << rounds_extra << " rounds): "
                  << (result ? "PASSED" : "FAILED") << "\n";
    }

    std::cout << "\n" << std::string(70, '=') << "\n";
    std::cout << "  All tests completed.\n";
    std::cout << std::string(70, '=') << "\n";

    return 0;
}
