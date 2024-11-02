#include <cmath>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <vector>
#include <limits>
#include <chrono>
#include <unordered_map>
#include <random>

using namespace std;

static random_device rd;
static default_random_engine generator(rd());

uint64_t random64(uint64_t from, uint64_t to)
{
    static uniform_int_distribution<long long unsigned> distribution(from,to);

    return distribution(generator);
}

uint64_t mul_mod(uint64_t a, uint64_t b, uint64_t modulo)
{
    // a %= modulo;
    // b %= modulo;

    // if (a <= numeric_limits<uint32_t>::max() && b <= numeric_limits<uint32_t>::max())
    // {
    //     return (a * b) % modulo;
    // }

    // uint64_t c = a & 0x00000000FFFFFFFF;
    // uint64_t d = b & 0x00000000FFFFFFFF;

    // a >>= 32;
    // b >>= 32;

    // return (((a * c) % modulo + (b * d) % modulo) % modulo + ((a * d) % modulo) + ((b * c) % modulo) % modulo) % modulo;

    // uint64_t res = 0;

    // while (a != 0) {
    //     if (a & 1) {

    //         res = (res + b) % modulo;
    //     }
    //     a >>= 1;
    //     b = (b << 1) % modulo;
    // }
    // return res;

    uint64_t c = (long double)a * b / modulo;
    int64_t ans = int64_t(a * b - c * modulo) % int64_t(modulo);
    if (ans < 0)
        ans += modulo;
    return ans;
}

uint64_t sub_mod(uint64_t a, uint64_t b, uint64_t modulo)
{
    return ((a % modulo) - (b % modulo) + modulo) % modulo;
}

uint64_t plus_mod(uint64_t a, uint64_t b, uint64_t modulo)
{
    uint64_t ans = a + b;
    if (ans < a || ans >= modulo)
        ans -= modulo;
    return ans;
}

uint64_t pow_mod(uint64_t base, uint64_t degree, uint64_t modulo)
{
    if (base == 0)
    {
        return 0;
    }
    if (base == 1 || degree == 0)
    {
        return 1;
    }

    uint64_t res = 1;
    uint64_t curr = base % modulo;

    while (degree)
    {
        if (degree & 0x1)
        {
            res = mul_mod(res, curr, modulo);
        }

        degree /= 2;
        curr = mul_mod(curr, curr, modulo);
    }

    return res;
}

uint64_t log_mod_naive(uint64_t x, uint64_t base, uint64_t modulo)
{
    uint64_t res = 1;
    base %= modulo;
    uint64_t curr = base;
    x %= modulo;

    while (curr != x )
    {
        curr = mul_mod(curr, base, modulo);
        res++;

        if (res == modulo)
        {
            cout << "panic! it's impossible if the input is correct!" << endl;
            return 0;
        }
    }

    return res;
}

uint64_t log_baby_step_giant_step(uint64_t x, uint64_t base, uint64_t modulo)
{
    uint64_t m = ceil(sqrt(modulo));

    unordered_map<uint64_t,uint64_t> baby_step_table;

    uint64_t pow = 1;
    for (uint64_t j = 0; j < m; j++)
    {
        baby_step_table[pow] = j;
        pow = mul_mod(pow, base, modulo);

    }

    uint64_t inverse = pow_mod(base, modulo - 1 - m , modulo);
    pow = x;

    for (uint64_t i = 0; i < m; i++)
    {
        auto it = baby_step_table.find(pow);

        if (it != baby_step_table.end())
        {
            return i * m + it->second;
        }

        pow = mul_mod(pow, inverse, modulo);

    }

    return 0;
}

uint64_t gen_prime(uint8_t bit_number, bool must_2_over_3 = true, uint8_t attempts = 20)
{
    if (bit_number < 7 || bit_number > 63)
    {
        cout << "incorrect bit number" << endl;
        return 0;
    }

    static auto gen_number = [](uint8_t bit_number, bool must_2_over_3)
    {
        while (true)
        {
            uint64_t res = random64(1ULL << bit_number, (1ULL << (bit_number + 1)) - 1);

            if (!(res % 2))
                res += 1;

            if (must_2_over_3 && res % 3 != 2)
            {
                continue;
            }

            return res;
        }

        return uint64_t(0);
    };

    static auto is_it_trivially_composite = [](uint64_t prime_candidate)
    {
        static vector<uint64_t> first_primes { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
                                             31, 37, 41, 43, 47, 53, 59, 61, 67,
                                             71, 73, 79, 83, 89, 97, 101, 103,
                                             107, 109, 113, 127, 131, 137, 139,
                                             149, 151, 157, 163, 167, 173, 179,
                                             181, 191, 193, 197, 199, 211, 223,
                                             227, 229, 233, 239, 241, 251, 257,
                                             263, 269, 271, 277, 281, 283, 293,
                                             307, 311, 313, 317, 331, 337, 347, 349 };

        for (const auto& p: first_primes)
        {
            if (!(prime_candidate % p))
                return true;
        }

        return false;
    };

    static auto is_miller_test_composite = [](uint64_t prime_candidate, uint8_t attempts)
    {
        static auto miller_test_composite = [](uint64_t prime_candidate, uint64_t d)
        {
            uint64_t a = random64(2, prime_candidate - 2);

            auto a_in_d = pow_mod(a, d, prime_candidate);

            if (a_in_d == 1 || a_in_d == prime_candidate - 1)
            {
                return false;
            }

            while (d != prime_candidate - 1)
            {
                a_in_d = mul_mod(a_in_d, a_in_d, prime_candidate);

                if (a_in_d == prime_candidate - 1)
                {
                    return false;
                }

                if (a_in_d == 1)
                {
                    return true;
                }

                d *= 2;
            }

            return true;
        };

        uint64_t d = (prime_candidate - 1) / 2;

        while (!(d % 2))
        {
            d /= 2;
        }

        for (uint8_t i = 0; i < attempts; i++)
        {
            if (miller_test_composite(prime_candidate, d))
            {
                return true;
            }
        }

        return false;
    };


    while (true)
    {
        auto prime_candidate = gen_number(bit_number, must_2_over_3);

        if (is_it_trivially_composite(prime_candidate) || is_miller_test_composite(prime_candidate, attempts))
        {
            continue;
        }

        return prime_candidate;
    }

    return 0;
}


uint64_t gen_safe_prime(uint8_t bit_number, int attempts = 2000)
{
    auto is_pocklington_prime = [](uint64_t prime_candidate, int attempts)
    {
        for (int i = 0; i < attempts; i++)
        {
            uint64_t a = random64(2, prime_candidate - 2);

            if (pow_mod(a, prime_candidate - 1 , prime_candidate) != 1)
            {
                continue;
            }

            if (gcd((a * a) - 1, prime_candidate) == 1)
            {
                return true;
            }
        }

        return false;
    };

    while (true)
    {
        uint64_t prime_candidate = 2 * gen_prime(bit_number - 1, 20) + 1;

        std::cout << "there is a prime candiate" << endl;

        if (!is_pocklington_prime(prime_candidate, attempts))
        {
            continue;
        }

        return prime_candidate;
    }

    return 0;
}

uint64_t generator_for_safe_prime(uint64_t modulo)
{
    for (uint64_t i = 2; i < modulo - 1; i++)
    {
        if (pow_mod(i, (modulo - 1) / 2, modulo) == modulo - 1)
        {
            return i;
        }
    }

    return 0;
}


class ModuloNumber
{
public:
    using uint128_t = unsigned __int128;

    ModuloNumber(uint64_t v, uint64_t m):val(v), modulo(m)
    {
        if (modulo < 3)
        {
            throw underflow_error("Can't guarantee consistency with such a modulo");
        }

        val %= modulo;
    }

    bool operator == (const ModuloNumber& x) const
    {
        return val == x.val && modulo == x.modulo;
    }

    bool operator != (const ModuloNumber& x)
    {
        return !this->operator == (x);
    }

    ModuloNumber operator + (const ModuloNumber& x) const
    {
        if (this->modulo != x.modulo)
        {
            throw invalid_argument("Consider explicit conversion here");
        }

        // - modulo here is to prevent overflow for large modulos
        // from the "modular" point of view any +- k * m operation don't change anything
        return ModuloNumber(val - modulo + x.val, modulo);
    }

    ModuloNumber& operator += (const ModuloNumber& x)
    {
        *this = this->operator + (x);
        return *this;
    }

    ModuloNumber& operator += (uint64_t x)
    {
        return this->operator += (ModuloNumber(x, modulo));
    }

    ModuloNumber operator - (const ModuloNumber& x) const
    {
        if (this->modulo != x.modulo)
        {
            throw invalid_argument("Consider explicit conversion here");
        }

        return ModuloNumber(val - x.val + modulo, modulo);
    }

    ModuloNumber& operator -= (const ModuloNumber& x)
    {
        *this = this->operator - (x);
        return *this;
    }

    ModuloNumber& operator -= (uint64_t x)
    {
        return this->operator -= (ModuloNumber(x, modulo));
    }

    ModuloNumber operator * (const ModuloNumber& x) const
    {
        if (this->modulo != x.modulo)
        {
            throw invalid_argument("Consider explicit conversion here");
        }

        return ModuloNumber((uint128_t(val) * uint128_t(x.val)) % modulo, modulo);

        // uint64_t c = (long double)val * x.val / modulo;
        // int64_t ans = int64_t(val * x.val - c * modulo) % int64_t(modulo);
        // if (ans < 0)
        //     ans += modulo;

        // return ModuloNumber(ans, modulo);

        // // auto t1 = __builtin_clzll(val);
        // // auto t2 = __builtin_clzll (x.val);
        // // //63 - t1 +  63 - t2 <= 63 => t1 + t2 >=  64
        // // if (t1 + t2 >= 63)
        // // {
        // //     return ModuloNumber(val * x.val, modulo);
        // // }

        // uint64_t a = val;
        // uint64_t c = x.val;

        // uint64_t b = a & 0x00000000FFFFFFFF;
        // uint64_t d = c & 0x00000000FFFFFFFF;

        // a >>= 32;
        // c >>= 32;

        // if (!a && !c)
        // {
        //     return ModuloNumber(b * d, modulo);
        // }

        // // ModuloNumber A(a, modulo);
        // // ModuloNumber B(b, modulo);
        // // ModuloNumber C(c, modulo);
        // // ModuloNumber D(d, modulo);

        // // ModuloNumber OneTo64(one_to_63, modulo);
        // // OneTo64 += OneTo64;


        // uint64_t temp2 = (a % modulo) * (d % modulo) % modulo;
        // uint64_t temp3 = (a % modulo) * (d % modulo) % modulo;

        // uint64_t res = (b % modulo) * (d % modulo) % modulo;

        // //return A * C * OneTo64 + (A * D + B * C) * ModuloNumber(one_to_32, modulo)  + B * D;
        // // return (((a * c) % modulo + (b * d) % modulo) % modulo + ((a * d) % modulo) + ((b * c) % modulo) % modulo) % modulo;

        // // uint64_t res = 0;

        // // while (a != 0) {
        // //     if (a & 1) {

        // //         res = (res + b) % modulo;
        // //     }
        // //     a >>= 1;
        // //     b = (b << 1) % modulo;
        // // }
        // // return res;
    }

    ModuloNumber& operator *= (const ModuloNumber& x)
    {
        *this = this->operator * (x);
        return *this;
    }

    ModuloNumber& operator *= (uint64_t x)
    {
        return this->operator *= (ModuloNumber(x, modulo));
    }

    // Division not each time is possible and not required
    //ModuloNumber operator / (const ModuloNumber& x) const

    ModuloNumber pow(uint64_t degree) const
    {
        if (!degree)
        {
            throw invalid_argument("Consider giving a positive degree here");
        }

        if (val == 0 || val == 1)
        {
            return *this;
        }

        ModuloNumber res(1, modulo);
        ModuloNumber curr = *this;

        while (degree)
        {
            if (degree & 0x1)
            {
                res *= curr;
            }

            degree /= 2;
            curr *= curr;
        }

        return res;
    }

    ModuloNumber inverse() const
    {
        // please notice that it's a Fermat inversion here
        // it won't work in general case if modulo isn't a prime
        // but for obvious reasons here we don't check it

        return pow(modulo - 2);
    }

    operator std::string() const
    {
        std::stringstream out;

        out << val << " mod " << modulo;

        return out.str();
    }

    static uint64_t naiveLog(const ModuloNumber& x,const ModuloNumber& base)
    {
        if (x.modulo != base.modulo)
        {
            throw invalid_argument("Consider explicit conversion here");
        }

        uint64_t res = 1;
        auto curr = base;


        while (curr != x )
        {
            curr *= base;
            res++;

            if (res == base.modulo)
            {
                throw runtime_error("This is impossible but we've reached modulo in the exponantiation");
            }
        }

        return res;
    }

    static uint64_t babyStepGiantStepLog(const ModuloNumber& x,const ModuloNumber& base)
    {
        if (x.modulo != base.modulo)
        {
            throw invalid_argument("Consider explicit conversion here");
        }

        uint64_t m = ceil(sqrt(base.modulo));

        unordered_map<uint64_t,uint64_t> baby_step_table;

        ModuloNumber pow(1, base.modulo);
        for (uint64_t j = 0; j < m; j++)
        {
            baby_step_table[pow.val] = j;
            pow *= base;
        }

        ModuloNumber inverse = base.pow(base.modulo - 1 - m);
        pow = x;

        for (uint64_t i = 0; i < m; i++)
        {
            auto it = baby_step_table.find(pow.val);

            if (it != baby_step_table.end())
            {
                return i * m + it->second;
            }

            pow *= inverse;

        }
        throw runtime_error("babyStepGiantStepLog failed");
        return 0;
    }

    static uint64_t pollardRhoLog(const ModuloNumber& x,const ModuloNumber& base)
    {
        if (x.modulo != base.modulo)
        {
            throw invalid_argument("Consider explicit conversion here");
        }

        uint64_t n = base.modulo - 1;

        auto new_xab = [x, base, n](ModuloNumber& x_, ModuloNumber& a, ModuloNumber& b)
        {
            switch (x_.val % 3)
            {
                case 0: x_ *= x_; a *= 2; b *= 2; break;
                case 1: x_ *= base; a += 1; break;
                case 2: x_ *= x; b += 1; break;
            }
        };

        ModuloNumber x_(1, x.modulo), a(0, n), b(0, n);
        ModuloNumber X = x_, A = a, B = b;

        for (uint64_t i = 1; i < n; ++i) {
            new_xab(x_, a, b);
            new_xab(X, A, B);
            new_xab(X, A, B);

            if (x_ == X)
            {
                return pollardRhoHelper(a, A, b, B, x, base);
            }
        }

        throw runtime_error("Pollard rho failed");
        return 0;
    }



    static void generateAndMeasure(uint8_t bitNumber)
    {
        //data: 1911286607 5 785146265

        if (bitNumber < 4 || bitNumber > 63)
        {
            throw invalid_argument("Consider meaningful amount of bits");
        }

       // auto p = gen_safe_prime(bitNumber);
       // auto g = generator_for_safe_prime(p);

       // auto x =  random64(2, p - 2);

        auto p = 305192652869879;
        auto g = 11;

        auto x =  252207972774029;

        cout << "data: " << p << ' ' << g << ' ' << x << endl;

        ModuloNumber test1(1ULL << 32, p);

        cout << string(test1 * test1) << endl;

        ModuloNumber X(x, p);
        ModuloNumber base(g, p);

        cout << "Let's check out the naivep algo" << endl;
        auto start = std::chrono::high_resolution_clock::now();
        //uint64_t degree = log_baby_step_giant_step(x, g, p);
        uint64_t degree = pollardRhoLog(X, base);
        auto stop = std::chrono::high_resolution_clock::now();
        cout << "And chect that it's correct " << (X == base.pow(degree)) << " " << degree << endl;
        std::cout << "it took us for = " << std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count() << std::endl;
    }

private:
    ModuloNumber operator /= (uint64_t d)
    {
        if (!d)
        {
            throw runtime_error("Zero isn't allowed!");
        }

        val /= d;
        modulo /= d;

        return *this;
    }

    // static constexpr uint64_t one_to_32 = (1ULL << 32);
    // static constexpr uint64_t one_to_63 = (1ULL << 63);

    // Look! this approach isn't general, it works because modulo is 2 * p
    static pair<ModuloNumber, uint64_t> solveLinearEquation(ModuloNumber a, ModuloNumber b)
    {
        if (a.modulo != b.modulo)
        {
            throw invalid_argument("Consider explicit conversion here");
        }

        cout << "solving " << a.val << "*x = " << b.val << " mod " << a.modulo << endl;

        uint64_t gcd_ = gcd(a.val, b.modulo);

        cout << "gcd = " << gcd_ << endl;

        if (b.val % gcd_)
        {
            throw invalid_argument("panic! no solutions here");
        }

        a /= gcd_;
        b /= gcd_;

        return make_pair(a.inverse() * b, gcd_);

    }

    static uint64_t pollardRhoHelper(ModuloNumber a, ModuloNumber A, ModuloNumber b, ModuloNumber B, const ModuloNumber& x,const ModuloNumber& base)
    {
        cout << string(B - b) << ' ' << string(a - A) << endl;
        auto res = solveLinearEquation(B - b, a - A);

        cout << "solution is " << string(res.first) << endl;

        if (res.second == 1)
        {
            return res.first.val;
        }

        uint64_t degree_ = res.first.val;
        auto pow_ = base.pow(degree_);

        if (pow_ == x)
        {
            return degree_;
        }

        uint64_t step = a.modulo / res.second;
        cout << "step " << step << endl;
        auto mul = base.pow(step);

        for(uint64_t i = 0; i < res.second - 1; i++)
        {
            pow_ *= mul;
            degree_ += step;

            cout << "degree candidate " << degree_ << endl;

            if (pow_ == x)
            {
                return degree_;
            }
        }

        throw runtime_error("Pollard rho failed");
        return 0;
    }


    uint64_t val; // always wrapped value in a range [0, modulo)
    uint64_t modulo;
};




uint64_t pow_int(uint32_t base, uint8_t degree)
{
    if (base == 0)
    {
        return 0;
    }
    if (base == 1 || degree == 0)
    {
        return 1;
    }

    uint64_t res = 1;
    uint64_t curr = base;

    while (degree)
    {
        if (degree & 0x1)
        {
            res *= curr;
        }

        degree /= 2;
        curr *= curr;
    }

    return res;
}

int8_t log_int(uint64_t x, uint32_t base)
{
    if (base > x || !base)
    {
        return -1;
    }

    if (x == 1)
    {
        return 0;
    }

    if (base == 1)
    {
        return -1;
    }

    // if (base == 2)
    // {
    //     return 63 - __builtin_clzll(x);
    // }

    vector<uint64_t> powers;
    powers.reserve(64);
    uint64_t curr = base;

    while (true)
    {
        powers.push_back(curr);

        if (curr > std::numeric_limits<uint32_t>::max())
            break;

        curr *= curr;
    }

    uint8_t res = 0;

    auto it = powers.rbegin();
    int i = 1;

    while (it != powers.rend())
    {
        auto curr = *it;

        if (x == curr)
        {
            return res + (1 << (powers.size() - i));
        }

        if (x > curr)
        {
            x /= curr;
            res += 1 << (powers.size() - i);
        }

        i++, it++;
    }

    return res;
}



// pair<int64_t, pair<int64_t, int64_t> > extendedEuclid(int64_t a, int64_t b)
// {
//     int64_t x = 1, y = 0;
//     int64_t xLast = 0, yLast = 1;
//     int64_t q, r, m, n;
//     while (a != 0)
//     {
//         q = b / a;
//         r = b % a;
//         m = xLast - q * x;
//         n = yLast - q * y;
//         xLast = x;
//         yLast = y;
//         x = m;
//         y = n;
//         b = a;
//         a = r;
//     }
//     return make_pair(b, make_pair(xLast, yLast));
// }

// __uint128_t modInverse(__uint128_t x, __uint128_t m)
// {
//     //return (extendedEuclid(a, modulo).second.first + modulo) % modulo;

//     // for (__uint128_t a = exchange(x, 1), b = exchange(m, 0); b; a = exchange(b, a % b)) {
//     //     x = exchange(m, x - (a / b) * m);
//     // }
//     // return x >= m ? x + m : x;

//     return x > 1 ? m - modInverse(m % x, x) * m / x : 1;
// }


uint64_t pollard_rho_log(uint64_t pow, uint64_t base, uint64_t modulo)
{
    uint64_t n = modulo - 1;
    auto new_xab = [pow, base, modulo, n](uint64_t& x, uint64_t& a, uint64_t& b)
    {
        switch (x % 3) {
        case 0: x = mul_mod(x, x,  modulo); a = mul_mod(a, 2, n); b =  mul_mod(b, 2, n);  break;
        case 1: x = mul_mod(x, base, modulo); a = plus_mod(a, 1, n);                  break;
        case 2: x = mul_mod(x, pow, modulo); b = plus_mod(b, 1, n);  break;
        }
    };

    auto solve_linear_equation = [](uint64_t a, uint64_t b, uint64_t modulo)
    {
        cout << "solving " << a << "*x = " << b << " mod " << modulo << endl;
        uint64_t gcd_ = gcd(a, modulo);

        cout << "gcd = " << gcd_ << endl;

        if (b % gcd_)
        {
            cout << "panic! no solutions here" << endl;
            return make_pair(0ULL, 0ULL);
        }

        a /= gcd_;
        b /= gcd_;
        modulo /= gcd_;

        return make_pair(mul_mod(pow_mod(a, modulo - 2, modulo), b, modulo ), gcd_);

    };

    uint64_t x = 1, a = 0, b = 0;
    uint64_t X = x, A = a, B = b;

    for (uint64_t i = 1; i < n; ++i) {
        new_xab(x, a, b);
        new_xab(X, A, B);
        new_xab(X, A, B);

        if (x == X)
        {

            cout << a << ' ' << A << ' ' << B << ' ' << b << endl;
            cout << (B - b) << ' ' << (a - A) << endl;

            auto res = solve_linear_equation(sub_mod(B, b, n), sub_mod(a, A, n), n);

            cout << "solution is " << res.first << endl;
            if (res.second == 1)
            {
                return res.first;
            }

            uint64_t degree_ = res.first;
            uint64_t pow_ = pow_mod(base, degree_, modulo);

            if (pow_ == pow)
            {
                return degree_;
            }

            uint64_t step = n / res.second;
            cout << "step " << step << endl;
            uint64_t mul = pow_mod(base, step, modulo);

            for(uint64_t i = 0; i < res.second - 1; i++)
            //while(true)
            {
                pow_ = mul_mod(pow_, mul, modulo);
                degree_ += step;

                cout << "degree candidate " << degree_ << endl;

                if (pow_ == pow)
                {
                    return degree_;
                }
            }

            cout << "fail to found.." << endl;
            return 0;
        }
    }

    cout << "fail to found.." << endl;
    return 0;
}

// uint64_t kangaro_log(uint64_t x, uint64_t base, uint64_t modulo, uint64_t a = 1,uint64_t b = 0, uint64_t attempts = 1000, uint64_t N = 100, uint64_t random_count = 100)
// {
//     if (!b)
//     {
//         b = modulo - 1;
//     }

//     for (uint64_t j = 0; j < attempts; j++)
//     {
//         auto mean = sqrt(b - a);
//         auto deviation = mean / 3;
//         normal_distribution distr{mean, deviation};

//         vector<uint64_t> steps;
//         steps.reserve(random_count);

//         for(uint64_t i = 0; i < random_count; i++)
//         {
//             auto temp = round(distr(generator));

//             if (temp < 0)
//             {
//                 temp = 2;
//             }

//             steps.push_back(temp);
//         }

//         uint64_t d = 0;
//         uint64_t x_i = 1;

//         for(uint64_t i = 0; i < N; i++)
//         {
//             auto step = steps[x_i % random_count];
//             x_i = mul_mod(pow_mod(base, step, modulo), x_i, modulo);
//             d += step;
//         }

//         uint64_t y = x;
//         uint64_t d_y = 0;

//         while (true)
//         {
//             auto step = steps[y % random_count];
//             y = mul_mod(pow_mod(base, step, modulo), y, modulo);
//             d_y += step;

//             if (y == x_i)
//             {
//                 cout << "found at " << j << " attempt" << endl;
//                 return (b + d - d_y) % (modulo - 1);
//             }

//             if (d_y > b - a + d)
//             {
//                 break;
//             }
//         }
//     }

//     return 0;
// }

// uint64_t gen_prime(uint8_t bit_number, bool must_2_over_3 = true, uint8_t attempts = 20)
// {
//     if (bit_number < 7 || bit_number > 63)
//     {
//         cout << "incorrect bit number" << endl;
//         return 0;
//     }

//     static auto gen_number = [](uint8_t bit_number, bool must_2_over_3)
//     {
//         while (true)
//         {
//             uint64_t res = random64(1ULL << bit_number, (1ULL << (bit_number + 1)) - 1);

//             if (!(res % 2))
//                 res += 1;

//             if (must_2_over_3 && res % 3 != 2)
//             {
//                 continue;
//             }

//             return res;
//         }

//         return uint64_t(0);
//     };

//     static auto is_it_trivially_composite = [](uint64_t prime_candidate)
//     {
//         static vector<uint64_t> first_primes { 2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
//                                              31, 37, 41, 43, 47, 53, 59, 61, 67,
//                                              71, 73, 79, 83, 89, 97, 101, 103,
//                                              107, 109, 113, 127, 131, 137, 139,
//                                              149, 151, 157, 163, 167, 173, 179,
//                                              181, 191, 193, 197, 199, 211, 223,
//                                              227, 229, 233, 239, 241, 251, 257,
//                                              263, 269, 271, 277, 281, 283, 293,
//                                              307, 311, 313, 317, 331, 337, 347, 349 };

//         for (const auto& p: first_primes)
//         {
//             if (!(prime_candidate % p))
//                 return true;
//         }

//         return false;
//     };

//     static auto is_miller_test_composite = [](uint64_t prime_candidate, uint8_t attempts)
//     {
//         static auto miller_test_composite = [](uint64_t prime_candidate, uint64_t d)
//         {
//             uint64_t a = random64(2, prime_candidate - 2);

//             auto a_in_d = pow_mod(a, d, prime_candidate);

//             if (a_in_d == 1 || a_in_d == prime_candidate - 1)
//             {
//                 return false;
//             }

//             while (d != prime_candidate - 1)
//             {
//                 a_in_d = mul_mod(a_in_d, a_in_d, prime_candidate);

//                 if (a_in_d == prime_candidate - 1)
//                 {
//                     return false;
//                 }

//                 if (a_in_d == 1)
//                 {
//                     return true;
//                 }

//                 d *= 2;
//             }

//             return true;
//         };

//         uint64_t d = (prime_candidate - 1) / 2;

//         while (!(d % 2))
//         {
//             d /= 2;
//         }

//         for (uint8_t i = 0; i < attempts; i++)
//         {
//             if (miller_test_composite(prime_candidate, d))
//             {
//                 return true;
//             }
//         }

//         return false;
//     };


//     while (true)
//     {
//         auto prime_candidate = gen_number(bit_number, must_2_over_3);

//         if (is_it_trivially_composite(prime_candidate) || is_miller_test_composite(prime_candidate, attempts))
//         {
//             continue;
//         }

//         return prime_candidate;
//     }

//     return 0;
// }


// uint64_t gen_safe_prime(uint8_t bit_number, int attempts = 2000)
// {
//     auto is_pocklington_prime = [](uint64_t prime_candidate, int attempts)
//     {
//         for (int i = 0; i < attempts; i++)
//         {
//             uint64_t a = random64(2, prime_candidate - 2);

//             if (pow_mod(a, prime_candidate - 1 , prime_candidate) != 1)
//             {
//                 continue;
//             }

//             if (gcd((a * a) - 1, prime_candidate) == 1)
//             {
//                 return true;
//             }
//         }

//         return false;
//     };

//     while (true)
//     {
//         uint64_t prime_candidate = 2 * gen_prime(bit_number - 1, 20) + 1;

//         std::cout << "there is a prime candiate" << endl;

//         if (!is_pocklington_prime(prime_candidate, attempts))
//         {
//             continue;
//         }

//         return prime_candidate;
//     }

//     return 0;
// }

// uint64_t generator_for_safe_prime(uint64_t modulo)
// {
//     for (uint64_t i = 2; i < modulo - 1; i++)
//     {
//         if (pow_mod(i, (modulo - 1) / 2, modulo) == modulo - 1)
//         {
//             return i;
//         }
//     }

//     return 0;
// }

void print_a_in_x(uint64_t modulo)
{
    if (modulo <= 2)
    {
        cout << "please use something more meaningful than " << modulo;
    }
    uint8_t digits_count = std::to_string(modulo).length();

    for (int i = 1; i < modulo; i++)
    {
        cout << "degree = " << std::setw(digits_count) << i << " |";
        for (int j = 1; j < modulo; j++)
        {
            cout << ' ' << std::setw(digits_count) << pow_mod(j, i, modulo) << " |";
        }
        cout << endl;
    }
}

void generate_data_and_measure(uint8_t bits_count, uint8_t count = 1)
{
    auto p = gen_safe_prime(bits_count);
    auto g = generator_for_safe_prime(p);

    uint64_t x =  random64(2, p - 2);

    cout << "data: " << p << ' ' << g << ' ' << x << endl;

    cout << "Let's check out the baby-step giant-step algo" << endl;
    auto start = std::chrono::high_resolution_clock::now();
    //uint64_t degree = log_baby_step_giant_step(x, g, p);
    uint64_t degree = pollard_rho_log(x, g, p);
    auto stop = std::chrono::high_resolution_clock::now();
    cout << "And chect that it's correct " << (x == pow_mod(g, degree, p)) << " " << degree << endl;
    std::cout << "it took us for = " << std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count() << std::endl;
}

void check_Carmichael_number(uint64_t modulo)
{
    uint64_t half_degree = (modulo - 1) / 2;

    bool all_is_one = true;
    bool some_half_degrees_arent = false;

    for (uint64_t i = 3; i < modulo; i++)
    {
        if (gcd(i, modulo) != 1)
        {
            continue;
        }

        auto res = pow_mod(i, half_degree, modulo);

        some_half_degrees_arent |= (res != 1) && (res != modulo - 1);

        if ((res != 1) && (res != modulo - 1))
        {
            cout << "some" << endl;
        }

        res = pow_mod(res, 2, modulo);

        all_is_one &= (res == 1);
    }

    cout << "all the coprime numbers satisfy the little Fermat's theorem ? " << all_is_one
         << endl << " but some half degrees are neither +1 nor -1 ? " << some_half_degrees_arent << endl;
}


int main()
{

    //cout << pollard_rho_log(3973579837, 7, 8227912079) << endl;
   // uint64_t correct_degree = log_baby_step_giant_step(3973579837, 7, 8227912079);
    //cout << "correct degree " <<  correct_degree << endl;
   // cout << "And chect that it's correct " << (3973579837 == pow_mod(7, correct_degree, 8227912079)) << endl;

    // cout <<  pollard_rho_log(5, 2, 1019) << endl;
    // return 0;
    //check_Carmichael_number(41041);

    ModuloNumber::generateAndMeasure(48);



    // cout << generator_for_safe_prime(23) << ' ' << generator_for_safe_prime(83) << std::endl;
     //cout << gen_prime(20) << ' ' << gen_prime(20) << endl;
    // cout << gen_safe_prime(20) << ' ' << gen_safe_prime(20) << endl;
    // cout << integer_pow(2, 1) << " " << integer_pow(3, 7) << " " << integer_pow(2, 10) << endl;
    // cout << "Hello World! " << (uint16_t)integer_log(762939453125, 5) <<  endl;

    // // print_a_x(17);
     //print_a_in_x(21);

    // print_a_in_x(23);

    // // uint64_t p = 17;

    // // for (int i = 1; i < p; i++)
    // // {
    // //     cout << "degree = " << i << "|";
    // //     for (int j = 1; j < p; j++)
    // //     {
    // //         cout << " " << mod_pow(j, i, p) << " |";
    // //     }
    // //     cout << endl;
    // // }

    // cout << "naive_mod_log(3, 5, 7) = " << naive_mod_log(3, 5, 7) << endl;

    // cout << endl << endl;

    // p = 10;

    // for (int i = 1; i < p; i++)
    // {
    //     cout << "degree = " << i << "|";
    //     for (int j = 1; j < p; j++)
    //     {
    //         cout << " " << mod_pow(j, i, p) << " |";
    //     }
    //     cout << endl;
    // }

    // 50 bits modulo
    // uint64_t modulo = 279685449069893;
    // uint64_t x = 39652674720629;
    // uint64_t base = 27466379178647;

    // 32 bits modulo
    // uint64_t modulo = 2432283587;
    // uint64_t x = 914017943;
    // uint64_t base = 812356553;

    // uint64_t modulo = 17;
    // uint64_t x = 7;
    // uint64_t base = 3;

    // cout << "Let's check out the babu-step giant-step algo" << endl;
    // auto start = std::chrono::high_resolution_clock::now();
    // uint64_t degree = baby_step_giant_step_log(x, base, modulo);
    // auto stop = std::chrono::high_resolution_clock::now();
    // cout << "And chect that it's correct " << (x == mod_pow(base, degree, modulo)) << endl;
    // std::cout << "it took us for = " << std::chrono::duration_cast<std::chrono::seconds>(stop - start).count() << std::endl;

    // cout << "Let's try to crack on it..." << endl;
    // auto start = std::chrono::high_resolution_clock::now();
    // uint64_t degree = naive_mod_log(x, base, modulo);
    // auto stop = std::chrono::high_resolution_clock::now();
    // cout << "And chect that it's correct " << (x == mod_pow(base, degree, modulo)) << endl;
    // std::cout << "it took us for = " << std::chrono::duration_cast<std::chrono::seconds>(stop - start).count() << std::endl;

    // cout << "Let's show integer_log correctness" << endl;

    // for (uint64_t base = 2; base <= std::numeric_limits<uint32_t>::max(); base++)
    // {
    //     uint64_t pow = base;

    //     for(uint8_t degree = 1; degree <= 63; degree++)
    //     {
    //         if (degree != integer_log(pow, base))
    //         {
    //             cout << "panic! " << (uint16_t)degree << " " << (uint16_t)integer_log(pow, base) << endl;
    //         }

    //         //filter overflow results here
    //         if (pow > std::numeric_limits<uint64_t>::max() / pow)
    //         {
    //             break;
    //         }
    //         pow *= base;
    //     }

    //     if (!(base % 10000000))
    //         cout << "done for base less or equal " << base << endl;
    // }


    return 0;
}
