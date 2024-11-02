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

    explicit operator uint64_t() const
    {
        return val;
    }

    bool operator == (const ModuloNumber& x) const
    {
        return val == x.val && modulo == x.modulo;
    }

    bool operator == (uint64_t x) const
    {
        return val == (x % modulo);
    }

    bool operator != (const ModuloNumber& x) const
    {
        return !this->operator == (x);
    }

    bool operator != (uint64_t x) const
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

    // it works as it's written for modulos which are 2p + 1
    static uint64_t generatorForSafePrime(uint64_t modulo)
    {
        for (uint64_t i = 2; i < modulo - 1; i++)
        {
            if (ModuloNumber(i, modulo).pow((modulo - 1) / 2) == modulo - 1)
            {
                return i;
            }
        }

        return 0;
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

class PrimeRandomGenerator
{

public:
    static uint64_t genSafePrime(uint8_t bit_number, uint8_t attempts = 20)
    {
        while (true)
        {
            uint64_t prime_candidate = 2 * genPrime(bit_number - 1, 20) + 1;

            //std::cout << "there is a prime candiate" << endl;

            if (!isPocklington_prime(prime_candidate, attempts))
            {
                continue;
            }

            return prime_candidate;
        }

        return 0;
    }

private:

    static random_device rd;
    static default_random_engine generator;

    static uint64_t random64(uint64_t from, uint64_t to)
    {
        static uniform_int_distribution<long long unsigned> distribution(from,to);

        return distribution(generator);
    }

    static uint64_t randomBits(uint8_t bit_number, bool odd = true)
    {
        uint64_t res = random64(1ULL << bit_number, (1ULL << (bit_number + 1)) - 1);

        if (odd && !(res % 2))
            res += 1;

        return res;
    }

    static bool isTriviallyComposite(uint64_t prime_candidate)
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
    }

    static bool isMillerTestComposite(uint64_t prime_candidate, uint8_t attempts = 20)
    {
        uint64_t d = (prime_candidate - 1) / 2;

        while (!(d % 2))
        {
            d /= 2;
        }

        for (uint8_t i = 0; i < attempts; i++)
        {
            ModuloNumber a(random64(2, prime_candidate - 2), prime_candidate);

            auto a_in_d = a.pow(d);

            // Fermat's test
            if (uint64_t(a_in_d) == 1 || a_in_d == prime_candidate - 1)
            {
                return false;
            }

            while (d != prime_candidate - 1)
            {
                a_in_d *= a_in_d;

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
        }

        return true;
    }

    static uint64_t genPrime(uint8_t bit_number, bool must_2_over_3 = true, uint8_t attempts = 20)
    {
        if (bit_number < 7 || bit_number > 63)
        {
            throw invalid_argument("Consider bit number between 7 and 63");
            return 0;
        }


        while (true)
        {
            uint64_t prime_candidate = 0;

            {
                prime_candidate = randomBits(bit_number, true);

            }
            while (!must_2_over_3 || prime_candidate % 3 == 2);

            if (isTriviallyComposite(prime_candidate) || isMillerTestComposite(prime_candidate, attempts))
            {
                continue;
            }

            return prime_candidate;
        }

        return 0;
    }

    static bool isPocklington_prime(uint64_t prime_candidate, int attempts = 20)
    {
        for (int i = 0; i < attempts; i++)
        {
            ModuloNumber a(random64(2, prime_candidate - 2), prime_candidate);

            if (a.pow(prime_candidate - 1) != 1)
            {
                continue;
            }

            if (gcd(uint64_t(a * a) - 1, prime_candidate) == 1)
            {
                return true;
            }
        }

        return false;
    };
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
            cout << ' ' << std::setw(digits_count) << uint64_t(ModuloNumber(j, modulo).pow(i)) << " |";
        }
        cout << endl;
    }
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

        auto res = ModuloNumber(i, modulo).pow(half_degree);

        some_half_degrees_arent |= (res != 1) && (res != modulo - 1);

        if ((res != 1) && (res != modulo - 1))
        {
            cout << "some" << endl;
        }

        res *= res;

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
