#include <cmath>
#include <cstring>
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

    uint64_t modulos() const
    {
        return modulo;
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

        uint64_t intermediate = val + x.val;

        if (intermediate >= val)
        {
            return ModuloNumber(intermediate, modulo);
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

        if ( val >= x.val )
        {
            return ModuloNumber(val - x.val, modulo);
        }

        // underflow case here
        return ModuloNumber(modulo - x.val + val, modulo);
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

        // unfortunately it's essential to multiply numbers whose intermediate value overflows 64 bits
        // the simplest but arguing way to do it is to use 128 bits numbers
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
    // let's use this operator privately doing something else, for convenience
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
            if (degree & 1)
            {
                res *= curr;
            }

            degree /= 2;
            curr *= curr;
        }

        return res;
    }

    // it works as it's written for modulos which are 2p + 1
    // it won't work for not safe primes
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

        auto new_xab = [x, base](ModuloNumber& x_, ModuloNumber& a, ModuloNumber& b)
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

private:
    // used in solving of a linear congruence
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

    static uint64_t extendedGcd(int64_t a, int64_t b, int64_t& x, int64_t& y)
    {
        x = 1, y = 0;
        int64_t x1 = 0, y1 = 1, a1 = a, b1 = b;

        while (b1)
        {
            int64_t q = a1 / b1;
            tie(x, x1) = make_tuple(x1, x - q * x1);
            tie(y, y1) = make_tuple(y1, y - q * y1);
            tie(a1, b1) = make_tuple(b1, a1 - q * b1);
        }

        return a1;
    }

    static pair<ModuloNumber, uint64_t> solveLinearEquation(ModuloNumber a, ModuloNumber b)
    {
        if (a.modulo != b.modulo)
        {
            throw invalid_argument("Consider explicit conversion here");
        }

        uint64_t gcd_ = std::gcd(a.val, a.modulo);

        if (b.val % gcd_)
        {
            throw invalid_argument("panic! no solutions here");
        }

        a /= gcd_;
        b /= gcd_;


        int64_t x = 0, y = 0;
        extendedGcd(a.val, a.modulo, x, y);

        return make_pair(ModuloNumber(x >= 0 ? x : x + a.modulos(), a.modulos()) * b, gcd_);
    }

    static uint64_t pollardRhoHelper(ModuloNumber a, ModuloNumber A, ModuloNumber b, ModuloNumber B, const ModuloNumber& x,const ModuloNumber& base)
    {
        auto res = solveLinearEquation(B - b, a - A);

        if (res.second == 1)
        {
            return res.first.val;
        }

        auto degree_ = ModuloNumber(res.first.val, a.modulos());
        auto pow_ = base.pow(uint64_t(degree_));

        if (pow_ == x)
        {
            return uint64_t(degree_);
        }

        const uint64_t step = a.modulo / res.second;
        auto mul = base.pow(step);

        for(uint64_t i = 0; i <= res.second - 1; i++)
        {
            pow_ *= mul;
            degree_ += step;

            if (pow_ == x)
            {
                return uint64_t(degree_);
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

            if (!isPocklington_prime(prime_candidate, attempts))
            {
                continue;
            }

            return prime_candidate;
        }

        return 0;
    }

    static uint64_t random64(uint64_t from, uint64_t to)
    {
        uniform_int_distribution<uint64_t> distribution(from,to);

        return distribution(generator);
    }

    static uint64_t randomBits(uint8_t bit_number, bool odd = true)
    {
        uint64_t res = random64(1ULL << (bit_number - 1), ((1ULL << bit_number) - 1));

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

            do
            {
                prime_candidate = randomBits(bit_number, true);

            }
            while (!must_2_over_3 || prime_candidate % 3 != 2);

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
                return false;
            }

            if (gcd(uint64_t(a * a) - 1, prime_candidate) == 1)
            {
                return true;
            }
        }

        return false;
    };

private:
    static random_device rd;
    static default_random_engine generator;
};


random_device PrimeRandomGenerator::rd;
default_random_engine PrimeRandomGenerator::generator(42);

class Measurer
{
public:
    using LogFunction = uint64_t (*)(const ModuloNumber& x,const ModuloNumber& base);
    using MeasureResult = pair<vector<uint8_t>, vector<uint64_t>>;

    static void genAndMeasureDLog(uint8_t from_bits, uint8_t to_bits, uint8_t bit_step = 1, uint8_t modulosCount = 3, uint8_t xCount = 3, uint64_t noMoreThanMillli = 30000)
    {
        if (from_bits >= to_bits || from_bits < 10 || to_bits >= 63 || !bit_step)
        {
            throw invalid_argument("Give valid limits");
        }

        vector<pair<uint8_t,uint64_t>> naive, baby, pollard;
        bool stopNaive = false, stopBaby = false, stopPollard = false;

        for (uint8_t count = from_bits; count < to_bits; count++)
        {
            auto res = genAndMeasureDLog(count,
                                         stopNaive ? nullptr : &ModuloNumber::naiveLog,
                                         stopBaby ? nullptr : &ModuloNumber::babyStepGiantStepLog,
                                         stopPollard ? nullptr : &ModuloNumber::pollardRhoLog,
                                         modulosCount, xCount);

            auto naiveVal = get<0>(res);
            auto babyVal = get<1>(res);
            auto pollardVal = get<2>(res);

            if (naiveVal)
            {
                naive.push_back({count, naiveVal});
                stopNaive = naiveVal > noMoreThanMillli;

                if (stopNaive)
                {
                    cout << "\033[31m stopping naive...\033[0m" << endl;
                }
            }

            if (babyVal)
            {
                baby.push_back({count, babyVal});
                stopBaby = babyVal > noMoreThanMillli;

                if (stopBaby)
                {
                    cout << "\033[31m stopping baby...\033[0m" << endl;
                }
            }

            if (pollardVal)
            {
                pollard.push_back({count, pollardVal});
                stopPollard = pollardVal > noMoreThanMillli;

                if (stopPollard)
                {
                    cout << "\033[31mstopping pollard...\033[0m" << endl;
                }
            }

            if (stopNaive && stopBaby && stopPollard)
            {
                cout << "\033[31mall the algorithms stopped...\033[0m" << endl;
                break;
            }
        }

        printArray("naive", convertHelper(naive));
        printArray("baby", convertHelper(baby));
        printArray("pollard", convertHelper(pollard));

    }
private:

    static uint64_t average(const vector<uint64_t>& v)
    {
        if (v.empty())
        {
            return 0;
        }

        return reduce(v.begin(), v.end()) / v.size();
    }

    static MeasureResult convertHelper(const vector<pair<uint8_t,uint64_t>>& v)
    {
        vector<uint8_t> x;
        vector<uint64_t> y;

        x.reserve(v.size());
        y.reserve(v.size());

        for (const auto& p: v)
        {
            x.push_back(p.first);
            y.push_back(p.second);
        }

        return {x, y};
    }

    static void printArray(string label, const MeasureResult& data)
    {
        cout << label << "_list_x = [";

        for (const auto& val: data.first)
        {
            cout << (uint16_t)val << ", ";
        }

        cout << "]" << endl;

        cout << label << "_list_y = [";

        for (const auto& val: data.second)
        {
            cout << val << ", ";
        }

        cout << "]" << endl;
    }

    static tuple<uint64_t, uint64_t, uint64_t> genAndMeasureDLog(uint8_t bit_number, LogFunction naiveF, LogFunction babyF, LogFunction pollardF, uint8_t modulosCount, uint8_t xCount)
    {
        vector<uint64_t> naive, baby, pollard;

        cout << "bit_number = " << uint16_t(bit_number) << " starting..." << endl;

        for (uint8_t i = 0; i < modulosCount; i++)
        {
            auto p = PrimeRandomGenerator::genSafePrime(bit_number);
            ModuloNumber base(ModuloNumber::generatorForSafePrime(p), p);

            cout << uint16_t(i) << "st modulo starting..." << endl;

            for (uint8_t j = 0; j < xCount; j++)
            {
                ModuloNumber x(PrimeRandomGenerator::random64(2, p - 2), p);

                if (naiveF)
                {
                    naive.push_back(measureDLog(x, base, naiveF, "naive"));
                }

                if (babyF)
                {
                    baby.push_back(measureDLog(x, base, babyF, "baby"));
                }

                if (pollardF)
                {
                    pollard.push_back(measureDLog(x, base, pollardF, "pollard"));
                }
            }

            cout << uint16_t(i) << "st modulo finishing..." << endl;
        }

        cout << "bit_number = " << uint16_t(bit_number) << " finishing..." << endl;

        return {average(naive), average(baby), average(pollard)};
    }


    static uint64_t measureDLog(const ModuloNumber& x,const ModuloNumber& base, LogFunction f, const string& label)
    {
        if (!f)
        {
            throw invalid_argument("Should be a valid pointer here " + label);
        }

        auto start = std::chrono::high_resolution_clock::now();
        uint64_t degree = f(x, base);
        auto stop = std::chrono::high_resolution_clock::now();
        auto base_in_x = base.pow(degree);

        if (x != base_in_x)
        {
            throw runtime_error("An algorithm works incorrectly! " + label + " base = " + to_string(uint64_t(base))
                                + ", x = " + to_string(uint64_t(x)) + ", modulo = " + to_string(base.modulos())
                                + ", degree = " + to_string(degree));
        }

        return  std::chrono::duration_cast<std::chrono::milliseconds>(stop - start).count();
    }
};


class Examples
{
public:
    static void Run()
    {
        cout << "2^10 = " << pow_int(2, 10) << endl
             << "3^4 =" << pow_int(3, 4) << endl;

        cout << "log(1024) by 2 " << uint16_t(log_int(1024, 2))  << endl
             << "log(81) by 3 " << uint16_t(log_int(81, 3)) << endl;

        cout << endl << endl;

        print_a_in_x(17);

        cout << endl << endl;

        print_a_in_x(10);

        check_Carmichael_number(561);
    }

private:

    static uint64_t pow_int(uint32_t base, uint8_t degree)
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

    static int8_t  log_int(uint64_t x, uint32_t base)
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

        //can be used as some simplification and so on...but not our aim here to implement fast log_int
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

    static void print_a_in_x(uint64_t modulo)
    {
        if (modulo <= 2)
        {
            throw underflow_error("please use something more meaningful here");
        }
        uint8_t digits_count = std::to_string(modulo).length();

        for (unsigned int i = 1; i < modulo; i++)
        {
            cout << "degree = " << std::setw(digits_count) << i << " |";
            for (unsigned int j = 1; j < modulo; j++)
            {
                cout << ' ' << std::setw(digits_count) << uint64_t(ModuloNumber(j, modulo).pow(i)) << " |";
            }
            cout << endl;
        }
    }


    static void check_Carmichael_number(uint64_t modulo)
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
                cout << "some aren't" << endl;
            }

            res *= res;

            all_is_one &= (res == 1);
        }

        cout << "all the coprime numbers satisfy the little Fermat's theorem ? " << all_is_one
             << endl << " but some half degrees are neither +1 nor -1 ? " << some_half_degrees_arent << endl;
    }

};

int main(int argc, char* argv[])
{
    bool measureIt = false;
    bool showExamples = false;

    if (argc > 1)
    {
        measureIt = !strcmp(argv[1],"--measure");
        showExamples = !strcmp(argv[1],"--examples");
    }

    if (measureIt)
    {
        Measurer::genAndMeasureDLog(16, 60);
    }
    else if (showExamples)
    {
        Examples::Run();
    }
    else
    {
        cout << endl << argv[0] << " use -- measure to measure it"
             << endl << "use --examples to show some examples" << endl;
    }

    return 0;
}
