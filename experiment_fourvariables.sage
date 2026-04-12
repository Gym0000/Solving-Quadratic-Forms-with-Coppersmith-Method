from re import findall
from subprocess import check_output
import time

def flatter(M):
    z = "[[" + "]\n[".join(" ".join(map(str, row)) for row in M) + "]]"
    ret = check_output(["flatter"], input=z.encode())
    return matrix(M.nrows(), M.ncols(), map(int, findall(rb"-?\d+", ret)))

def reduce_lattice(L, delta=0.75, ifFlatter=True):
    """
    Reduces a lattice basis using a lattice reduction algorithm (currently LLL).
    :param L: the lattice basis
    :param delta: the delta parameter for LLL (default: 0.75)
    :return: the reduced basis
    """
    start = time.time()
    if ifFlatter:
        print(f"Reducing a {L.nrows()} x {L.ncols()} lattice with flatter...")
        resultMat=flatter(L)
       
    else:
        print(f"Reducing a {L.nrows()} x {L.ncols()} lattice...")
        resultMat=L.LLL(delta)
    end = time.time()
    print(f"lattice reduction time: {end - start:.2f}")
    return resultMat


def bmod(x, p):
    return (x + p // 2) % p - p // 2


def adjust_bound(bound, a0):
    new_bound = bound
    while gcd(a0, new_bound) != 1:
        new_bound += 1
        if new_bound >= 2 * bound:
            raise ValueError("Cannot adjust bound to make gcd(a0, bound)=1 within range.")
    return new_bound


def modulu_grobnerbasis(p, polys):
    pr = P.change_ring(GF(p))
    I = pr * polys
    print(f"Trying modulus {p} and I.dimension()={I.dimension()}")
    if I.dimension() == 0:
        solutions = I.variety()
        sol = []
        for form in solutions:
            sol.append((bmod((form[x1].lift()), p),bmod((form[x2].lift()), p),bmod((form[x3].lift()), p),bmod((form[x4].lift()), p)))
        return sol
    else:
        return None


def crt_grobnerbasis(p, polys):
    """
    Simplified CRT-based solver for very large prime modulus p (> 2^31-1).
    - Factor p into several ~2^28-sized distinct primes whose product M > p.
    - For each small prime pi:
        * Build ideal over GF(pi) with a libSingular-backed ring.
        * Compute I.dimension(); if dim != 0, return None immediately.
        * If dim == 0, compute I.variety() and record all solutions (tuples).
    - Finally, take the Cartesian product of all per-prime solution sets and
      combine coordinates via CRT to get solutions modulo M, then map to
      centered representatives modulo p and return all candidates.

    Returns:
        - list of 4-tuples (integers centered modulo p) if successful
        - None if any small-prime ideal has dim != 0 or some failure occurs
    """
    # Safety: only handle big p here
    P.<x1, x2, x3, x4> = PolynomialRing(ZZ)

    if p <= 2**31 - 1:
        raise ValueError("This simplified version is intended for p > 2^31-1 only.")

    # 1) Build a list of distinct primes around 2^28 until product exceeds p
    target = Integer(p)
    primes = []
    prod = Integer(1)

    # Start near 2^28; make sure it's odd and prime
    q = next_prime(Integer(1) << 28)
    # Step size between primes to avoid being too close; arbitrary
    step = 1 << 20

    while prod <= target:
        primes.append(q)
        prod *= q
        q = next_prime(q + step)

        # Hard stop to avoid infinite loops in pathological cases
        if len(primes) > 64:
            raise RuntimeError("Too many small primes were needed; adjust size/step.")

    # 2) For each small prime, compute dim and variety
    all_solutions_mod = []  # list of lists of 4-tuples of ints modulo that prime
    for pi in primes:
        # Build a libSingular-backed polynomial ring over GF(pi)
        
        pr = P.change_ring(GF(pi))
        I = pr * polys
        # First: dimension test
        try:
            dim = I.dimension()
        except Exception as e:
            # If dimension fails, regard as invalid
            print(f"dimension() over GF({pi}) failed: {e}")
            return None

        if dim != 0:
            # As requested: any non-zero dimension -> stop and return None
            return None

        # Zero-dimensional: compute variety
        try:
            sols = I.variety()
        except Exception as e:
            print(f"variety() over GF({pi}) failed: {e}")
            return None

        if not sols:
            # No solutions at this prime -> Cartesian product would be empty
            return None

        sols_tuples = []
        # print(sols)
        for s in sols:
            a = int(s[x1]); b = int(s[x2]); c = int(s[x3]); d = int(s[x4])
            sols_tuples.append((a % pi, b % pi, c % pi, d % pi))
        all_solutions_mod.append((pi, sols_tuples))

    # 3) Cartesian product over all primes' solution sets, applying CRT per coordinate
    from itertools import product

    moduli = [pi for (pi, _) in all_solutions_mod]
    solution_lists = [sols for (_, sols) in all_solutions_mod]
    M = Integer(1)
    for m in moduli:
        M *= m

    # Combine each tuple of per-prime solutions into one modulo M using CRT
    results = []
    for combo in product(*solution_lists):
        # combo is a tuple of length len(primes), each an (x1,x2,x3,x4) modulo its pi
        coords = []
        for coord_idx in range(4):
            residues = [combo[i][coord_idx] for i in range(len(primes))]
            try:
                x_coord = crt(residues, moduli)  # Sage's CRT over ZZ
            except Exception as e:
                print(f"CRT failed on coordinate {coord_idx} with residues {residues}: {e}")
                x_coord = None
            if x_coord is None:
                coords = None
                break
            coords.append(int(x_coord % M))
        if coords is None:
            continue

        # Map to centered representatives modulo p (as requested)
        # We have a representative modulo M; reduce to modulo p and center
        x1 = bmod(coords[0], M)
        x2 = bmod(coords[1], M)
        x3 = bmod(coords[2], M)
        x4 = bmod(coords[3], M)
        results.append((x1, x2, x3, x4))

   
    return results if results else None


def four_variables_JM(pol, X, Y, Z, W, realsol, m=2):
    P.<x1, x2, x3, x4> = PolynomialRing(ZZ)
    f = pol
    degf = 2
    deltax = deltay = deltaz = deltaw = degf * (m - 1)
    pol = pol(x1, x2, x3, x4)
    pol = P(pol / gcd(pol.coefficients()))
    a0 = pol(0, 0, 0, 0)

    W_val = max(abs(i) for i in pol(x1 * X, x2 * Y, x3 * Z, x4 * W).coefficients())
    R = W_val * (X^deltax * Y^deltay * Z^deltaz * W^deltaw)

    if gcd(a0, X) != 1:
        X = adjust_bound(X, a0)
    if gcd(a0, Y) != 1:
        Y = adjust_bound(Y, a0)
    if gcd(a0, Z) != 1:
        Z = adjust_bound(Z, a0)
    if gcd(a0, W) != 1:
        W = adjust_bound(W, a0)
    if gcd(a0, W_val) != 1:
        W_val = adjust_bound(W_val, a0)

    R = W_val * (X^deltax * Y^deltay * Z^deltaz * W^deltaw)

    a0inv = inverse_mod(a0, R)
    polq = P(sum((i * a0inv % R) * j for i, j in zip(pol.coefficients(), pol.monomials())))
    polynomials = []
    for i in range(deltax + degf + 1):
        for j in range(deltay + degf - i + 1):
            for k in range(deltaz + degf - i - j + 1):
                for t in range(deltaw + degf - i - j - k + 1):
                    if 0 <= i + j + k + t <= (m - 1) * degf:
                        polynomials.append(
                            polq * x1^i * x2^j * x3^k * x4^t *
                            X^(deltax - i) * Y^(deltay - j) * Z^(deltaz - k) * W^(deltaw - t)
                        )
                    else:
                        polynomials.append(
                            x1^i * x2^j * x3^k * x4^t * R
                        )

    monomials = []
    for poly in polynomials:
        for mono in poly.monomials():
            if mono not in monomials:
                monomials.append(mono)
    monomials.sort()
    print(f"Number of monomials: {len(monomials)}")
    print(f"Number of polynomials: {len(polynomials)}")

    L = matrix(ZZ, len(monomials))
    for i in range(len(monomials)):
        for j in range(len(monomials)):
            L[i, j] = polynomials[i](X * x1, Y * x2, Z * x3, W * x4).monomial_coefficient(monomials[j])

    L = matrix(ZZ, sorted(L, reverse=True))

    L = reduce_lattice(L, ifFlatter=True)
    n = len(monomials)
    pols = [None] * n
    pol_unused = []
    count_real = count_hg = 0
    polynomials_hg = [f]
    polynomials_real = [f]
    for i in range(n):
        pols[i] = P(sum(map(mul, zip(L[i], monomials)))(x1 / X, x2 / Y, x3 / Z, x4 / W))
        if n * sum([L[i, j] ** 2 for j in range(n)]) <= R ** 2:
            polynomials_hg.append(pols[i])
            polynomials_real.append(pols[i])
            count_hg += 1
            count_real += 1
        else:
            pol_unused.append(pols[i])
            if pols[i](realsol) == 0:
                count_real += 1
                polynomials_real.append(pols[i])
    print(f"Number of polynomials satisfying Howgrave-Graham Lemma: {count_hg}")
    print(f"Number of polynomials in fact is useful: {count_real}")
    p = next_prime(2 * X)
    pr = P.change_ring(GF(p))
    I_hg = pr * polynomials_hg
    I_real = pr * polynomials_real
    print(f"Trying modulus {p} and I_hg.dimension()={I_hg.dimension()}")
    print(f"Trying modulus {p} and I_real.dimension()={I_real.dimension()}")

    def check_solution(f, sols_list):
        if sols_list is None:
            return None
        sol = []
        for solution in sols_list:
            if f(solution) == 0:
                sol.append(solution)
        if len(sol) >= 1:
            print(f"Found {len(sol)} solutions {sol}.")
            return sol
        else:
            return None

    if p < 2 ** 31 - 1:
        sol = check_solution(f, modulu_grobnerbasis(p, polynomials_hg))
        if sol is not None:
            return sol
        else:
            for pol in pol_unused:
                tmp_polys = polynomials_hg + [pol]
                sol = check_solution(f, modulu_grobnerbasis(p, tmp_polys))
                if sol is not None:
                    return sol
        print("Coppersmith algebraic independence assumption fails!")

    else:
        sol = check_solution(f, crt_grobnerbasis(p, polynomials_hg))
        if sol is not None:
            return sol
        else:
            for pol in pol_unused:
                tmp_polys = polynomials_hg + [pol]
                print("Trying CRT grobner basis.")
                tmp_sol = crt_grobnerbasis(p, tmp_polys)
                print(f"index {pol_unused.index(pol)}: {tmp_sol}")
                sol = check_solution(f, tmp_sol)
                if sol is not None:
                    return sol
        print("Coppersmith algebraic independence assumption fails!")
    return None



P.<x1, x2, x3, x4> = PolynomialRing(ZZ)

forms = [
  {
    "p": 24554940634497023,
    "iso_degree": 199508892655288473,
    "quadratic_form": 2*x1^2 + x1*x4 + 2*x2^2 + x2*x3 + 3069367579312128*x3^2 + 3069367579312128*x4^2,
    "sol": [7, 1, 4, 7],
    "known_variables": [1, 2], # indices of the variables that we know; for example [2, 3] means we know x3 and x4
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 32,
    "quadratic_form": 4*x1^2 + 2*x1*x2 + 4*x1*x3 + x1*x4 + 6*x2^2 + x2*x3 + 6*x2*x4 + 11956566944641502957704189594909498993478297403838643406058180334130656750162*x3^2 + 5978283472320751478852094797454749496739148701919321703029090167065328375081*x3*x4 + 17934850416962254436556284392364248490217446105757965109087270501195985125243*x4^2,
    "sol": [1, 2, 0, 0],
    "known_variables": [0],
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**100,
    "quadratic_form": 237684487542793012780631851008*x1^2 + 158456325028528675187087900672*x1*x2 + 11852140596306291853529975864*x1*x3 - 196113268065311140224151971939*x1*x4 + 633825300114114700748351602688*x2^2 + 596168357077332235711287531421*x2*x3 + 101745988080523586886298584190*x2*x4 + 113184818679426280593331075426937368682915116826*x3^2 + 75456545786284187042467149290781092699393451444*x3*x4 + 301826183145136747915503626961815403581827345301*x4^2,
    "sol": [-2, 1, 0, 0],
    "known_variables": [1, 2],
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**120,
    "quadratic_form": 41538374868278621028243970633760768*x1^2 + 20825056980564116836958222982316228*x1*x3 + 36941148124127244989345096640962019*x1*x4 + 955382621970408283649611324576497664*x2^2 + 295365850822101723236606668429124125*x2*x3 + 478976310552974687250039128593273244*x2*x4 + 71960995160054093208529545814718687390660*x3^2 + 83300227922256467347832891929264912*x3*x4 + 1655102371831838747847223059215386233660968*x4^2,
    "sol": [-3, 1, 0, 0],
    "known_variables": [2, 3],
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**140,
    "quadratic_form": 40473403944771042310329985208052973550*x1^2 + 9748251956265421211829331742284787136*x1*x2 + 9748251956265421211829331742284787136*x1*x3 + 24976524946590553383304748705963317367*x1*x4 + 77454633550189127124614625500468942822*x2^2 + 48985934264245616245264531878868621177*x2*x3 - 9748251956265421211829331742284787136*x2*x4 + 902419591443790462258239566163618070005*x3^2 + 214461543037839266660245298330265316992*x3*x4 + 1716006642762988328172501652596769393989*x4^2,
    "sol": [9, -59, 2, -26],
    "known_variables": [0, 1],
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**150,
    "quadratic_form": 3897547560480989392878390612806074489*x1^2 + 2549863555395826816290179291063255984*x1*x3 - 2316483448965540237620928129585942081*x1*x4 + 89643593891062756036202984094539713247*x2^2 + 49087054174737412952161615483258835949*x2*x3 + 58646861774104016774674123694454887632*x2*x4 + 774065686297346099914796435657452606484*x3^2 + 15299181332374960897741075746379535904*x3*x4 + 17649300171967851438470970389282875615042*x4^2,
    "sol": [11643, -379, -1076, 12],
    "known_variables": [0, 1],
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**160,
    "quadratic_form": 120864756928231872170197654963601902031*x1^2 + 40379784023742363682691476922140013988*x1*x2 - 80210377761494289609629402238643748110*x1*x3 - 49019009704082514622267696968581725297*x1*x4 + 194680861828862664977080049082731556942*x2^2 + 156088821196201368396536230067211356461*x2*x3 + 147083019515271147858011236632623029956*x2*x4 + 410215661800567766037607854071586163516*x3^2 + 205107830900283883018803927035793081758*x3*x4 + 615323492700851649056411781107379245274*x4^2,
    "sol": [99533, -30399, 42217, -4004],
    "known_variables": [0, 1],
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**165,
    "quadratic_form": 138247101726295456755875073486750847154*x1^2 + 21460434255412846014100199109945618216*x1*x2 - 7153478085137615338033399703315206072*x1*x3 + 29955363653541474694836788320420187257*x1*x4 + 212291917471350331602636068408707319455*x2^2 + 12846160333952246577905930722776062645*x2*x3 + 14306956170275230676066799406630412144*x2*x4 + 325428104581287603783196981068692664128*x3^2 + 50074346595963307366233797923206442504*x3*x4 + 501050875206347183111794445486198453599*x4^2,
    "sol": [262357, -418875, -48673, -49152],
    "known_variables": [0, 1],
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**170,
    "quadratic_form": 155092426386982356343410631537502978702*x1^2 + 97600888830184995641397091875629292760*x1*x2 - 141722642629186478030282780799584443096*x1*x3 + 102925910518743119548873625692803306041*x1*x4 + 200388882109716746247505562304808983849*x2^2 + 66658376797360879806403365504646046331*x2*x3 - 133592588073144497498337041536539322566*x2*x4 + 420654471643757990568942777257913418616*x3^2 + 136898674658815950195209675413050796969*x3*x4 + 534370352292577989993348166146157290264*x4^2,
    "sol": [1911741, -1865026, 564043, -1711420],
    "known_variables": [1],
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**180,
    "quadratic_form": 114727094697098328038541868720587464332*x1^2 + 57363547348549164019270934360293732166*x1*x2 - 28479759541472593460427953409958276582*x1*x3 - 64241305342996695015173358540893910087*x1*x4 + 172090642045647492057812803080881196498*x2^2 + 107849336702650797042639444539987286411*x2*x3 + 53621647152122415697508451614710758954*x2*x4 + 438674171214814889852260952383628095579*x3^2 + 240696905263511890021451441249282755226*x3*x4 + 641658245062352046518091646325782127247*x4^2,
    "sol": [32633575, 16717795, -56942632, 3254465],
    "known_variables": [0, 1],
  }, 
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**200,
    "quadratic_form": 75977507322256808994564300613717071702*x1^2 + 71077098819583582676450096983765637052*x1*x2 + 61276281814237130040221689723862767752*x1*x3 - 24540546577584089835376781243100016933*x1*x4 + 190037733524410719386446026068558561316*x2^2 + 101081845212453080230152729062412381001*x2*x3 - 117464224688263639962258626749242336732*x2*x4 + 416366109651826182081987167299419812007*x3^2 + 338853688248787918094879801256809309090*x3*x4 + 1009791571838362253388691364274969076717*x4^2,
    "sol": [-88672782002, 49105680072, 46212705221, -584134663],
    "known_variables": [0, 1],
  },
  {
    "p": 11956566944641502957704189594909498993478297403838643406058180334130656750161,
    "iso_degree": 2**210,
    "quadratic_form": 122666453208910159294119827758251198761*x1^2 + 111804888627617729773666447208431934036*x1*x2 - 55902444313808864886833223604215967018*x1*x3 - 21990898934841116371930693219530726715*x1*x4 + 130365434097852927774128925626239586077*x2^2 + 14291918045898347891921595351542339399*x2*x3 + 55902444313808864886833223604215967018*x2*x4 + 665594788403821010051695980527613326657*x3^2 + 614926887451897513755165459646375637198*x3*x4 + 707939183293006236691746018801549456895*x4^2,
    "sol": [2959622489098, -3197305538683, -326156486709, -251632385605],
    "known_variables": [0, 1],
  },
  {
    "p" : 1440277892930363003468057636460118658103216465232904393614497292026369681635352019311970201,
    "iso_degree": 2**200,
    "quadratic_form": 2127448841056343541941029118293939656222437743*x1^2 + 862072184156666365618462032568060450526091666*x1*x2 + 1149429578875555154157949376757413934034788888*x1*x3 - 1166934923077423231012926852929447451002044287*x1*x4 + 3224592067252482317547911408316664487006783801*x2^2 + 2674350965562897604670593547460753895612008613*x2*x3 - 1436786973594443942697436720946767417543486110*x2*x4 + 3270006872778995071102689973024780783150181181*x3^2 + 287357394718888788539487344189353483508697222*x3*x4 + 4275935596284428135585570803097389284513972017*x4^2,
    "sol": [-15068121, -16403852, 10345209, -15303904],
    "known_variables": [0],
  },
  {
    "p" : 1440277892930363003468057636460118658103216465232904393614497292026369681635352019311970201,
    "iso_degree": 2**200,
    "quadratic_form": 947442558547499972840090421664780500336286440*x1^2 + 222006505247077872557498510378590966953279576*x1*x2 - 111003252623538936278749255189295483476639788*x1*x3 - 598611935794803365606328367133797078491262105*x1*x4 + 2076521737242843912895070711882323289019664958*x2^2 + 1364417874194459371231528920245815290480456467*x2*x3 + 333009757870616808836247765567886450429919364*x2*x4 + 4246455340240184179990987786478999409438502557*x3^2 + 1110032526235389362787492551892954834766397880*x3*x4 + 8910336328722272511846960593876907168369535861*x4^2,
    "sol": [15897369, -1415259, -12319644, 10153267],
    "known_variables": [3],
  },
  {
    "p" : 1440277892930363003468057636460118658103216465232904393614497292026369681635352019311970201,
    "iso_degree": 2**250,
    "quadratic_form": 1643332766101844214369642768247707011958882782*x1^2 + 613212358032362104529337538068517299682741852*x1*x2 - 833816100074240010621935384221344825186798156*x1*x3 - 641296424125833205755372092979332694344129735*x1*x4 + 2531634056987311977844282810634284876357134721*x2^2 + 1174375686802198456073921359081127561694614119*x2*x3 + 1383993965780451328512540392857465954617818330*x2*x4 + 3631344221856063323658586904120920512077487708*x3^2 + 1815672110928031661829293452060460256038743854*x3*x4 + 5447016332784094985487880356181380768116231562*x4^2,
    "sol": [613633309143435, 572710628618534, 118276914749744, -186344445742222],
    "known_variables": [0, 1],
  },
  {
    "p" : 2579908397044906386174096217920439652593588922415368592793419268598829754333482685849358216105220563528103302315835492749673140151624434689229190967453,
    "iso_degree": 2**330,
    "quadratic_form": 1476039848139568345957398233132065551070118393558818672086906013422308893138*x1^2 + 467183475178706746354846443735702396922025500428240632379497048864323244128*x1*x2 + 1476039848139568345957398233132065551070118393558818672086906013422308893138*x1*x3 + 1005668566614985649538186943083580981351153002547376000963797900179059174999*x1*x4 + 1788278465337625016639908319382448772211377472962964127041821744241368380148*x2^2 + 470371281524582696419211290048484569718965391011442671123108113243249718139*x2*x3 - 1554686727748271643462485097514597573750364722748843810852073219809206758084*x2*x4 + 4428119544418705037872194699396196653210355180676456016260718040266926679414*x3^2 + 1669199068081321715624027157724655396582170307052688562058836040060874460814*x3*x4 + 5498659717285475788199468871406120419542179321772875713585637679458057504659*x4^2,
    "sol": [-990745790576, 123088323358, -213144802835, -121167473484],
    "known_variables": [0],
  },
  {
    "p" : 2579908397044906386174096217920439652593588922415368592793419268598829754333482685849358216105220563528103302315835492749673140151624434689229190967453,
    "iso_degree": 2**350,
    "quadratic_form": 792814094238074816311294249299816506127060782526568837239990406585018399342*x1^2 + 729559611627376495080121883635622292234872769455952237838528517143500125208*x1*x2 - 126508965221396642462344731328388427784376026141233198802923778883036548268*x1*x3 - 92439550656919203670534041208748189688915496550713595433723813897548576841*x1*x4 + 1425220769706644503891765175620557379431451726884856135672588802994049841977*x2^2 + 1036438064055048321369829247892078670652357708930725114684136586363637548697*x2*x3 + 661762704531159522543164700334247882158285145401855557829592054557599308330*x2*x4 + 5885762180140416422908128784899725897103637900640851733557802839771296521590*x3^2 + 5506235284476226495521094590914560613750509822217152137149031503122186876786*x3*x4 + 10244641040307818310911135987374584567100620169531294879212323418356078240169*x4^2,
    "sol": [-71248566063074, -373594624032602, -134171483042985, 482723357768614],
    "known_variables": [0, 1],
  },
  {
    "p" : 2579908397044906386174096217920439652593588922415368592793419268598829754333482685849358216105220563528103302315835492749673140151624434689229190967453,
    "iso_degree": 2**390,
    "quadratic_form": 1361010983718916658037840523539496710738722176429112993100841721663420475498*x1^2 + 907340655812611105358560349026331140492481450952741995400561147775613650332*x1*x2 - 689569705975493478565984082846556011754042401285269143832701594526268503936*x1*x3 + 952103710884452183371588595901648032477092414747750548042764231230972947427*x1*x4 + 1814681311625222210717120698052662280984962901905483990801122295551227300664*x2^2 + 952103710884452183371588595901648032477092414747750548042764231230972947427*x2*x3 + 1554162081890292760335704507729840037323451478212192557138778280189006636866*x2*x4 + 4562363360614762576247532632811943963605707960059484351918916594796767096591*x3^2 + 3041575573743175050831688421874629309070471973372989567945944396531178064394*x3*x4 + 6083151147486350101663376843749258618140943946745979135891888793062356128788*x4^2,
    "sol": [-138398247611548888645, -1111598436980824259864, -7769179677861888979, -48648347616847355727],
    "known_variables": [0, 1],
  },
  {
    "p" : 2579908397044906386174096217920439652593588922415368592793419268598829754333482685849358216105220563528103302315835492749673140151624434689229190967453,
    "iso_degree": 2**395,
    "quadratic_form": 1130034136687505223431383342016877945848167765629507899157871130096471745721*x1^2 + 185240425265208501957508201476445768465066101222770410868862347690707399916*x1*x2 - 370480850530417003915016402952891536930132202445540821737724695381414799832*x1*x3 + 699403471957215712897589040602568081964459246458845367400721261922522954753*x1*x4 + 1322015403943574738654015971178662486872639538940334818574664074968820211022*x2^2 + 792739732393516673074647126784049645633989191556862753247849218781026675485*x2*x3 + 555721275795625505872524604429337305395198303668311232606587043072122199748*x2*x4 + 5556834423001225156979858623902908165571308883049522109942227693623855007873*x3^2 + 926202126326042509787541007382228842325330506113852054344311738453536999580*x3*x4 + 6470072629063422253004492726621090088858902777054648014102628439556345474012*x4^2,
    "sol": [-759040873721068948730, 1703294315244566194473, -3868190553487666421745, 252389899827062979905],
    "known_variables": [0, 1],
  },
]


for ind, form in enumerate(forms):

  p = form["p"]
  iso_degree = form["iso_degree"]
  quadratic_form = form["quadratic_form"]
  sol = form["sol"]

  f = quadratic_form - iso_degree 
  iso_deg = form["iso_degree"].bit_length()
  S = spline([(58, 3), (6, 2), (101, 2), (121, 2), (141, 6), (151, 14), (161, 17), (166, 19), (171, 21), (181, 26), (201, 37), (211, 42), (251, 50), (331, 40), (351, 49), (391, 70), (396, 72)])
  b = 2**ceil(S(iso_deg))
  bounds = (b, b, b, b)
  for i in range(4):
      assert abs(sol[i]) <= b
  if iso_degree > p ** (2/3) or iso_degree < p ** (1/2):
      continue
  
  assert f(sol) == 0
  start = time.time()
  print("==================================================================================================")
  print("f: ", f)
  print("solution: ", sol)
  print("bounds:", bounds)
  M = [2, 3, 4]
  for i in M:
      print("m: ", i)
      if four_variables_JM(f, b, b, b, b, sol, m=i) != None:
          break
  end = time.time()
  print(f"Solving time for f is : {end - start:.2f}")
