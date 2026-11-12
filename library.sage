import itertools
import numpy as np

def base_number_field(f):
	K = f.parent().base_ring()
	if K.is_field():
		return K
	return K.number_field() # K is an order

###################################################################
### Compute q
###################################################################

# decides if f is monic and integral
def is_monic_integral( f ):
	return f.is_monic() and all( c.is_integral() for c in f )

# computes q for a polynomial f over QQ
def abspoly_q( f, prec = 200 ):
	roots = f.roots( ring=ComplexField(prec) )
	return sum([ m * abs(x)**2 for x, m in roots ]) / f.degree()

# computes q for an element alpha of a number field
def elm_q( alpha, prec = 200, embeddings=None ):
	if embeddings == None:
		return abspoly_q( alpha.absolute_minpoly(), prec=prec )
	return sum([ sigma(alpha).norm() for sigma in embeddings ]) / len(embeddings)

def relpoly_q_alt( f, embeddings ):
	total = RR(0)
	for sigma in embeddings:
		coeffs = [complex(sigma(f[i])) for i in range(f.degree(), -1, -1)]
		total += sum( CC(x).norm() for x in np.roots(coeffs) )
	return total / f.degree() / len(embeddings)

### Decomposition quality
def elm_q_exact(alpha, embeddings):
	return sum(sigma(alpha).norm() for sigma in embeddings) / len(embeddings)

def is_decomposition_exact( alpha, beta ):
	K = beta.parent()
	if not K.is_field():
		K = K.number_field()
	embeddings = K.embeddings(QQbar)
	qx = elm_q_exact(alpha,embeddings)
	qy = elm_q_exact(alpha-2*beta,embeddings)
	return qx >= qy

def elm_decomp_quality( alpha, beta, prec = 200 ):
	if beta==0 or beta==alpha or not beta.is_integral():
		return -Infinity
	K = beta.parent()
	if not K.is_field():
		K = K.number_field()
	embeddings = K.complex_embeddings(prec=prec)
	score = elm_q( alpha, embeddings=embeddings ) - elm_q( alpha-2*beta, embeddings=embeddings )
	if abs(score) < 2^(10-prec/2): # insufficiently certain, proceed to exact arithmetic
		if is_decomposition_exact( alpha,  beta ):
			return 0
		return -Infinity
	return score	

def relpoly_decomp_quality( f, prec = 200 ):
	K = base_number_field(f)
	L.<beta> = K.extension(f)
	return elm_decomp_quality(K.gen(),beta,prec=prec)

def abspoly_decomp_quality( f, g ):
	K.<alpha> = QQ.extension( f )
	P.<Y> = K[]
	g2 = g(Y).factor()[0][0]
	return relpoly_decomp_quality( g2 )

def is_strongly_indecomposable( alpha ):
	embeddings = alpha.parent().embeddings(QQbar)
	return elm_q_exact( alpha, embeddings ) < 2

###################################################################
### List candidates
###################################################################

# computes the term-wise bounds obtained from Lemma XYZ
def maclaurin_bound( deg, q_bound = 4 ):
	P.<X> = RR[]
	f = (X+(q_bound+0.001)**.5)^deg
	return [ x.floor() for x in list(f) ]

# decides whether an element a of a number field is a root of unity
def is_root_of_unity( a ):
	return a.absolute_minpoly().is_cyclotomic()

# decides whether the quotient of roots of irreducible polynomials f and g is a root of unity
def quotient_is_root_of_unity( f, g ):
	if f[0].abs()^g.degree() != g[0].abs()^f.degree():
		return False
	K.<a> = NumberField(f)
	P.<X> = K[]
	for g2, _ in P(g).factor():
		L.<b> = K.extension(g2)
		if is_root_of_unity(a/b):
			return True
	return False

# computes all irreducible monic polynomials in ring up to isometry of degree deg and with q at most q_bound
def get_all_candidates( ring, deg, q_bound = 4, verbose = False ):
	P.<X> = QQ[]
	b = maclaurin_bound( deg, q_bound )
	L1 = [ P(l) for l in itertools.product(*([range(-r,r+1) for r in b[:-1]]+[range(1,2)])) ]
	L2 = list(filter(lambda f: f.is_irreducible(), L1 ))
	L3 = list(filter(lambda f: abspoly_q(f) <= q_bound, L2 ))
	L4 = [ f for i,f in enumerate(L3) if all( not quotient_is_root_of_unity(f,g) for g in L3[:i] ) ]
	if verbose:
		print("Number of polynomials satisfying Maclaurin bound :",len(L1))
		print("Number of which are irreducible :",len(L2))
		print("Number of which have q <=",q_bound,":",len(L3))
		print("Number of which are unique up to roots of unity :",len(L4))
	return L4

### Check decomposition
def elm_is_decomp( alpha, beta ):
	return elm_decomp_quality( alpha, beta ) >= -10**(-50) and beta.is_integral() # Should think how to fix

def relpoly_is_decomp( f ):
	return relpoly_decomp_quality( f ) >= -10**(-50) and is_monic_integral(f)

def abspoly_is_decomp( f, g ):
	return abspoly_decomp_quality( f, g ) >= -10**(-50) and is_monic_integral(g)

###################################################################
### File I/O
###################################################################

# writes the list L of polynomials and their data to a file at path
def write_algebraic_integers( L, path = "data.txt" ):
	with open(path,"w") as file:
		for f, status, g in L:
			for c in f:
				file.write(str(c))
				file.write(" ")
			file.write(status)
			file.write(" ")
			if status == "decomposable" or status == "indecomposable":
				for c in g:
					for d in c:
						file.write(str(d))
						file.write(" ")
			file.write("\n")

# breaks up a list L into a list of lists of size s
def chunks(L,s):
    for i in range(0,len(L),s):
        yield L[i:i + s]

# reads a list of polynomials and their data from a file at path
def read_algebraic_integers( path = "data.txt" ):
	P.<X> = QQ[]
	L = []
	with open(path,"r") as file:
		for line in file:
			words = line.split()
			status_position = 0
			for i, word in enumerate(words):
				try:
					words[i] = QQ(word)
				except TypeError:
					status_position = i
			degree = status_position-1
			status = words[status_position]
			f = P(words[:status_position])
			K.<alpha> = QQ.extension(f)
			P2.<Y> = K[]
			g = P2([K(elm) for elm in chunks(words[status_position+1:],degree)])
			L.append((f,status,g))
	return L

# initializes the list of polynomial candidates of degree 3
def initialize_algebraic_integers( path = "data.txt", verbose = False ):
	P.<X> = QQ[]
	L = [ (f,"indeterminate",P(0)) for f in get_all_candidates( P, 3, 4.0, verbose ) ]
	write_algebraic_integers( L, path )
	return L

###################################################################
### Exp bounded polynomials
###################################################################

def real_poly_check( f, r, a ):
	result = [True,True]
	if a <= 0.0:
		result[1] = False
	if f(r) > 1.0:
		result = [False,False]
	if f(0)*exp(a*r**2) > 1.0:
		result[0] = False
	X = f.parent().gen()
	B = (f.derivative()-2*a*X*f)
	if B == 0:
		return [False,False]
	for x in B.real_roots():
		if 0.0 <= x and f(x)*exp(-a*(x**2-r**2) ) > 1.0:
			if x <= r:
				result[0] = False
			if x >= r:
				result[1] = False
	return tuple(result)

def real_exponentially_bounded_interval( f, r, L, R ):
	if f(r) > 1.0: # Unsalvageble
		return [0.0,-1.0]
	if L == None:
		L, R = -1.0, 1.0
		while real_poly_check( f, r, R ) != (False,True): R *= 2
		while real_poly_check( f, r, L ) != (True,False): L *= 2
	A, B = L, R
	C, D = L, R
	for _ in range(20):
		M1 = (A+B)/2
		if real_poly_check( f, r, M1 )[1] == True:
			B = M1
		else:
			A = M1
		M2 = (C+D)/2
		if real_poly_check( f, r, M2 )[0] == True:
			C = M2
		else:
			D = M2
		if A > D:
			return [0.0,-1.0]
	return [(A+B)/2,(C+D)/2]	

def exponentially_bounded_interval( f, r, places ):
	interval = [None,None]
	P.<X> = RealField(prec=places[0].codomain().prec())[]
	for sigma in places:
		g = P([ abs(sigma(a)) for a in f ])
		interval = real_exponentially_bounded_interval( g, r, *interval )
		if interval[0] > interval[1]:
			break
	return interval

def is_exponentially_bounded( f, r, prec = 200, return_scalar = False ): 
	interval = exponentially_bounded_interval( f, r, f.parent().base_ring().places( prec=prec ) )
	if return_scalar:
		return ( interval[0] < interval[1], (interval[0]+interval[1])/2 )
	return interval[0] < interval[1]

###################################################################
### Computation
###################################################################

load("lattice.sage")

def compute( f ):
	print(f)
	K.<a> = NumberField(f)
	P.<X> = K[]
	# check if trivially indecomposable
	if is_strongly_indecomposable( a ):
		return "indecomposable", P(0)
	# check if decomposable in own field
	result = decomposable_from_order(f)
	if result[0] == "decomposable":
		return result
	# check if decomposable in small field extension
	for d in range(2,17):
		result = decomposable_from_lattice(f,degree=d,sol_max=100,doubling=False) 
		if result[0] == "decomposable":
			return result
	# check for indecomposability_certificate
	result = indecomposable_from_lattice(f,degree=16,sol_max=100)
	if result[0] == "indecomposable":
		return result

	
def compute_all( L = None, path = "data.txt" ):
	if L == None:
		L = read_algebraic_integers(path)
	else:
		path = None
	for i in range(len(L)):
		if L[i][1] == "indeterminate":
			result = compute(L[i][0])
			if result != None:
				print(result[0])
				L[i] = L[i][0], result[0], result[1]
	if path != None:
		write_algebraic_integers(L, path)

###################################################################
### Verification
###################################################################

### Verifier
def verify_decomposable(g, verbose=False):
	if not g.is_irreducible():
		return False
	K = base_number_field(g)
	alpha = K.gen()
	L.<beta> = K.extension(g)
	if beta == 0 or beta == alpha or not beta.is_integral():
		return False
	return is_decomposition_exact(alpha,beta)

def verify_indecomposable(g):
	K = base_number_field(g)
	alpha = K.gen()
	if g.degree() < 0:
		return is_strongly_indecomposable(alpha)
	for gi,_ in g.change_ring(K).factor():
		if verify_decomposable(gi):
			return False
	X = g.parent().gen()
	h = g(X+alpha/2)
	r = sqrt(elm_q(alpha/2))
	return is_exponentially_bounded(h,r)

def verify_entry(T):
	f, status, g = T
	if status == "indeterminate":
		return True
	elif status == "decomposable":
		return verify_decomposable(g,verbose=True)
	elif status == "indecomposable":
		return verify_indecomposable(g)
	raise ValueError

def verify_all( path = "data.txt" ):
	return all( verify_entry(T) for T in read_algebraic_integers( path ) )

def status_all( path = "data.txt" ):
	group = { "indeterminate" : [0,Infinity,-Infinity], "decomposable" : [0,Infinity,-Infinity,Infinity], "indecomposable" : [0,Infinity,-Infinity] }
	for f, status, g in read_algebraic_integers():
		group[status][0] += 1
		q = abspoly_q(f)
		group[status][1] = min( group[status][1], q )
		group[status][2] = max( group[status][2], q )
		if status == "decomposable":
			group[status][3] = min( group[status][3], relpoly_decomp_quality(g) )
	return group

def scrub_all( path = "data.txt" ):
	L = read_algebraic_integers( path )
	for i in range(len(L)):
		if not verify_entry(L[i]):
			print(L[i])
			L[i] = (L[i][0],"indeterminate",0)
	write_algebraic_integers( L )
