from sage.modules.free_module_integer import IntegerLattice
from fpylll import IntegerMatrix, LLL, GSO, CVP, Enumeration, BKZ, EvaluatorStrategy, EnumerationError
import time
from sage.rings.number_field.all import is_real_place

###################################################################
### Same field decompositions
###################################################################

class OrderLattice:
    def dimension(self):
        return len(self.basis)

    def encode( self, x ):
        v = []
        for sigma in self.Sigma:
            y = sigma(x)*10**self.prec
            if is_real_place( sigma ):
                v.append( y.integer_part() )
            else:
                y = RR(sqrt(2))*y
                v.append( y.real().integer_part() )
                v.append( y.imag().integer_part() )                
        return vector(v)
        
    def decoded_vector_to_element( self, y ): 
        return sum( yi*bi for yi,bi in zip( y, self.R.basis() ) )

    def __init__( self, order, precision = 7 ):
        self.R = order
        self.prec = precision
        self.Sigma = self.R.number_field().places( prec=200 )
        self.basis = self.R.basis()
        self.A = IntegerMatrix.from_matrix( [ self.encode( b ) for b in self.basis ] )
        self.G = GSO.Mat( self.A )
        self.G.update_gso()

    def closest_vector( self, x ):
        v = self.encode( x )
        w = CVP.closest_vector( self.A, v )
        return self.decode( w )

    def close_vectors( self, x, count=10 ):
        t = self.G.from_canonical(self.encode(x))
        E = Enumeration( self.G, nr_solutions=count, strategy=EvaluatorStrategy.BEST_N_SOLUTIONS )
        results = E.enumerate( 0, self.A.nrows, 100**(self.prec+1), 0, target = t )
        return [ self.decoded_vector_to_element([int(ri) for ri in r]) for _,r in results ]

def decomposable_from_order( f, verbose = 0 ):
    K.<alpha> = QQ.extension( f )
    P.<X> = K[]
    R = K.OK()
    L = OrderLattice( R )
    maxq = -Infinity
    for beta in L.close_vectors( alpha/2, count = 20 ):
        maxq = max(maxq,elm_decomp_quality( alpha, beta ))
        if elm_decomp_quality( alpha, beta ) > -0.000000001:
            return "decomposable", X - beta
    return "indeterminate", P(0)

###################################################################
### Extension decompositions
###################################################################

def pad_list( L, n ):
    return L + [0]*(n-len(L))

def split_list( L, d ):
    return [L[d*i:d*(i+1)] for i in range(len(L)//d)]

class PolynomialLattice:
    def dimension(self):
        return len(self.basis)

    def encode( self, f ):
        g = f.change_ring(self.P.base_ring().number_field())
        X = g.parent().gen()
        g = f.substitute({X:X+self.c})
        g = g.substitute({X:self.r.exact_rational()*X}) # somehow prevent blowup from exact rational
        if self.doubling:
            return vector([ v for c in pad_list( list(g), 2*self.degree )[::2] for v in self.order_lattice.encode( c ) ])
        return vector([ v for c in pad_list( list(g), self.degree ) for v in self.order_lattice.encode( c ) ])

    def decoded_vector_to_element( self, y ): # fix
        return sum( yi * bi for yi,bi in zip(y,self.basis) )
        #self.P([self.order_lattice.decoded_vector_to_element(yi) for yi in split_list(y,self.order_lattice.R.degree()) ])

    def __init__( self, polynomial_ring, degree, doubling=False, center=None, radius=None, precision=7, bkz_size=20 ):
        self.P = polynomial_ring
        self.doubling = doubling
        order = self.P.base_ring()
        self.c = order.number_field().gen() / 2 if center == None else center
        self.r = sqrt(elm_q( self.c )) if radius == None else radius
        self.order_lattice = OrderLattice( order, precision=precision )
        self.degree = degree
        X = self.P.gen()
        if doubling:
            self.basis = [ b*X**i*(self.P(2*self.c)-X)**i for i in range(self.degree) for b in self.order_lattice.basis ]
        else:
            self.basis = [ b*X**i for i in range(self.degree) for b in self.order_lattice.basis ]
        self.A = IntegerMatrix.from_matrix( [ self.encode( b ) for b in self.basis ] )
        self.B = IntegerMatrix(self.A)
        self.U = IntegerMatrix.identity(self.dimension())
        par = BKZ.Param(block_size=bkz_size,strategies=BKZ.DEFAULT_STRATEGY)
        BKZ.reduction(self.B, par, U=self.U)
        self.G = GSO.Mat(self.B) 
        self.G.update_gso() 

    def _enumerator(self, target, count):
        bound = (10**self.order_lattice.prec)*self.dimension()
        while True:
            try:
                E = Enumeration( self.G, nr_solutions=count, strategy=EvaluatorStrategy.BEST_N_SOLUTIONS )
                results = []
                if target == None:
                    results = E.enumerate( 0, self.B.nrows, bound, 0 )
                else:
                    t = self.G.from_canonical(self.encode(target))
                    results = E.enumerate( 0, self.B.nrows, bound, 0, target=t )
                results = [ vector([int(xi) for xi in x]) for (_,x) in results ]
                shifted = [ self.U.multiply_left(x) for x in results ]
                return [ self.decoded_vector_to_element(x).change_ring(self.order_lattice.R.number_field()) for x in shifted ]
            except EnumerationError:
                bound *= 100

    def short_elements( self, count ):
        return self._enumerator( None, count )

    def close_elements( self, target, count ):
        return self._enumerator( target, count )

def decomposable_from_lattice( f, degree=10, sol_max=20, doubling=False ):
    K.<alpha> = QQ.extension(f)
    R = K.OK()
    P.<Y> = R[]
    c = alpha/2
    qc = elm_q(c)
    L = PolynomialLattice( P, degree, doubling=doubling, bkz_size=35 )
    target = (Y-c)**degree - Y**degree
    if doubling:
        target = (Y^2-c^2)**degree - Y**(2*degree)
    candidates = L.close_elements( target, sol_max )
    embeddings = K.complex_embeddings()
    for g in candidates:
        h = Y**degree + g
        if doubling:
            h = (Y*(Y-alpha))**degree + g
        h0 = h(Y+c)
        if qc - relpoly_q_alt(h0,embeddings) > 0.0001:
            if verify_decomposable(h):
                return "decomposable", h
            print("false positive")
    return "indeterminate", P(0)

def indecomposable_from_lattice( f, degree=10, sol_max=20 ):
    K.<alpha> = QQ.extension(f)
    R = K.OK()
    P.<Y> = R[]
    c = alpha/2
    L = PolynomialLattice( P, degree, doubling=True, bkz_size=35 )
    candidates = L.short_elements( sol_max )
    for g in candidates:
        h = g(Y+c)
        r = sqrt(elm_q(c))
        if is_exponentially_bounded(h,r):
            return "indecomposable", g
    return "indeterminate", P(0)
