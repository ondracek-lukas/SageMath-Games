# encoding: utf8
# Copyright (C) 2017 Lukáš Ondráček <ondracek.lukas@gmail.com>, use under GNU GPLv3 or higher

r"""
Conway games.

This module implements (finitely represented) Conway numbers/games for combinatorial games analysis.

It contain class `Game` and predefined games `zero`, `star`, `up`, `down`, `nimber(n)`.

.. SEEALSO:: `Game`

AUTHOR: Lukáš Ondráček (2017)

"""
from sage.all_cmdline import *
from sage.structure.unique_representation import CachedRepresentation
from sage.misc.cachefunc import CachedMethod,CachedFunction

f = lambda self,other: False
r = lambda self: 'Fuzzy'
Fuzzy = type("Fuzzy", (), {'__gt__':f, '__ge__':f, '__lt__':f, '__le__':f,'__repr__':r})()
del f,r

class Game(CachedRepresentation):
    r"""
    The "Game" class represents Conway numbers/games.

    It consists of two sets (left L and right R) of games,
    which represents possible options of left and right player.

    Game() interprets
      * two iterables as sets L and R,
      * one iterable as set L == R (impartial game),
      * integer or dyadic fraction as a value game should equal to,
      * no parameters as zero game.
    Newly created instance is in its canonical form,
    i.e. it doesn't contain reversible moves or dominated options.
    Equal games are represented by the same instance.

    Sum, subtraction, multiplication, negation, length (aka birthday)
    and comparing operators are defined on Game instances.
    Every time Game instance is expected (e.g. as the other operand)
    the first (and only) parameter of its constructor can be used instead.

    There are predefined games
    zero, star, up, down, nimber(n).

    EXAMPLES::

        sage: Game()           # == zero
        0g
        sage: Game(2).strExpanded()
        '{{{|}|}|}'
        sage: Game([2*up], [star, down])
        {2↑|*,↓}g
        sage: 0 < up < 1/16
        True
        sage: Game(5) - Game(5.5)
        -1/2g
        sage: Game([1,2,3])    # == {1,2,3}g == {1,2,3|1,2,3}g
        {3|1}g
        sage: nimber(5)+nimber(3)
        *6g
        sage: len(Game(1/4))
        3
    """
    @staticmethod
    def __classcall__(cls, arg=None, arg2=None):
        if arg2 != None:
            L = [Game(g) for g in arg]
            R = [Game(g) for g in arg2]
        elif arg == None:
            R=[]; L=[]
        elif isinstance(arg, Game):
            return arg;
        elif hasattr(arg, '__iter__'):
            L = R = [Game(g) for g in arg]
        elif -_oo < arg < _oo:
            arg=_Rational(arg)
            if not _is_power_of_two(arg.denominator()):
                raise ValueError("The number is not a dyadic rational.")
            L=[]; R=[]; l=-_oo; m=_Rational(0); r=_oo
            while arg != m:
                if arg > m:
                    L = [Game(L,R)]
                    l = m
                    m = (l+r)/2 if r<_oo else m+1
                else:
                    R = [Game(L,R)]
                    r = m
                    m = (l+r)/2 if l>-_oo else m-1
        else:
            raise ValueError("Wrong arguments.")

        g=super(Game, cls).__classcall__(cls, frozenset(L), frozenset(R)); # non-canonical form

        arr=[]
        L=list(g.L)
        while L:
            x=L.pop(0)
            reversible=False
            for xr in x.R:
                if xr <= g:          # x is reversible move
                    reversible=True
                    L.extend(xr.L)
                    break
            if reversible: continue
            c=0
            for y in list(L):
                c=Game._cmp(x,y)
                if c>0: L.remove(y)  # y is dominated by x
                if c<0: break;       # x is dominated by y
            if not c<0: arr.append(x)
        L=arr
        arr=[]
        R=list(g.R)
        while R:
            x=R.pop(0)
            reversible=False
            for xl in x.L:
                if xl >= g:           # x is reversible move
                    reversible=True
                    R.extend(xl.R)
                    break
            if reversible: continue
            c=0
            for y in list(R):
                c=Game._cmp(x,y)
                if c<0: R.remove(y)  # y is dominated by x
                if c>0: break;       # x is dominated by y
            if not c>0: arr.append(x)
        R=arr

        return super(Game, cls).__classcall__(cls, frozenset(L), frozenset(R)); # canoninal form

    def __init__(self, L, R):
        self.L=L
        self.R=R


    @CachedMethod
    def _repr(self, expanded=False):
        Lrep = [ l._repr(expanded) for l in self.L ]
        Rrep = [ r._repr(expanded) for r in self.R ]
        if not expanded:
            if all(-_oo<l<_oo for l in Lrep) and all(-_oo<r<_oo for r in Rrep):
                if Lrep:
                    if Rrep:
                        if max(Lrep)<min(Rrep):
                            return (max(Lrep)+min(Rrep))/_Rational(2)
                    else:
                        return max(Lrep)+1
                else:
                    if Rrep:
                        return min(Rrep)-1
                    else:
                        return 0

            if self == star:
                return "*"
            if self == up:
                return "↑"
            if self == down:
                return "↓"

        if not expanded and self.L == self.R:
            if self == nimber(len(self.L)):
                return "*" + str(len(self.L))
            return "{"  + ",".join([str(rep) for rep in Lrep]) + "}"

        if not expanded:
            if self == (len(self)-1)*up:
                return str(len(self)-1) + "↑"
            if self == (len(self)-1)*down:
                return str(len(self)-1) + "↓"

        return "{"  + ",".join([str(lrep) for lrep in Lrep]) + "|" + ",".join([str(rrep) for rrep in Rrep]) + "}"

    def __repr__(self):
        return str(self._repr()) + 'g'
    def strExpanded(self): return self._repr(True)
    def str(self): return self._repr()


    @staticmethod
    @CachedFunction
    def _sum(x, y):
        return Game(
                [ xl + y  for xl in x.L ] +
                [ x  + yl for yl in y.L ],
                [ xr + y  for xr in x.R ] +
                [ x  + yr for yr in y.R ])

    def __add__(self, right):
        return Game._sum(self, Game(right))
    def __radd__(self, left):
        return Game._sum(Game(left), self)

    @CachedMethod
    def __neg__(self):
        return Game(
                [ -r for r in self.R ],
                [ -l for l in self.L ])

    def __sub__(self, right):
        return self+(-Game(right))
    def __rsub__(self, left):
        return Game(left)+(-self)

    @staticmethod
    @CachedFunction
    def _mul(x, y):
        return Game(
                [ xl * y  + x  * yl - xl * yl for xl in x.L for yl in y.L ] +
                [ xr * y  + x  * yr - xr * yr for xr in x.R for yr in y.R ],
                [ xl * y  + x  * yr - xl * yr for xl in x.L for yr in y.R ] +
                [ x  * yl + xr * y  - xr * yl for yl in y.L for xr in x.R ])
    def __mul__(self, right):
        return Game._mul(self, Game(right))
    def __rmul__(self, left):
        return Game._mul(Game(left), self);

    @staticmethod
    @CachedFunction
    def _cmp(x, y):
        x_le_y = all( not Game._cmp(xl,y) >= 0 for xl in x.L ) and \
                 all( not Game._cmp(x,yr) >= 0 for yr in y.R )
        y_le_x = all( not Game._cmp(yl,x) >= 0 for yl in y.L ) and \
                 all( not Game._cmp(y,xr) >= 0 for xr in x.R )
        if x_le_y:
            if y_le_x:
                return 0
            else:
                return -1
        else:
            if y_le_x:
                return 1
            else:
                return Fuzzy

    def __gt__(self, other):
        return Game._cmp(self, Game(other)) > 0
    def __lt__(self, other):
        return Game._cmp(self, Game(other)) < 0
    def __ge__(self, other):
        return Game._cmp(self, Game(other)) >= 0
    def __le__(self, other):
        return Game._cmp(self, Game(other)) <= 0

    @CachedMethod
    def _depth(self):
        if self==zero:
            return 0
        else:
            return max((l._depth() for l in self.L | self.R))+1

    def __len__(self):
        return self._depth()



zero=Game()
star=Game([zero],[zero])
up  =Game([zero],[star])
down=Game([star],[zero])
@CachedFunction
def nimber(n):
    r"""
    The "nimber" function creates a Game Nim with one heap of given size.
    """
    return Game([nimber(i) for i in range(n)]);


# clean the namespace
__all__ = {"Game", "zero", "star", "up", "down", "nimber", "Fuzzy"}
_needed = {"oo", "Rational", "is_power_of_two"}
for _k in globals().keys():
    if _k in _needed:
        globals()['_'+_k] = globals()[_k]
    if not _k.startswith("_") and _k not in __all__:
        del globals()[_k]
del _k, _needed
__all__ = list(__all__)
