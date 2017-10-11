# vim: ft=python
import games as g

@CachedFunction
def chocolate(n,m):
    return g.Game(
            [chocolate(n, i) + chocolate(n,   m-i) for i in [1..m-1]] +
            [chocolate(i, m) + chocolate(n-i, m  ) for i in [1..n-1]] )

def chocolateResult(n,m):
    game = chocolate(n,m);
    if game == g.star:
        print("First player has a winning strategy.")
    elif game == g.zero:
        print("Second player has a winning strategy.")
    else:
        print("Was it really a chocolate?")

