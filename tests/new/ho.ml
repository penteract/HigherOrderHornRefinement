#a composition of permutations is a permutation

#given an integer p representing a permutation of [1..n], apply p to i
perm n p i = assert (i<fact n && i>=0)
  let last = 1 + div p (fact (n-1)) in
    if i==n then last else
      let r = perm (n-1) (mod p (fact (n-1))) i in
        if r>=last then r+1 else r


#better than a function
divmod a b q r <= 0<=r && r<b && a=b*q+r

comp f g x = f (g x)

goal:
E p q n. 0<=p && p<fact n && 0<=q && q<fact n && comp (perm n p) (perm n q) i == perm n z i
#I would like to say that for all p,q there exists z, but can't mix quantifiers.
