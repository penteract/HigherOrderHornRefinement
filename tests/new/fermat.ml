
pow b x = if x==0 then 1 else b*pow b (x-1)

main a b c n = if a>0 && b>0 && c>0 && n>2 then assert pow a n + pow b n /= pow c n else assert true
