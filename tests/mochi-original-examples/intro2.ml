let f x g : unit = g(x+1)
let h y = assert (y>0)
let main n = if n>=0 then f n h
