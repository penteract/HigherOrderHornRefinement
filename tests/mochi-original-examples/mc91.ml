let rec mc91 x =
  if x > 100 then
    x - 10
  else
    mc91 (mc91 (x + 11))
let main n = if n <= 101 then assert (mc91 n = 91)
