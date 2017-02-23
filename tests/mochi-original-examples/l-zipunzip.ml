let f g x y : int = g (x + 1) (y + 1)
let rec unzip x k =
  if x=0 then
    k 0 0
  else
    unzip (x - 1) (f k)
let rec zip x y =
  if x = 0 then
    if y = 0 then
      0
    else
      assert false
  else
    if y = 0 then
      assert false
    else
      1 + zip (x - 1) (y - 1)
let main n = unzip n zip
