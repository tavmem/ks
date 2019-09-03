tk:("F";"G")
call:{ nm:*tk; tk::1 _ tk; if[nm~"G"; :0]; call(); nm }
call()
