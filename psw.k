
/ details for ks
a: 0: `"C:/msys64/home/tavme/ks/ggg"
a: a," "
c: & "~" = *:'a
r: & "#" = *:'a
b: (#a)#0
b[c]: 2
b[r+1]: b[r+1]-2
b: +\b
a: (b #' " "),'a
`"C:/msys64/home/tavme/ks/ksd" 0: a

/ summary for ks
a: 0: `"C:/msys64/home/tavme/ks/ggg"
a: a," "
a: a[& ("~" = *:'a) | "#" = *:'a]
c: & "~" = *:'a
r: -1 _ & "#" = *:'a
b: (#a)#0
b[c]: 2
b[r+1]: b[r+1]-2
b: +\b
/a: 2 _' (b #' " "),'a
a: (b #' " "),'a
`"C:/msys64/home/tavme/ks/kss" 0: a
