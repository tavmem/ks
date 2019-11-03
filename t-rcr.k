tokens: ((`id;"F")
(`oparen;"(")
(`id;"G")
(`oparen;"(")
(`cparen;")")
(`comma;",")
(`id;"H")
(`oparen;"(")
(`cparen;")")
(`cparen;")"))

peek: {x~tokens[;0][0]}
eat: {
  t: *tokens
  tokens :: 1 _ tokens
  if[~x~t[0]; \echo "no match for ",$x; : 0]
  t}

parse_call: {
  name:eat[`id]@1
  ae: parse_arg_exprs()
  .((`name;name);(`arg_exprs;ae))}

parse_arg_exprs: {
  arg_exprs:()
  eat[`oparen]
  if[~peek[`cparen]
    arg_exprs:,parse_call()
    while[peek[`comma]
      eat[`comma]
      arg_exprs,:,parse_call()]]
  eat[`cparen]
  arg_exprs}

parse_call()
