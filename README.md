

How I use this repositiory
-----------

Obviously, you can use this stuff any way you want, but here are some tips on what it was designed to do.

The key script is ps.k ...  which you will need to modify so it has your directory structure.

Suppose that you want to examine the details of how a particular command is processed by kona.

Take, for example, a recent issue, #561:
```
(.((`a;1);(`b;2)))(,`a)
```
The first 3 (preparation) commands are done in the ~/ks directory:
```
rlwrap -n ./k > ggg
(.((`a;1);(`b;2)))(,`a)
\\
```
ps.k expects to find the output file ```ggg```

Then, the final 2 commands, which are also done in the ~/ks directory:
```
rlwrap -n ~/kona/k ps
\\
```
You get 2 results:

ksd	(k-show-details)

kss	(k-show-summary)



