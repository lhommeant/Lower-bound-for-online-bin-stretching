# Lower-bound-for-online-bin-stretching

Contains source code associated with the following article: https://arxiv.org/abs/2207.04931

This code aims to compute lower bounds for the online bin stretching problem. 
Two different versions are here: the first one, in the folder _proofless_, does not construct a tree proof of the lower bound, unlike the second one, in the folder _tree-proof_. The first one hence uses less memory than the second. 

Warning: The second one may require too much memory to prove a difficult bound. It is recommended to watch out for memory usage while using the second version. 


To compile, one just need to execute the "compile.sh".
It will results it an executable file "bound_finder". 
Options are listed with -h.

Example of usage to prove the bound 19/14 for 3 bins: ./bound_finder -p 3 14 19
