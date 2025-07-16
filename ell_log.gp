/* GP code (pari.math.u-bordeaux.fr)
It computes elliptic presentations and the descent step of the discrete-log algorithm in https://arxiv.org/abs/2206.10327
*/



/* GLOBAL CHOICES
We work in characteristic 2.

On the elliptic curve we will use will have coordinate functions, always 'X and  'Y, (Xglobal, Yglobal below).

Irreducible divisors on the elliptic curve will be the vanishing locus of ideal os the form F(X), G(X,Y), encoded as pairs [F(X), G(X,Y)], monic, reduced as below. 
General divisors will be n x 2 matrices, where the first columns contains irreducible divisor and the second columns the respective multiplicities

For finite fields F_q, K..., we will denote the generator gq, gK... in the variable 'tq, 'tK ..

Marking problems, questions or improvements with ?? or ???
*/


default(parisizemax,"8G");
setrand(2025);


Xglobal = 'X;
Yglobal = varhigher('Y);
ZeroDivisor = matrix(0,2);
debug = 0;
info = 1;
verbose_for_example = 1;



global_debug_var=0;


\\ # ==================== general ==================== # 

my_eval(p,x) = if(variable(p), subst(p,variable(p),x), p)  +x-x;

my_global_eval(poly,P) = subst(subst(poly,Yglobal,P[2]),Xglobal,P[1]);


ffEmbed(x,y) = ffmap(ffembed(x,y),x); \\ given x in F_q, y of F_Q, returns the image of x in F_Q (shortening code)


ffEmbedding(x,y) = (t -> ffmap(ffembed(x,y),t)); \\ given x in F_q, y of F_Q, returns the embedding F_q in F_Q (shortening code) ?? not used

change_coeff_W(embed,W) = Pol( apply(ceof_in_X->ffmap(embed,ceof_in_X), Vec(W + Xglobal+Yglobal-Xglobal-Yglobal)), Yglobal);

field_in_standard(poly, varK = 'tK, generator_K = 0) = {
  \\  input: poly in F_q[x] irreducible
  \\ output: [iso1,iso2, gK] where iso1 is an isomorphism F_q[x]/poly --> F_Q and iso2 its inverse and gK is a generator of F_Q
  my(gq,q,d,gK,qembed,poly_K,r, iso1,rrel,rpowers,rpowers_vec,v,M,vtarget,gKimage,iso2);
  gq = vecsum(Vec(poly));
  q = 2^(gq.f);
  d = poldegree(poly);
  gK = ffgen(q^d, varK); \\ F_Q
  if(generator_K, gK = generator_K);
  qembed = ffembed(gq,gK); 
  poly_K =ffmap(qembed,poly); 
  r = polrootsmod(poly_K)[1]; \\ root of poly in K
  iso1 = (P -> my_eval( ffmap(qembed, lift(P)) , r));  \\versione lunga  [variable(poly), r, qembed,(P -> my_eval( ffmap(qembed,P.pol) , r))];
  \\ We have done iso1, now the inverse. We need to write gK as a polynomial in r with coefficients in F_q
  rrel = ffmaprel(ffinvmap(qembed),r);  
  rpowers = [(rrel^(d-1-i)).pol| i<-[0..d-1]];
  rpowers_vec = List([]);
  foreach(rpowers,p,
    v = Vec(p);    /* Extract the polynomial's coefficients */
    while (#v < d, v = concat(0,v));
    listput(rpowers_vec,v~);
  );
  M = matconcat(Vec(rpowers_vec));
  vtarget = [1,0]; \\ vector version of gK 
  while (#vtarget < d, vtarget = concat(0,vtarget));
  if(d==1,
    gKimage = Mod(ffgen(gq), poly);
    ,
    gKimage = Mod(Pol(matsolve(M,vtarget~)~, variable(poly)), poly);
  );
  \\  print(my_eval(liftall(minpoly(gK)),gKimage)); \\ for debugging
  iso2 = (P -> my_eval( (P+gK-gK).pol , gKimage)) ;  \\vecchia versione  iso2 = [gk, gKimage, (P -> my_eval( P.pol , gKimage)) ];
  [iso1,iso2, gK];
}







\\ # ==================== Elliptic presentation ==================== # 


find_E(g,n) = {
  \\ input:  g a generator of F_q with q = 2^e and n an integer 
  \\ output: [E,P], an elliptic curve E with a point P of order n
  my(vec,vec2,d,a,b,E,P,o, flag);
  d = g.f;
  for(k = 0, 2^d - 1,   /* ``for cycle'' that yields all elements a in F_{2^d} (exploiting binary)*/
    vec = Vec(binary(k));  
    while(#vec < d, vec = concat(0, vec));  
    a = my_eval(Pol(vec),g);
    for(k2 = 1, 2^d - 1,  \\ same for b, just not 1
      vec2 = Vec(binary(k2));  
      while(#vec2 < d, vec2 = concat(0, vec2)); 
      b = my_eval(Pol(vec2),g);
      \\ Now the elliptic curve
      E = ellinit([1+g-g, a+g-g ,0+g-g,0+g-g, b+g-g]);
      if(ellgroup(E)[1]%n == 0,
        flag = 1;
        while(flag,
          P = random(E);
          o = ellorder(E,P);
          if( o%n==0, flag = 0);
        );
        P = ellmul(E,P,o/n);
        return([E, P]);
      );
    );
  );
}


find_presentation(e) = {
  \\ input: e positive integer 
  \\ output: [g,E,P,W,[F,p1]], where g is a generator of F_q. E/F_q an elliptic curve with a point P and Weierstrass equation W. Then [F(Xglobal), p1 = Yglobal+G(Xglobal)] generate the ideal M in the definition. This five object give an elliptic presentation of an extension of F_{2^e}
  my(logq,flag,q,g,n,hopeEP,E,P,Xlocal,Ylocal,W,Psum,p1,p2,p11,q1,q2,q3,F,factors);
  \\  logq = ceil(log(e)/log(2))-1; ??
  logq = ceil(log(e)/log(2))-3;
  flag = 1;
  while(flag,
    q = 2^logq;
    g = ffgen(q, 'tq); \\ generator of F_q
    n = e/gcd(e,logq);
    hopeEP = find_E(g,n); \\ hopefully elliptic curve with point of right order
    if(hopeEP!=0, flag = 0; [E,P] = hopeEP, logq=logq+1);
  );
  \\  q = 2^logq;
  \\  g = ffgen(q, 'tq); \\ generator of F_q
  \\  n = e/gcd(e,logq);
  \\  [E,P] = find_E(g,n); \\ elliptic curve with point of right order
  Xlocal = 'Xlocal;
  Ylocal = 'Ylocal;
  Psum = elladd(E,P,[(1+g-g)*Xlocal,(1+g-g)*Ylocal]);
  p1 = Xlocal^q*denominator(Psum[1])-numerator(Psum[1]);
  p1 = subst(subst(p1,Xlocal,Xglobal),Ylocal,Yglobal); \\ we would like to use Xglobal and Yglobal,  but GP's variables priority would create problems in the line above 
  p2 = Ylocal^q*denominator(Psum[2])-numerator(Psum[2]);
  p2 = subst(subst(p2,Xlocal,Xglobal),Ylocal,Yglobal);
  W = (1+g-g)*(Yglobal)^2+(E[1]*Xglobal+E[3]+g-g)*Yglobal - ((1+g-g)*Xglobal^3+E[2]*Xglobal^2+E[4]*Xglobal+E[5]);  
  \\ p1,p2,W describe the ideal of points such that phi(Q)=Q+P. We lower a bit the degree in X and Y and look for an ideal in the primary decomposition
  p1 = p1%W;
  p2 = p2%W;
  if(variable(p1)!=Yglobal, return(0)); \\?? here we are supposeing that p1 is of the form Y*(element of F_q), but if the code works it is correct
  p11 = polcoeff(p1,1);
  if(subst(p11,Xglobal,0)!=p11, return(0));
  p1 = p1/subst(p11,Xglobal,0);
  q1 = polresultant(W,p1);
  q2 = polresultant(W,p2);
  q3 = polresultant(p1,p2);
  F = gcd(q1,gcd(q2,q3));
  factors = factor(F)[,1];
  \\  print("sono qui");
  foreach(factors, factor, if(poldegree(factor)==n,F = factor));
  if(poldegree(F)!=n, return(0));  
  [g,E,P,W,[F,p1]];
}



find_presentation_small(e) = {
  \\ input: e positive integer 
  \\ output: [g,E,P,W,[F,p1]], where g is a generator of F_q. E/F_q an elliptic curve with a point P and Weierstrass equation W. Then [F(Xglobal), p1 = Yglobal+G(Xglobal)] generate the ideal M in the definition. This five object give an elliptic presentation of an extension of F_{2^e}
  my(logq,flag,q,g,n,hopeEP,E,P,Xlocal,Ylocal,W,Psum,p1,p2,p11,q1,q2,q3,F,factors);
  logq = 2;
  flag = 1;
  while(flag,
    q = 2^logq;
    g = ffgen(q, 'tq); \\ generator of F_q
    n = e/gcd(e,logq);
    hopeEP = find_E(g,n); \\ hopefully elliptic curve with point of right order
    if(hopeEP!=0, flag = 0; [E,P] = hopeEP, logq=logq+1);
  );
  Xlocal = 'Xlocal;
  Ylocal = 'Ylocal;
  Psum = elladd(E,P,[(1+g-g)*Xlocal,(1+g-g)*Ylocal]);
  print("here Psum in find_presentation_small: ",Psum);
  p1 = Xlocal^q*denominator(Psum[1])-numerator(Psum[1]);
  p1 = subst(subst(p1,Xlocal,Xglobal),Ylocal,Yglobal); \\ we would like to use Xglobal and Yglobal,  but GP's variables priority would create problems in the line above 
  p2 = Ylocal^q*denominator(Psum[2])-numerator(Psum[2]);
  p2 = subst(subst(p2,Xlocal,Xglobal),Ylocal,Yglobal);
  W = (1+g-g)*(Yglobal)^2+(E[1]*Xglobal+E[3]+g-g)*Yglobal - ((1+g-g)*Xglobal^3+E[2]*Xglobal^2+E[4]*Xglobal+E[5]);  
  \\ p1,p2,W describe the ideal of points such that phi(Q)=Q+P. We lower a bit the degree in X and Y and look for an ideal in the primary decomposition
  p1 = p1%W;
  p2 = p2%W;
  if(variable(p1)!=Yglobal, return(0)); \\?? here we are supposeing that p1 is of the form Y*(element of F_q), but if the code works it is correct
  p11 = polcoeff(p1,1);
  if(subst(p11,Xglobal,0)!=p11, return(0));
  p1 = p1/subst(p11,Xglobal,0);
  q1 = polresultant(W,p1);
  q2 = polresultant(W,p2);
  q3 = polresultant(p1,p2);
  F = gcd(q1,gcd(q2,q3));
  factors = factor(F)[,1];
  \\  print("sono qui");
  foreach(factors, factor, if(poldegree(factor)==n,F = factor));
  if(poldegree(F)!=n, return(0));  
  [g,E,P,W,[F,p1]];
}

test() = {
for(i=24,50, tmp = find_presentation_small(i);print([i,tmp[1].f,poldegree(tmp[5][1])]););
for(i=50,100, tmp = find_presentation_small(i);print([i,tmp[1].f,poldegree(tmp[5][1])]););
for(i=45,70, tmp = find_presentation_small(i*2+1);print([2*i+1,tmp[1].f,poldegree(tmp[5][1])]););
for(i=10,50, tmp = find_presentation_small(i*2);print([2*i,tmp[1].f,poldegree(tmp[5][1])]););
}


\\ # ==================== divisors ==================== # 

y_coord_div(W,p) = {
  \\  input: W a weierstrass equation and p an irreducible polynomial in the X appearing in W (with Y hagving  higher priority I think?)
  \\  output: the list of all irreducible divisors lying over p(X) (either 1 or 2)
  my(output, iso1,iso2,W_mod_p,q_in_Xvar, D);
  [iso1, iso2] = field_in_standard(p);
  W_mod_p = Pol(apply(iso1,Vec(W)),Yglobal);
  output = List([]);
  foreach( factor(W_mod_p)[,1], q,
    q_in_Xvar = Pol(apply(iso2,Vec(q)),variable(q));
    D = [p, lift(q_in_Xvar)];
    listput(output, D);
  );
  output;
}


irreducible_divisor_deg(D) = if(D==[0], 1, poldegree(D[1])*poldegree(D[2]));

divisor_to_point(D,E) = {
  \\  Input: D = (p(x),f(y,x)) an irreducible divisor (in the variable Xglobal, Yglobal) on E elliptic curve
  \\  output: a point Q on E, defined over an extension of the finite field.
  my(F,d,gQ,qembed,F_F_Q,x_coord,G,y_coord);
  F = if(variable(D[1])==Xglobal, D[1], polcoeff(D[1],0)); \\ remove the Y
  d = poldegree(F)*poldegree(D[2]);
  \\  if(debug, print("divisor_to_point: let us check the degrees are correct: here D, F and the degree of the pieces: ", D," ", poldegree(F), " ",poldegree(D[2])));
  gQ = ffgen(2^((E.j.f)*d));
  \\  we transform the divisor into a point on F_Q
  qembed = ffembed(E.j,gQ);
  F_F_Q =ffmap(qembed,F); 
  x_coord = polrootsmod(F_F_Q)[1]; \\ root of poly in K
  G = Pol(   apply(T ->  subst(ffmap(qembed,T),Xglobal,x_coord) , Vec(D[2])), Yglobal);
  y_coord = polrootsmod(G)[1]; \\ root of poly in K
  [x_coord,y_coord];
}




divisor_sum(D1,D2) = {
\\ Sum of two divisors D1 and D2
  my(l1,D,next_row,flag_not_found);
  l1 = #D1[,1];
  D = matrix((#D1[,1])+(#D2[,1]),2, i,j, if (i <= l1, D1[i,j], 0));
  next_row = l1+1;
  for(i=1, #D2[,1],
    flag_not_found = 1;
    for(ii=1, l1,
      if( flag_not_found && (D[ii,1]==D2[i,1]),
        D[ii,2]= D[ii,2]+D2[i,2];
        flag_not_found =0; 
      );
    );
    if(flag_not_found,
      D[next_row,1] = D2[i,1];
      D[next_row,2] = D2[i,2];
      next_row++;
    );
  );
  matrix(next_row-1, 2, i,j,D[i,j]);
}


divisor_neg(D) = matrix(matsize(D)[1],matsize(D)[2],i,j, if(j==1, D[i,j], -D[i,j]));

divisor_mul(D,k) = matrix(matsize(D)[1],matsize(D)[2],i,j, if(j==1, D[i,j], k*D[i,j]));

divisor_clean(D) = {
  \\  eliminate zeroes
  my(rows);
  rows = select(i-> D[i,2]!=0, [1..(#D[,1])]);
  matrix(#rows,2,i,j,D[rows[i],j]);
}


divisor_points_degree(D) = vecsum(D[,2]);

divisor_degree(D) = vecsum(vector(#D[,1],i, irreducible_divisor_deg(D[i,1])*D[i,2]));

\\ # ==================== 2^deg ==================== # 



lift_2_power(poly,F, max_iterations=10000) = {
  \\ input: two univariate polynomials over F_q. They need to be in the same variable.
  \\ output: a polynomial of degree 2^n being irreducible and being congruent to poly  modulo F
  my(f,Xlocal,g,n,count);
  \\  setrand(2025);
  Xlocal = variable(F);
  g = polcoeff(F,0);
  n = ceil(log(poldegree(F))/log(2));
  count = 1;
  for(j=1,max_iterations,
    for(i=1,max_iterations,
      f = poly + F*(Xlocal^(2^n-poldegree(F))*random(g) + random(g)); \\ random(g)*Xlocal^(2^n-poldegree(F)-1)+random(g)*Xlocal^2+
      if(polisirreducible(f), 
        if(verbose_for_example,
          print("lift_2_power: we have made the foloowing number of tries: "count);
          print((f - poly)/F)
        );
        return(f));
      count++;
    );
    n = n+1;
  );
  print("lift_2_power: ERROR did not work");
  0;
};





\\ # ==================== factor base ==================== # 

combconrip(L, d) = {
  \\ input: a list L and a positive integer d
  \\ output: the vector of all elements in L^d
    my(n = #L);
    if (d == 1, 
        vector(n, i, [L[i]]), /* Caso base */
        concat(apply(i -> apply(x -> concat(L[i], x), combconrip(L, d - 1)),  [1..n])
        )
    );
}


all_ff(g) = {
  \\ input: g a generator of a finite field
  \\  output: a list of all elements of that finite field
  my(out,d,vec);
  out = List([]);
  d = g.f;
  for(k = 0, 2^d - 1,   /* ``for cycle'' that yields all elements a in F_{2^d} (exploiting binary)*/
    vec = Vec(binary(k));  
    while(#vec < d, vec = concat(0, vec));  
    listput(out, my_eval(Pol(vec),g));
  );
  out;
}



irreducible_polys(g,d) = {
  \\  input: g a generator of a finite field (say F_q) and d an integer
  \\ output: a list of all irreducible monic polynomials of degree d in F_q[Xglobal]
  my(n, indices = vector(d, i, 1), allff,out,p);
  allff = all_ff(g);
  n = #allff;
  out = List([]);
  while(1,
      /* Call the process function on the current combination */
    p =  Xglobal^d + Pol(vector(d, i, allff[indices[i]]), Xglobal);
    \\  print(p);
    if(polisirreducible(p), listput(out,p));
    /* Update indices for the next combination */
    my(k = d);
    while (k > 0 && indices[k] == n, k--); /* Find the rightmost index to increment */
    if (k == 0, break); /* Exit if all combinations are done */
    indices[k]++;
    for (j = k + 1, d, indices[j] = 1); /* Reset subsequent indices */
  );
  out;
}


irreducible_divisors(W,d) = {
  \\  input: W a weierstrass equation over F_q (must be in Xglobal and Yglobal) and d an integer
  \\ output: a list of all irreducible divisors on the elliptic curve defined by W, of degree dividing d
  my(g,Xvar, n, indices, allff,out,p,iso1, iso2, gK,W_mod_p,D,q_in_X);
  g = vecsum(apply(x-> vecsum(Vec(x)),Vec(W)));
  allff = all_ff(g);
  n = #allff;
  out = List([]);
  fordiv(d,dd, \\ we go through all polynomials in x of degree dd dividing d
    indices = vector(dd, i, 1);
    while(1,
      /* Call the process function on the current combination */
      p =  Xglobal^dd + Pol(vector(dd, i, allff[indices[i]]), Xglobal); \\polynomial in X then we "find the Y"
      if(polisirreducible(p),
        [iso1, iso2,gK] = field_in_standard(p);
        W_mod_p = Pol(apply(iso1,Vec(W)),Yglobal);
        \\  W_mod_p_factor = factor(W_mod_p);
        foreach( factor(W_mod_p)[,1], q,
          q_in_X = Pol(apply(iso2,Vec(q)),Yglobal);
          D = [p, lift(q_in_X)];
          if(d% (dd*poldegree(q))==0,  listput(out,D));
          if(debug, 
            if(poldegree(q)==2 && q_in_X!=W, 
              print("Error in irreducible_divisors, here is q_in_X: ", q_in_X); )
          );
        );
      );
      /* Update indices for the next combination */
      my(k = dd);
      while (k > 0 && indices[k] == n, k--); /* Find the rightmost index to increment */
      if (k == 0, break); /* Exit if all combinations are done */
      indices[k]++;
      for (j = k + 1, dd, indices[j] = 1); /* Reset subsequent indices */
    );
  );
  out;
}




\\ # ==================== traps ==================== # 



translate_divisor(D,P,E,W) = {
  \\  Input: D = (p(x),f(y,x)) an irreducible divisor on E elliiptic curve, P a point on E and W a weierstyrass equation for E. D and W must use the variables Xglobal and Yglobal
  \\  output: the divisor D' = D+P  
  my(F,d,gQ,qembed,F_F_Q,x_coord,G,y_coord,point_traslated,iso1,iso2,tmp);
  F = if(variable(D[1])==Xglobal, D[1], polcoeff(D[1],0)); \\ remove the Y
  d = poldegree(F)*poldegree(D[2]);
  gQ = ffgen(2^((E.j.f)*d));
  \\  we transform the divisor into a point on F_Q
  qembed = ffembed(E.j,gQ);
  F_F_Q =ffmap(qembed,F); 
  x_coord = polrootsmod(F_F_Q)[1]; \\ root of poly in K
  G = Pol(   apply(T ->  subst(ffmap(qembed,T),Xglobal,x_coord) , Vec(D[2])), Yglobal);
  y_coord = polrootsmod(G)[1]; \\ root of poly in K
  point_traslated = elladd(ellinit(ffmap(qembed,E[1..5])), ffmap(qembed,P), [x_coord,y_coord]);
  if(point_traslated == [0], return([0]));
  F = (1+E.j-E.j)*minpoly(ffmaprel(ffinvmap(qembed),point_traslated[1]), Xglobal);
  if(poldegree(F)==d,
    [iso1,iso2,tmp] = field_in_standard(F,'TQ,gQ);
    G = Yglobal - iso2(point_traslated[2]);
  ,
    G = subst(W,Xglobal,Mod(X,F));
  );
  return([F,lift(G)]);
}





find_traps(E,W,P) ={
  \\  input: E elliptic curve over a certain F_q, W a Weiestrass equation for E and P a point in E(F_q)
  \\  output: a list of all irreducible divisors D on E containing all the trap points   
  my(q,output,poly,X1,Y1,Xq,Yq,Xq2,Yq2,Xq3,Yq3,generic_point, generic_pointq,generic_pointq2,formal_frobenius, make_global,a_point,p1,p2,q1,q2,q3);
  q = 2^(E.j.f);
  \\  print(q);
  output = List([ [0] ]);
  \\  2-torsion
  poly = elldivpol(E,2,Xglobal);
  foreach(factor(poly)[,1], fact,
    foreach( y_coord_div(W,fact) ,D, 
      listput(output, D);
    );
  );
  \\  weapons to deal with  the Frobenius. We  store the variable differently because then we get a sparse-like representation
  [X1,Y1,Xq,Yq,Xq2,Yq2,Xq3,Yq3] = ['X1,'Y1,'Xq,'Yq,'Xq2,'Yq2,'Xq3,'Yq3];
  generic_point = [(1+E.j-E.j)*'X1,(1+E.j-E.j)*'Y1];
  generic_pointq = [(1+E.j-E.j)*'Xq,(1+E.j-E.j)*'Yq];
  generic_pointq2 = [(1+E.j-E.j)*'Xq2,(1+E.j-E.j)*'Yq2];
  formal_frobenius = (T -> subst(subst(subst(subst(subst(subst(T,Xq2,Xq3),Yq2,Yq3),Xq,Xq2),Yq,Yq2),X1,Xq),Y1,Yq) );
  make_global =  (T -> subst(subst(subst(subst(subst(subst(subst(subst(T,Xq3,Xglobal^(q^3)),Yq3,Yglobal^(q^3)),Xq2,Xglobal^(q^2)),Yq2,Yglobal^(q^2)),Xq,Xglobal^q),Yq,Yglobal^q),X1,Xglobal),Y1,Yglobal));
  \\  (2phi-1) (X,Y) = P_0
  a_point =  elladd(E, elladd(E,generic_pointq,generic_pointq) , ellneg(E,generic_point));
  p1 = vecprod(factor(denominator(a_point[1]))[,1]); \\ in the denonminator there are x of points such that 2phi-1 = 0. If we add P_0 to them we find all points such that 2phi-1 =P_0   
  p1 = make_global(p1)%W;
  poly = polresultant(W,p1);
  foreach(factor(poly)[,1], fact,
    foreach( y_coord_div(W,fact) ,D, 
      listput(output, translate_divisor(D,P,E,W)));
  );
  \\  (phi+1) (X,Y) = P_0
  a_point =  elladd(E,generic_pointq, generic_point);
  p1 = vecprod(factor(denominator(a_point[1]))[,1]); \\ in the denonminator there are x of points such that 2phi-1 = 0. If we add P_0 to them we find all points such that 2phi-1 =P_0   
  p1 = make_global(p1)%W;
  poly = polresultant(W,p1);
  foreach(factor(poly)[,1], fact,
    foreach( y_coord_div(W,fact) ,D, 
      listput(output, translate_divisor(D,P,E,W)));
  );
  output;
}














find_traps_for_exemple(E,W,P) ={
  \\  input: E elliptic curve over a certain F_q, W a Weiestrass equation for E and P a point in E(F_q)
  \\  output: a list of all irreducible divisors D on E containing all the trap points   
  my(q,output,poly,X1,Y1,Xq,Yq,Xq2,Yq2,Xq3,Yq3,generic_point, generic_pointq,generic_pointq2,formal_frobenius, make_global,a_point,p1,p2,q1,q2,q3);
  q = 2^(E.j.f);
  output = List([ [0] ]);
  \\  weapons to deal with  the Frobenius. We  store the variable differently because then we get a sparse-like representation
  [X1,Y1,Xq,Yq,Xq2,Yq2,Xq3,Yq3] = ['X1,'Y1,'Xq,'Yq,'Xq2,'Yq2,'Xq3,'Yq3];
  generic_point = [(1+E.j-E.j)*'X1,(1+E.j-E.j)*'Y1];
  generic_pointq = [(1+E.j-E.j)*'Xq,(1+E.j-E.j)*'Yq];
  generic_pointq2 = [(1+E.j-E.j)*'Xq2,(1+E.j-E.j)*'Yq2];
  formal_frobenius = (T -> subst(subst(subst(subst(subst(subst(T,Xq2,Xq3),Yq2,Yq3),Xq,Xq2),Yq,Yq2),X1,Xq),Y1,Yq) );
  make_global =  (T -> subst(subst(subst(subst(subst(subst(subst(subst(T,Xq3,Xglobal^(q^3)),Yq3,Yglobal^(q^3)),Xq2,Xglobal^(q^2)),Yq2,Yglobal^(q^2)),Xq,Xglobal^q),Yq,Yglobal^q),X1,Xglobal),Y1,Yglobal));
  \\  (2phi-1) (X,Y) = P_0
  a_point =  elladd(E, elladd(E,generic_pointq,generic_pointq) , ellneg(E,generic_point));
  p1 = vecprod(factor(denominator(a_point[1]))[,1]); \\ in the denonminator there are x of points such that 2phi-1 = 0. If we add P_0 to them we find all points such that 2phi-1 =P_0   
  print("find_traps_for_exemple: here is 2 phi: ", elladd(E,generic_pointq,generic_pointq));
  p1 = make_global(p1)%W;
  \\  print("find_traps_for_exemple: here is p1: ", p1)
  poly = polresultant(W,p1);
  \\  print("find_traps_for_exemple: here is poly: ", poly);
  foreach(factor(poly)[,1], fact,
    foreach( y_coord_div(W,fact) ,D, 
      listput(output, translate_divisor(D,P,E,W)));
  );
  return(output);
  \\  (phi+1) (X,Y) = P_0
  a_point =  elladd(E,generic_pointq, generic_point);
  p1 = vecprod(factor(denominator(a_point[1]))[,1]); \\ in the denonminator there are x of points such that 2phi-1 = 0. If we add P_0 to them we find all points such that 2phi-1 =P_0   
  p1 = make_global(p1)%W;
  poly = polresultant(W,p1);
  foreach(factor(poly)[,1], fact,
    foreach( y_coord_div(W,fact) ,D, 
      listput(output, translate_divisor(D,P,E,W)));
  );
  output;
}












is_trap_point(Q,E,P) = {
  \\  input: Q a point on the elliptic curve E, and P = P_0
  \\  output: true if Q is a trap point, false otherwise
  my(qembed,q,Enew,Pnew,Frob,answer,a_point, alreadytrap);
  if(Q==[0], return(1));
  qembed = ffembed(E.j,vecsum(Q));
  q = 2^(E.j.f);
  Frob = (R -> apply(T->T^q,R));
  Enew = ffmap(qembed,E);
  Pnew = ffmap(qembed,P);
  a_point = elladd(Enew, ellmul(Enew, Frob(Q),2), ellneg(Enew,Q)); \\2phi-1
  alreadytrap =0;
  answer = ellmul(Enew,Q,2)==[0];
  if(debug && (!alreadytrap)&& answer, print("is_trap_point: the point is a trap because of the 1st condition"); alreadytrap=1; );
  answer = answer || (elladd(Enew,elladd(Enew, Frob(Frob(a_point)), ellneg(Enew,Frob(a_point)) ),a_point)  ==  Pnew);
  if(debug && (!alreadytrap)&& answer, print("is_trap_point: the point is a trap because of the 2nd condition"); alreadytrap=1; );
  answer = answer || (elladd(Enew,Frob(a_point),a_point)  ==  ellmul(Enew,Pnew,2));
  if(debug && (!alreadytrap)&& answer, print("is_trap_point: the point is a trap because of the 3rd condition"); alreadytrap=1; );
  answer = answer || (elladd(Enew, Frob(Frob(Frob(Frob(Q)))), ellneg(Enew,Q)) ==  ellmul(Enew,Pnew,4));
  if(debug && (!alreadytrap)&& answer, print("is_trap_point: the point is a trap because of the 4th condition"); alreadytrap=1; );
  answer = answer || (ellmul(Enew,elladd(Enew, Frob(Frob(Frob(Q))), ellneg(Enew,Q)),2)  ==  ellmul(Enew,Pnew,6));
  if(debug && (!alreadytrap)&& answer, print("is_trap_point: the point is a trap because of the 5st condition"); alreadytrap=1; );
  a_point = elladd(Enew, ellmul(Enew, Frob(Q),2), Q); \\2phi+1
  answer = answer || (elladd(Enew,Frob(a_point),ellneg(Enew,a_point))  ==  ellmul(Enew,Pnew,2));
  if(debug && (!alreadytrap)&& answer, print("is_trap_point: the point is a trap because of the 6st condition"); alreadytrap=1; );
  answer;
}


is_trap_divisor(D,E,P) = if(D==[0],1, is_trap_point(divisor_to_point(D,E),E,P));


find_super_traps(E,P) = {
  \\  input : E/F_q, P a rational point
  \\ output: the list of all points Q such that phi(Q) = Q+P all in the same extension of F_q
  my(n,q,Xlocal,Ylocal,W,Psum,p1,p2,p11,q1,q2,q3,F,gK,q_embed_K,y_from_x,fact_K,output,factors);
  g = ffgen(E.j);
  q = 2^(g.f);
  Xlocal = 'Xlocal;
  Ylocal = 'Ylocal;
  Psum = elladd(E,P,[(1+g-g)*Xlocal,(1+g-g)*Ylocal]);
  p1 = Xlocal^q*denominator(Psum[1])-numerator(Psum[1]);
  p1 = subst(subst(p1,Xlocal,Xglobal),Ylocal,Yglobal); \\ we would like to use Xglobal and Yglobal,  but GP's variables priority would create problems in the line above 
  p2 = Ylocal^q*denominator(Psum[2])-numerator(Psum[2]);
  p2 = subst(subst(p2,Xlocal,Xglobal),Ylocal,Yglobal);
  W = (1+g-g)*(Yglobal)^2+(E[1]*Xglobal+E[3]+g-g)*Yglobal - ((1+g-g)*Xglobal^3+E[2]*Xglobal^2+E[4]*Xglobal+E[5]);  
  \\ p1,p2,W describe the ideal of points such that phi(Q)=Q+P. We lower a bit the degree in X and Y and look for an ideal in the primary decomposition
  p1 = p1%W;
  p2 = p2%W;
  if(variable(p1)!=Yglobal, return(0)); \\?? here we are supposeing that p1 is of the form Y*(element of F_q), but if the code works it is correct
  p11 = polcoeff(p1,1);
  if(subst(p11,Xglobal,0)!=p11, return(0));
  p1 = p1/subst(p11,Xglobal,0);
  q1 = polresultant(W,p1);
  q2 = polresultant(W,p2);
  q3 = polresultant(p1,p2);
  F = gcd(q1,gcd(q2,q3));
  n= ellorder(E,P);
  gK = ffgen(q^n,'bb); \\bad points :)
  q_embed_K = ffembed(g,gK);
  output = List([]);
  y_from_x = - ffmap(q_embed_K,polcoeff(p1,0)); \\p1 has the shape Y+f(x)
  factors = factor(F)[,1];
  foreach(factors, factor, 
    if(poldegree(factor)==n,
      fact_K = ffmap(q_embed_K,factor);
      foreach(polrootsmod(fact_K),x_coord,
        y_coord =  subst(y_from_x,Xglobal,x_coord); 
        listput(output,[x_coord,y_coord]);
      ); 
    )
  );
  output;
}



\\ # ==================== Div(f) ==================== # 

order_of_series(S,var, max_iterations = 1000) = {
  \\  input: S a series in the variable var;
  \\  output: the maximum n such that var^n divides S
  if(S==0, print("order_of_series: Error we have a zero series ",S); return("ERROR"));
  my(S1);
  S1 = S;
  for(i=0,max_iterations,
    if(subst(S1,var,0)!=0, return(i), S1 = S1/var);
  );
  print("order_of_series: Error we arrived to maximuum iterations ");
  "ErroR";
}


ell_series_at_a_point(W,P, prec, var = 'a_P ) = {
  \\  input: W a weierstrass equation, P a point on the affine part of the corresponding curve and a variable t
  \\  output: [xt,yt] power series of the form [t,series(t)] or [series(t),t] where t is a local parameter at P on the curve and [xt,yt] is a "formal" point.
  my(X_ser, Y_ser,W_temp);
  if( my_global_eval(deriv(W,Yglobal), P) !=0,
    X_ser = P[1] + var + O(var^(prec+1));
    Y_ser = P[2] + O(var^(prec+1)); 
    W_temp = subst(W,Xglobal,X_ser);
    for(i=1, ceil(log(prec)/log(2)+1),
      Y_ser = Y_ser - subst(W_temp,Yglobal,Y_ser)/subst(deriv(W_temp,Yglobal),Yglobal,Y_ser);
    );
  , \\otherwise we express X in terms of Y 
    \\  if(debug, print("ell_series_at_a_point: we want to express X in terms of Y"));
    X_ser = P[1] +  O(var^(prec+1));
    Y_ser = P[2] + var + O(var^(prec+1)); 
    W_temp = subst(W,Yglobal,Y_ser);
    for(i=1, ceil(log(prec)/log(2)+1),
      X_ser = X_ser - subst(W_temp,Xglobal,X_ser)/subst(deriv(W_temp,Xglobal),Xglobal,X_ser);
    );
  );
  [X_ser,Y_ser];
}


divisor_of_affine_as_points(poly, W, E, var_result = 'gz) = {
  \\  input: poly a polynomial in Xglobal and Yglobal, W a weierstrass equation for E, var_result a variable used for the necessary field extension
  \\  output: the divisor of zeroes and poles of poly as a function on E.
  my(maxdeg,Tinf,g_L, q_embed_L, E_L,xinf,yinf,n_pole,poly_mod_W,F_in_X, answer_as_list, facts_X,min_deg,g_full,q_embed_full,E_full,W_full,L_embed_full,poly_full,var_series,fact_full,y_coords,new_point,series_at_point,multiplicity_at_point,answer );
  if((poldegree(poly,Yglobal)==0)&&(poldegree(poly,Xglobal)==0), return(ZeroDivisor));
  \\  FIRST MULTIPLICITY AT INFTY
  Tinf = 'Tinf;
  maxdeg = poldegree(poly,Yglobal)*3+poldegree(poly,Xglobal)*2+6;
  g_L = vecsum(Vec(vecsum(Vec(poly))));
  \\  if(debug, print("divisor_of_affine_as_points: here is poly and g_L ",[poly,g_L]));
  if(type(g_L)=="t_FFELT", g_L = ffgen(g_L), g_L = ffgen(g_L+E.j));
  poly_fixed = poly*(1+g_L-g_L);
  q_embed_L = ffembed(E.j,g_L);
  E_L = ffmap(q_embed_L, E);
  W_L = change_coeff_W(q_embed_L,W);
  [xinf,yinf] = ellformalpoint(E_L, maxdeg, Tinf); 
  series_at_inf = subst(subst(poly_fixed,Yglobal,yinf),Xglobal,xinf);
  \\  if(debug, print("divisor_of_affine_as_points: here is the series at infinity: ", series_at_inf));
  n_pole =  poldegree(denominator(truncate(series_at_inf)), Tinf);
  \\  THEN POSSIBLE X's OF POINTS
  poly_mod_W = poly_fixed%W_L;
  poly_mod_W = poly_mod_W*(1+g_L-g_L);
  if(poly_mod_W==0, print("divisor_of_affine_as_points: input was the 0 function: ",poly_fixed); return(0) );
  if((poldegree(poly_mod_W,Yglobal)==0)&&(poldegree(poly_fixed,Xglobal)==0), return(ZeroDivisor));
  if(poldegree(poly_mod_W,Yglobal)==0, 
    F_in_X = subst(poly_mod_W, Yglobal,0);
    \\  if(debug, print("divisor_of_affine_as_points: poldegree(poly_mod_W,Yglobal)==0, F_in_X: " F_in_X));
  , 
    F_in_X = polresultant(poly_mod_W,W_L,Yglobal);
  );
  answer_as_list=List([]);
  facts_X = factor(F_in_X)[,1];
  min_deg = lcm(apply(poldegree,facts_X));
  g_full = ffgen( (g_L.p)^((g_L.f)*2*min_deg) );
  q_embed_full = ffembed(E.j,g_full);
  E_full = ffmap(q_embed_full, E);
  W_full = change_coeff_W(q_embed_full,W);
  L_embed_full = ffembed(g_L,g_full);
  poly_full = change_coeff_W(L_embed_full,poly_fixed);
  var_series = 'as;
  foreach(facts_X, fact,
    fact_full = ffmap(L_embed_full, fact);
    foreach(polrootsmod(fact_full), x_coord,
      y_coords = ellordinate(E_full, x_coord);
      if(#y_coords==0, print("divisor_of_affine_as_points: WE DID NOT FIND THE Y Coordinate of a point in the right field"));
      foreach(y_coords, y_coord,
        new_point = [x_coord, y_coord];
        parametrization_new_point =  ell_series_at_a_point(W_full,new_point,  maxdeg, var_series);
        series_at_point = my_global_eval(poly_full, parametrization_new_point);
        \\  series_at_point = my_global_eval(poly_full, ell_series_at_a_point(W_full,new_point,  maxdeg, var_series) );
        multiplicity_at_point = order_of_series(series_at_point, var_series);
        if((multiplicity_at_point == 0) && (my_global_eval(poly_full,new_point)==0), print("ERRORE IN divisor_of_affine_as_points: zero multiplicity but the polynomial vanishes at the point") );
        if((multiplicity_at_point) && (my_global_eval(poly_full,new_point)), print("ERRORE IN divisor_of_affine_as_points: non-zero multiplicity but the polynomial does not vanish at the point") );
        if(multiplicity_at_point, listput(answer_as_list,[new_point, multiplicity_at_point]) );
      );
    );
  );
  answer = matrix(#answer_as_list +1,2);
  for(i=1, #answer_as_list,
    answer[i,1] = answer_as_list[i][1];
    answer[i,2] = answer_as_list[i][2]
  );
  answer[#answer_as_list+1,1] = [0];
  answer[#answer_as_list+1,2] = -n_pole;
  if(divisor_points_degree(answer), 
    print("divisor_of_affine_as_points: ERROR THE RESULT DOES NOT HAVE DEgree 0. Here is the input: ", poly, " ",W," ", E);
    global_debug_var = [poly,W,E];
  );
  answer;
}


divisor_of_affine_as_points_fixed_field(poly, W, E) = {
  \\  input: poly a polynomial in Xglobal and Yglobal, W a weierstrass equation for E, all in the same extension
  \\  output: the divisor of zeroes and poles of poly as a function on E, in the field where everything is defined.
  my(maxdeg,Tinf,g_L, q_embed_L, E_L,xinf,yinf,n_pole,poly_mod_W,F_in_X, answer_as_list, facts_X,min_deg,g_full,q_embed_full,E_full,W_full,L_embed_full,poly_full,var_series,fact_full,y_coords,new_point,series_at_point,multiplicity_at_point,answer );
  if((poldegree(poly,Yglobal)==0)&&(poldegree(poly,Xglobal)==0), return(ZeroDivisor));
  \\  FIRST MULTIPLICITY AT INFTY
  Tinf = 'Tinf;
  maxdeg = poldegree(poly,Yglobal)*3+poldegree(poly,Xglobal)*2+6;
  g_L = vecsum(Vec(vecsum(Vec(poly))));
  g_L = ffgen(g_L+E.j);
  poly_fixed = poly*(1+g_L-g_L);
  [xinf,yinf] = ellformalpoint(E, maxdeg, Tinf); 
  series_at_inf = subst(subst(poly_fixed,Yglobal,yinf),Xglobal,xinf);
  \\  if(debug, print("divisor_of_affine_as_points_fixed_field: here is the series at infinity: ", series_at_inf));
  n_pole =  poldegree(denominator(truncate(series_at_inf)), Tinf);
  \\  THEN POSSIBLE X's OF POINTS
  poly_mod_W = poly_fixed%W;
  poly_mod_W = poly_mod_W*(1+g_L-g_L);
  if(poly_mod_W==0, print("divisor_of_affine_as_points_fixed_field: input was the 0 function: ",poly_fixed); return(0) );
  if((poldegree(poly_mod_W,Yglobal)==0)&&(poldegree(poly_fixed,Xglobal)==0), return(ZeroDivisor));
  if(poldegree(poly_mod_W,Yglobal)==0, 
    F_in_X = subst(poly_mod_W, Yglobal,0);
    \\  if(debug, print("divisor_of_affine_as_points_fixed_field: poldegree(poly_mod_W,Yglobal)==0, F_in_X: " F_in_X));
  , 
    F_in_X = polresultant(poly_mod_W,W,Yglobal);
  );
  answer_as_list=List([]);
  var_series = 'as;
  foreach(polrootsmod(F_in_X), x_coord,
    y_coords = ellordinate(E, x_coord);
    if(#y_coords==0, print("divisor_of_affine_as_points_fixed_field: WE DID NOT FIND THE Y Coordinate of a point in the right field"));
    foreach(y_coords, y_coord,
      new_point = [x_coord, y_coord];
      parametrization_new_point =  ell_series_at_a_point(W,new_point,  maxdeg, var_series);
      series_at_point = my_global_eval(poly, parametrization_new_point);
      \\  series_at_point = my_global_eval(poly, ell_series_at_a_point(W,new_point,  maxdeg, var_series) );
      multiplicity_at_point = order_of_series(series_at_point, var_series);
      if((multiplicity_at_point == 0) && (my_global_eval(poly,new_point)==0), print("ERRORE IN divisor_of_affine_as_points_fixed_field: zero multiplicity but the polynomial vanishes at the point") );
      if((multiplicity_at_point) && (my_global_eval(poly,new_point)), print("ERRORE IN divisor_of_affine_as_points_fixed_field: non-zero multiplicity but the polynomial does not vanish at the point") );
      if(multiplicity_at_point, listput(answer_as_list,[new_point, multiplicity_at_point]) );
    );
  );
  answer = matrix(#answer_as_list +1,2);
  for(i=1, #answer_as_list,
    answer[i,1] = answer_as_list[i][1];
    answer[i,2] = answer_as_list[i][2]
  );
  answer[#answer_as_list+1,1] = [0];
  answer[#answer_as_list+1,2] = -n_pole;
  if(divisor_points_degree(answer), 
    print("divisor_of_affine_as_points_fixed_field: ERROR THE RESULT DOES NOT HAVE DEgree 0. Here is the input: ", poly, " ",W," ", E);
    global_debug_var = [ poly,W,E];
  );
  answer;
}



my_numerator_denominator(f) = {
  \\ input: f a rational function in Xglobal and Yglobal (maybe of the form Y^2/(1+X)+Y^3-2/X);
  \\ output: [num, den] where num, den are polynomials in X,Y and num/den = f
  my(num, den,sum_coeffs);
  if( type(f)== "t_RFRAC",
    \\  fraction 
    if((variable(f)!=Yglobal)&&(variable(f)!=Xglobal), 
      print("my_numerator_denominator: error 14"); return(0)
    );
    [num,den] = [numerator(f),denominator(f)];
  , \\ NO FRACTION
    if(type(f)== "t_POL",
      if(variable(f)==Xglobal,
      \\  polynomial in X
        [num,den] = [f,1];      
      ,
        if(variable(f)==Yglobal,
          \\  polynomial in Y and then? we look at coefficients
          sum_coeffs = vecsum(Vec(f))+Xglobal-Xglobal;
          if(type(sum_coeffs)=="t_RFRAC",
          \\  polynomial in Y but not in X
            if(variable(sum_coeffs)!=Xglobal, 
              print("my_numerator_denominator: error 13"); return(0)
            );
            den = lcm(apply(denominator, Vec(f)));
            num = numerator(f*den);
          ,
          \\  polynomial in Y and X
            if((type(sum_coeffs)!="t_POL"), 
              print("my_numerator_denominator: error 12"); return(0)
            );
            [num,den] = [f,1];
          );
        ,
          print("my_numerator_denominator: error 11: poly in what?"); 
          return(0);  
        ); 
      );
    , \\ NO POLYNOMIAL
      if(type(f)== "t_FFELT",
        [num,den] = [f,1];
      ,
        if(type(f)== "t_INT",
          [num,den] = [f,1];
        ,
          print("my_numerator_denominator: error 10, unknown type"); 
          return(0);  
        );
      );
    ); 
  );
  num = num+Xglobal+Yglobal-Xglobal-Yglobal;
  den = den+Xglobal+Yglobal-Xglobal-Yglobal;
  \\  if(debug, print([num, den]));
  if((variable(den)!=Yglobal)||(type(den)!="t_POL"),  
    print("my_numerator_denominator: error 1"); return(0);  
  );
  if((variable(num)!=Yglobal)||(type(num)!="t_POL"),  
    print("my_numerator_denominator: error 2"); return(0);  
  );
  foreach(Vec(den),coeff,
    if((variable(coeff+Xglobal-Xglobal)!=Xglobal)||(type(coeff+Xglobal-Xglobal)!="t_POL"),  
      print("my_numerator_denominator: error 3"); return(0);  
    );
  );
  foreach(Vec(num),coeff,
    if((variable(coeff+Xglobal-Xglobal)!=Xglobal)||(type(coeff+Xglobal-Xglobal)!="t_POL"),  
      print("my_numerator_denominator: error 4"); return(0);  
    );
  );
  if((num/den)!=f, print("my_numerator_denominator: error 5"); return(0) );
  [num,den];
}



divisor_of_function_as_points(f, W, E, var_result = 'gz) = {
  \\ input: f a rational function in Yglobal and Xglobal, W a weierstrass  equation of an elliptic curve E over a finite field (the same for W and E and f) and var_result a variable
  \\  output: a divisor representing div f, as sum of points, all defined over the same extension. The field extension has variable var_result.
  my(num, den,var_num,var_den,div_num,div_den,deg_k_num,deg_k_den,gk_full,knum_embed_kfull,kden_embed_kfull,output);
  [num,den] = my_numerator_denominator(f);
  var_num = 'gnum;
  div_num = divisor_of_affine_as_points(num, W, E, var_num);
  var_den = 'gden;
  div_den = divisor_of_affine_as_points(den, W, E, var_den);
  \\  find field to a common one (full)
  deg_full = E.j.f; \\ the degree of the field containing points in div_num
  for(i=1, #div_num[,1], 
    if(div_num[i,1]!=[0], deg_full = lcm(deg_full, div_num[i,1][2].f) );
  );
  for(i=1, #div_den[,1], 
    if(div_den[i,1]!=[0], deg_full = lcm(deg_full, div_den[i,1][2].f); );
  );
  gk_full = ffgen((E.j.p)^deg_full, var_result);
  gk = vecsum(apply(x->vecsum(Vec(x)), Vec(den))) + vecsum(apply(x->vecsum(Vec(x)), Vec(num)));
  if(type(gk)=="t_INT", gk = E.j);
  \\  gk = ffgen(gk);
  k_embed_full = ffembed(gk,gk_full);
  num = change_coeff_W(k_embed_full,num);
  den = change_coeff_W(k_embed_full,den);
  W_full = change_coeff_W(k_embed_full, W);
  E_full = ffmap(k_embed_full,E);
  div_num = divisor_of_affine_as_points_fixed_field(num, W_full, E_full);
  div_den = divisor_of_affine_as_points_fixed_field(den, W_full, E_full);
  output = divisor_sum(div_num, divisor_neg(div_den));
  divisor_clean(output);
}




divisor_of_function_as_points_with_field_extension(f, W, E, var_result = 'gz) = {
  \\ input: f a rational function in Yglobal and Xglobal, W a weierstrass  equation of an elliptic curve E over a finite field (the same for W and E and f) and var_result a variable
  \\  output: a divisor representing div f, as sum of points, all defined over the same extension. The field extension has variable var_result.
  my(num, den,var_num,var_den,div_num,div_den,deg_k_num,deg_k_den,gk_full,knum_embed_kfull,kden_embed_kfull,output);
  [num,den] = my_numerator_denominator(f);
  var_num = 'gnum;
  div_num = divisor_of_affine_as_points(num, W, E, var_num);
  var_den = 'gden;
  div_den = divisor_of_affine_as_points(den, W, E, var_den);
  \\  find field to a common one (full)
  deg_full = E.j.f; \\ the degree of the field containing points in div_num
  for(i=1, #div_num[,1], 
    if(div_num[i,1]!=[0], deg_full = lcm(deg_full, div_num[i,1][2].f) );
  );
  for(i=1, #div_den[,1], 
    if(div_den[i,1]!=[0], deg_full = lcm(deg_full, div_den[i,1][2].f); );
  );
  gk_full = ffgen((E.j.p)^deg_full, var_result);
  gk = vecsum(apply(x->vecsum(Vec(x)), Vec(den))) + vecsum(apply(x->vecsum(Vec(x)), Vec(num)));
  if(type(gk)=="t_INT", gk = E.j);
  \\  gk = ffgen(gk);
  k_embed_full = ffembed(gk,gk_full);
  num = change_coeff_W(k_embed_full,num);
  den = change_coeff_W(k_embed_full,den);
  W_full = change_coeff_W(k_embed_full, W);
  E_full = ffmap(k_embed_full,E);
  div_num = divisor_of_affine_as_points_fixed_field(num, W_full, E_full);
  div_den = divisor_of_affine_as_points_fixed_field(den, W_full, E_full);
  output = divisor_sum(div_num, divisor_neg(div_den));
  output = divisor_clean(output);
  [gk_full,output];
}


point_to_divisor(point,q_embed_L,W) = {
  \\  input: point is a point in E(L) where E elliptic curve E/F_q defined by a Weierstrass equation W/F_q and  q_embed_L is an embedding of F_q in L
  \\  output: an irreducible divisor D on E defined over F_q that contains Q
  my(inv_emb,F,G,rel_elt,poly_elt,rel_gn);
  inv_emb = ffinvmap(q_embed_L);
  rel_gn = ffmaprel(inv_emb,ffgen(point[1]));
  poly_elt = point[1].pol;
  rel_elt = my_eval(poly_elt, rel_gn);
  \\  rel_elt = subst(poly_elt,variable(poly_elt), rel_gn ) + rel_gn-rel_gn;
  \\  if(debug, print("point_to_divisor: here ",rel_elt); );
  my(poltmp);
  poltmp = minpoly(rel_elt);
  if(!polisirreducible(poltmp), print("PROBLEM IN point_to_divisor"));
  poltmp = ffmap(q_embed_L,poltmp);
  if(my_eval(poltmp,point[1]), print("PROBLEM2 IN point_to_divisor"));
  F = minpoly(rel_elt,Xglobal);
  F = F + q_embed_L[1]-q_embed_L[1];
  foreach(y_coord_div(W,F), D,
    G = change_coeff_W(q_embed_L,D[2]);
    if(my_global_eval(G,point)==0, return(D));
  );
  print("point_to_divisor: Error, no polynomial in y was found");
  global_test_var_2 = [point,q_embed_L,W];
  0;
}


test() = {
  [gq,E,P,W,idealM] = find_presentation(45);
  gQ = ffgen(2^(12*gq.f));
  emb = ffembed(gq,gQ);
  EQ = ffmap(emb,E);
  WQ = change_coeff_W(emb,W);
  x_coord = random(gQ);
  y_coord = ellordinate(EQ,x_coord);
  if(#y_coord,  Q = [x_coord,y_coord[1]];  print(Q);   D1 = point_to_divisor(Q,emb,W); D2 = point_to_divisor_old(Q,emb,W); print(D1==D2);)
}


norm_of_divisor_of_function(f, gk, gq, W, E) = {
  \\  input: f a rational function in Xglobal and Yglobal over a finite field k with an element gk,  gq an element of a subfield,  W a Weierstrass in Xglobal and Yglobal of an elliptic curve E over F_q (where gq is)
  \\  output: Norm_{k/gq}(div(f))
  my(Wk,Ek,gL,D_as_points,var_L,k_card,L_deg_k,D_as_orbits,next_row,point,is_point_new,orbit,is_conj_found,q_embed_k,q_embed_L,k_embed_L,L_deg_q,output,stabilizer_size,new_div,multiplicity_norm);
  q_embed_k = ffembed(gq,gk);
  Wk = change_coeff_W(q_embed_k,W);
  Ek = ffmap(q_embed_k,E);
  var_L = 'g_points;
  [gL, D_as_points] = divisor_of_function_as_points_with_field_extension(f, Wk, Ek, var_L);
  \\  if(debug, print("norm_of_divisor_of_function: here [gL, D_as_points] ", [gL, D_as_points]));
  k_card = (gk.p)^(gk.f);
  L_deg_k = (gL.f)/(gk.f);
  D_as_orbits = matrix(#D_as_points[,1],2);
  next_row = 1;
  for(i = 1, #D_as_points[,1],
    point = D_as_points[i,1];
    is_point_new=1;
    for(j=1,next_row-1,
      orbit = D_as_orbits[j,1];
      foreach(orbit, point_in_orbit, if(point == point_in_orbit, is_point_new=0) );
    );
    if(is_point_new,
    \\  now we look for all the points in the Galois(L/k)-orbit of point and we check that each appears once, with multplicity 1
      orbit = vector(L_deg_k, j, apply(x->x^(k_card^j) ,point));
      D_as_orbits[next_row,1]=orbit;
      D_as_orbits[next_row,2]=D_as_points[i,2];
      next_row++;
      \\  we add a check
      is_conj_found = 0;
      foreach(orbit, conjugate,
        for(j = 1, #D_as_points[,1],
          if(D_as_points[j,1]==conjugate,
            if(is_conj_found, 
              print("norm_of_divisor_of_function: ERRRRRROR, a conjugate has been found twice")
            ,
              is_conj_found=1;
              if(D_as_points[j,2]!=D_as_points[i,2], print("norm_of_divisor_of_function: ERRRRRROR, a conjugate has a different multiplicity than another"));
            );
          );
        );
        if(!is_conj_found, if(is_conj_found, print("norm_of_divisor_of_function: ERRRRRROR, a conjugate has not been found")););
        is_conj_found = 0;
      );
    ); 
  );
  D_as_orbits = matrix(next_row-1,2,i,j,D_as_orbits[i,j]);
  \\  finally we apply the norm to each orbit
  k_embed_L = ffembed(gk,gL);
  q_embed_L = ffembed(gq,gL); \\ we now correct it
  q_embed_L[2] = ffmap(k_embed_L, ffmap(q_embed_k,q_embed_L[1]));
  L_deg_q = (gL.f)/(gq.f);
  output = ZeroDivisor;
  for(i=1, #D_as_orbits[,1],
    orbit =D_as_orbits[i,1];
    point = orbit[1];
    if(point==[0],
      output = divisor_sum(output, Mat([[0], D_as_orbits[i,2]*(L_deg_q/L_deg_k)]));
    ,
      stabilizer_size = 0; \\ stabilizer of point in Galois(L/k)
      foreach(orbit, other_point, if(other_point==point, stabilizer_size++));
      new_div = point_to_divisor(point,q_embed_L,W);
      multiplicity_norm =   L_deg_q/(stabilizer_size*irreducible_divisor_deg(new_div));
      output = divisor_sum(output, Mat([new_div, multiplicity_norm*D_as_orbits[i,2]]));
    );
  );
  divisor_clean(output);
}


test() ={
  [gq,E,P,W,idealM] = find_presentation(40);
  gQ = ffgen(2^12);
  emb = ffembed(gq,gQ);
  EQ = ffmap(emb,E);
  WQ = change_coeff_W(emb,W);
  x_coord = gQ^2+1;
  y_coord = ellordinate(EQ,x_coord);
  Q = [x_coord,y_coord[1]];
  PP = ffmap(emb,P);
   D2 = norm_of_divisor_of_function((Yglobal-Q[2])/(Xglobal-Q[1]) - (Yglobal-PP[2])/(Xglobal-PP[1]),gQ,gq,W,E)
}







\\ # ==================== 3-2 descent ==================== # 



my_f(a,b) = (b[2]-a[2])/(b[1]-a[1]); \\the f_a(b) as at the beginning of chapter 8.1 of the article

my_crossratio(a,b,c,d) = (c-a)*(d-b)/((b-a)*(d-c));


descentThreeTwo_section8(Q,q,E,P_0, super_traps, max_iterations = 1000) = {
  \\  input: the elliptic curve E, and P_0 over a field k and Q defined over an extension of degree 3.
  \\  output: a point P as in section 8, which we can use to do the descent
  my(k_card,gk, g_full,deg_full_over_q,q_embed_full,E_full,R,Q0,R0,Q1,R1,Q2,R2, q_embed_k,k_embed_full, deg_ktrap,g_ktrap, traps_embed_ktrap,traps_ktrap, k_embed_ktrap, E_k,x_answer,y_answer,P_full,f_PQ0,f_PQ1,f_PQ2,f_PR0,f_PR1,f_PR2,M,a,b,c,d,P_trap,Q0_trap,Q1_trap,Q2_trap,R0_trap,R1_trap,R2_trap,last_check,k_embed_full_inv,split_condition1,f_PQ0_ktrap,f_PQ1_ktrap,f_PQ2_ktrap,f_PR0_ktrap,f_PR1_ktrap,f_PR2_ktrap,Bcross);
  \\?? at the moment we do not check if Q is a supertrap
  k_card = (E.j.p)^((vecsum(Q).f)/3);
  gk = ffgen(E.j); 
  g_full = ffgen(vecsum(Q)); \\ full field containing Q
  if((g_full.f)/((gk.f))!= 3, print("descentThreeTwo_section8: Error, the following point is not of degree 3 ",Q));
  k_embed_full = ffembed(gk, g_full);
  E_full = ffmap(k_embed_full,E);
  R = elladd(E_full,Q, ffmap(k_embed_full,P_0)); \\ actually this is phi(R) 
  deg_full_over_q = (g_full.f) / logint(q,g_full.p) ;
  for(i=1, deg_full_over_q-1,  R = apply(t->t^q,R)); \\ now R should be correct
  if(debug, if([R[1]^q,R[2]^q] != elladd(E_full,Q, ffmap(k_embed_full,P_0)), print("descentThreeTwo_section8: ERROR: R is not correct")));
  \\ GALOIS CONJ over k (defined below) OF R, Q
  [Q0,R0]= [Q,R];
  [Q1,R1]= [Q,R];
  for(i=1, deg_full_over_q/3, R1 = apply(t->t^q,R1); Q1 = apply(t->t^q,Q1));
  [Q2,R2]= [Q1,R1];
          print("here I am3");
  for(i=1, deg_full_over_q/3, R2 = apply(t->t^q,R2); Q2 = apply(t->t^q,Q2));
  \\  FIELD kTrap containing k and ALSO THE SUPER TRAPS
  \\  ??? with the supertraps we are using composition of embeddings, we do not trust what we do
  deg_ktrap = lcm(g_full.f,super_traps[1][1].f);
  g_ktrap = ffgen((gk.p)^deg_ktrap);
  traps_embed_ktrap = ffembed(super_traps[1][1], g_ktrap);
  traps_ktrap = apply(P -> ffmap(traps_embed_ktrap,P),super_traps);
  k_embed_ktrap = ffembed(gk, g_ktrap);
  full_embed_ktrap = ffembed(g_full, g_ktrap);
  \\  NOW WE LOOK FOR P AND THE REST
      print("here I am2"); 
  for(number_iterations=1, max_iterations,
    x_answer = random(gk);
    y_answer = ellordinate(E,x_answer);
    if(#y_answer
    ,
    y_answer = y_answer[1];
    P_full = ffmap(k_embed_full,[x_answer,y_answer]);
    f_PQ0 = my_f(P_full,Q0)+g_full-g_full;
    f_PQ1 = my_f(P_full,Q1)+g_full-g_full;
    f_PQ2 = my_f(P_full,Q2)+g_full-g_full;
    f_PR0 = my_f(P_full,R0)+g_full-g_full;
    f_PR1 = my_f(P_full,R1)+g_full-g_full;
    f_PR2 = my_f(P_full,R2)+g_full-g_full;
    if((f_PQ0!=f_PQ1)&&(f_PQ0!=f_PQ2)&&(f_PQ2!=f_PQ1)&&(f_PR0!=f_PR1)&&(f_PR0!=f_PR2)&&(f_PR2!=f_PR1)
    ,
    \\  M = [f_PQ0,1+g_full-g_full,f_PR0*f_PQ0,f_PR0; f_PQ1,1+g_full-g_full,f_PR1*f_PQ1,f_PR1; f_PQ2,1+g_full-g_full,f_PR2*f_PQ2,f_PR2];
    \\  ?? A correctiion: my_f(P_full,R0)^q
    M = [f_PQ0,1+g_full-g_full,f_PR0^q*f_PQ0,f_PR0^q; f_PQ1,1+g_full-g_full,f_PR1^q*f_PQ1,f_PR1^q; f_PQ2,1+g_full-g_full,f_PR2^q*f_PQ2,f_PR2^q];
    [a,b,c,d] = matker(M)[,1];
    if((a*d!=b*c) && (c*d^q !=c^q*a)
    ,
    [a,b,c,d] = [a/c,b/c,1+c-c,d/c];
    k_embed_full_inv = ffinvmap(k_embed_full);
    [a,b,c,d] = ffmap(k_embed_full_inv,[a,b,c,d]);
    if((a==[])|| (b==[]) || (c==[]) || (d==[]), print("descentThreeTwo_section8: could not force a,b,c,d into k!"));
    \\  THE CONDITION ON z and a,b,c,d is also satisfied if cX^(q+1)+dX^q+aX+b has all its roots in k. i.e. if X^k_card is congruent to X modulo cX^(q+1)+dX^q+aX+b.
    split_condition1 = Mod(Xglobal,c*Xglobal^(q+1)+d*Xglobal^(q)+a*Xglobal+b);
    split_condition1 = (split_condition1^k_card == split_condition1);
    \\  if(debug, print("descentThreeTwo_section8: iteration and number of roots ", number_iterations, " " ,#polrootsmod(c*Xglobal^(q+1)+d*Xglobal^(q)+a*Xglobal+b))); 
    if( split_condition1,
      last_check = 1;
      [f_PQ0_ktrap,f_PQ1_ktrap,f_PQ2_ktrap,f_PR0_ktrap,f_PR1_ktrap,f_PR2_ktrap] = apply(x->ffmap(full_embed_ktrap,x), [f_PQ0,f_PQ1,f_PQ2,f_PR0,f_PR1,f_PR2]);
      P_trap = ffmap(k_embed_ktrap,[x_answer,y_answer]);
      foreach(traps_ktrap, B,
        last_check = last_check && ([x_answer^q,y_answer^q]!= elladd(E,ellneg(E,P_0),[x_answer,y_answer]) );
        Bcross = my_f(B, P_trap);
        last_check = last_check && ( my_crossratio(f_PQ0_ktrap,f_PQ1_ktrap,f_PQ2_ktrap, Bcross)!= my_crossratio(f_PR0_ktrap,f_PR1_ktrap,f_PR2_ktrap, Bcross )^q );
      );
    if(last_check,
     print("descentThreeTwo_section8: we arrived after ", number_iterations ," iterations"); 
     return([[x_answer,y_answer],a,b,c,d] )
    ,     if(debug,print("descentThreeTwo_section8: in iteration "number_iterations, " we could not avoit supertraps"));
    ); \\ check we avoid supertraps
    ,     
    \\ if(debug,print("descentThreeTwo_section8: in iteration "number_iterations, " dT^{q+1}+cT^q+aT+b is split was not split"));
    ); \\ check dT^{q+1}+cT^q+aT+b is split
    ,     if(debug,print("descentThreeTwo_section8: in iteration "number_iterations, " ad-bc or cd^q-ac^q were null"));
    ); \\ check ad-bc e cd^q-ac^q not 0
    ,     if(debug,print("descentThreeTwo_section8: in iteration "number_iterations, " f_P(sigma^i Q) were not distinct"));
    ); \\ check distinctness of f_P(sigma^i Q)
    ,     
    \\  if(debug,print("descentThreeTwo_section8: in iteration "number_iterations, " did not find y"));
    ); \\check y exists 
  );
  print("descentThreeTwo_section8 DID NOT WORK!!");
  0;
}



descentThreeTwo(D,E,W,P_0,super_traps, max_iterations = 100000) = {
  \\  input: th elliptic curve E (over F_q), with Weierstrass equation W and P_0 a point, D an irreducible divisor on E of degree 3d and super_traps a list ot all points, over an extensiton such that P^q = P_0+Q. 
  \\  output: a divisor D2 that is equivalent to D and of essntial degree dividing 2 d
  my(q,Q,Q1,Q2 section_8_data,a,b,c,d,x_coord, y_coord, point_found, gk,Wk, Dk,k_deg_q, deg_kq,q_embed_k, Ek, P_0k, Fk_1, iso1, iso2,Gk1_mod_p, Gk1_in_Xvar,D1, f,Psum,ftilde,k_full_divisor,k_divisor, g_numerator,D_g_numerator,flag_found_D,var_polyq,D0,Den, Dnum,polyabcd,debug_var,output);
  if(D==[0], return(D));
  if(is_trap_divisor(D,E,P_0), return(D));
  if(irreducible_divisor_deg(D)%3, print("Error in descentThreeTwo, here is desccentThreeTwo: the following divisor is not of degree divisible by 3 ",D));
  \\?? at the moment we do not check irreducibility of D
  \\  AS a first thing we go to the field k where we do a lot of the computations (then we will take a norm)
  q = (E.j.p)^(E.j.f);
  k_deg_q =  irreducible_divisor_deg(D)/3;
  gk = ffgen(q^k_deg_q, 'gk);
  q_embed_k = ffembed(E.j, gk);
  [Ek,P_0k] = [ffmap(q_embed_k, E),ffmap(q_embed_k, P_0)];
  Wk = change_coeff_W(q_embed_k, W);
  Dk = [ffmap(q_embed_k, D[1]), change_coeff_W(q_embed_k, D[2])];
  \\  now we construct an irreducible factor D1 of D_k
  Fk_1 =  factor(Dk[1])[1,1];
  \\ ?? forse bisogna essere sicuri che  Fk_1 abbia X come variabile principale 
  [iso1, iso2] = field_in_standard(Fk_1);
  Gk1_mod_p = Pol(apply(iso1,Vec(Dk[2])),Yglobal);
  Gk1_mod_p = factor(Gk1_mod_p)[1,1];
  Gk1_in_Xvar = Pol(apply(iso2,Vec(Gk1_mod_p)),Yglobal);
  D1 = [Fk_1, lift(Gk1_in_Xvar)];
  \\  if(debug, print("descentThreeTwo: here is D1 ",D1) );
  \\  now we can take Q compatibly and use section 8
  Q = divisor_to_point(D1,Ek);
  if(is_trap_point(Q,E,P_0), 
    print("descentThreeTwo: ERROR it was not a trap, why? whyyy?"); 
    \\  return(D);
  ); 
  section_8_data = descentThreeTwo_section8(Q,q,Ek,P_0k, super_traps, max_iterations);
  \\  ???? super_traps depends on the embedding!!!!!!!
  if(section_8_data==0, return(0));
  [point_found,a,b,c,d] = section_8_data; 
  [x_coord, y_coord] = point_found;
  \\ Now we compute the norm of div(g) and we remove D.
  f = (Yglobal-y_coord)/(Xglobal-x_coord);
  Psum = elladd(Ek, P_0k, [(1+gk-gk)*Xglobal,(1+gk-gk)*Yglobal]);
  ftilde = (Psum[2]-y_coord^q)/(Psum[1]-x_coord^q);
  g_numerator = c*f*ftilde + d*ftilde+a*f+b;
  D_g_numerator = norm_of_divisor_of_function(g_numerator, gk, gq, W, E);
  output = divisor_neg(D_g_numerator);
  flag_found_D = 0;
  for(i=1,#output[,1],
    if((output[i,1]==D)&&output[i,2],
      if(flag_found_D, 
        print("descentThreeTwo: WARNING, we found D multiple times!")
      ,
        flag_found_D = 1;
        output[i,2] = output[i,2]+1;
      );
    );
  );
  if(!flag_found_D,print("descentThreeTwo: WARNING, we did not find D"));
  output = divisor_clean(output);
  for(i=1,#output[,1],
    if((output[i,1]==D), print("descentThreeTwo: WARNING, we did not cancel D") );
  );
  var_polyq = 'var_polyq;
  polyabcd = c*(var_polyq)^(q+1) + d*(var_polyq)^(q) + a*(var_polyq) + b;
  debug_var = 0;
  foreach(polrootsmod(polyabcd), r,
    D0 = norm_of_divisor_of_function(f-r, gk, gq, W, E);
  \\  TO WRITE: if(debug, .. check that D0 contains -P  and [0] with coefficient -1 and )
    debug_var++;
    output = divisor_sum(output, D0);
  );
  if(debug_var!=q+1, print("descentThreeTwo: ERROR, polyabcd does not split on k, ", debug_var," ",polyabcd ));
  output;
}

test() = {
  [gq,E,P,W,idealM] = find_presentation(40);
  gQ = ffgen(2^(3*12*gq.f));
  emb = ffembed(gq,gQ);
  EQ = ffmap(emb,E);
  WQ = change_coeff_W(emb,W);
  \\  x_coord = gQ^2+gQ+1;
  x_coord = gQ^4+gQ+1;
  y_coord = ellordinate(EQ,x_coord);
  Q = [x_coord,y_coord[1]];
  D = point_to_divisor(Q,emb,W);
  trapsuper = find_super_traps(E,P); 
  D2 = descentThreeTwo(D,E,W,P,trapsuper)
}



\\ # ==================== 4-3 descent ==================== # 


descentFourThree_section9(Q,q,E,P_0, super_traps, max_iterations = 100000) = {
  \\  input: the elliptic curve E, and P_0 over a field k and Q defined over an extension of degree 4 of k, super_traps a list of points very bad (the ones such that phi_q(point) = point+P_0).
  \\  output: [P,Ptilde,alpha,beta,a,b,c,d]  as in section 9, which we can use to do the descent
  my(k_card,gk, g_full,deg_full_over_q,q_embed_full,E_full,R,Q0,R0,Q1,R1,Q2,R2, q_embed_k,k_embed_full, deg_ktrap,g_ktrap, traps_embed_ktrap,traps_ktrap, k_embed_ktrap, E_k,x_answer,y_answer,P_full,f_PQ0,f_PQ1,f_PQ2,f_PR0,f_PR1,f_PR2,M,a,b,c,d,P_trap,Q0_trap,Q1_trap,Q2_trap,R0_trap,R1_trap,R2_trap,last_check,k_embed_full_inv,split_condition1,f_PQ0_ktrap,f_PQ1_ktrap,f_PQ2_ktrap,f_PR0_ktrap,f_PR1_ktrap,f_PR2_ktrap,Bcross,alpha,Ptilde_not_found,Ptilde,Ptilde_full, to_check, x_Ptilde,y_Ptilde );
  \\?? at the moment we do not check if Q is a supertrap
  k_card = (E.j.p)^((vecsum(Q).f)/4);
  gk = ffgen(E.j); 
  g_full = ffgen(vecsum(Q)); \\ full field containing Q
  if((g_full.f)/((gk.f))!= 4, print("descentFourThree_section9: Error, the following point is not of degree 4 ",Q));
  k_embed_full = ffembed(gk, g_full);
  E_full = ffmap(k_embed_full,E);
  R = elladd(E_full,Q, ffmap(k_embed_full,P_0)); \\ actually this is phi(R) 
  deg_full_over_q = (g_full.f) / logint(q,g_full.p) ;
  for(i=1, deg_full_over_q-1,  R = apply(t->t^q,R)); \\ now R should be correct
  if(debug, if([R[1]^q,R[2]^q] != elladd(E_full,Q, ffmap(k_embed_full,P_0)), print("descentFourThree_section9: ERROR: R is not correct")));
  \\ GALOIS CONJ over k (defined below) OF R, Q
  [Q0,R0]= [Q,R];
  [Q1,R1]= [Q,R];
  for(i=1, deg_full_over_q/4, R1 = apply(t->t^q,R1); Q1 = apply(t->t^q,Q1));
  [Q2,R2]= [Q1,R1];
          \\  print("here I am3");
  for(i=1, deg_full_over_q/4, R2 = apply(t->t^q,R2); Q2 = apply(t->t^q,Q2));
  [Q3,R3]= [Q2,R2];
          \\  print("here I am3");
  for(i=1, deg_full_over_q/4, R3 = apply(t->t^q,R3); Q3 = apply(t->t^q,Q3));
  \\  FIELD kTrap containing k and ALSO THE SUPER TRAPS
  \\  ??? with the supertraps we are using composition of embeddings, we do not trust what we do
  deg_ktrap = lcm(g_full.f,super_traps[1][1].f);
  g_ktrap = ffgen((gk.p)^deg_ktrap);
  traps_embed_ktrap = ffembed(super_traps[1][1], g_ktrap);
  traps_ktrap = apply(P -> ffmap(traps_embed_ktrap,P),super_traps);
  k_embed_ktrap = ffembed(gk, g_ktrap);
  full_embed_ktrap = ffembed(g_full, g_ktrap);
  \\  WE start looking for Ptilde
  Ptilde_not_found = 1;
  while(Ptilde_not_found,
    x_Ptilde = random(gk);
    y_Ptilde = ellordinate(E,x_Ptilde);
    if(#y_Ptilde,
      Ptilde = [x_Ptilde,y_Ptilde[1]];
      Ptilde_full = ffmap(k_embed_full,Ptilde);
      to_check = [Q1,Q2,Q3,Q0,R1,R2,R3,R0];
      Ptilde_not_found=0;
      for(i=1,8,
        for(j=i+1,8,
          if(my_f(Ptilde_full,to_check[i]) == my_f(Ptilde_full,to_check[j]), Ptilde_not_found==1);
        );
      );
    );    
  );
  Ptilde_full = ffmap(k_embed_full,Ptilde);
  Q_s = [Q0,Q1,Q2,Q3];
  R_s = [R0,R1,R2,R3];
  l_s = vector(4,i,my_f(Ptilde_full,Q_s[i]));
  r_s = vector(4,i,my_f(Ptilde_full,R_s[i]));
  \\  NOW WE LOOK FOR P AND THE REST
      print("here I am2"); 
  for(number_iterations=1, max_iterations,
    x_answer = random(gk);
    alpha = random(gk);
    y_answer = ellordinate(E,x_answer);
    if(#y_answer
    ,
    y_answer = y_answer[1];
    P_full = ffmap(k_embed_full,[x_answer,y_answer]);
    alpha_full = ffmap(k_embed_full,alpha);
    \\  now we look for beta... the equation is a bit complicated.. we look at 9.2.2 
    var_beta = 'var_beta;
    L_pols = matrix(4,4,i,j,  (l_s[j]-l_s[i])*alpha_full + (my_f(P_full,Q_s[i])-my_f(P_full,Q_s[j]))*var_beta + (my_f(P_full,Q_s[i])*l_s[j]-my_f(P_full,Q_s[j])*l_s[i])  );
    R_pols = matrix(4,4,i,j,  (r_s[j]-r_s[i])*alpha_full + (my_f(P_full,R_s[i])-my_f(P_full,R_s[j]))*var_beta + (my_f(P_full,R_s[i])*r_s[j]-my_f(P_full,R_s[j])*r_s[i])  );
    eq_beta = L_pols[1,3]*L_pols[2,4]*(R_pols[1,2]^q)*(R_pols[3,4]^q) - L_pols[1,2]*L_pols[3,4]*(R_pols[1,3]^q)*(R_pols[2,4]^q);
    eq_beta = eq_beta/(Vec(eq_beta)[1]); \\ now monic and we try to push it to k
    k_embed_full_inv = ffinvmap(k_embed_full);
    \\  if(debug,ffmap(k_embed_full_inv,Vec(eq_beta)));
    eq_beta = ffmap(k_embed_full_inv,eq_beta);
    betas = polrootsmod(eq_beta);
    if(#betas,
    foreach(betas, beta,
      beta_full = ffmap(k_embed_full,beta);
      is_beta_eligible_CN = 1;
      for(i=1,4, if((l_s[i]+beta_full==0)||(r_s[i]+beta_full==0)  ,is_beta_eligible_CN=0)  );
      if(is_beta_eligible_CN,
      fQ_s = vector(4,i, (my_f(P_full,Q_s[i])+alpha_full)/(l_s[i]+beta_full));
      fR_s = vector(4,i, (my_f(P_full,R_s[i])+alpha_full)/(r_s[i]+beta_full));
      are_values_distinct = 1;
      for(i=1,4,
        for(j=i+1,4,
          if(fQ_s[i] == fQ_s[j], are_values_distinct==0);
        );
      );
      for(i=1,4,
        for(j=i+1,4,
          if(fR_s[i] == fR_s[j], are_values_distinct==0);
        );
      );
      if(are_values_distinct,
      \\  if(debug, print("descentFourThree_section9: here the value of f in Q and f(R)^q ",[fQ_s[1],fR_s[1]^q] ));
      M = [fQ_s[1],1+g_full-g_full,fR_s[1]^q*fQ_s[1],fR_s[1]^q; fQ_s[2],1+g_full-g_full,fR_s[2]^q*fQ_s[2],fR_s[2]^q; fQ_s[3],1+g_full-g_full,fR_s[3]^q*fQ_s[3],fR_s[3]^q];
      [a,b,c,d] = matker(M)[,1];
      if((a*d!=b*c) && (c*d^q !=c^q*a),
      [a,b,c,d] = [a/c,b/c,1+c-c,d/c];
      [a,b,c,d] = ffmap(k_embed_full_inv,[a,b,c,d]);
      if((a==[])|| (b==[]) || (c==[]) || (d==[]), print("descentFourThree_section9: could not force a,b,c,d into k!"));
      \\  THE CONDITION ON z and a,b,c,d is also satisfied if cX^(q+1)+dX^q+aX+b has all its roots in k. i.e. if X^k_card is congruent to X modulo cX^(q+1)+dX^q+aX+b.
      split_condition1 = Mod(Xglobal,c*Xglobal^(q+1)+d*Xglobal^(q)+a*Xglobal+b);
      split_condition1 = (split_condition1^k_card == split_condition1);
      \\  if(debug, print("descentFourThree_section9: iteration and number of roots ", number_iterations, " " ,#polrootsmod(c*Xglobal^(q+1)+d*Xglobal^(q)+a*Xglobal+b))); 
      if( split_condition1,    
        last_check = 1;
        fQ_s_trap = apply(x->ffmap(full_embed_ktrap,x),fQ_s);  
        fR_s_trap = apply(x->ffmap(full_embed_ktrap,x),fR_s);  
        P_trap = ffmap(k_embed_ktrap,[x_answer,y_answer]);
        Ptilde_trap = ffmap(k_embed_ktrap,Ptilde);
        foreach(traps_ktrap, B,
          last_check = last_check && ([x_answer^q,y_answer^q]!= elladd(E,ellneg(E,P_0),[x_answer,y_answer]) );
          Bcross = (my_f(P_trap,B)+ffmap(full_embed_ktrap,alpha_full))/(  my_f(Ptilde_trap,B) + ffmap(full_embed_ktrap,beta_full));
          last_check = last_check && ( my_crossratio(fQ_s_trap[1],fQ_s_trap[2],fQ_s_trap[3], Bcross)!= my_crossratio(fR_s_trap[1],fR_s_trap[2],fR_s_trap[3], Bcross )^q );
        );
      if(last_check,
      print("descentFourThree_section9: we arrived after ", number_iterations ," iterations"); 
      return([[x_answer,y_answer],Ptilde,alpha,beta,a,b,c,d] )
      ,     if(debug,print("descentFourThree_section9: in iteration "number_iterations, " we could not avoit supertraps"));
      ); \\ check we avoid supertraps
      ,     
      \\ if(debug,print("descentFourThree_section9: in iteration "number_iterations, " dT^{q+1}+cT^q+aT+b is split was not split"));
      ); \\ check dT^{q+1}+cT^q+aT+b is split
      ,     if(debug,print("descentFourThree_section9: in iteration "number_iterations, " ad-bc or cd^q-ac^q were null"));
      ); \\ check ad-bc e cd^q-ac^q not 0   
      ,     if(debug,print("descentFourThree_section9: in iteration "number_iterations, " f(sigma^i Q) or f(sigma^i R) were not distinct"));
      ); \\ check distinctness of f(sigma^i Q) and f(sigma^i R) 
      ,     if(debug,print("descentFourThree_section9: in iteration "number_iterations, " beta wanted to make us divide by zero"));
      ) \\ check we do not have to divide by 0
    ) \\for all betas
      ,
    \\  if(debug,print("descentFourThree_section9: in iteration "number_iterations, " did not find any beta"));
    )  \\ look for beta
    ,     
    \\  if(debug,print("descentFourThree_section9: in iteration "number_iterations, " did not find y"));
    ); \\check y exists 
  );
  print("descentFourThree_section9 DID NOT WORK!!");
  0;
}


my_f_as_function(point) = (Yglobal-point[2])/(Xglobal-point[1]) ;

descentFourThree(D,E,W,P_0,super_traps, max_iterations = 1000000) = {
  \\  input: th elliptic curve E (over F_q), with Weierstrass equation W and P_0 a point, D an irreducible divisor on E of degree 4d and super_traps a list ot all points, over an extensiton such that P^q = P_0+Q. 
  \\  output: a divisor D2 that is equivalent to D whose components have  essntial degree dividing 3 d or 2d
  my(q,Q,Q1,Q2 section_9_data,a,b,c,d, x_coord, y_coord, point_found, P,Ptilde,alpha,beta,Ptoq,Ptildetoq, gk,Wk, Dk,k_deg_q, deg_kq,q_embed_k, Ek, P_0k, Fk_1, iso1, iso2,Gk1_mod_p, Gk1_in_Xvar,D1, f,Psum,ftilde,k_full_divisor,k_divisor, g_numerator,D_g_numerator,flag_found_D,var_polyq,D0,Den, Dnum,polyabcd,debug_var,output);
  if(D==[0], return(D));
  if(is_trap_divisor(D,E,P_0), return(D));
  if(irreducible_divisor_deg(D)%4, print("Error in descentFourThree, here is desccentThreeTwo: the following divisor is not of degree divisible by 4 ",D));
  \\?? at the moment we do not check irreducibility of D
  \\  AS a first thing we go to the field k where we do a lot of the computations (then we will take a norm)
  q = (E.j.p)^(E.j.f);
  k_deg_q =  irreducible_divisor_deg(D)/4;
  gk = ffgen(q^k_deg_q, 'gk);
  if(verbose_for_example, print(gk.mod));
  q_embed_k = ffembed(E.j, gk);
  [Ek,P_0k] = [ffmap(q_embed_k, E),ffmap(q_embed_k, P_0)];
  Wk = change_coeff_W(q_embed_k, W);
  Dk = [ffmap(q_embed_k, D[1]), change_coeff_W(q_embed_k, D[2])];
  \\  now we construct an irreducible factor D1 of D_k
  Fk_1 =  factor(Dk[1])[1,1];
  \\ ?? we might check that the main variable of Fk_1  is X 
  [iso1, iso2] = field_in_standard(Fk_1);
  Gk1_mod_p = Pol(apply(iso1,Vec(Dk[2])),Yglobal);
  Gk1_mod_p = factor(Gk1_mod_p)[1,1];
  Gk1_in_Xvar = Pol(apply(iso2,Vec(Gk1_mod_p)),Yglobal);
  D1 = [Fk_1, lift(Gk1_in_Xvar)];
  Q = divisor_to_point(D1,Ek);
  if(verbose_for_example, print(" ") );
  if(verbose_for_example, print("descentFourThree here is D_{32}^Q: "point_to_divisor(Q,ffembed(gk,Q[1]),Wk)) );
  if(verbose_for_example, print("descentFourThree here is t in gk ",ffembed(ffgen(E.j),gk) ));
  if(is_trap_point(Q,E,P_0), 
    print("descentFourThree: ERROR it was not a trap, why? whyyy?"); 
    \\  return(D);
  ); 
  section_9_data = descentFourThree_section9(Q,q,Ek,P_0k, super_traps, max_iterations);
  \\  ?? super_traps depends on the embedding!!!!!!! \\  
  if(section_9_data==0, return(0));
  [P,Ptilde,alpha,beta,a,b,c,d] = section_9_data;
  if(verbose_for_example, print("descentFourThree here is P: "P ));
  if(verbose_for_example, print("descentFourThree here is Ptilde: "Ptilde ));
  if(verbose_for_example, print("descentFourThree here is alpha: "alpha ));
  if(verbose_for_example, print("descentFourThree here is beta: "beta ));
  if(verbose_for_example, print("descentFourThree here is a: "a ));
  if(verbose_for_example, print("descentFourThree here is b: "b ));
  if(verbose_for_example, print("descentFourThree here is c: "c ));
  if(verbose_for_example, print("descentFourThree here is d: "d ));
  
  \\  compute f and f^phi circ translation
  f = (my_f_as_function(P)+alpha)/(my_f_as_function(Ptilde)+beta);
  Psum = elladd(Ek, P_0k, [(1+gk-gk)*Xglobal,(1+gk-gk)*Yglobal]);
  Ptoq = apply(c->c^q,P);
  Ptildetoq = apply(c->c^q,Ptilde);
  ftilde =  ((Psum[2]-Ptoq[2])/(Psum[1]-Ptoq[1]) + alpha^q) / ( (Psum[2]-Ptildetoq[2])/(Psum[1]-Ptildetoq[1]) + beta^q);
  \\ Now we compute the norm of div(g) and we remove D.
  g_numerator = c*f*ftilde + d*ftilde+a*f+b;
  D_g_numerator = norm_of_divisor_of_function(g_numerator, gk, gq, W, E);
  output = divisor_neg(D_g_numerator);
  flag_found_D = 0;
  for(i=1,#output[,1],
    if((output[i,1]==D)&&output[i,2],
      if(flag_found_D, 
        print("descentFourThree: WARNING, we found D multiple times!")
      ,
        flag_found_D = 1;
        output[i,2] = output[i,2]+1;
      );
    );
  );
  if(!flag_found_D,print("descentFourThree: WARNING, we did not find D"));
  output = divisor_clean(output);
  for(i=1,#output[,1],
    if((output[i,1]==D), print("descentFourThree: WARNING, we did not cancel D") );
  );
  var_polyq = 'var_polyq;
  polyabcd = c*(var_polyq)^(q+1) + d*(var_polyq)^(q) + a*(var_polyq) + b;
  debug_var = 0;
  foreach(polrootsmod(polyabcd), r,
    D0 = norm_of_divisor_of_function(f-r, gk, gq, W, E);
    debug_var++;
    output = divisor_sum(output, D0);
  );
  if(debug_var!=q+1, print("descentFourThree: ERROR, polyabcd does not split on k, ", debug_var," ",polyabcd ));
  output;
}


test() = {
  [gq,E,P,W,idealM] = find_presentation(20);
  gQ = ffgen(2^(4*12*gq.f));
  emb = ffembed(gq,gQ);
  EQ = ffmap(emb,E);
  WQ = change_coeff_W(emb,W);
  \\  x_coord = gQ^2+gQ+1;
  x_coord = gQ^4+1;
  y_coord = ellordinate(EQ,x_coord);
  Q = [x_coord,y_coord[1]];
  D = point_to_divisor(Q,emb,W);
  trapsuper = find_super_traps(E,P); 
  D2 = descentFourThree(D,E,W,P,trapsuper)
}


\\ # ==================== Full Descent ==================== # 



full_descent(D,E,W,P_0,super_traps, threadshold, max_iterations= 1000000) = {
  \\  input: the elliptic curve E (over F_q), with Weierstrass equation W and P_0 a point, D a divisor on E of essential degree is a power of 2 times a power of 3. and super_traps a list ot all points, over an extensiton such that P^q = P_0+Q; threadshold a positive  integer 
  \\  output: a divisor D2 that is equivalent to D whose components have degree less than threadshold 
  my(max_deg, output, number_of_passatas,irr_div,new_piece,output_new);
  number_of_passatas = 1;
  output = D;
  output_new = D;
  max_deg = vecmax(apply(irreducible_divisor_deg, output[,1]));
  while(max_deg>threadshold,
    if(debug, print("HERE FULL DESCENT: \n\n\n, n_passata and maxdeg = ", [number_of_passatas, max_deg]);
    print(output);
    );
    for( i=1, #output[,1],
      irr_div = output[i,1];
      \\  if(debug,print(irr_div));
      if(irreducible_divisor_deg(irr_div)==max_deg,
        if((max_deg%3)==0,
          new_piece = descentThreeTwo(irr_div,E,W,P_0,super_traps, max_iterations);
        ,
          new_piece = descentFourThree(irr_div,E,W,P_0,super_traps, max_iterations);
        );
        new_piece = divisor_mul(new_piece, output[i,2]);
        output_new = divisor_sum(output_new, Mat([irr_div,-output[i,2]]) );
        output_new = divisor_sum(output_new,new_piece);
        output_new =   divisor_clean(output_new);
      );
    );
    output = output_new;
    max_deg = vecmax( apply(irreducible_divisor_deg, output[,1] ) );
    number_of_passatas++;
  );
  output;
}


test() = {
  [gq,E,P,W,idealM] = find_presentation(18);
  gQ = ffgen(2^(4*12*gq.f));
  emb = ffembed(gq,gQ);
  EQ = ffmap(emb,E);
  WQ = change_coeff_W(emb,W);
  \\  x_coord = gQ^2+gQ+1;
  x_coord = gQ^4+1;
  y_coord = ellordinate(EQ,x_coord);
  Q = [x_coord,y_coord[1]];
  D = point_to_divisor(Q,emb,W);
  trapsuper = find_super_traps(E,P); 
  div = [D,1;[0], -1];
  D2 = full_descent(div,E,W,P,trapsuper, 20)
}
\\  test()


reduce_to_factor_base(poly,gq,E,P_0,W,idealM,super_traps,threadshold,max_iterations=1000000) = {
  \\  input: poly a polynomial in Xglobal, gq E,P_0,W,idealM as in the elliptic presentation; super_traps a list of points such that point^q = point+P_0, threadsholdm the degree of divisors in the factor base.
  \\  output a divisor which of the essential degree at most threadshold and which is equivalent to div(f)
  my(polyy, poly_lifted,D);
  polyy = poly;
  if(poldegree(polyy,Yglobal), polyy=polyy%idealM[2]);
  if(poldegree(polyy,Yglobal), print("reduce_to_factor_base: ERROR, we could not eliminate the Yglobal"));
  if(variable(polyy)==Yglobal, polyy = polcoeff(polyy,0));
  if(polyy==0, print("reduce_to_factor_base: ERROR, poly is zero"));
  if(variable(polyy)==0, return(ZeroDivisor));
  if(variable(polyy)!=Xglobal, print("reduce_to_factor_base: ERROR, not constant, not a poly in Xglobal"));  

  poly_lifted = lift_2_power(polyy,idealM[1]);
  D = norm_of_divisor_of_function(poly_lifted, gq, gq, W, E);
  full_descent(D,E,W,P_0,super_traps, threadshold, max_iterations);
}

test() = {
  [gq,E,P,W,idealM] = find_presentation(34);
  [gq,E,P,W,idealM] = find_presentation_small(95);
  reduce_to_factor_base(Xglobal^15-gq,gq,E,P,W,idealM,trapsuper,13,100000)
}
\\ test()





\\ # ==================== COMPUTE IN EXAMPLE ==================== # 



print("Presentation for 2^93");
eK = 3*31
gK = ffgen(2^eK);
[gq,E,P,W,idealM]= find_presentation_small(3*31);
print([gq.f, poldegree(idealM[1])]);
print(gq.mod);
print(W);
print(P); 
print("\n\n\n");






print("Presentation for 2^30");
e = 30;
gK = ffgen(2^eK);

[gq,E,P_0,W,idealM]= find_presentation_small(e);
print([gq.f, poldegree(idealM[1])]);
print(gq.mod);
print(W);
print(P); 
print(idealM);
print("\n\n\n");






print("factor base");
factor_base = irreducible_divisors(W,2);
print(factor_base);
print("\n\n\n");




print("traps");
some_traps = find_traps_for_exemple(E,W,P_0);
print(some_traps);
print("\n\n\n");










print("Check g is a multiplicative generator");
ord_tmp = (2^e)-1;
facts_tmp = factor(ord_tmp)[,1];
gK = Mod(Xglobal,idealM[1]);
gen = gK^3+1;
hen = gK^5+gq;
print(gen);
foreach(facts_tmp,fact,print(gen^(ord_tmp/fact)-1!=0) );
print(hen);
print("\n\n\n");







print("lift");
elt_relation = (gen^2024)*(hen^2025);
setrand(2025); 
f_1 = lift_2_power(lift(elt_relation), idealM[1], 1000);
D = norm_of_divisor_of_function(f_1, gq, gq, W, E);
print(elt_relation);
print();
print(f_1);
print(D);
print(apply(irreducible_divisor_deg, D[,1]));
print("\n\n\n");




print("descent")
div = Mat([D[1,1],1]);
trapsuper = find_super_traps(E,P_0); 
D2 = full_descent(div,E,W,P_0,trapsuper, 10);
print(D2);
print("\n\n\n");





\\  print("trap descent")
\\  divt = Mat([some_traps[9],1]);
\\  D3 = full_descent(divt,E,W,P_0,trapsuper, 10);
\\  descentFourThree(some_traps[9],E,W,P_0,trapsuper, 1000000);
