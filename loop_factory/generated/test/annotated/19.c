int main1(int k,int n,int p,int q){
  int l, i, v;

  l=q;
  i=l;
  v=k;

  
  /*@

    loop invariant l == \at(q, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);


    loop invariant k == \at(k, Pre) && n == \at(n, Pre) && p == \at(p, Pre) && q == \at(q, Pre);

    loop invariant (k == 0) ==> (v == 0);


    loop invariant (\at(q, Pre) >= 0) ==> (0 <= i && i <= \at(q, Pre));

    loop invariant (\at(q, Pre) <= 0) ==> (\at(q, Pre) <= i && i <= 0);


    loop invariant i <= \at(q, Pre);


    loop invariant (\at(k, Pre) <= 0) ==> v * i >= \at(k, Pre) * \at(q, Pre);


    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      v = v*2;
      i = i/2;
  }

}