int main1(int m,int n,int p,int q){
  int l, i, v;

  l=(p%7)+12;
  i=0;
  v=l;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v >= l;


    loop invariant l == (p % 7) + 12;

    loop invariant 0 <= i;


    loop invariant l == (\at(p, Pre) % 7) + 12;

    loop invariant (i == 0) ==> (v == l);

    loop invariant p == \at(p, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && q == \at(q, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns i, v;

  */
  while (i<l) {
      if ((i%4)==0) {
          v = v+v;
      }
      i = i+1;
  }

}