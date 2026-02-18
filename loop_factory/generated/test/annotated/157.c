int main1(int m,int n,int p,int q){
  int l, i, v;

  l=p-6;
  i=0;
  v=1;

  
  /*@

    loop invariant l == \at(p, Pre) - 6;


    loop invariant v >= 1;

    loop invariant i >= 0;

    loop invariant l == p - 6;


    loop invariant p == \at(p, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant 0 <= i;


    loop invariant (l <= 1) ==> (v == 1);

    loop invariant (l < 0) || (i <= l);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      if (v+1<l) {
          v = v+v;
      }
      i = i+1;
  }

}