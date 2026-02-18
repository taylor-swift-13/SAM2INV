int main1(int a,int m,int n,int q){
  int l, i, v;

  l=n;
  i=l;
  v=6;

  
  /*@


    loop invariant i <= n;

    loop invariant l == n;

    loop invariant a == \at(a, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant v >= 6;

    loop invariant v % 6 == 0;

    loop invariant (i > q+3) ==> (v == 6);

    loop invariant v > 0;


    loop invariant (i >= q+4) ==> (v == 6);

    loop assigns v, i;

  */
  while (i>0) {
      if (i<q+4) {
          v = v+v;
      }
      i = i-1;
  }

}