int main1(int a,int m,int q){
  int l, i, v, k, g, f, r;

  l=43;
  i=1;
  v=i;
  k=q;
  g=-4;
  f=m;
  r=a;

  
  /*@

    loop invariant v == i;

    loop invariant k == q + 2*i - 2;

    loop invariant 1 <= i && i <= 2*l;

    loop invariant a == \at(a, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns v, k, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v*2;
      k = k+v;
      i = i*2;
  }

}