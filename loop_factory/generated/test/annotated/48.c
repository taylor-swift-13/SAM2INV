int main1(int a,int m,int p,int q){
  int l, i, v;

  l=11;
  i=l;
  v=2;

  
  /*@

    loop invariant 0 <= i <= 11;

    loop invariant l == 11;

    loop invariant v == 2 - (11 - i) * q;

    loop invariant a == \at(a, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant v == 2 - q * (l - i);

    loop invariant v == 2 - (l - i) * q;

    loop invariant i <= 11;

    loop invariant v + (11 - i) * q == 2;

    loop assigns v, i;

  */
  while (i>0) {
      v = v-q;
      i = i-1;
  }

}