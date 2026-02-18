int main1(int a,int b,int p,int q){
  int l, i, v, n, m;

  l=65;
  i=l;
  v=l;
  n=l;
  m=4;

  
  /*@

    loop invariant i >= 0;

    loop invariant v - m == l - 4;

    loop invariant m + 4*i == 4 + 4*l;

    loop invariant l == 65;

    loop invariant v == 325 - 4*i;

    loop invariant m == 264 - 4*i;

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && p == \at(p, Pre) && q == \at(q, Pre);

    loop invariant 0 <= i <= 65;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns i, v, m;

    loop variant i;

  */
  while (i>0) {
      v = v+4;
      m = m+4;
      i = i-1;
  }

}