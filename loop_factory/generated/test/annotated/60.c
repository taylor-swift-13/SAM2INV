int main1(int b,int m,int n,int p){
  int l, i, v, g;

  l=80;
  i=0;
  v=b;
  g=-3;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant v == \at(b, Pre) + i*(i-1)/2;

    loop invariant (i == 0) ==> (g == -3);

    loop invariant (i > 0) ==> (g >= 0);

    loop invariant l == 80;

    loop invariant i <= l;

    loop invariant v == b + i*(i-1)/2;

    loop invariant (b == \at(b, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre));

    loop invariant v == b + (i*(i-1))/2;

    loop invariant (i > 0) ==> (g > 0);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i && i <= l;

    loop assigns v, g, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      g = g*g;
      i = i+1;
  }

}