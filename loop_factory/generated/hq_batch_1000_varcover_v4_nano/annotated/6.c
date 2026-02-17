int main1(int b,int m,int q){
  int l, i, v, x, y, g, t, f;

  l=52;
  i=0;
  v=b;
  x=i;
  y=m;
  g=1;
  t=q;
  f=m;

  
  /*@

    loop invariant i % 2 == 0;

    loop invariant 0 <= i && i <= l;

    loop invariant v == \at(b, Pre) + (i/2) * ((i/2) - 1);

    loop invariant x == 0;

    loop invariant y == \at(m, Pre);

    loop invariant t == \at(q, Pre);

    loop assigns v, x, y, t, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+i;
      x = x*x;
      y = y+v*x;
      if (t*t<=l+5) {
          t = t+x;
      }
      i = i+2;
  }

}