int main1(int a,int b,int m,int p){
  int l, i, v, s, r;

  l=(p%7)+8;
  i=0;
  v=-8;
  s=3;
  r=p;

  
  /*@

    loop invariant i == 0;

    loop invariant l == (p % 7) + 8;

    loop invariant v >= -8;

    loop invariant v % 2 == 0;

    loop invariant 4*s == v*v + 4*v - 20;

    loop invariant p == \at(p, Pre);

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant l == (\at(p, Pre) % 7) + 8;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant i >= 0;

    loop invariant s == (v*v)/4 + v - 5;

    loop assigns v, s;

  */
  while (i<l) {
      v = v+1;
      s = s+1;
      v = v+1;
      s = s+v;
  }

}