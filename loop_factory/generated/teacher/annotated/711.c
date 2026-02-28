int main1(int a,int b,int k,int m){
  int x, z, c, r, v, p, y, w;

  x=42;
  z=0;
  c=0;
  r=1;
  v=6;
  p=0;
  y=m;
  w=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p >= 0;
  loop invariant p <= x + 1;
  loop invariant v == 6 + 2*p;
  loop invariant r == p*p + 5*p + 1;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant c >= 0;
  loop invariant r >= 1;
  loop invariant v >= 6;
  loop invariant x == 42;

  loop invariant c == p*(p*p + 6*p - 4)/3;
  loop assigns p, c, r, v;
*/
while (p<=x) {
      p = p+1;
      c = c+r;
      r = r+v;
      v = v+2;
  }

}
