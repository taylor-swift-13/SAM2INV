int main1(int a,int m,int n,int p){
  int s, h, v, b, j, e;

  s=21;
  h=s;
  v=a;
  b=-6;
  j=-6;
  e=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (e == 3 || e == 36);
  loop invariant (v == a || v == 36);
  loop invariant (h >= 0);
  loop invariant (h <= 21);
  loop invariant s == 21;
  loop invariant b == -6;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant h >= 0;
  loop invariant h <= 21;
  loop invariant h < 21 ==> e == b*b;
  loop invariant h < 21 ==> v == b*b;
  loop invariant e == 3 || e == b*b;
  loop invariant v == a || v == b*b;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 0 <= h;
  loop invariant h <= s;
  loop invariant e >= 0;
  loop assigns e, v, h;
*/
while (h>=1) {
      e = e*e+v;
      v = v%6;
      e = b*b;
      v = b*b;
      h = h-1;
  }

}
