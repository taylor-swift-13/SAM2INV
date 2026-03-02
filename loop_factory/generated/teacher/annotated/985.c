int main1(int a,int m){
  int d, r, v, s;

  d=51;
  r=1;
  v=m;
  s=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant d == 51;
  loop invariant r == 1;
  loop invariant (v - \at(m, Pre)) % 3 == 0;

  loop invariant v >= \at(m, Pre);
  loop invariant 1 <= r && r <= d;

  loop invariant d == 51 && r == 1;
  loop invariant (v - \at(m, Pre)) % 3 == 0 && v >= \at(m, Pre);
  loop invariant (m + 7 == 0) ==> (s + v + 6 == 0);

  loop invariant r == 1 && r <= d && v >= \at(m, Pre) && d == 51;
  loop invariant r == 1 && d == 51 && (v - \at(m, Pre)) % 3 == 0;
  loop invariant m == \at(m, Pre) && a == \at(a, Pre) && r <= d;
  loop invariant d == 51 && r == 1 && m == \at(m, Pre) && a == \at(a, Pre);

  loop invariant (v - \at(m, Pre)) % 3 == 0 && v >= \at(m, Pre) && r <= d - 3;
  loop assigns v, s;
*/
while (r<=d-4) {
      v = v+3;
      s = s+s;
      s = s+v;
  }

}
