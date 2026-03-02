int main1(int b,int q){
  int r, v, m, p;

  r=59;
  v=r;
  m=-5;
  p=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m % 5 == 0 && m <= -5 && v >= 0;
  loop invariant v <= 59 && b == \at(b, Pre) && q == \at(q, Pre);
  loop invariant r == 59;
  loop invariant 0 <= v && v <= r;
  loop invariant m <= -5;
  loop invariant m * v <= 0;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant m % 5 == 0 && m <= -5;
  loop invariant v >= 0 && v <= r && r == 59;
  loop invariant m * v >= -295 && m <= -5;
  loop invariant v >= 0 && v <= 59;
  loop invariant m * v >= -295;
  loop invariant v >= 0;
  loop invariant v <= r;
  loop invariant 2*m*(v/2) == m*(v - v%2);
  loop invariant v >= 0 && v <= r;
  loop invariant m < 0;
  loop invariant b == \at(b, Pre) && q == \at(q, Pre);
  loop invariant v <= 59;
  loop invariant m % 5 == 0;
  loop assigns m, v;
*/
while (v>=1) {
      m = m*2;
      v = v/2;
  }

}
