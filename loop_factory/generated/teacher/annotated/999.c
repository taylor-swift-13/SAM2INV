int main1(int m,int p){
  int h, t, v;

  h=(p%28)+16;
  t=0;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 0;
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant h == (\at(p, Pre) % 28) + 16;

  loop invariant (5 > p + h) ==> ((v - \at(m, Pre)) % 2 == 0);
  loop invariant p == \at(p,Pre) && m == \at(m,Pre) && h == \at(p,Pre) % 28 + 16 && t == 0;

  loop invariant h + p == \at(p, Pre) + (\at(p, Pre) % 28) + 16;
  loop invariant p == \at(p, Pre) && m == \at(m, Pre) && h == \at(p, Pre) % 28 + 16;
  loop invariant (t + 5 <= p + h) || ((v - \at(m, Pre)) % 2 == 0);
  loop invariant t == 0 && p == \at(p, Pre) && m == \at(m, Pre) && h == (\at(p, Pre) % 28 + 16);
  loop invariant v >= \at(m, Pre) || v >= 0;
  loop invariant p == \at(p, Pre) && h == \at(p, Pre) % 28 + 16;

  loop assigns v;
*/
while (1) {
      v = v+2;
      if (t+5<=p+h) {
          v = v-v;
      }
      else {
          v = v+t;
      }
  }

}
