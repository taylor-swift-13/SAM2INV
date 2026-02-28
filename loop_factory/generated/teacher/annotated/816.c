int main1(int b,int p){
  int t, e, h;

  t=24;
  e=0;
  h=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant h >= 0;
  loop invariant e % 3 == 0;
  loop invariant 0 <= e;
  loop invariant e <= t;
  loop invariant h >= e + 24;
  loop invariant t == 24;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant h >= t;
  loop invariant h % 2 == 0;
  loop invariant h >= 24;
  loop assigns h, e;
*/
while (e<=t-3) {
      h = h+h;
      if (h<e+3) {
          h = h+4;
      }
      e = e+3;
  }

}
