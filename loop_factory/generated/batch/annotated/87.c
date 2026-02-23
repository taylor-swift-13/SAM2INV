int main1(int k,int p){
  int h, g, s;

  h=p-7;
  g=0;
  s=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == \at(p, Pre) - 7;
  loop invariant p == \at(p, Pre) && k == \at(k, Pre);

  loop invariant h < 6 ==> s == -3;
  loop invariant p == \at(p, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant g >= 0;
  loop invariant (h >= 0) ==> g <= h;
  loop invariant s % 3 == 0 && s < 0;
  loop invariant (h < 6) ==> s == -3;
  loop invariant h == p - 7;
  loop invariant s <= -3;
  loop invariant s % 3 == 0;
  loop invariant (h < 6) ==> (s == -3);
  loop assigns g, s;
*/
while (g<h) {
      if (g+6<=g+h) {
          s = s+s;
      }
      g = g+1;
  }

}
