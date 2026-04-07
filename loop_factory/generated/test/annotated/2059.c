int main1(){
  int i3, t2, s, pu1, k9s, bhr;
  i3=1;
  t2=0;
  s=t2;
  pu1=t2;
  k9s=6;
  bhr=i3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= t2);
  loop invariant (t2 <= i3);
  loop invariant (bhr == 1);
  loop invariant (k9s == 6 + bhr * t2);
  loop invariant pu1 == (6 * t2) + (bhr * (t2 * (t2 - 1) / 2));
  loop invariant s == (6 * (t2 * (t2 - 1) / 2)) + (bhr * (t2 * (t2 - 1) * (t2 - 2) / 6));
  loop invariant 2 * pu1 == 12 * t2 + bhr * (t2 * (t2 - 1));
  loop invariant 6 * s == 18 * t2 * (t2 - 1) + bhr * (t2 * (t2 - 1) * (t2 - 2));
  loop invariant s == (3 * t2 * (t2 - 1) + bhr * (t2 * (t2 - 1) * (t2 - 2) / 6));
  loop assigns s, pu1, k9s, t2;
*/
while (1) {
      if (!(t2 < i3)) {
          break;
      }
      s += pu1;
      pu1 = pu1 + k9s;
      k9s += bhr;
      t2++;
  }
}