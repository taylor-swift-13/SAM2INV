int main1(int s){
  int a1, r9, x2v;
  a1=s;
  r9=0;
  x2v=r9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a1 == \at(s, Pre);
  loop invariant s >= \at(s, Pre);
  loop invariant ((s - \at(s, Pre)) % 3) == 0;
  loop invariant r9 >= 0;
  loop invariant x2v >= 0;
  loop invariant r9 == (((s - \at(s, Pre)) / 3) * \at(s, Pre)) + ((3 * ((s - \at(s, Pre)) / 3) * ((((s - \at(s, Pre)) / 3) - 1))) / 2);
  loop invariant x2v == ((((s - \at(s, Pre)) / 3) * (((s - \at(s, Pre)) / 3 + 1)) * (\at(s, Pre) + ((s - \at(s, Pre)) / 3) - 1)) / 2);
  loop invariant 6 * r9 == (s - \at(s, Pre)) * (s + \at(s, Pre) - 3);
  loop invariant 54 * x2v == (s - \at(s, Pre)) * ((s - \at(s, Pre)) + 3) * (s + 2 * \at(s, Pre) - 3);
  loop invariant 54 * x2v == (s - \at(s, Pre)) * (s - \at(s, Pre) + 3) * (s + 2 * \at(s, Pre) - 3);
  loop invariant (s - \at(s, Pre)) % 3 == 0;
  loop invariant (s*s - \at(s, Pre)*\at(s, Pre) - 6*r9 - 3*(s - \at(s, Pre))) == 0;
  loop invariant r9 >= 0 && x2v >= 0;
  loop invariant 2 * r9 == 2 * ((s - \at(s, Pre)) / 3) * \at(s, Pre) + 3 * ((s - \at(s, Pre)) / 3) * (((s - \at(s, Pre)) / 3) - 1);
  loop invariant 2 * x2v == ((s - \at(s, Pre)) / 3) * (((s - \at(s, Pre)) / 3) + 1) * (\at(s, Pre) + ((s - \at(s, Pre)) / 3) - 1);
  loop assigns r9, s, x2v;
*/
while (r9 < a1) {
      r9 = r9 + s;
      s = s + 3;
      x2v = x2v + r9;
  }
}