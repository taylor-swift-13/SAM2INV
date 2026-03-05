int main1(int p){
  int fs, a;
  fs=(p%11)+15;
  a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fs == \at(p, Pre) % 11 + 15;
  loop invariant a % 2 == 0;
  loop invariant 0 <= a;
  loop invariant a <= fs + 1;
  loop invariant p == \at(p, Pre) + (a/2) * ((a/2) + 1);
  loop assigns a, p;
*/
while (a<fs) {
      a += 2;
      if (a<=a) {
          a = a;
      }
      p = p + a;
  }
}