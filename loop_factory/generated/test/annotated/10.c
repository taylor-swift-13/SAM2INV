int main1(int b,int p){
  int hc, s, c;
  hc=0;
  s=-17004;
  c=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == -17004 + ((b - \at(b, Pre)) * (b - \at(b, Pre) + 7)) / 2;
  loop invariant p == \at(p, Pre);
  loop invariant (b - \at(b, Pre)) == (c - 6);
  loop invariant hc == 0;
  loop invariant c >= 6;
  loop assigns b, p, s, c;
*/
while (s<=-3) {
      s = s+c-2;
      b += 1;
      p = p + hc;
      c = c + 1;
  }
}