int main1(int m){
  int r0, p4, hc, le4a, max;
  r0=m-8;
  p4=r0+5;
  hc=p4;
  le4a=0;
  max=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r0 == m - 8;
  loop invariant le4a == 0;
  loop invariant max == 1;
  loop invariant hc == (r0+5) * (((r0+5) - p4) + 1)
                           - (((r0+5) - p4) * (((r0+5) - p4) - 1)) / 2;
  loop invariant 0 <= p4 - r0 <= 5;
  loop assigns hc, le4a, max, p4;
*/
while (1) {
      if (!(p4>r0)) {
          break;
      }
      hc += p4;
      le4a = le4a*le4a;
      max = max+hc*le4a;
      p4 = p4 - 1;
  }
}