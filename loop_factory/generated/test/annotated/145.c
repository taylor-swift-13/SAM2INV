int main1(int e){
  int ict, vix, n9h;
  ict=69;
  vix=0;
  n9h=ict;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n9h == ict - vix;
  loop invariant e == \at(e, Pre) + ict * vix - vix * (vix + 1) / 2;
  loop invariant 0 <= vix <= ict;
  loop assigns e, vix, n9h;
*/
while (1) {
      if (!(vix<ict)) {
          break;
      }
      vix++;
      n9h = ict-vix;
      e = e + n9h;
  }
}