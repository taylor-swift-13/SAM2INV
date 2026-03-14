int main1(){
  int sw, xw, gns;
  sw=1+19;
  xw=0;
  gns=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (xw == 0) ==> (gns == -1);
  loop invariant sw == 1 + 19;
  loop invariant 0 <= xw;
  loop invariant xw <= sw;
  loop invariant (xw > 0) ==> (gns == sw - xw + 2);
  loop assigns gns, xw;
*/
while (xw<sw) {
      gns = sw-xw;
      xw += 1;
      gns++;
  }
}