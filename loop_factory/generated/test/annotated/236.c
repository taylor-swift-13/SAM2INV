int main1(int n){
  int hl9, hz;
  hl9=66;
  hz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hz >= 0;
  loop invariant n - \at(n, Pre) >= hz;
  loop invariant hz <= 2*hl9 + 1;
  loop invariant hl9 == 66;
  loop assigns hz, n;
*/
while (hz<=hl9) {
      hz = 2*hz;
      hz++;
      n += hz;
  }
}