int main1(int e){
  int hyn, wt, dg04, j;
  hyn=e+12;
  wt=hyn;
  dg04=e*3;
  j=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (wt == hyn && j == 0) || (wt == 5 && j == dg04 * hyn);
  loop invariant dg04 == 3 * e;
  loop invariant hyn == \at(e, Pre) + 12;
  loop invariant e == \at(e, Pre);
  loop assigns j, wt;
*/
while (wt>5) {
      j = j+dg04*wt;
      wt = 5;
  }
}