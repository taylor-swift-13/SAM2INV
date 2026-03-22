int main1(){
  int ob, q, dv, i, j6;
  ob=1;
  q=ob;
  dv=1;
  i=0;
  j6=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j6 == 1 + dv*i;
  loop invariant dv >= 1;
  loop invariant (ob - dv) >= 0;
  loop invariant ob == 1;
  loop invariant i == 0;
  loop assigns dv, i, j6;
*/
while (1) {
      if (!(dv<ob)) {
          break;
      }
      dv = 2*dv;
      i = i + 1;
      j6 += dv;
  }
}