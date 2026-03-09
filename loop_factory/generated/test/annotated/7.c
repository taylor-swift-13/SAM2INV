int main1(){
  int x, sj, uo, gv;
  x=1;
  sj=x;
  uo=12;
  gv=sj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 1;
  loop invariant uo == 3*gv + 9;
  loop invariant uo >= 12;
  loop assigns gv, uo;
*/
while (uo<=x-1) {
      uo = uo + 3;
      gv += x;
  }
}