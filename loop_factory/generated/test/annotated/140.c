int main1(){
  int af, km, m, n7mp;
  af=1+15;
  km=0;
  m=8;
  n7mp=km;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n7mp == 0;
  loop invariant m - 2*n7mp*km == 8;
  loop invariant 0 <= km <= af;
  loop invariant af == 16;
  loop assigns m, km;
*/
while (1) {
      if (!(km<=af-1)) {
          break;
      }
      m = m+n7mp+n7mp;
      km = km + 1;
  }
}