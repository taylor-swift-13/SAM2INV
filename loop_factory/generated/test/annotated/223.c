int main1(int t,int u){
  int ug, bq, vm;
  ug=38;
  bq=0;
  vm=bq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == \at(t, Pre);
  loop invariant vm >= 0;
  loop invariant bq == 0;
  loop invariant ug == 38;
  loop invariant u == \at(u, Pre) + vm * ug;
  loop assigns vm, u;
*/
while (bq<=ug-1) {
      vm += 1;
      u = u+ug-bq;
  }
}