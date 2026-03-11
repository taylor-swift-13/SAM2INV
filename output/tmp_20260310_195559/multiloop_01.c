int main1(int a,int m){
  int qf, rg8, kb, o;
  qf=m+4;
  rg8=qf;
  kb=m;
  o=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qf == \at(m, Pre) + 4;
  loop invariant a == \at(a, Pre);
  loop invariant qf - rg8 >= 0;
  loop assigns rg8;
*/
while (rg8>=1) {
      rg8--;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kb == \at(m, Pre);
  loop invariant qf >= \at(m, Pre) + 4;
  loop invariant a == \at(a, Pre) + (qf - (\at(m, Pre) + 4)) * rg8;
  loop invariant o >= 0;
  loop invariant rg8 <= \at(m, Pre) + 4;
  loop assigns a, qf, o;
*/
while (qf<kb) {
      o = kb-qf;
      qf += 1;
      a = a + rg8;
  }
/*@
  assert !(qf<kb) &&
         (qf == \at(m, Pre) + 4);
*/

}