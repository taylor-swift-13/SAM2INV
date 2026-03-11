int main1(int o,int u){
  int ipsj, cxn7, cd;
  ipsj=(o%20)+5;
  cxn7=(o%20)+5;
  cd=(o%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ipsj == cxn7;
  loop invariant cxn7 == cd;
  loop invariant ipsj <= ((\at(o, Pre) % 20) + 5);
  loop invariant o >= \at(o, Pre);
  loop assigns ipsj, cxn7, cd, o;
*/
while (ipsj>0) {
      if (cxn7>0) {
          if (cd>0) {
              ipsj--;
              cxn7--;
              cd -= 1;
          }
      }
      o += cxn7;
  }
/*@
  assert !(ipsj>0) &&
         (ipsj == cxn7);
*/


  int __aux_10=0;
  while (__aux_10 < 3) { __aux_10 = __aux_10 + 1; }
}