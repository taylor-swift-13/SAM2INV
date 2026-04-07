int main1(int v){
  int nqop, e1, o0u8, zk;
  nqop=(v%38)+20;
  e1=0;
  o0u8=0;
  zk=nqop;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= e1;
  loop invariant nqop == \at(v, Pre) % 38 + 20;
  loop invariant nqop <= zk;
  loop invariant zk <= nqop + 1;
  loop invariant (e1 == 0) ==> (zk == nqop && o0u8 == 0);
  loop invariant (e1 == 0) || (e1 == nqop);
  loop assigns zk, o0u8, e1;
*/
while (e1<=nqop-1) {
      zk++;
      o0u8 = o0u8+zk*zk*zk;
      e1 = nqop;
  }
}