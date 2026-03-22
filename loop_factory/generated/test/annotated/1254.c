int main1(){
  int rlb, rzm, po, zk, ayy;
  rlb=76;
  rzm=rlb;
  po=-2;
  zk=rzm;
  ayy=rlb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zk >= 76;
  loop invariant rlb == 76;
  loop invariant rzm >= 0;
  loop invariant ayy == rlb * (1 + (zk - rlb)) + ((zk - rlb) * (zk - rlb + 1)) / 2;
  loop assigns zk, ayy, po, rzm;
*/
while (rzm>0) {
      zk++;
      ayy = ayy + zk;
      po = po+zk*zk*zk*zk*zk;
      rzm = 0;
  }
}