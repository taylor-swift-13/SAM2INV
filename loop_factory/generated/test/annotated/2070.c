int main1(){
  int g, zk, shq, niss, rv28;
  g=1+11;
  zk=0;
  shq=5;
  niss=zk;
  rv28=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant shq == 5 + zk*(zk + 1)/2;
  loop invariant (0 <= zk && zk <= g && rv28 == -6);
  loop invariant niss >= zk * rv28;
  loop invariant niss <= zk * shq;
  loop invariant shq <= 5 + g*(g+1)/2;
  loop assigns niss, zk, shq;
*/
while (zk < g) {
      niss = zk % 2 == 0 ? niss + shq : niss + rv28;
      zk++;
      shq = shq + zk;
  }
}