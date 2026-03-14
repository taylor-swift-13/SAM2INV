int main1(){
  int nseq, p, z7ap, b79, lt, uha, wmj7;
  nseq=64;
  p=nseq;
  z7ap=0;
  b79=(1%28)+10;
  lt=-4;
  uha=3;
  wmj7=nseq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wmj7 == p * z7ap + 64;
  loop invariant nseq == 64;
  loop invariant b79 == 11 - (z7ap*(z7ap - 1))/2;
  loop invariant lt == -4 + (p + 2) * z7ap;
  loop invariant z7ap >= 0;
  loop invariant p == 64;
  loop assigns b79, lt, z7ap, wmj7;
*/
while (b79>z7ap) {
      b79 -= z7ap;
      lt += 2;
      z7ap += 1;
      wmj7 += p;
      lt += p;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uha == 3;
  loop invariant nseq >= 0;
  loop assigns b79, lt, z7ap, nseq, wmj7;
*/
while (nseq>0) {
      lt = lt+1*1;
      z7ap = z7ap+1*1;
      b79 = b79+1*1;
      nseq -= 1;
      wmj7 += uha;
  }
}