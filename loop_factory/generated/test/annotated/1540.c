int main1(){
  int l, z, fqc, nl, l1, cy7, cq, x, cwq;
  l=1;
  z=0;
  fqc=4;
  nl=6;
  l1=l;
  cy7=8;
  cq=z;
  x=1*4;
  cwq=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 4 + z;
  loop invariant l1 == l + z/2;
  loop invariant z <= l + 1;
  loop invariant l == 1;
  loop invariant (z == 0) ==> (fqc == 4);
  loop invariant z >= 0;
  loop invariant l1 >= 0;
  loop invariant l1 <= l + 1;
  loop invariant cy7 == 8;
  loop invariant fqc % 3 == (1 + z) % 3;
  loop invariant nl % 5 == (6 + z * (z + 1) / 2) % 5;
  loop assigns z, x, fqc, nl, l1, cy7, cwq, cq;
*/
while (z <= l) {
      z += 1;
      x = x + 1;
      fqc = (fqc + 1) % 3;
      nl = (nl + z) % 5;
      if (!(!(z % 2 == 0))) {
          l1++;
      }
      if (z % 3 == 0) {
          cy7 = (cy7 * 2) % 7;
      }
      cwq = (cwq + l1) % 9;
      cq = cq + cwq;
      cq += 1;
  }
}