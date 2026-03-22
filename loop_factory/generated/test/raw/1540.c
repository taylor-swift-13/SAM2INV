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
