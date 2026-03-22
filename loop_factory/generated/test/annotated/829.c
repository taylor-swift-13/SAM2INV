int main1(int d){
  int f, e3, x3, fq, t87, nne;
  f=d-4;
  e3=0;
  x3=8;
  fq=f;
  t87=(d%6)+2;
  nne=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == d - 4;
  loop invariant nne == d + (fq - f);
  loop invariant t87 == ((d % 6) + 2) + f * (fq - f) + ((fq - f) * (fq - f + 1)) / 2;
  loop invariant nne == fq + 4;
  loop invariant fq <= f;
  loop invariant f == \at(d, Pre) - 4;
  loop assigns e3, x3, fq, t87, nne;
*/
while (fq<f) {
      e3 = e3*t87+d;
      x3 = x3*t87;
      fq += 1;
      t87 = t87 + fq;
      nne = nne + 1;
  }
}