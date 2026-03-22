int main1(int c){
  int nfh, kn, e, ltu;
  nfh=c+24;
  kn=0;
  e=1;
  ltu=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(c, Pre) + kn*kn + 2*kn;
  loop invariant e == (kn+1)*(kn+1);
  loop invariant ltu == 2*kn + 1;
  loop invariant kn >= 0;
  loop invariant nfh == \at(c, Pre) + 24;
  loop assigns c, e, kn, ltu;
*/
while (1) {
      if (!(e<=nfh)) {
          break;
      }
      ltu += 2;
      kn++;
      c = c + ltu;
      e = e + ltu;
  }
}