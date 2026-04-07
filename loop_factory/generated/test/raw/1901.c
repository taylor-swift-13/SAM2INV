int main1(int p){
  int uyx6, rsa, cfy, kvt, b2ry, hwqr, au, zr, a2j, j0c;

  uyx6=(p%21)+9;
  rsa=0;
  cfy=rsa;
  kvt=p+2;
  b2ry=p;
  hwqr=25;
  au=p;
  zr=rsa;
  a2j=rsa;
  j0c=uyx6;

  while (rsa < uyx6) {
      a2j = rsa % p;
      if ((a2j == 0)) {
          cfy++;
      }
      if ((a2j == 1)) {
          kvt += 1;
      }
      if ((a2j == 2)) {
          b2ry += 1;
      }
      j0c = a2j;
      hwqr = hwqr + a2j;
      if ((rsa % p == 0)) {
          au++;
      }
      else {
          zr += 1;
      }
      p += zr;
      rsa += 1;
      p += p;
  }

}
