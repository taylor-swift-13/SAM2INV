int main1(){
  int zmf, k, d4n3, z, e;

  zmf=50;
  k=zmf;
  d4n3=0;
  z=0;
  e=zmf;

  while (z<zmf) {
      z += 1;
      e = e + zmf;
      d4n3++;
      e = e*2;
  }

  while (d4n3<=z-1) {
      e = e+k*d4n3;
      k = k+(e%3);
      d4n3 = z;
  }

}
