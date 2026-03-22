int main1(int m,int l){
  int k31, eya, agu, bck, ehwb, h, fnk3, bn;

  k31=(l%31)+4;
  eya=0;
  agu=-2;
  bck=eya;
  ehwb=5;
  h=0;
  fnk3=16;
  bn=0;

  while (eya < k31) {
      eya++;
      if (!(bn!=0)) {
          bn = 0;
      }
      else {
          bn = 1;
      }
      if (fnk3<k31+2) {
          agu = agu + 5;
      }
      h += bn;
      ehwb = ehwb + 3;
      l += 2;
      fnk3 = fnk3+(eya%2);
      bck += bn;
      agu += 4;
      bck = bck + agu;
      ehwb += bck;
  }

}
