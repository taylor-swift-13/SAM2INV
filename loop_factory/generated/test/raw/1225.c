int main1(int r,int l){
  int qs3, ar, krk, k8, a8, aj;

  qs3=r;
  ar=r;
  krk=0;
  k8=-4;
  a8=-3;
  aj=-6;

  while (a8<=qs3) {
      ar += krk;
      krk = krk + k8;
      a8 = a8 + 1;
      k8 += 4;
      r = r+a8+ar;
      aj = aj+k8+k8;
  }

}
