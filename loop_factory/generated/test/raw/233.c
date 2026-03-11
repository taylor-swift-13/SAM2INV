int main1(int r,int b){
  int r9v, uc, t0j, hu, gkx8;

  r9v=161;
  uc=r9v;
  t0j=-6;
  hu=0;
  gkx8=-5;

  while (uc-2>=0) {
      b += 1;
      gkx8 = gkx8+r9v-uc;
      hu = hu+t0j*uc;
      uc = uc + 1;
  }

  while (gkx8>t0j) {
      hu += 1;
      r9v += uc;
      uc = uc + hu;
      gkx8 = t0j;
  }

}
