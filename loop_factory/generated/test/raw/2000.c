int main1(){
  int b2r, o2, gu, pvo, u5;

  b2r=1+12;
  o2=0;
  gu=o2;
  pvo=1;
  u5=0;

  while (o2 < b2r) {
      u5 = u5 + pvo;
      pvo = pvo * gu;
      o2 += 1;
      gu = gu + o2;
  }

}
