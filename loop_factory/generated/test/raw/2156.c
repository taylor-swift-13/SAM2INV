int main1(int l){
  int g4p, pon, jg4, v3, sun;

  g4p=l+9;
  pon=0;
  jg4=0;
  v3=g4p;
  sun=l;

  while (pon < g4p) {
      l = l+g4p-pon;
      jg4 = (pon++, jg4 + v3);
      v3 += sun;
      pon = g4p;
  }

}
