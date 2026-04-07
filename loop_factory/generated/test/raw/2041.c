int main1(){
  int hw, l, ugh, sik, hz, en;

  hw=1-5;
  l=0;
  ugh=10;
  sik=hw;
  hz=l;
  en=l;

  while (l < hw) {
      ugh = ugh+(sik%4);
      hz = hz+(en%9);
      l = l + 1;
      en = en + 3;
  }

}
