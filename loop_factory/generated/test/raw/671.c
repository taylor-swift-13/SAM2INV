int main1(){
  int gq0r, ru, z58, e, zgl, ckn;

  gq0r=1+14;
  ru=0;
  z58=0;
  e=0;
  zgl=gq0r;
  ckn=ru;

  while (e<gq0r) {
      e += 1;
      z58 = z58 + 1;
      zgl = zgl*2;
      ckn = ckn + z58;
  }

  while (1) {
      if (!(e>4)) {
          break;
      }
      z58 = z58+gq0r*e;
      gq0r = gq0r + e;
      gq0r += ckn;
      e = 4;
  }

}
