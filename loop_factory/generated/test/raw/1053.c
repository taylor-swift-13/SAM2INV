int main1(){
  int kha, s, bhb, pn9h, f, h9;

  kha=1-7;
  s=0;
  bhb=5;
  pn9h=-4;
  f=s;
  h9=s;

  while (pn9h<kha) {
      pn9h += 1;
      bhb = bhb + 1;
      h9 = h9 + pn9h;
      f = f*2;
  }

  while (1) {
      kha = kha + pn9h;
      bhb += kha;
      pn9h += 1;
      f = f + 1;
      if (f>=s) {
          break;
      }
  }

}
