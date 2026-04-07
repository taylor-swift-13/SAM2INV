int main1(int y){
  int aq, c00, lmha, re, l0, q;

  aq=y+16;
  c00=0;
  lmha=aq;
  re=aq;
  l0=12;
  q=-5;

  while (1) {
      if (!(c00 < aq && l0 - (c00 + 1) * y >= 0)) {
          break;
      }
      lmha = lmha*2+2;
      q = q+(l0%6);
      c00 = c00 + 1;
      re = (2)+(re*lmha);
  }

}
