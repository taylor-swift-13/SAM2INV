int main1(){
  int ly, ea0g, cet, w, kv, l6;

  ly=62;
  ea0g=ly;
  cet=0;
  w=3;
  kv=0;
  l6=ly;

  while (ea0g>0) {
      w += cet;
      l6 = l6 + 1;
      cet = cet + ea0g;
      ea0g = 0;
  }

  while (cet<=l6-1) {
      kv = kv + w;
      ea0g = ea0g + kv;
      w = w*4;
      cet = l6;
  }

}
