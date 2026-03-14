int main1(){
  int l4, m8, t0, xra, t, uqy;

  l4=1;
  m8=1;
  t0=1;
  xra=3;
  t=0;
  uqy=m8;

  while (t0<=l4) {
      xra = xra+2*t0-1;
      t += l4;
      t0 += 1;
  }

  while (uqy<m8) {
      xra = m8-uqy;
      uqy += 4;
      l4 = l4 + xra;
  }

}
