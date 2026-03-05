int main67(int t,int k){
  int w5z8, r, ue8, v, dw, mwyl, o5x, nrh, hdr0;

  w5z8=(k%6)+7;
  r=w5z8+2;
  ue8=0;
  v=0;
  dw=-2;
  mwyl=0;
  o5x=t+13;
  nrh=0;
  hdr0=0;

  while (1) {
      if (!(r>w5z8)) {
          break;
      }
      ue8++;
      v += ue8;
      t = t+(ue8%5);
      mwyl = mwyl+(ue8%4);
      dw = dw+(v%5);
      k = k+w5z8-r;
  }

  while (1) {
      if (!(hdr0<o5x)) {
          break;
      }
      hdr0 = o5x-hdr0;
      hdr0 = hdr0 + 1;
      t += o5x;
      k = k - 1;
      t += 1;
      k += nrh;
  }

}
