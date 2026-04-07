int main1(int i){
  int h0vs, qik5, i9, ys, pm, nvgb, y, qh, n6x;

  h0vs=(i%18)+11;
  qik5=0;
  i9=3;
  ys=h0vs;
  pm=0;
  nvgb=11;
  y=qik5;
  qh=i;
  n6x=h0vs;

  while (qik5<h0vs) {
      if (qik5%3==1) {
          i9 = i9 + 1;
      }
      else {
          ys += 1;
      }
      if (qik5%3==2) {
          pm += 1;
      }
      else {
      }
      nvgb = nvgb+(i9%4);
      i = i + 1;
      y = (y+i9)%3;
      n6x = (n6x+pm)%8;
      qh = qh+(i9%4);
      y = y/2;
      qik5 = h0vs;
  }

}
