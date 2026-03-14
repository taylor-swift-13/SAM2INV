int main1(int g,int v){
  int j6v, x, s, qf, d, hf1a;

  j6v=27;
  x=j6v;
  s=0;
  qf=(g%28)+10;
  d=v;
  hf1a=8;

  while (qf>s) {
      qf = qf - s;
      v++;
      s++;
      d += x;
      d = d*2;
  }

  while (1) {
      if (!(qf>x)) {
          break;
      }
      qf -= x;
      v = v + 3;
      d = d+j6v-hf1a;
      g = (1)+(g);
      x = x + 1;
  }

}
