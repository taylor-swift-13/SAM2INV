int main1(){
  int vq, hb, v, c6nc, xu;

  vq=57;
  hb=vq;
  v=-1;
  c6nc=0;
  xu=hb;

  while (hb>0) {
      if (!(!(v+1<=vq))) {
          v++;
      }
      else {
          v = vq;
      }
      xu = xu+v-v;
      c6nc = c6nc + 3;
      xu = xu + xu;
      hb = 0;
  }

}
