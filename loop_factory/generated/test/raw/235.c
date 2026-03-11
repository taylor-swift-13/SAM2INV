int main1(int k){
  int vt, w, rp, o8, id, g4;

  vt=29;
  w=1;
  rp=vt;
  o8=0;
  id=vt;
  g4=vt;

  while (w<vt) {
      o8 += rp;
      id = id + w;
      rp = rp + o8;
      w = vt;
  }

  while (1) {
      if (!(rp<=vt-1)) {
          break;
      }
      w = w + k;
      rp++;
      k += 1;
      g4 = g4 + w;
  }

}
