int main1(){
  int cp, vh5, ujb, vis, k, s;

  cp=55;
  vh5=cp;
  ujb=(1%40)+2;
  vis=0;
  k=8;
  s=2;

  while (ujb!=vis) {
      vis = ujb;
      k = k+vis-vis;
      ujb = (ujb+cp/ujb)/2;
  }

  while (1) {
      if (!(s!=vh5)) {
          break;
      }
      vh5 = s;
      s = (s+cp/s)/2;
      ujb = ujb + k;
  }

}
