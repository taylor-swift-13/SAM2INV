int main1(int c){
  int ty, ja, pa, ajje, pl;

  ty=c*5;
  ja=ty;
  pa=0;
  ajje=0;
  pl=8;

  while (ajje<=ty-1) {
      ajje += 1;
      pa = pa + c;
      pl = pl + pa;
  }

  while (pa+4<=ja) {
      ty += pl;
      pl = pl + ty;
      ja = (pa+4)-1;
  }

}
