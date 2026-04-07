int main1(){
  int r, e, mw, g, ilb, mm, ij, i;

  r=1*4;
  e=3;
  mw=18;
  g=14;
  ilb=0;
  mm=e;
  ij=e;
  i=e;

  while (e<r) {
      if (ilb==0) {
          mw = mw + 3;
          g = g - 3;
          ilb = 1;
      }
      else {
          mw = mw - 3;
          g = g + 3;
          ilb = 0;
      }
      e += 1;
      if (i+2<r) {
          i = i - g;
      }
      mm = mm + ilb;
      mm = mm+ij+i;
  }

}
