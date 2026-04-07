int main1(){
  int w, ve, udy, n5;

  w=5;
  ve=0;
  udy=0;
  n5=0;

  while (1) {
      if (!(ve < w)) {
          break;
      }
      ve = ve + 1;
      udy = udy + ve;
      n5 = n5 + (w - ve);
  }

}
