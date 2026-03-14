int main1(){
  int an, a6, w0;

  an=1;
  a6=0;
  w0=an;

  while (a6<an) {
      w0 = an-a6;
      a6++;
      if (w0+6<an) {
          w0 += 1;
      }
  }

  while (1) {
      if (!(an<=a6-1)) {
          break;
      }
      an = an + 1;
  }

}
