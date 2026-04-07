int main1(int c){
  int fmxv, yuo, o1no, nrz, b95;

  fmxv=0;
  yuo=(c%60)+60;
  o1no=(c%9)+2;
  nrz=0;
  b95=0;

  while (1) {
      if (yuo<=o1no*nrz+b95) {
          break;
      }
      if (b95==o1no-1) {
          b95 = 0;
          nrz++;
      }
      else {
          b95++;
      }
      c = c + fmxv;
  }

}
