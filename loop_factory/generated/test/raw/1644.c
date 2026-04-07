int main1(){
  int w8, g4, hnq, h;

  w8=1*5;
  g4=0;
  hnq=0;
  h=5;

  while (1) {
      if (!(g4<w8&&h>0)) {
          break;
      }
      g4 += 1;
      hnq += h;
      h = h - 1;
  }

}
