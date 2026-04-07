int main1(){
  int dc, yiy, hek, t9, ez;

  dc=(1%22)+13;
  yiy=0;
  hek=-8;
  t9=0;
  ez=yiy;

  while (1) {
      if (!(yiy < dc)) {
          break;
      }
      hek = hek + 1;
      yiy = (ez = ez + 2*yiy + 1, yiy + 1);
      ez = ez*3+(t9%6)+3;
  }

}
