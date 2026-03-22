int main1(int g){
  int px, ufr, y, seq, s9x;

  px=g*4;
  ufr=0;
  y=1;
  seq=0;
  s9x=0;

  while (1) {
      if (!(y<=px)) {
          break;
      }
      seq = seq+2*y-1;
      y++;
      s9x = s9x+px-ufr;
  }

  while (s9x<=px-1) {
      s9x++;
      seq = (px)+(-(s9x));
      y = y + seq;
  }

}
