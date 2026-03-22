int main1(int v){
  int an, bku, d7, mr, sh, y72, r;

  an=17;
  bku=0;
  d7=0;
  mr=0;
  sh=-6;
  y72=bku;
  r=an;

  while (d7<an) {
      mr = mr + d7;
      d7 += 1;
      sh = sh + an;
      y72 += r;
      r = r + sh;
      y72 += bku;
  }

  while (1) {
      y72++;
      if (y72>=an) {
          break;
      }
  }

}
