int main1(){
  int xp, fo8v, s65, ld, iyb, hy, m5, ir5;

  xp=1;
  fo8v=4;
  s65=xp;
  ld=6;
  iyb=-5;
  hy=fo8v;
  m5=3;
  ir5=0;

  while (fo8v+1<=xp) {
      if (!(!(fo8v<xp/2))) {
          s65 = s65 + 1;
      }
      else {
          s65 += ld;
      }
      if ((fo8v%2)==0) {
          ld = hy-ld;
      }
      m5 += s65;
      iyb = iyb+(fo8v%2);
      ir5 = ir5 + 3;
      m5 = ld+iyb+hy;
      ld++;
      hy = hy + fo8v;
      xp = (fo8v+1)-1;
  }

}
