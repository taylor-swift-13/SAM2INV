int main1(){
  int a3y, za, d, orb, r;

  a3y=0;
  za=0;
  d=(1%28)+10;
  orb=0;
  r=a3y;

  while (1) {
      if (!(d>za)) {
          break;
      }
      d = d - za;
      r += d;
      za = (1)+(za);
      orb = orb+(d%5);
  }

}
