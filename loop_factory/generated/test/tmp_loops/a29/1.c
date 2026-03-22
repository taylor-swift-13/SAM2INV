int main1(int h,int w){
  int u0, byx9, ka, au, x, xy6, cv, b2, ix, s;

  u0=(w%40)+16;
  byx9=2;
  ka=3;
  au=4;
  x=0;
  xy6=u0;
  cv=-6;
  b2=w*4;
  ix=-8;
  s=0;

  while (1) {
      if (!(byx9<u0)) {
          break;
      }
      au++;
      x = x + 1;
      if (au>=6) {
          au -= 6;
          ka = ka + 1;
      }
      byx9 = byx9 + 1;
      if ((byx9%7)==0) {
          h = h%2;
      }
      s += 2;
      b2 = b2 + 3;
      ix += x;
      xy6 = xy6*2+2;
      cv = cv*xy6+2;
  }

}
