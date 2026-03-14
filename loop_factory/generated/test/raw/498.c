int main1(int h,int v){
  int ee9, my, spy, lx7, o, sx, iti;

  ee9=v;
  my=ee9;
  spy=0;
  lx7=(h%28)+10;
  o=-6;
  sx=8;
  iti=my;

  while (lx7>spy) {
      lx7 -= spy;
      iti += my;
      spy = spy + 1;
      o += my;
      v = v+(spy%3);
  }

  while (spy>o) {
      spy = spy - o;
      h = h + sx;
      iti = iti*4+3;
      o = o + 1;
      lx7 = lx7*iti+3;
  }

}
