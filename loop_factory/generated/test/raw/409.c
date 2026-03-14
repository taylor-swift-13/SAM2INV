int main1(int f){
  int akp, ggn, lvg, r, t84g, ax;

  akp=(f%10)+18;
  ggn=0;
  lvg=30;
  r=0;
  t84g=1;
  ax=0;

  for (; lvg>0&&ggn<akp; ggn++) {
      if (lvg<=t84g) {
          ax = lvg;
      }
      else {
          ax = t84g;
      }
      t84g = t84g + 1;
      r = r + ax;
      lvg = lvg - ax;
  }

}
