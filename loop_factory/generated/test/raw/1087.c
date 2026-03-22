int main1(int c){
  int i, ppm, w, ai, lv, s5o;

  i=c*4;
  ppm=i;
  w=0;
  ai=(c%28)+10;
  lv=i;
  s5o=c;

  while (ai>w) {
      ai = ai - w;
      w += 1;
      s5o = s5o + w;
      c = c+(w%7);
      lv = ((w%3))+(lv);
  }

  for (; lv+1<=ppm; lv++) {
  }

}
