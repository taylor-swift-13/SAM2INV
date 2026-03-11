int main1(int t){
  int g, e, mh0, sw, a5;

  g=47;
  e=g;
  mh0=18;
  sw=1;
  a5=0;

  while (mh0>0&&sw<=g) {
      if (!(mh0<=sw)) {
          mh0 = 0;
      }
      else {
          mh0 -= sw;
      }
      e += 1;
      sw = sw + 1;
      a5 = a5 + 1;
  }

}
