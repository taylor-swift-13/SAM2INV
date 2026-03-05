int main1(){
  int jb, o, pf1t;

  jb=1+5;
  o=3;
  pf1t=0;

  for (; o<jb; o = o + 1) {
      pf1t++;
      if (pf1t>=3) {
          pf1t = pf1t - 3;
          pf1t++;
      }
  }

}
