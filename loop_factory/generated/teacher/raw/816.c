int main1(int b,int p){
  int t, e, h;

  t=24;
  e=0;
  h=t;

  while (e<=t-3) {
      h = h+h;
      if (h<e+3) {
          h = h+4;
      }
      e = e+3;
  }

}
