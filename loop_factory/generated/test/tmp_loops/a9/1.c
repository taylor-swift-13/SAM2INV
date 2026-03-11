int main1(int c,int w){
  int mqj, ll, u3h, s;

  mqj=w*2;
  ll=0;
  u3h=2;
  s=1;

  while (ll<=mqj-1) {
      if (u3h>=9) {
          s = -1;
      }
      if (!(u3h>2)) {
          s = 1;
      }
      u3h = u3h + s;
      ll = ll + 1;
  }

}
