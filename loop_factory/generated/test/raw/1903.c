int main1(){
  int l, bt, mu, ur, y12, u, b, t75r;

  l=102;
  bt=0;
  mu=l;
  ur=4;
  y12=bt;
  u=0;
  b=25;
  t75r=-3;

  while (bt+4<=l) {
      if (bt%3==2) {
          mu++;
      }
      else {
          ur = ur + 1;
      }
      if (bt%3==0) {
          y12++;
      }
      else {
      }
      b += bt;
      b += t75r;
      t75r = (u)+(t75r);
      if (b+2<l) {
          b = b + u;
      }
      else {
          u += t75r;
      }
      l = (bt+4)-1;
  }

}
