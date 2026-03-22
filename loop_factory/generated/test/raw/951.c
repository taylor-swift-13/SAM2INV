int main1(int m,int n){
  int t, tonb, tz, hi;

  t=n;
  tonb=0;
  tz=0;
  hi=0;

  while (1) {
      if (!(tonb<t)) {
          break;
      }
      if (tz+4<=t) {
          tz += 4;
      }
      else {
          tz = t;
      }
      n = n + 3;
      hi += tz;
      m += tz;
      tonb = t;
  }

}
