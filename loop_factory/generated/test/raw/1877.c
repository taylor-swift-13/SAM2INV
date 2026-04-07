int main1(){
  int n8v, ds, nx, ss, kd, aqo, psw, uya, a2d, y;

  n8v=1+21;
  ds=0;
  nx=0;
  ss=ds;
  kd=0;
  aqo=n8v;
  psw=0;
  uya=0;
  a2d=ds;
  y=0;

  while (ds < n8v) {
      if ((ds % 2) == 0) {
          nx += 1;
          y++;
      }
      else {
          ss += 1;
          a2d++;
      }
      ds += 1;
      if ((ds%2)==0) {
          kd = psw-kd;
      }
      psw = psw+ss-ss;
      kd = kd + 5;
      uya += 1;
      psw += 2;
      aqo += psw;
  }

}
