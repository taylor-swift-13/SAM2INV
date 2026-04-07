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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ds <= n8v;
  loop invariant nx == y;
  loop invariant a2d == ss;
  loop invariant aqo == n8v + ds*(ds + 1);
  loop invariant ss == ds / 2;
  loop invariant uya == ds;
  loop invariant y  == ((ds + 1) / 2);
  loop invariant psw == 2 * uya;
  loop invariant aqo == 22 + ds*(ds+1);
  loop invariant (ds % 2 == 0) ==> (kd == ds);
  loop invariant (ds % 2 != 0) ==> (kd == ds + 4);
  loop assigns nx, y, ss, a2d, ds, kd, psw, uya, aqo;
*/
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