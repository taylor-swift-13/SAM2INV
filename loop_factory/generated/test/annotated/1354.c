int main1(){
  int cj2, qd, rp, tdt, mu, n;
  cj2=1+24;
  qd=0;
  rp=(1%28)+8;
  tdt=(1%22)+5;
  mu=0;
  n=cj2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((tdt == 6  && rp == 9  && mu == 0  && n == 25) ||
                    (tdt == 3  && rp == 18 && mu == 0  && n == 650) ||
                    (tdt == 1  && rp == 36 && mu == 18 && n == 423150) ||
                    (tdt == 0  && rp == 72 && mu == 54 && n > 0));
  loop invariant rp % 9 == 0;
  loop invariant tdt >= 0;
  loop invariant tdt <= 6;
  loop invariant rp >= 9;
  loop invariant mu >= 0;
  loop invariant mu <= 54;
  loop invariant rp * tdt <= 54;
  loop invariant n >= cj2;
  loop invariant qd == 0;
  loop invariant cj2 == 25;
  loop invariant n > 0;
  loop assigns mu, tdt, rp, n;
*/
while (tdt!=0) {
      if (tdt%2==1) {
          mu += rp;
          tdt = tdt - 1;
      }
      tdt = tdt/2;
      rp = 2*rp;
      n = n + qd;
      n = n*n+n;
  }
}