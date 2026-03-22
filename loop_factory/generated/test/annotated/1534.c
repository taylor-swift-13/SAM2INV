int main1(){
  int fd, c, qvc6, x, m0, pmo, o, bh0;
  fd=(1%25)+15;
  c=0;
  qvc6=c;
  x=fd;
  m0=c;
  pmo=c;
  o=1;
  bh0=fd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= qvc6;
  loop invariant qvc6 <= fd/2;
  loop invariant ((c <= fd/2) ==> (qvc6 == c));
  loop invariant ((c > fd/2) ==> (qvc6 == fd - c));
  loop invariant ((c <= fd/2) ==> (x == fd + c));
  loop invariant ((c > fd/2) ==> (x == 2*fd - c));
  loop invariant 0 <= c <= fd;
  loop invariant -c <= qvc6 <= c;
  loop invariant 16 - c <= x <= 16 + c;
  loop invariant 16 <= bh0 <= 17;
  loop invariant bh0 == fd + (c/9);
  loop assigns c, qvc6, x, bh0, o, m0, pmo;
*/
while (c < fd) {
      c = c + 1;
      if (!(!(c <= fd/2))) {
          qvc6 = qvc6 + 1;
          x = x + 1;
      }
      else {
          qvc6--;
          x--;
      }
      if ((c%9)==0) {
          bh0++;
      }
      o += x;
      m0 += qvc6;
      pmo += qvc6;
      pmo = pmo - 1;
      m0++;
  }
}