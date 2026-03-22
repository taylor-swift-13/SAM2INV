int main1(){
  int zk5, wds, l6x;
  zk5=0;
  wds=(1%28)+10;
  l6x=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l6x - 5 <= 6 * zk5;
  loop invariant wds + (zk5*(zk5 - 1))/2 == 11;
  loop invariant 0 <= zk5 <= 5;
  loop assigns wds, zk5, l6x;
*/
while (1) {
      if (!(wds>zk5)) {
          break;
      }
      wds -= zk5;
      zk5 = zk5 + 1;
      l6x = l6x+(wds%7);
  }
}