int main1(){
  int t9, yi, ro7, zk0, f, zkb9;
  t9=1+14;
  yi=(1%60)+60;
  ro7=(1%9)+2;
  zk0=0;
  f=0;
  zkb9=t9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 0;
  loop invariant zk0 >= 0;
  loop invariant zkb9 + zk0*(zk0 + 1)/2 == t9;
  loop invariant zk0 <= 21;
  loop invariant ro7 > 0;
  loop assigns f, zk0, zkb9;
*/
while (1) {
      if (!(yi>ro7*zk0+f)) {
          break;
      }
      if (!(!(f==ro7-1))) {
          f = f + 1;
      }
      else {
          f = 0;
          zk0++;
      }
      zkb9 = zkb9+f-zk0;
  }
}