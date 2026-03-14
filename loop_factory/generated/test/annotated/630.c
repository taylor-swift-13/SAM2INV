int main1(int z,int q){
  int i2w, oj, wkmv, a3, w, u, zh;
  i2w=47;
  oj=0;
  wkmv=0;
  a3=0;
  w=0;
  u=3;
  zh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zh == i2w * oj;
  loop invariant 0 <= oj;
  loop invariant oj <= i2w;
  loop invariant 0 <= w;
  loop invariant w < 5;
  loop invariant 0 <= a3;
  loop invariant a3 < 5;
  loop invariant i2w == 47;
  loop invariant u == 3;
  loop assigns a3, wkmv, w, zh, oj;
*/
while (1) {
      if (!(oj<i2w)) {
          break;
      }
      a3 = oj%5;
      if (oj>=u) {
          w = (oj-u)%5;
          wkmv = wkmv+a3-w;
      }
      else {
          wkmv += a3;
      }
      zh += i2w;
      oj++;
  }
}