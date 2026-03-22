int main1(int u){
  int w, t25, atw, f, b;
  w=u;
  t25=0;
  atw=t25;
  f=t25;
  b=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == \at(u, Pre);
  loop invariant b == w;
  loop invariant f % 2 == 0;
  loop invariant atw == t25 * (b % 4);
  loop invariant t25 >= 0;
  loop invariant f >= 2 * t25;
  loop assigns f, atw, t25;
*/
while (1) {
      if (!(t25 < w)) {
          break;
      }
      f = f*2+(f%2)+2;
      atw = atw+(b%4);
      t25 = t25 + 1;
  }
}