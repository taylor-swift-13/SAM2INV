int main1(int u,int d){
  int pk, r5, fg, ev, d05, o;
  pk=0;
  r5=d;
  fg=pk;
  ev=3;
  d05=(d%35)+8;
  o=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r5 >= d;
  loop invariant ev == fg + 3;
  loop invariant fg >= 0;
  loop invariant d05 <= (\at(d, Pre) % 35) + 8;
  loop invariant r5 >= \at(d, Pre);
  loop assigns ev, r5, fg, d05, o;
*/
while (1) {
      if (!(d05>=1)) {
          break;
      }
      ev = ev+d05*d05;
      r5 = r5+fg*fg;
      fg = fg+d05*d05;
      d05--;
      o = o + r5;
  }
}