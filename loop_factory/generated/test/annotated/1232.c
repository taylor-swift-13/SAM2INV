int main1(){
  int p4, ju4r, f3, x, ll, f;
  p4=1+4;
  ju4r=p4;
  f3=3;
  x=ju4r;
  ll=0;
  f=ju4r;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p4 == 5;
  loop invariant x >= 5;
  loop invariant f3 >= 3;
  loop invariant ll == 6*(f - p4);
  loop invariant f == p4 || f == p4 + 1;
  loop assigns f, f3, x, ll;
*/
while (1) {
      if (f>p4) {
          break;
      }
      f3 += x;
      x += ll;
      ll += 6;
      f = (1)+(f);
      f3 = f3*f3+f3;
  }
}