int main1(int r,int o){
  int h, ek, d, dvu;
  h=r+22;
  ek=0;
  d=2;
  dvu=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == r + 22;
  loop invariant 2 <= d <= 6;
  loop invariant (h >= 0) ==> (0 <= ek <= h);
  loop invariant (d % 2) == (ek % 2);
  loop invariant (dvu == -1) || (dvu == 1);
  loop invariant 0 <= ek;
  loop invariant -ek <= d - 2 <= ek;
  loop assigns ek, d, dvu;
*/
while (ek<h) {
      if (d>=6) {
          dvu = -1;
      }
      if (!(d>2)) {
          dvu = 1;
      }
      d = d + dvu;
      ek++;
  }
}