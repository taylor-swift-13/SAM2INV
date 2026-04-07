int main1(int w){
  int ypw, r, p0, tti;
  ypw=(w%7)+14;
  r=0;
  p0=ypw;
  tti=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ypw == (\at(w, Pre) % 7) + 14;
  loop invariant tti >= 8;
  loop invariant p0 >= ypw;
  loop invariant w == \at(w, Pre) + r;
  loop invariant 0 <= r <= ypw;
  loop assigns w, r, tti, p0;
*/
while (r < ypw) {
      w += 1;
      r = r + 1;
      tti = tti+(tti%7);
      p0 += p0;
  }
}