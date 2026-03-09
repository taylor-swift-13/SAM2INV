int main1(int w){
  int fsy, jl, y07, rrw, o02h;
  fsy=w+12;
  jl=0;
  y07=1;
  rrw=0;
  o02h=jl;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rrw == (y07 - 1) * (y07 - 1);
  loop invariant o02h == y07 * (y07 + 1) / 2 - 1;
  loop invariant w == \at(w, Pre) + 3 * (y07 - 1);
  loop invariant fsy == \at(w, Pre) + 12;
  loop invariant y07 >= 1;
  loop assigns rrw, y07, w, o02h;
*/
while (1) {
      if (!(y07<=fsy)) {
          break;
      }
      rrw = rrw+2*y07-1;
      y07 += 1;
      w = w + 3;
      o02h += y07;
  }
}