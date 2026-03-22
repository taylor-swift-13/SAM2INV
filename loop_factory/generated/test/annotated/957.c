int main1(int c,int d){
  int dlw, hln, l;
  dlw=d+5;
  hln=0;
  l=d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == \at(d, Pre) + 2*hln;
  loop invariant c == \at(c, Pre) + (hln * (hln + 1)) / 2;
  loop invariant dlw == \at(d, Pre) + 5;
  loop invariant d - l == hln;
  loop invariant 0 <= hln;
  loop assigns l, hln, d, c;
*/
while (hln<dlw) {
      l += 2;
      hln++;
      d = d + 3;
      c += hln;
  }
}