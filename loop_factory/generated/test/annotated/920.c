int main1(int e,int y){
  int pp, b7ey, u;
  pp=(y%40)+6;
  b7ey=1;
  u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pp == (y % 40) + 6;
  loop invariant 0 <= u;
  loop invariant 1 <= b7ey;
  loop invariant e == \at(e, Pre) + (2*b7ey) - 2 + u;
  loop invariant e >= \at(e,Pre) + 3*u;
  loop assigns e, u, b7ey;
*/
while (b7ey<=pp) {
      b7ey = 2*b7ey;
      u = u + 1;
      e = e + b7ey;
      e += 1;
  }
}