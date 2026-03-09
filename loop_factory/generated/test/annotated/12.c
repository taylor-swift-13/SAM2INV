int main1(int t){
  int b, y, yp5;
  b=t;
  y=-13637;
  yp5=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yp5 >= b;
  loop invariant 4*(y + 13637) == yp5*yp5 - b*b + 2*yp5 - 2*b;
  loop invariant 2*(t - y) == \at(t, Pre) + yp5 + 27274;
  loop invariant 0 <= (yp5 - \at(t, Pre)) / 2;
  loop invariant b == \at(t, Pre);
  loop assigns y, yp5, t;
*/
while (y<=-3) {
      y = y+yp5+2;
      yp5 += 2;
      t += yp5;
      t += 1;
  }
}